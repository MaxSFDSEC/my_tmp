#include <locale.h>
#include <wchar.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <cpuid.h>
#include <unistd.h>
#include <ctype.h>

#include <sys/ioctl.h>
#include <net/if.h>
#include <netinet/in.h>

# define SHA_LONG unsigned int

# define SHA256_DIGEST_LENGTH    32

#define MD32_REG_T int

# define SHA_LBLOCK      16
# define SHA_CBLOCK      (SHA_LBLOCK*4)/* SHA treats input data as a
                                        * contiguous array of 32 bit wide
                                        * big-endian values. */

# define SHA256_CBLOCK   (SHA_LBLOCK*4)/* SHA-256 treats input data as a
                                        * contiguous array of 32 bit wide
                                        * big-endian values. */

#define HASH_CBLOCK             SHA_CBLOCK

#define HASH_CTX SHA256_CTX

#define HASH_LONG               SHA_LONG

typedef struct SHA256state_st {
    SHA_LONG h[8];
    SHA_LONG Nl, Nh;
    SHA_LONG data[SHA_LBLOCK];
    unsigned int num, md_len;
} SHA256_CTX;

static const SHA_LONG K256[64] = {
    0x428a2f98UL, 0x71374491UL, 0xb5c0fbcfUL, 0xe9b5dba5UL,
    0x3956c25bUL, 0x59f111f1UL, 0x923f82a4UL, 0xab1c5ed5UL,
    0xd807aa98UL, 0x12835b01UL, 0x243185beUL, 0x550c7dc3UL,
    0x72be5d74UL, 0x80deb1feUL, 0x9bdc06a7UL, 0xc19bf174UL,
    0xe49b69c1UL, 0xefbe4786UL, 0x0fc19dc6UL, 0x240ca1ccUL,
    0x2de92c6fUL, 0x4a7484aaUL, 0x5cb0a9dcUL, 0x76f988daUL,
    0x983e5152UL, 0xa831c66dUL, 0xb00327c8UL, 0xbf597fc7UL,
    0xc6e00bf3UL, 0xd5a79147UL, 0x06ca6351UL, 0x14292967UL,
    0x27b70a85UL, 0x2e1b2138UL, 0x4d2c6dfcUL, 0x53380d13UL,
    0x650a7354UL, 0x766a0abbUL, 0x81c2c92eUL, 0x92722c85UL,
    0xa2bfe8a1UL, 0xa81a664bUL, 0xc24b8b70UL, 0xc76c51a3UL,
    0xd192e819UL, 0xd6990624UL, 0xf40e3585UL, 0x106aa070UL,
    0x19a4c116UL, 0x1e376c08UL, 0x2748774cUL, 0x34b0bcb5UL,
    0x391c0cb3UL, 0x4ed8aa4aUL, 0x5b9cca4fUL, 0x682e6ff3UL,
    0x748f82eeUL, 0x78a5636fUL, 0x84c87814UL, 0x8cc70208UL,
    0x90befffaUL, 0xa4506cebUL, 0xbef9a3f7UL, 0xc67178f2UL
};

#  define HOST_c2l(c,l)   (l =(((unsigned long)(*((c)++)))<<24),          \
                         l|=(((unsigned long)(*((c)++)))<<16),          \
                         l|=(((unsigned long)(*((c)++)))<< 8),          \
                         l|=(((unsigned long)(*((c)++)))    )           )

#  define HOST_l2c(l,c)   (*((c)++)=(unsigned char)(((l)>>24)&0xff),      \
                         *((c)++)=(unsigned char)(((l)>>16)&0xff),      \
                         *((c)++)=(unsigned char)(((l)>> 8)&0xff),      \
                         *((c)++)=(unsigned char)(((l)    )&0xff),      \
                         l)

# define Sigma0(x)       (ROTATE((x),30) ^ ROTATE((x),19) ^ ROTATE((x),10))
# define Sigma1(x) (ROTATE((x),26) ^ ROTATE((x),21) ^ ROTATE((x),7))
# define sigma0(x)       (ROTATE((x),25) ^ ROTATE((x),14) ^ ((x)>>3))
# define sigma1(x)       (ROTATE((x),15) ^ ROTATE((x),13) ^ ((x)>>10))

# define ROTATE(a,n)     (((a)<<(n))|(((a)&0xffffffff)>>(32-(n))))
# define Ch(x,y,z)       (((x) & (y)) ^ ((~(x)) & (z)))
# define Maj(x,y,z)      (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))

#define HASH_MAKE_STRING(c,s)   do {    \
        unsigned long ll;               \
        unsigned int  nn;               \
        switch ((c)->md_len)            \
        {                               \
            case SHA256_DIGEST_LENGTH:  \
                for (nn=0;nn<SHA256_DIGEST_LENGTH/4;nn++)       \
                {   ll=(c)->h[nn]; (void)HOST_l2c(ll,(s));   }  \
                break;                  \
            default:                    \
                if ((c)->md_len > SHA256_DIGEST_LENGTH) \
                    return 0;                           \
                for (nn=0;nn<(c)->md_len/4;nn++)                \
                {   ll=(c)->h[nn]; (void)HOST_l2c(ll,(s));   }  \
                break;                  \
        }                               \
        } while (0)

static void sha256_block_data_order(SHA256_CTX *ctx, const void *in,
                                    size_t num);

#define HASH_BLOCK_DATA_ORDER   sha256_block_data_order

typedef void *(*memset_t)(void *, int, size_t);
static volatile memset_t memset_func = memset;

void OPENSSL_cleanse(void *ptr, size_t len)
{
    memset_func(ptr, 0, len);
}


int SHA256_Final(unsigned char *md, HASH_CTX *c)
{
    unsigned char *p = (unsigned char *)c->data;
    size_t n = c->num;

    p[n] = 0x80;                /* there is always room for one */
    n++;

    if (n > (HASH_CBLOCK - 8)) {
        memset(p + n, 0, HASH_CBLOCK - n);
        n = 0;
        HASH_BLOCK_DATA_ORDER(c, p, 1);
    }
    memset(p + n, 0, HASH_CBLOCK - 8 - n);

    p += HASH_CBLOCK - 8;
#if   defined(DATA_ORDER_IS_BIG_ENDIAN)
    (void)HOST_l2c(c->Nh, p);
    (void)HOST_l2c(c->Nl, p);
#elif defined(DATA_ORDER_IS_LITTLE_ENDIAN)
    (void)HOST_l2c(c->Nl, p);
    (void)HOST_l2c(c->Nh, p);
#endif
    p -= HASH_CBLOCK;
    HASH_BLOCK_DATA_ORDER(c, p, 1);
    c->num = 0;
    OPENSSL_cleanse(p, HASH_CBLOCK);

    HASH_MAKE_STRING(c, md);
    return 1;
}


#  define ROUND_00_15(i,a,b,c,d,e,f,g,h)          do {    \
        T1 += h + Sigma1(e) + Ch(e,f,g) + K256[i];      \
        h = Sigma0(a) + Maj(a,b,c);                     \
        d += T1;        h += T1;                } while (0)

#  define ROUND_16_63(i,a,b,c,d,e,f,g,h,X)        do {    \
        s0 = X[(i+1)&0x0f];     s0 = sigma0(s0);        \
        s1 = X[(i+14)&0x0f];    s1 = sigma1(s1);        \
        T1 = X[(i)&0x0f] += s0 + s1 + X[(i+9)&0x0f];    \
        ROUND_00_15(i,a,b,c,d,e,f,g,h);         } while (0)

static void sha256_block_data_order(SHA256_CTX *ctx, const void *in,
                                    size_t num)
{
    unsigned MD32_REG_T a, b, c, d, e, f, g, h, s0, s1, T1;
    SHA_LONG X[16];
    int i;
    const unsigned char *data = in;
    const union {
        long one;
        char little;
    } is_endian = {
        1
    };

    while (num--) {

        a = ctx->h[0];
        b = ctx->h[1];
        c = ctx->h[2];
        d = ctx->h[3];
        e = ctx->h[4];
        f = ctx->h[5];
        g = ctx->h[6];
        h = ctx->h[7];

        if (!is_endian.little && sizeof(SHA_LONG) == 4
            && ((size_t)in % 4) == 0) {
            const SHA_LONG *W = (const SHA_LONG *)data;

            T1 = X[0] = W[0];
            ROUND_00_15(0, a, b, c, d, e, f, g, h);
            T1 = X[1] = W[1];
            ROUND_00_15(1, h, a, b, c, d, e, f, g);
            T1 = X[2] = W[2];
            ROUND_00_15(2, g, h, a, b, c, d, e, f);
            T1 = X[3] = W[3];
            ROUND_00_15(3, f, g, h, a, b, c, d, e);
            T1 = X[4] = W[4];
            ROUND_00_15(4, e, f, g, h, a, b, c, d);
            T1 = X[5] = W[5];
            ROUND_00_15(5, d, e, f, g, h, a, b, c);
            T1 = X[6] = W[6];
            ROUND_00_15(6, c, d, e, f, g, h, a, b);
            T1 = X[7] = W[7];
            ROUND_00_15(7, b, c, d, e, f, g, h, a);
            T1 = X[8] = W[8];
            ROUND_00_15(8, a, b, c, d, e, f, g, h);
            T1 = X[9] = W[9];
            ROUND_00_15(9, h, a, b, c, d, e, f, g);
            T1 = X[10] = W[10];
            ROUND_00_15(10, g, h, a, b, c, d, e, f);
            T1 = X[11] = W[11];
            ROUND_00_15(11, f, g, h, a, b, c, d, e);
            T1 = X[12] = W[12];
            ROUND_00_15(12, e, f, g, h, a, b, c, d);
            T1 = X[13] = W[13];
            ROUND_00_15(13, d, e, f, g, h, a, b, c);
            T1 = X[14] = W[14];
            ROUND_00_15(14, c, d, e, f, g, h, a, b);
            T1 = X[15] = W[15];
            ROUND_00_15(15, b, c, d, e, f, g, h, a);

            data += SHA256_CBLOCK;
        } else {
            SHA_LONG l;

            (void)HOST_c2l(data, l);
            T1 = X[0] = l;
            ROUND_00_15(0, a, b, c, d, e, f, g, h);
            (void)HOST_c2l(data, l);
            T1 = X[1] = l;
            ROUND_00_15(1, h, a, b, c, d, e, f, g);
            (void)HOST_c2l(data, l);
            T1 = X[2] = l;
            ROUND_00_15(2, g, h, a, b, c, d, e, f);
            (void)HOST_c2l(data, l);
            T1 = X[3] = l;
            ROUND_00_15(3, f, g, h, a, b, c, d, e);
            (void)HOST_c2l(data, l);
            T1 = X[4] = l;
            ROUND_00_15(4, e, f, g, h, a, b, c, d);
            (void)HOST_c2l(data, l);
            T1 = X[5] = l;
            ROUND_00_15(5, d, e, f, g, h, a, b, c);
            (void)HOST_c2l(data, l);
            T1 = X[6] = l;
            ROUND_00_15(6, c, d, e, f, g, h, a, b);
            (void)HOST_c2l(data, l);
            T1 = X[7] = l;
            ROUND_00_15(7, b, c, d, e, f, g, h, a);
            (void)HOST_c2l(data, l);
            T1 = X[8] = l;
            ROUND_00_15(8, a, b, c, d, e, f, g, h);
            (void)HOST_c2l(data, l);
            T1 = X[9] = l;
            ROUND_00_15(9, h, a, b, c, d, e, f, g);
            (void)HOST_c2l(data, l);
            T1 = X[10] = l;
            ROUND_00_15(10, g, h, a, b, c, d, e, f);
            (void)HOST_c2l(data, l);
            T1 = X[11] = l;
            ROUND_00_15(11, f, g, h, a, b, c, d, e);
            (void)HOST_c2l(data, l);
            T1 = X[12] = l;
            ROUND_00_15(12, e, f, g, h, a, b, c, d);
            (void)HOST_c2l(data, l);
            T1 = X[13] = l;
            ROUND_00_15(13, d, e, f, g, h, a, b, c);
            (void)HOST_c2l(data, l);
            T1 = X[14] = l;
            ROUND_00_15(14, c, d, e, f, g, h, a, b);
            (void)HOST_c2l(data, l);
            T1 = X[15] = l;
            ROUND_00_15(15, b, c, d, e, f, g, h, a);
        }

        for (i = 16; i < 64; i += 8) {
            ROUND_16_63(i + 0, a, b, c, d, e, f, g, h, X);
            ROUND_16_63(i + 1, h, a, b, c, d, e, f, g, X);
            ROUND_16_63(i + 2, g, h, a, b, c, d, e, f, X);
            ROUND_16_63(i + 3, f, g, h, a, b, c, d, e, X);
            ROUND_16_63(i + 4, e, f, g, h, a, b, c, d, X);
            ROUND_16_63(i + 5, d, e, f, g, h, a, b, c, X);
            ROUND_16_63(i + 6, c, d, e, f, g, h, a, b, X);
            ROUND_16_63(i + 7, b, c, d, e, f, g, h, a, X);
        }

        ctx->h[0] += a;
        ctx->h[1] += b;
        ctx->h[2] += c;
        ctx->h[3] += d;
        ctx->h[4] += e;
        ctx->h[5] += f;
        ctx->h[6] += g;
        ctx->h[7] += h;

    }
}

int SHA256_Update(HASH_CTX *c, const void *data_, size_t len)
{
    const unsigned char *data = data_;
    unsigned char *p;
    HASH_LONG l;
    size_t n;

    if (len == 0)
        return 1;

    l = (c->Nl + (((HASH_LONG) len) << 3)) & 0xffffffffUL;
    if (l < c->Nl)              /* overflow */
        c->Nh++;
    c->Nh += (HASH_LONG) (len >> 29); /* might cause compiler warning on
                                       * 16-bit */
    c->Nl = l;

    n = c->num;
    if (n != 0) {
        p = (unsigned char *)c->data;

        if (len >= HASH_CBLOCK || len + n >= HASH_CBLOCK) {
            memcpy(p + n, data, HASH_CBLOCK - n);
            HASH_BLOCK_DATA_ORDER(c, p, 1);
            n = HASH_CBLOCK - n;
            data += n;
            len -= n;
            c->num = 0;
            /*
             * We use memset rather than OPENSSL_cleanse() here deliberately.
             * Using OPENSSL_cleanse() here could be a performance issue. It
             * will get properly cleansed on finalisation so this isn't a
             * security problem.
             */
            memset(p, 0, HASH_CBLOCK); /* keep it zeroed */
        } else {
            memcpy(p + n, data, len);
            c->num += (unsigned int)len;
            return 1;
        }
    }

    n = len / HASH_CBLOCK;
    if (n > 0) {
        HASH_BLOCK_DATA_ORDER(c, data, n);
        n *= HASH_CBLOCK;
        data += n;
        len -= n;
    }

    if (len != 0) {
        p = (unsigned char *)c->data;
        c->num = (unsigned int)len;
        memcpy(p, data, len);
    }
    return 1;
}

int SHA256_Init(SHA256_CTX *c) {
    memset(c, 0, sizeof(*c));
    c->h[0] = 0x6a09e667UL;
    c->h[1] = 0xbb67ae85UL;
    c->h[2] = 0x3c6ef372UL;
    c->h[3] = 0xa54ff53aUL;
    c->h[4] = 0x510e527fUL;
    c->h[5] = 0x9b05688cUL;
    c->h[6] = 0x1f83d9abUL;
    c->h[7] = 0x5be0cd19UL;
    c->md_len = SHA256_DIGEST_LENGTH;
    return 1;
}

/* taken from OpenSSL library */
unsigned char *SHA256(const unsigned char *d, size_t n, unsigned char *md)
{
    SHA256_CTX c;
    static unsigned char m[SHA256_DIGEST_LENGTH];

    if (md == NULL)
        md = m;
    SHA256_Init(&c);
    SHA256_Update(&c, d, n);
    SHA256_Final(md, &c);
    OPENSSL_cleanse(&c, sizeof(c));
    return md;
}

// More AntiVM checks
//  TODO: BIOS name ?
//  TODO: all low level instructions to detect VM ?
//  TODO: arm ?
/*  TODO: what about arm ? */
/*  TODO: I tested everything only in VMWare ! */
#define CHECK_BIT(var,pos) ((var) & (1<<(pos)))

/* Common MACs for well-known VMs 
 * https://www.techrepublic.com/blog/data-center/mac-address-scorecard-for-common-virtual-machine-platforms/
 */


/* TODO: add salt or something more interesting to make it different ? */
#define VMWARE_MAC    "a604e69f601953ca2bfda9759021b9586ca59fdbecb0d2a61d931de725f1fca8" // 00:50:56
#define VMWARE_MAC2   "e3f06b77752346e6ab2730d373ab3b850ef07dbe20f9eb64bee65b6f4ec2ecfa" // 00-0C-29
#define VMWARE_MAC3   "1cac23119319b80b4f89279394d1dcec0ebf5525cf6e2248be0c6f89f3a080e5" // 00-05-69
#define HYPERV_MAC    "980fa460286ba9d6d79cbb802e05ae8c2cfb7751eeb50e19b2c9a0398799db80" // 00-03-FF
#define PARALLELS_MAC "329361a955a9e79e6d245c2d63358491ad4c42522c2e654172cecb243943e74a" // 00-1C-42
#define VIRON_MAC     "75d0e67df1b81567f945a4325995aed8b57ef78a2336c21fb62326950bdf62a4" // 00-0F-4B
#define XEN_MAC       "23365c29dbb43b0f468c80a445fd3539766cbcec3826be1518e206615f3a1b9b" // 00-16-3E
#define SUNVBOX_MAC   "ccc9b3105046dbaaf8457d892939aa4ffdf4229e9c7b1165e7f78c350e940f0e" // 08-00-27

int strcmp_hash(const char *clear_text_str, const char *hash_str) {
    unsigned char digest[SHA256_DIGEST_LENGTH];
    int i = 0;

    /* get SHA256 checksum for the string */    
    SHA256((const unsigned char *)clear_text_str, strlen(clear_text_str), (unsigned char*)&digest);    
    char hash_str2[SHA256_DIGEST_LENGTH*2+1];

    /* converting into string */
    for(i = 0; i < SHA256_DIGEST_LENGTH; i++)
         sprintf(hash_str2, "%02x", (unsigned int)digest[i]);

    if (strlen(hash_str) < strlen(hash_str2))
        return strlen(hash_str);

    /* comparing two hashes */
    for (i = 0; i < strlen(hash_str2); i++) {
        if (hash_str2[i] != hash_str[i])
            return i;
    }
    return 0;
}


int compare_macs(const char *mac_address) {
    if (!strcmp_hash(mac_address, VMWARE_MAC))
        return 1;
    if (!strcmp_hash(mac_address, VMWARE_MAC2))
        return 1;
    if (!strcmp_hash(mac_address, VMWARE_MAC3))
        return 1;
    if (!strcmp_hash(mac_address, HYPERV_MAC))
        return 1;
    if (!strcmp_hash(mac_address, PARALLELS_MAC))
        return 1;
    if (!strcmp_hash(mac_address, VIRON_MAC))
        return 1;
    if (!strcmp_hash(mac_address, XEN_MAC))
        return 1;
    if (!strcmp_hash(mac_address, SUNVBOX_MAC))
        return 1;
    return 0;
}

static
void inline str_to_upper(char *str) {
    int i = 0;
    while(str[i]) {
       str[i] = toupper(str[i]);
       i++;
    }
}

/** The function reads MACs for all available interfaces and checks them
  * against well-known VMs.
  *
  * Parameters:
  *    const char *interface - check against specific interface or specify
  *    NULL to check all available interfaces.
  *
  * NOTE: The function might cause false positives if a target
  *       machine is used as a host for VMs (in this case VM manager
  *       usually installs virtual network adapter which has well-known
  *       MAC address). One solution would be to check only specific
  *       interface (e.g. eth0) which is less likely assigned for VM's
  *       network adapter.
  */
int get_mac_addr(const char *interface) {
    struct ifreq ifr;
    struct ifconf ifc;
    char buf[1024];
    char mac_string[9];

    int sock = socket(AF_INET, SOCK_DGRAM, IPPROTO_IP);
    if (sock == -1) { /* TODO: handle error */ };

    ifc.ifc_len = sizeof(buf);
    ifc.ifc_buf = buf;
    if (ioctl(sock, SIOCGIFCONF, &ifc) == -1) { /* handle error */ }

    struct ifreq* it = ifc.ifc_req;
    const struct ifreq* const end = it + (ifc.ifc_len / sizeof(struct ifreq));

    for (; it != end; ++it) {
        strcpy(ifr.ifr_name, it->ifr_name);

        if (interface != NULL && !strcmp(ifr.ifr_name, interface))
            continue; /* skip not interesting for us interfaces */

        if (ioctl(sock, SIOCGIFFLAGS, &ifr) == 0) {
            if (!(ifr.ifr_flags & IFF_LOOPBACK)) { // don't count loopback
                if (ioctl(sock, SIOCGIFHWADDR, &ifr) == 0) {
                    /* converting MAC into string */
                    snprintf(mac_string, sizeof(mac_string), "%02x-%02x-%02x",
                             toupper((unsigned char)ifr.ifr_hwaddr.sa_data[0]),
                             toupper((unsigned char)ifr.ifr_hwaddr.sa_data[1]),
                             toupper((unsigned char)ifr.ifr_hwaddr.sa_data[2]));
                    mac_string[8] = '\0';
                    str_to_upper(mac_string);
                    if (compare_macs(mac_string)) /* checking the MAC string */
                        return 1;
                }
            }
        }
        else { /* TODO: handle error */ }
    }
    return 0;
}

/** The function returns CPUs count */
int get_cpu_count() {
    return sysconf(_SC_NPROCESSORS_ONLN);
    /* macOS https://stackoverflow.com/questions/150355/programmatically-find-the-number-of-cores-on-a-machine */
}

/* took it from Linux kernel http://lxr.linux.no/#linux+v2.6.39/arch/x86/include/asm/processor.h#L173 */
static inline void native_cpuid(unsigned int *eax, unsigned int *ebx,
                                unsigned int *ecx, unsigned int *edx) {
    /* ecx is often an input as well as an output. */
    asm volatile("cpuid"
            : "=a" (*eax),
              "=b" (*ebx),
              "=c" (*ecx),
              "=d" (*edx)
            : "0" (*eax), "2" (*ecx));
}

#define CHECK_VM        0x00000000
#define CHECK_VMWARE    0x00000001
#define CHECK_MicHV     0x00000002
#define CHECK_KVM       0x00000004 /* not yet implemented */
#define CHECK_PARALLELS 0x00000008
#define CHECK_XENHVM    0x00000010
#define CHECK_VBOX      0x00000020
#define CHECK_POWERVM   0x00000040 /* not yet implemented */
#define CHECK_QEMU      0x00000080 /* not yet implemented */

/* list of known CPU vendors */
#define CPUID_VENDOR_VMWARE       "20363130fb1925091562bf260bb0e279aba45a8741389a9c63f61761c4cdf8cd" //VMwareVMware
#define CPUID_VENDOR_XENHVM       "87d189fd343c361294c284fc9f0d334c58d793b1e00fd2099120d418eff2b579" //XenVMMXenVMM
#define CPUID_VENDOR_MICROSOFT_HV "c637938c6a6bb16526e78f1979cc934584aa36615a02a66ef30caa690b343e5d" //Microsoft Hv
#define CPUID_VENDOR_PARALLELS    "691e119edd51627f3a49b7181855f37b765931af4a4583c5366f3affdb001610" // lrpepyh vr
#define CPUID_VENDOR_VIRTUALBOX   "ad52a7938ee33693ea05375547e4819742dd37a23b8bc5c99b6010323ac85489" //vboxboxvbox

/** The function performs cpuid check against known Virtual Machines.
  * To check against specific virtual machine a user should use parameter
  * flags.
  * Parameters:
  *    int flags - must be specified to check against specific VMs using defines
  *                listed above.
  * NOTE: in case if paravirtualization is switched off in VM settings, this
          function will always return false.
  */

/* the functions below are based on this article https://kb.vmware.com/s/article/1009458 */
int cpu_id_check(int flags) {
    unsigned int eax, ebx, ecx, edx;
    char hyper_vendor_id[13];

    eax = 1;
    native_cpuid(&eax, &ebx, &ecx, &edx);

    if  (CHECK_BIT(ecx, 31)) {
       /* virtualization is enabled! */
       if (flags == CHECK_VM)
           return 1; /* that's all our caller wanted to check */

       /* Our caller wants to check against specific VM,
          let's get a vendor name. */
       eax = 0x40000000;
       native_cpuid(&eax, &ebx, &ecx, &edx);
       memcpy(hyper_vendor_id + 0, &ebx, 4);
       memcpy(hyper_vendor_id + 4, &ecx, 4);
       memcpy(hyper_vendor_id + 8, &edx, 4);
       hyper_vendor_id[12] = '\0';

#ifdef DEBUG
       printf("Vendor ID: %s\n", hyper_vendor_id);
#endif

       /* checking against specific vendor */
       if ((flags & CHECK_VMWARE) && 
           !strcmp_hash(hyper_vendor_id, CPUID_VENDOR_VMWARE)) 
           return 1;
       else if ((flags & CHECK_MicHV) && 
                !strcmp_hash(hyper_vendor_id, CPUID_VENDOR_MICROSOFT_HV)) 
           return 1;
       else if ((flags & CHECK_PARALLELS) && 
                !strcmp_hash(hyper_vendor_id, CPUID_VENDOR_PARALLELS)) 
           return 1;
       else if ((flags & CHECK_XENHVM) && 
                !strcmp_hash(hyper_vendor_id, CPUID_VENDOR_XENHVM)) 
           return 1;
       else if ((flags & CHECK_VBOX) &&
                !strcmp_hash(hyper_vendor_id, CPUID_VENDOR_VIRTUALBOX))
           return 1;
    }
    
    return 0;
}
/*
int dmi_check(void) {         
    char string[10];
    GET_BIOS_SERIAL(string); // we need to implement this function http://git.savannah.gnu.org/cgit/dmidecode.git/
    if (!memcmp(string, "VMware-", 7) || !memcmp(string, "VMW", 3))
        return 1; // DMI contains VMware specific string.
    else
        return 0;
}
*/

int main(int argc, char * argv[]) {
    int i = 0;
    if (cpu_id_check(CHECK_VMWARE))
        printf("Hello VMWare\n");
    printf("Number of CPU cores %d\n", get_cpu_count());
    if (get_mac_addr(NULL))
        printf("Hello VMWare(MAC)\n");
    printf("Hello World\n");

    unsigned char digest[SHA256_DIGEST_LENGTH];
    char string[] = "hello world";
    
    SHA256((unsigned char*)&string, strlen(string), (unsigned char*)&digest);    

    char mdString[SHA256_DIGEST_LENGTH*2+1];

    for(i = 0; i < SHA256_DIGEST_LENGTH; i++)
         sprintf(&mdString[i*2], "%02x", (unsigned int)digest[i]);

    printf("SHA256 digest: %s\n", mdString);

    return 0;
}
