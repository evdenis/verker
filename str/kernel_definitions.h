#ifndef __KERNEL_DEFINITIONS_H__
#define __KERNEL_DEFINITIONS_H__

#define E2BIG 7

#define EINVAL 22

#define NULL ((void *)0)

#define PAGE_SHIFT 12

#define REPEAT_BYTE(x) ((~0ul / 0xff) * (x))

#define _S 0x20

#define __AC(X,Y) (X ##Y)

#define __BUG_C0 "2:\t.long 1b - 2b, %c0 - 2b\n"

#define ___PASTE(a,b) a ##b

#define __max(t1,t2,max1,max2,x,y) ({ t1 max1 = (x); t2 max2 = (y); (void) (&max1 == &max2); max1 > max2 ? max1 : max2; })

#define __visible __attribute__((externally_visible))

#define annotate_unreachable() 

#define barrier_data(ptr) __asm__ __volatile__("": :"r"(ptr) :"memory")

#define unlikely(x) __builtin_expect(!!(x), 0)

#define zero_bytemask(mask) (mask)

#define WORD_AT_A_TIME_CONSTANTS { REPEAT_BYTE(0x01), REPEAT_BYTE(0x80) }

#define _AC(X,Y) __AC(X,Y)

#define __PASTE(a,b) ___PASTE(a,b)

#define __ismask(x) (_ctype[(int)(unsigned char)(x)])

#define tolower(c) __tolower(c)

#define unreachable() do { annotate_unreachable(); __builtin_unreachable(); } while (0)

#define BUG() do { asm volatile("1:\tud2\n" ".pushsection __bug_table,\"a\"\n" __BUG_C0 "\t.word %c1, 0\n" "\t.org 2b+%c2\n" ".popsection" : : "i" (__FILE__), "i" (__LINE__), "i" (sizeof(struct bug_entry))); unreachable(); } while (0)

#define PAGE_SIZE (_AC(1,UL) << PAGE_SHIFT)

#define __UNIQUE_ID(prefix) __PASTE(__PASTE(__UNIQUE_ID_, prefix), __COUNTER__)

#define isspace(c) ((__ismask(c)&(_S)) != 0)

#define BUG_ON(condition) do { if (unlikely(condition)) BUG(); } while (0)

#define max(x,y) __max(typeof(x), typeof(y), __UNIQUE_ID(max1_), __UNIQUE_ID(max2_), x, y)

enum {
 false = 0,
 true = 1
};

typedef long __kernel_long_t;

typedef unsigned long __kernel_ulong_t;

typedef _Bool bool;

typedef unsigned long long u64;

typedef unsigned char u8;

struct bug_entry {
 signed int bug_addr_disp;
 signed int file_disp;
 unsigned short line;
 unsigned short flags;
};

struct word_at_a_time {
 const unsigned long one_bits, high_bits;
};

typedef __kernel_ulong_t __kernel_size_t;

typedef __kernel_long_t __kernel_ssize_t;

typedef __kernel_size_t size_t;

typedef __kernel_ssize_t ssize_t;
//------------------------------------------------------------------------------

extern const unsigned char _ctype[];

static inline unsigned char __tolower(unsigned char c);

static inline unsigned long create_zero_mask(unsigned long bits);

static inline unsigned long find_zero(unsigned long mask);

static inline unsigned long has_zero(unsigned long a, unsigned long *bits, const struct word_at_a_time *c);

static inline unsigned long prep_zero_mask(unsigned long a, unsigned long bits, const struct word_at_a_time *c);

extern void *memcpy(void *to, const void *from, size_t len);

void *memset(void *s, int c, size_t n);

#endif // __KERNEL_DEFINITIONS_H__
