#ifndef __PARSE_INTEGER_H__
#define __PARSE_INTEGER_H__

#define ULLONG_MAX (~0ULL)

#define unlikely(x) __builtin_expect(!!(x), 0)

typedef unsigned int u32;

typedef unsigned long long u64;

typedef unsigned char uint8_t;

typedef unsigned long __kernel_ulong_t;

typedef __kernel_ulong_t __kernel_size_t;

typedef __kernel_size_t size_t;

static inline char _tolower(const char c)
{
	return c | 0x20;
}

static inline u64 div_u64_rem(u64 dividend, u32 divisor, u32 *remainder)
{
	*remainder = dividend % divisor;
	return dividend / divisor;
}

#ifndef div_u64
static inline u64 div_u64(u64 dividend, u32 divisor)
{
	u32 remainder;
	return div_u64_rem(dividend, divisor, &remainder);
}
#endif

#define KSTRTOX_OVERFLOW (1U << 31)

#endif // __PARSE_INTEGER_H__
