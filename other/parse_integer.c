#include <defs.h>
#include <ctype.h>

#define KSTRTOX_OVERFLOW      (1U << 31)

#define ULLONG_MAX   (~0ULL)

typedef unsigned int u32;

typedef unsigned long long u64;


/**
 * div64_u64 - unsigned 64bit divide with 64bit divisor
 */
/*@ requires divisor != 0;
    ensures \result == dividend / divisor;
 */
static inline u64 div64_u64(u64 dividend, u64 divisor)
{
	return dividend / divisor;
}

/**
 * div_u64_rem - unsigned 64bit divide with 32bit divisor with remainder
 *
 * This is commonly provided by 32bit archs to provide an optimized 64bit
 * divide.
 */
/*@ requires divisor != 0;
    requires \valid(remainder);
    assigns *remainder;
    ensures \result   == dividend / divisor;
    ensures *remainder == dividend % divisor;
 */
static inline u64 div_u64_rem(u64 dividend, u32 divisor, u32 *remainder)
{
	*remainder = dividend % divisor;
	return dividend / divisor;
}

/**
 * div_u64 - unsigned 64bit divide with 32bit divisor
 *
 * This is the most common 64bit divide and should be used if possible,
 * as many 32bit archs can optimize this variant better than a full 64bit
 * divide.
 */
#ifndef div_u64
/*@ requires divisor != 0;
    assigns \nothing;
    ensures \result == dividend / divisor;
 */
static inline u64 div_u64(u64 dividend, u32 divisor)
{
	u32 remainder;
	return div_u64_rem(dividend, divisor, &remainder);
}
#endif


/*
 * Convert non-negative integer string representation in explicitly given radix
 * to an integer.
 * Return number of characters consumed maybe or-ed with overflow bit.
 * If overflow occurs, result integer (incorrect) is still returned.
 *
 * Don't you dare use this function.
 */

/*@ requires \valid(s);
    requires \valid(p);
    requires base == 16 || base == 10 || base == 8;
    assigns *p;
 */
unsigned int _parse_integer(const char *s, unsigned int base, unsigned long long *p)
{
	unsigned long long res;
	unsigned int rv;

	res = 0;
	rv = 0;
	while (*s) {
		unsigned int val;

		if ('0' <= *s && *s <= '9')
			val = *s - '0';
		else if ('a' <= _tolower(*s) && _tolower(*s) <= 'f')
			val = _tolower(*s) - 'a' + 10;
		else
			break;

		if (val >= base)
			break;
		/*
		 * Check for overflow only if we are within range of
		 * it in the max base we support (16)
		 */
		if (unlikely(res & (~0ull << 60))) {
			if (res > div_u64(ULLONG_MAX - val, base))
				rv |= KSTRTOX_OVERFLOW;
		}
		res = res * base + val;
		rv++;
		s++;
	}
	*p = res;
	return rv;
}
