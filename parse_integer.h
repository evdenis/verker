#ifndef __PARSE_INTEGER_H__
#define __PARSE_INTEGER_H__

#include "kernel_definitions.h"
#include "strlen.h"


static inline char _tolower(const char c)
{
	return c | 0x20;
}

/*@ requires \valid(remainder);
    requires divisor != 0;
    assigns *remainder;
    ensures *remainder == dividend % divisor;
    ensures \result == dividend / divisor;
 */
static inline u64 div_u64_rem(u64 dividend, u32 divisor, u32 *remainder)
{
	*remainder = dividend % divisor;
	return dividend / divisor;
}

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

#define KSTRTOX_OVERFLOW (1U << 31)

#endif // __PARSE_INTEGER_H__