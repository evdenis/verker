#include "check_bytes8.h"

static void *check_bytes8(const u8 *start, u8 value, unsigned int bytes)
{
	/*@ loop invariant 0 <= bytes <= \at(bytes,Pre);
	    loop invariant \at(start,Pre) <= start <= \at(start,Pre) + \at(bytes,Pre);
	    loop invariant start - \at(start,Pre) == \at(bytes,Pre) - bytes;
	    loop invariant \forall u8 *i; \at(start,Pre) <= i < start ==> *i == value;
	    loop variant bytes;
	 */
	while (bytes) {
		if (*start != value)
			return (void *)start;
		start++;
		bytes--;
	}
	//@ assert bytes == 0;
	return NULL;
}
