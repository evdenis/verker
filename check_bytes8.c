#include "check_bytes8.h"

static void *check_bytes8(const u8 *start, u8 value, unsigned int bytes)
{
	//@ ghost u8 *ostart = start;
	//@ ghost unsigned int obytes = bytes;

	/*@ loop invariant 0 <= bytes <= obytes;
	    loop invariant ostart <= start <= ostart + obytes;
	    loop invariant start - ostart == obytes - bytes;
	    loop invariant \forall u8 *i; ostart <= i < start ==> *i == value;
	    loop invariant check_bytes8(ostart, value, obytes) == check_bytes8(start, value, bytes);
	    loop variant bytes;
	 */
	while (bytes) {
		if (*start != value)
			return (void *)start;
		start++;
		bytes--;
	}
	//@ assert bytes == 0;
	//@ assert check_bytes8(ostart, value, obytes) == \null;
	return NULL;
}
