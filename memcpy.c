#include "memcpy.h"

void *memcpy(void *dest, const void *src, size_t count)
{
	char *tmp = dest;
	const char *s = src;
	//@ ghost size_t ocount = count;

	/*@ loop invariant 0 <= count <= ocount;
	    loop invariant (char *)dest <= tmp <= (char *)dest + ocount;
	    loop invariant (char *)src <= s <= (char *)src + ocount;
	    loop invariant tmp - dest == s - src == ocount - count;
	    loop invariant \forall integer i; 0 <= i < ocount - count ==>
	                   ((char *)dest)[i] == ((char *)src)[i];
	    loop variant count;
	 */
	while (count--/*@%*/)
		*tmp++ = *s++;
	//@ assert count == (size_t %)(-1);
	return dest;
}