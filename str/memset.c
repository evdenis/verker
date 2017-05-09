#include "memset.h"

void *memset(void *s, int c, size_t count)
{
	char *xs = s;
	//@ ghost size_t ocount = count;

	/*@ loop invariant 0 <= count <= ocount;
	    loop invariant (char *)s <= xs <= (char *)s + ocount;
	    loop invariant xs - s == ocount - count;
	    loop invariant \forall char *p; (char *)s <= p < xs ==> *p == (char %)c;
	    loop variant count;
	 */
	while (count--/*@%*/)
		*xs++ = (char)/*@%*/c; // CODE_CHANGE:
	//@ assert count == (size_t %)(-1);
	return s;
}