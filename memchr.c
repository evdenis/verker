#include "memchr.h"

void *memchr(const void *s, int c, size_t n)
{
	const unsigned char *p = s;
	/*@ loop invariant 0 <= n <= \at(n,Pre);
	    loop invariant (u8 *)s <= p <= (u8 *)s + \at(n,Pre);
	    loop invariant p - s == \at(n,Pre) - n;
	    loop invariant \forall u8 *k; (u8 *)s <= k < p ==> *k != (u8 %) c;
	    loop variant n;
	 */
	while (n-- /*@%*/ != 0) {
		if ((unsigned char)/*@%*/c == *p++) {
			return (void *)(p - 1);
		}
	}
	//@ assert n == (size_t %)(-1);
	return NULL;
}
