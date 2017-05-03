#include "memchr.h"

/*@ requires \typeof(s) <: \type(u8 *);
    requires \valid((u8 *)s+(0..n-1));
    requires c == (u8 %) c;
    assigns \nothing;
    behavior found:
       assumes \exists integer i; 0 <= i < n && ((u8 *)s)[i] == c;
       ensures \base_addr(s) == \base_addr(\result);
       ensures s <= \result <= s + n;
       ensures \exists integer i; 0 <= i < n &&
               (\forall integer j; 0 <= j < i ==> ((u8 *)s)[j] != c) &&
               ((u8 *)s)[i] == c &&
               \result == (u8 *)s + i;
    behavior not_exists:
       assumes \forall integer i; 0 <= i < n ==> ((u8 *)s)[i] != c;
       ensures \result == \null;
    complete behaviors;
    disjoint behaviors;
 */
void *memchr(const void *s, int c, size_t n)
{
	const unsigned char *p = s;
	/*@ loop invariant 0 <= n <= \at(n,Pre);
	    loop invariant \base_addr(s) == \base_addr(p);
	    loop invariant (u8 *)s <= p <= (u8 *)s + \at(n,Pre);
	    loop invariant p - s == \at(n,Pre) - n;
	    loop invariant \forall integer i; 0 <= i < \at(n,Pre) - n ==> ((u8 *)s)[i] != c;
	    loop variant n;
	 */
	while (n-- /*@%*/ != 0) {
		if ((unsigned char)c == *p++) {
			//@ assert c == *(p - 1);
			//@ assert \forall integer i; 0 <= i < p - s - 1 ==> ((u8 *)s)[i] != c;
			//@ assert \exists integer i; 0 <= i < \at(n,Pre) && ((u8 *)s)[i] == c;
			//@ assert \exists integer i; 0 <= i < \at(n,Pre) && (\forall integer j; 0 <= j < i ==> ((u8 *)s)[j] != c) && ((u8 *)s)[i] == c;
			return (void *)(p - 1);
		}
	}
	//@ assert n == (size_t %)(-1);
	return NULL;
}
