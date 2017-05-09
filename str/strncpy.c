#include "strncpy.h"

/*@ requires valid_strn(src, count);
    requires \valid(dest+(0..strnlen(src, count)));
    requires \base_addr(dest) != \base_addr(src);
    assigns dest[0..strnlen(src, count)];
    ensures valid_strn(\result, count);
    ensures \result == dest;
    ensures \forall integer i; 0 <= i <= strnlen(src, count) ==> \result[i] == src[i];
 */
char *strncpy(char *dest, const char *src, size_t count)
{
	char *tmp = dest;
	//@ ghost char *osrc = src;
	//@ ghost size_t ocount = count;
	//@ assert valid_strn(osrc, ocount);

	/*@ loop invariant osrc <= src <= osrc + strnlen(osrc, ocount);
	    loop invariant dest <= tmp <= dest + ocount;
	    loop invariant 0 <= count <= ocount;
	    loop invariant tmp - dest == ocount - count;
	    loop invariant valid_strn(src, count);
	    loop invariant strnlen(src, count) == strnlen(osrc, ocount) - (src - osrc);
	    loop invariant \forall integer i; 0 <= i < src - osrc ==> dest[i] == osrc[i];
	    loop variant count;
	*/
	while (count) {
		if ((*tmp = *src) != 0)
			src++;
		tmp++;
		count--;
	}
	// assert dest[-1] == '\0' && src[-1] == '\0';
	//@ assert valid_strn(tmp, ocount);
	return dest;
}