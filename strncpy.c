#include "strncpy.h"

/**
 * strncpy - Copy a length-limited, C-string
 * @dest: Where to copy the string to
 * @src: Where to copy the string from
 * @count: The maximum number of bytes to copy
 *
 * The result is not %NUL-terminated if the source exceeds
 * @count bytes.
 *
 * In the case where the length of @src is less than  that  of
 * count, the remainder of @dest will be padded with %NUL.
 *
 */

#include "strlen.h"

/*@ requires valid_str(src);
    requires \valid(dest+(0..strnlen(src, count)));
    requires \base_addr(dest) != \base_addr(src);
    assigns dest[0..strnlen(src, count)];
    ensures \result == dest;
    behavior exceed:
       assumes count >= strlen(src);
       ensures \forall integer i; 0 <= i <= strlen(src) ==> \result[i] == src[i];
       ensures valid_str(\result);
       ensures \forall integer i; strlen(src) <= i <= count - strlen(src) ==> \result[i] == '\0';
    behavior not_exceed:
       assumes count < strlen(src);
       ensures \forall integer i; 0 <= i <= count ==> \result[i] == src[i];
       ensures valid_strn(\result, count);
    complete behaviors;
    disjoint behaviors;
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
	    loop invariant valid_str(src);
	    //loop invariant strnlen(src, count) == strnlen(osrc, ocount) - (src - osrc);
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
