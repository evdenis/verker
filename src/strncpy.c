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
    requires \valid(dest+(0..count-1));
    requires \separated(dest+(0..count-1), src+(0..strlen(src)));
    requires strlen(src) <= LONG_MAX;
    terminates \true;
    assigns dest[0..count-1];
    assigns \result \from dest;
    exits \false;
    ensures \result == dest;
    behavior exceed:
       assumes count > strlen{Pre}(src);
       ensures \forall integer i; 0 <= i <= strlen{Pre}(src) ==>
               dest[i] == \at(src[i], Pre);
       ensures \forall integer i; strlen{Pre}(src) <= i < count ==>
               dest[i] == '\0';
       ensures valid_str(dest);
       ensures strlen(dest) == strlen{Pre}(src);
    behavior not_exceed:
       assumes count <= strlen{Pre}(src);
       ensures \forall integer i; 0 <= i < count ==>
               dest[i] == \at(src[i], Pre);
    complete behaviors;
    disjoint behaviors;
 */
char *strncpy(char *dest, const char *src, size_t count)
{
	char *tmp = dest;
	//@ ghost char *osrc = (char *)src;
	//@ ghost size_t ocount = count;
	//@ ghost size_t n = elim_valid_str(osrc);
	//@ ghost intro_valid_str_len(osrc, n);
	//@ ghost size_t k = 0;

	/*@ loop invariant idx:       tmp == dest + k;
	    loop invariant bound:     0 <= k <= ocount;
	    loop invariant left:      count == ocount - k;
	    loop invariant srcpos:    src == osrc + (k < n ? k : n);
	    loop invariant untouched: \forall integer i; 0 <= i <= n ==>
	                              osrc[i] == \at(src[i], Pre);
	    loop invariant copied:    \forall integer i; 0 <= i < k && i <= n ==>
	                              dest[i] == \at(src[i], Pre);
	    loop invariant padded:    \forall integer i; n < i < k ==> dest[i] == '\0';
	    loop assigns count, src, tmp, k, dest[0..ocount-1];
	    loop variant count;
	*/
	while (count) {
		if ((*tmp = *src) != 0)
			src++;
		tmp++;
		count--;
		//@ ghost k++;
	}
	//@ assert k == ocount;
	//@ ghost if (ocount > n) intro_valid_str_len(dest, n);
	return dest;
}

#ifdef DUMMY_MAIN
#include <string.h>

int main(int argc, char *argv[])
{
	const char *s = "1234567890";
	char d[strlen(s)];

	strncpy(d, s, strlen(s));
	strncpy(d, s, strlen(s) / 2);

	return 0;
}
#endif
