#include "strncat.h"

/*@ requires valid_strn(src, count);
    requires valid_str(dest);
    requires strlen(dest) + count <= SIZE_MAX;
    requires strlen(dest) <= LONG_MAX;
    requires \valid(dest+(0..strlen(dest)+count));
    requires \separated(dest+(0..strlen(dest)+count), src+(0..count));
    terminates \true;
    assigns dest[strlen{Pre}(dest)..strlen{Pre}(dest)+count];
    assigns \result \from dest;
    exits \false;
    ensures \result == dest;
    ensures \forall integer i; 0 <= i < strlen{Pre}(dest) ==>
            \at(dest[i], Pre) == \result[i];
    ensures \forall integer i;
            0 <= i < strnlen{Pre}(src, count) ==>
            \at(src[i], Pre) == \result[strlen{Pre}(dest) + i];
    ensures valid_str(\result);
    ensures strlen(\result) == strlen{Pre}(dest) + strnlen{Pre}(src, count);
 */
char *strncat(char *dest, const char *src, size_t count)
{
	char *tmp = dest;
	//@ ghost size_t d = elim_valid_str(tmp);
	//@ ghost intro_valid_str_len(tmp, d);
	//@ ghost size_t j = 0;
	//@ ghost char *osrc = (char *)src;
	//@ ghost size_t ocount = count;
	//@ ghost size_t n = elim_valid_strn(osrc, ocount);
	//@ ghost intro_valid_strn_len(osrc, ocount, n);
	//@ ghost valid_strn_len(osrc, ocount);

	if (count) {
		/*@ loop invariant idx:   dest == tmp + j;
		    loop invariant bound: 0 <= j <= d;
		    loop invariant kept:  \forall integer i; 0 <= i <= d ==>
		                          tmp[i] == \at(dest[i], Pre);
		    loop assigns dest, j;
		    loop variant d - j;
		 */
		while (*dest) {
			dest++;
			//@ ghost j++;
		}
		//@ assert j == d;
		//@ ghost char *mdest = dest;
		//@ ghost size_t k = 0;

		/*@ loop invariant idx1:      src == osrc + k;
		    loop invariant idx2:      dest == mdest + k;
		    loop invariant bound:     0 <= k <= n;
		    loop invariant left:      count == ocount - k;
		    loop invariant pos:       count > 0;
		    loop invariant untouched: \forall integer i; 0 <= i <= n ==>
		                              osrc[i] == \at(src[i], Pre);
		    loop invariant prefix:    \forall integer i; 0 <= i < d ==>
		                              tmp[i] == \at(dest[i], Pre);
		    loop invariant copied:    \forall integer i; 0 <= i < k ==>
		                              mdest[i] == \at(src[i], Pre);
		    loop assigns count, src, dest, k, mdest[0..ocount];
		    loop variant count;
		 */
		while ((*dest++ = *src++) != 0) {
			/* the copied character was not the terminator, so k is still
			 * inside the source's strnlen */
			//@ assert osrc[k] != '\0';
			//@ assert nul: n < ocount ==> osrc[n] == '\0';
			//@ assert pos: count > 0 && k < ocount;
			//@ assert k < n;
			//@ ghost k++;
			if (--count == 0) {
				*dest = '\0';
				break;
			}
		}
		//@ assert k == n;
		//@ assert mdest == tmp + d;
		//@ ghost intro_valid_str_len(tmp, (size_t)(d + n));
	}
	return tmp;
}

#ifdef DUMMY_MAIN
#include <string.h>

int main(int argc, char *argv[])
{
	const char *s = "12345";
	char d[strlen(s) + 4];

	d[0] = '1'; d[1] = '1'; d[2] = '1'; d[3] = '\0';
	strncat(d, s, strlen(s));
	strncat(d, s, strlen(s) - 3);

	return 0;
}
#endif
