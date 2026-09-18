#include "strncat.h"

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
		//@ assert scanned: j == d;
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
		    loop assigns count, src, dest, k, mdest[0..n];
		    loop variant count;
		 */
		while ((*dest++ = *src++) != 0) {
			/* the copied character was not the terminator, so k is still
			 * inside the source's strnlen */
			//@ assert nonzero: osrc[k] != '\0';
			//@ assert nul: n < ocount ==> osrc[n] == '\0';
			//@ assert pos: count > 0 && k < ocount;
			//@ assert copied_bound: k < n;
			//@ ghost k++;
			if (--count == 0) {
				*dest = '\0';
				break;
			}
		}
		//@ assert copied_all: k == n;
		//@ assert suffix: mdest == tmp + d;
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
