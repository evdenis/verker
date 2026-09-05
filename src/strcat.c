#include "strcat.h"

char *strcat(char *dest, const char *src)
{
	char *tmp = dest;
	//@ ghost size_t d = elim_valid_str(tmp);
	//@ ghost intro_valid_str_len(tmp, d);
	//@ ghost size_t j = 0;

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

	//@ ghost char *osrc = (char *)src;
	//@ ghost char *mdest = dest;
	//@ ghost size_t n = elim_valid_str(osrc);
	//@ ghost intro_valid_str_len(osrc, n);
	//@ ghost size_t k = 0;

	/*@ loop invariant idx1:      src == osrc + k;
	    loop invariant idx2:      dest == mdest + k;
	    loop invariant bound:     0 <= k <= n;
	    loop invariant untouched: \forall integer i; 0 <= i <= n ==>
	                              osrc[i] == \at(src[i], Pre);
	    loop invariant prefix:    \forall integer i; 0 <= i < d ==>
	                              tmp[i] == \at(dest[i], Pre);
	    loop invariant copied:    \forall integer i; 0 <= i < k ==>
	                              mdest[i] == \at(src[i], Pre);
	    loop assigns src, dest, k, mdest[0..n];
	    loop variant n - k;
	 */
	while ((*dest++ = *src++) != '\0') {
		//@ ghost k++;
	}
	//@ assert k == n;
	//@ assert mdest == tmp + d;
	//@ ghost intro_valid_str_len(tmp, (size_t)(d + n));
	return tmp;
}

#ifdef DUMMY_MAIN
#include <string.h>

int main(int argc, char *argv[])
{
	const char *s = "12345";
	char d[strlen(s) + 4];

	d[0] = '1'; d[1] = '1'; d[2] = '1'; d[3] = '\0';
	strcat(d, s);

	return 0;
}
#endif
