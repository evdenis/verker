#include "strcpy.h"

char *strcpy(char *dest, const char *src)
{
	char *tmp = dest;
	//@ ghost char *osrc = (char *)src;
	//@ ghost size_t n = elim_valid_str(osrc);
	//@ ghost intro_valid_str_len(osrc, n);
	//@ ghost size_t k = 0;

	/*@ loop invariant idx1:      src == osrc + k;
	    loop invariant idx2:      dest == tmp + k;
	    loop invariant bound:     0 <= k <= n;
	    loop invariant untouched: \forall integer i; 0 <= i <= n ==>
	                              osrc[i] == \at(src[i], Pre);
	    loop invariant copied:    \forall integer i; 0 <= i < k ==>
	                              tmp[i] == \at(src[i], Pre);
	    loop assigns src, dest, k, tmp[0..n];
	    loop variant n - k;
	*/
	while ((*dest++ = *src++) != '\0') {
		//@ ghost k++;
	}
	//@ assert k == n;
	//@ ghost intro_valid_str_len(tmp, n);
	return tmp;
}

#ifdef DUMMY_MAIN
#include <string.h>

int main(int argc, char *argv[])
{
	const char *s = "1234567890";
	char d[strlen(s)];

	strcpy(d, s);

	return 0;
}
#endif
