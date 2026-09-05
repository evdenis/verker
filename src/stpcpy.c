#include "stpcpy.h"

char *stpcpy(char *__restrict__ dest, const char *__restrict__ src)
{
	//@ ghost char *osrc = (char *)src;
	//@ ghost char *odest = dest;
	//@ ghost size_t n = elim_valid_str(osrc);
	//@ ghost intro_valid_str_len(osrc, n);
	//@ ghost size_t k = 0;

	/*@ loop invariant idx1:      src == osrc + k;
	    loop invariant idx2:      dest == odest + k;
	    loop invariant bound:     0 <= k <= n;
	    loop invariant untouched: \forall integer i; 0 <= i <= n ==>
	                              osrc[i] == \at(src[i], Pre);
	    loop invariant copied:    \forall integer i; 0 <= i < k ==>
	                              odest[i] == \at(src[i], Pre);
	    loop assigns src, dest, k, odest[0..n];
	    loop variant n - k;
	*/
	while ((*dest++ = *src++) != '\0') {
		//@ ghost k++;
	}
	//@ assert k == n;
	//@ ghost intro_valid_str_len(odest, n);

	return --dest;
}

#ifdef DUMMY_MAIN
#include <string.h>

int main(int argc, char *argv[])
{
	const char *s = "1234567890";
	char d[strlen(s)];

	stpcpy(d, s);

	return 0;
}
#endif
