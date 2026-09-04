#include "strreplace.h"

char *strreplace(char *s, char old, char new)
{
	//@ ghost char *os = s;
	//@ ghost size_t n = elim_valid_str(os);
	//@ ghost intro_valid_str_len(os, n);
	//@ ghost size_t k = 0;

	/*@ loop invariant idx:       s == os + k;
	    loop invariant bound:     0 <= k <= n;
	    loop invariant untouched: \forall integer i; k <= i <= n ==>
	                              os[i] == \at(s[i], Pre);
	    loop invariant replaced:  \forall integer i; 0 <= i < k ==>
	                              \at(s[i], Pre) == old ==> os[i] == new;
	    loop invariant kept:      \forall integer i; 0 <= i < k ==>
	                              \at(s[i], Pre) != old ==> os[i] == \at(s[i], Pre);
	    loop assigns s, k, os[0..n-1];
	    loop variant n - k;
	*/
	for (; *s; ++s) {
		if (*s == old)
			*s = new;
		//@ ghost k++;
	}
	//@ assert k == n;
	//@ assert strlen(s) == 0;
	/* every position below n now holds either its original non-NUL value or
	 * 'new', so when 'new' is not the terminator the length is unchanged */
	//@ ghost if (new != '\0') intro_valid_str_len(os, n);
	return s;
}

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	char s[] = "1234567890";

	strreplace(s, '6', '5');
	strreplace(s, '\0', '5');

	return 0;
}
#endif
