#include "strreplace.h"

char *strreplace(char *s, char old, char new)
{
	//@ ghost char *os = s;
	//@ ghost size_t len = strlen(os);

	/*@ loop invariant valid_str(s);
	    loop invariant valid_str(os);
	    loop invariant os <= s <= os + len;
	    loop invariant \forall char *k; s <= k < (os + len) ==>
               \at(*k,Pre) == *k;
	    loop invariant \forall char *p; os <= p < s ==>
	       \at(*p, Pre) == old ==> *p == new;
	    loop invariant \forall char *p; os <= p < s ==>
	       \at(*p, Pre) != old ==> *p == \at(*p, Pre);
	    loop assigns s, os[0..len-1];
	    loop variant SIZE_MAX - (s - os);
	*/
	for (; *s; ++s)
		if (*s == old)
			*s = new;
	//@ assert strlen(s) == 0;
	//@ assert s - os == strlen{Pre}(os);
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
