#include "strreplace.h"

/*@ requires valid_str(s);
    requires old != '\0';
    requires new != '\0';
    requires old != new;
    assigns s[0..strlen(s)];
    ensures \result == s + strlen(s);
 */
char *strreplace(char *s, char old, char new)
{
	//@ ghost char *os = s;
	/*@ loop invariant valid_str(s);
	    loop invariant os <= s <= os + strlen(os);
	    loop invariant s == 
	    //loop invariant \forall char *p;
	    //   os <= p < s &&
	    //   \at(*p,Pre) != old ==> *p == \at(*p,Pre);
	    loop invariant \forall char *p;
	       os <= p < s &&
	       \at(*p,Pre) == old ==> *p == new;
	    loop assigns os[0..strlen(os)];
	    loop variant strlen(os) - (s - os);
	 */
	for (; *s; ++s)
		if (*s == old)
			*s = new;
	return s;
}