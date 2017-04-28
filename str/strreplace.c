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
	/*@ loop invariant \base_addr(s) == \base_addr(\at(s,Pre));
	    loop invariant valid_str(s);
	    loop invariant \at(s,Pre) <= s <= \at(s,Pre) + strlen(\at(s,Pre));
	    loop invariant \forall integer i;
	       (0 <= i < s - \at(s,Pre)) &&
	       \at(s[\at(i,Here)],Pre) != old ==> s[i] == old;
	    loop invariant \forall integer i;
	       (0 <= i < s - \at(s,Pre)) &&
	       \at(s[\at(i,Here)],Pre) == old ==> s[i] == new;
	    loop assigns \at(s[0..strlen(s)],Pre);
	    loop variant strlen(\at(s,Pre)) - (s - \at(s,Pre));
	 */
	for (; *s; ++s)
		if (*s == old)
			*s = new;
	return s;
}