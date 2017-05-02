#include "strrchr.h"

/*@ requires valid_str(s);
    requires ((char %)c) == c;
    assigns \nothing;
    ensures \base_addr(\result) == \base_addr(s);
    ensures \result == \null || s <= \result <= s + strlen(s) && *\result == c;
    ensures \forall integer i; 0 <= i <= strlen(s) &&;
 */
char *strrchr(const char *s, int c)
{
	const char *last = NULL;
	/*@ loop invariant \base_addr(s) == \base_addr(\at(s,Pre));
	    loop invariant \at(s,Pre) <= s <= \at(s,Pre) + strlen(\at(s,Pre));
	    loop invariant valid_str(s);
	    loop invariant last == \null || *last == c;
	    loop variant strlen(\at(s,Pre)) - (s - \at(s,Pre));
	 */
	do {
		if (*s == (char)c)
			last = s;
	} while (*s++);
	//@ assert s[-1] == '\0';
	return (char *)last;
}