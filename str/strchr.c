#include "strchr.h"

char *strchr(const char *s, int c)
{
	/*@ loop invariant valid_str(s);
	    loop invariant \base_addr(s) == \base_addr(\at(s,Pre));
	    loop invariant \at(s,Pre) <= s <= \at(s,Pre) + strlen(\at(s,Pre));
	    loop invariant \forall integer i; 0 <= i < s - \at(s,Pre) ==> \at(s[i],Pre) != c;
	    loop variant strlen(\at(s,Pre)) - (s - \at(s,Pre));
	 */
	for (; *s != (char)c; ++s)
		if (*s == '\0')
			return NULL;
	//@ assert s <= \at(s,Pre) + strlen(\at(s,Pre));
	return (char *)s;
}