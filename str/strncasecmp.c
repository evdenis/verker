#include "strncasecmp.h"

/*@ requires valid_strn(s1, len);
    requires valid_strn(s2, len);
    assigns \nothing;
 */
int strncasecmp(const char *s1, const char *s2, size_t len)
{
	/* Yes, Virginia, it had better be unsigned */
	unsigned char c1, c2;
	//@ ghost size_t olen = len;
	//@ ghost char *os1 = s1, *os2 = s2;

	if (!len)
		return 0;

	/*@ loop invariant 0 <= len <= olen;
	    loop invariant os1 <= s1 <= os1 + strnlen(os1, olen);
	    loop invariant os2 <= s2 <= os2 + strnlen(os2, olen);
	    loop invariant s1 - os1 == s2 - os2 == olen - len;
	    loop invariant valid_strn(s1, len) && valid_strn(s2, len);
	    loop variant len;
	 */
	do {
		c1 = (unsigned char) /*@%*/ *s1++; // CODE_CHANGE:
		c2 = (unsigned char) /*@%*/ *s2++; // CODE_CHANGE:
		if (!c1 || !c2)
			break;
		if (c1 == c2)
			continue;
		c1 = tolower(c1);
		c2 = tolower(c2);
		if (c1 != c2)
			break;
	} while (--len);
	return (int)c1 - (int)c2;
}