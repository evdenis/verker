#include "strncasecmp.h"

/*@ requires valid_strn(s1, len);
    requires valid_strn(s2, len);
    assigns \nothing;
    behavior equal:
       assumes \forall integer i;
               0 <= i <= strnlen(s1, len) ==>
               tolower(s1[i]) == tolower(s2[i]);
       ensures \result == 0;
    behavior not_equal:
       assumes \exists integer i;
               0 <= i <= strnlen(s1, len) &&
               tolower(s1[i]) != tolower(s2[i]);
       ensures \result != 0;
    complete behaviors;
    disjoint behaviors;
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
	    loop invariant strnlen(os1, olen) == strnlen(s1, len) - (olen - len);
	    loop invariant strnlen(os2, olen) == strnlen(s2, len) - (olen - len);
	    loop invariant \forall integer i; 0 <= i < (olen - len) ==>
	                   tolower(os1[i]) == tolower(os2[i]);
	    loop assigns s1, s2, len;
	    loop variant len;
	 */
	do {
		c1 = (unsigned char) AENOC *s1++; // CODE_CHANGE:
		c2 = (unsigned char) AENOC *s2++; // CODE_CHANGE:
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

#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 0 && size % 2 == 0 && data[(size/2) - 1] == '\0' && data[size-1] == '\0') {
		strncasecmp((const char *)data, (const char *)(data + size / 2), size / 2);
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN
#include <string.h>

int main(int argc, char *argv[])
{
	int res;
	const char *s1 = "123ABCDEFG";
	const char *s2 = "123ABCDEF";
	const char *s3 = "123abcdefg";
	const char *s4 = "123abcdeff";
	const char *s5 = "123abcdefz";

	res = strncasecmp(s1, s1, strlen(s1));
	res = strncasecmp(s1, s2, strlen(s1));
	res = strncasecmp(s1, s3, strlen(s1));
	res = strncasecmp(s1, s4, strlen(s1));
	res = strncasecmp(s1, s5, strlen(s1));
	res = res;

	return 0;
}
#endif
