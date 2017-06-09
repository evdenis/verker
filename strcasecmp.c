#include "strcasecmp.h"

int strcasecmp(const char *s1, const char *s2)
{
	int c1, c2;
	//@ ghost char *os1 = s1;
	//@ ghost char *os2 = s2;

	/*@ loop invariant valid_str(s1) && valid_str(s2);
	    loop invariant os1 <= s1 <= os1 + strlen(os1);
	    loop invariant os2 <= s2 <= os2 + strlen(os2);
	    loop invariant s1 - os1 == s2 - os2;
	    loop invariant \forall integer i; 0 <= i < s1 - os1 ==>
	                   tolower(os1[i]) == tolower(os2[i]);
	    loop variant strlen(os1) - (s1 - os1);
	*/
	do {
		c1 = tolower(*s1++);
		c2 = tolower(*s2++);
	} while (c1 == c2 && c1 != 0);
	//@ ghost int res = c1 - c2;
	//@ assert c1 == c2 ==> c1 == 0 && res == 0;
	/*@ assert c1 != c2 ==>
	    \exists integer i; 0 <= i <= strlen(os1) &&
	            (\forall integer j; 0 <= j < i ==> tolower(os1[j]) == tolower(os2[j])) &&
	            tolower(os1[i]) != tolower(os2[i]) &&
	       res == tolower(os1[i]) - tolower(os2[i]) &&
	       i == s1 - os1 - 1;
	 */
	return c1 - c2;
}

#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 0 && size % 2 == 0 && data[(size/2) - 1] == '\0' && data[size-1] == '\0') {
		strcasecmp((const char *)data, (const char *)(data + size / 2));
	}
	return 0;
}
#endif
