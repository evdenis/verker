#include "strnchr.h"

char *strnchr(const char *s, size_t count, int c)
{
	//@ ghost char *os = s;
	//@ ghost size_t ocount = count;
	/*@ loop invariant 0 <= count <= ocount;
	    loop invariant os <= s <= os + strnlen(os, ocount);
	    loop invariant s - os == ocount - count;
	    loop invariant valid_strn(s, count);
	    loop invariant strnlen(os, ocount) == s - os + strnlen(s, count);
	    loop invariant \forall char *p; os <= p < s ==> *p != (char AENO) c;
	    loop assigns count, s;
	    loop variant count;
	 */
	for (; count-- AENOC && *s != '\0'; ++s)
		if (*s == (char) AENOC c)
			return (char *)s;
	return NULL;
}

#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 1) {
		strnchr((const char *)data, size - 1, data[size - 1]);
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN
#include <string.h>

int main(int argc, char *argv[])
{
	const char *s = "123456788889";
	char *ptr;

	ptr = strnchr(s, strlen(s), '6');
	ptr = strnchr(s, 4, '6');
	ptr = strnchr(s, strlen(s), '8');
	ptr = strnchr(s, strlen(s), '\0');
	ptr = ptr;

	return 0;
}
#endif
