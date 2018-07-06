#include "strchr.h"

char *strchr(const char *s, int c)
{
	//@ ghost char *os = s;
	/*@ loop invariant valid_str(s);
	    loop invariant os <= s <= os + strlen(os);
	    loop invariant \forall char *p; os <= p < s ==> *p != (char ACSL_EXT_NO_OVERFLOW) c;
	    loop invariant strchr(s, (char ACSL_EXT_NO_OVERFLOW) c) == strchr(os, (char ACSL_EXT_NO_OVERFLOW) c);
	    loop variant strlen(os) - (s - os);
	 */
	for (; *s != (char) ACSL_EXT_NO_OVERFLOW_CMNT c; ++s)
		if (*s == '\0')
			return NULL;
	//@ assert (char ACSL_EXT_NO_OVERFLOW) c != '\0' <==> s < os + strlen(os);
	//@ assert (char ACSL_EXT_NO_OVERFLOW) c == '\0' <==> s == os + strlen(os);
	return (char *)s;
}


#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 1 && data[size-1] == '\0') {
		strchr((const char *)data + 1, *data);
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	const char *s = "123456788889";
	char *ptr;

	ptr = strchr(s, '6');
	ptr = strchr(s, '8');
	ptr = strchr(s, '\0');
	ptr = ptr;

	return 0;
}
#endif
