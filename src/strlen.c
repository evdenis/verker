#include "strlen.h"

size_t strlen(const char *s)
{
	const char *sc;
	/*@ loop invariant bound:  0 <= sc - s <= strlen(s);
	    loop invariant valid:  valid_str(sc);
	    loop invariant offset: strlen(s) == strlen(sc) + (sc - s);
	    loop assigns sc;
	    loop variant strlen(s) - (sc - s);
	 */
	for (sc = s; *sc != '\0'; ++sc)
		/*@ ghost valid_str_shift((char *)sc); */ ;
	//@ ghost valid_str_len((char *)s);
	//@ assert 0 <= sc - s <= strlen(s);
	return sc - s;
}

#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 0 && data[size - 1] == '\0') {
		strlen((const char *)data);
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN
#include <assert.h>

int main(void)
{
	assert(strlen("123456789") == 9);
	return 0;
}
#endif
