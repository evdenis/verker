#include "strlen.h"

size_t strlen(const char *s)
{
	const char *sc;
	/*@ loop invariant s <= sc <= s + strlen(s);
	    loop invariant valid_str(sc);
	    loop invariant strlen(s) == strlen(sc) + (sc - s);
	    loop assigns sc;
	    loop variant strlen(s) - (sc - s);
	 */
	for (sc = s; *sc != '\0'; ++sc)
		/* nothing */;
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

int main(int argc, char *argv[])
{
	strlen("123456789");
	return 0;
}
#endif
