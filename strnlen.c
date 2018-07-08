#include "strnlen.h"

size_t strnlen(const char *s, size_t count)
{
	const char *sc;
	/*@ loop invariant 0 <= count <= \at(count,Pre);
	    loop invariant s <= sc <= s + strnlen(s,\at(count,Pre));
	    loop invariant sc - s == (\at(count,Pre) - count);
	    loop invariant valid_strn(sc, count);
	    loop invariant strnlen(s,\at(count,Pre)) == strnlen(sc, count) + (sc - s);
	    loop invariant \forall integer i; 0 <= i < sc - s ==> s[i] != '\0';
	    loop variant count;
	 */
	for (sc = s; count-- AENOC && *sc != '\0'; ++sc)
		/* nothing */;

	return sc - s;
}


#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	strnlen((const char *)data, size);
	return 0;
}
#endif

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	strnlen("123456789", 5);
	strnlen("123456789", 20);

	return 0;
}
#endif
