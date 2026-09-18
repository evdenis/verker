#include "strnlen.h"

size_t strnlen(const char *s, size_t count)
{
	const char *sc;
	//@ ghost size_t ocount = count;
	//@ ghost size_t k = 0;
	/*@ loop invariant bound:  0 <= count <= ocount;
	    loop invariant idx:    sc == s + k;
	    loop invariant offset: k == ocount - count;
	    loop invariant valid:  valid_strn(sc, count);
	    loop invariant len:    strnlen(s, ocount) == strnlen(sc, count) + k;
	    loop invariant nz:     \forall integer i; 0 <= i < k ==> s[i] != '\0';
	    loop assigns count, sc, k;
	    loop variant count;
	 */
	for (sc = s; count-- && *sc != '\0'; ++sc) {
		//@ ghost valid_strn_shift((char *)sc, (size_t)(count + 1));
		//@ ghost k++;
	}
	//@ ghost valid_strn_len((char *)s, ocount);
	//@ assert sc - s == k;
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
#include <assert.h>

int main(void)
{
	assert(strnlen("123456789", 5) == 5);
	assert(strnlen("123456789", 20) == 9);
	return 0;
}
#endif
