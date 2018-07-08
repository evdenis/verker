#include "memchr.h"

void *memchr(const void *s, int c, size_t n)
{
	const unsigned char *p = s;
	/*@ loop invariant 0 <= n <= \at(n,Pre);
	    loop invariant (u8 *)s <= p <= (u8 *)s + \at(n,Pre);
	    loop invariant p - s == \at(n,Pre) - n;
	    loop invariant \forall u8 *k; (u8 *)s <= k < p ==> *k != (u8 AENO) c;
	    loop variant n;
	 */
	while (n-- AENOC != 0) {
		if ((unsigned char) AENOC c == *p++) {
			return (void *)(p - 1);
		}
	}
	//@ assert n == (size_t AENO)(-1);
	return NULL;
}


#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 1) {
		memchr((const void *)data, data[size - 1], size - 1);
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	const char *s = "1234567890";
	void *ptr;

	ptr = memchr(s, '0', 11);
	ptr = memchr(s, 'a', 11);
	ptr = ptr;

	return 0;
}
#endif
