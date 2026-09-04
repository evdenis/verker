#include "memchr.h"

void *memchr(const void *s, int c, size_t n)
{
	const char *p = /*CODE_CHANGE:*/s;
	/*@ loop invariant bound:   0 <= n <= \at(n,Pre);
	    loop invariant offset:  p == (char *)s + (\at(n,Pre) - n);
	    loop invariant nomatch: \forall integer i; 0 <= i < \at(n,Pre) - n ==>
	                            ((char *)s)[i] != (char) c;
	    loop assigns n, p;
	    loop variant n;
	 */
	while (n-- != 0) {
		if (/*CODE_CHANGE:*/(char) c == *p++) {
			return (void *)(p - 1);
		}
	}
	//@ assert n == (size_t)(-1);
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
