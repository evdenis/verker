#include "strnchr.h"

char *strnchr(const char *s, size_t count, int c)
{
	//@ ghost char *os = (char *)s;
	//@ ghost size_t ocount = count;
	//@ ghost size_t k = 0;
	/*@ loop invariant bound:   0 <= count <= ocount;
	    loop invariant idx:     s == os + k;
	    loop invariant offset:  k == ocount - count;
	    loop invariant valid:   valid_strn(s, count);
	    loop invariant len:     strnlen(os, ocount) == k + strnlen(s, count);
	    loop invariant nomatch: \forall integer i; 0 <= i < k ==> os[i] != (char) c;
	    loop assigns count, s, k;
	    loop variant count;
	 */
	for (; count-- && *s != '\0'; ++s) {
		if (*s == (char) c) {
			//@ ghost valid_strn_shift((char *)s, (size_t)(count + 1));
			//@ assert k < strnlen(os, ocount);
			return (char *)s;
		}
		//@ ghost valid_strn_shift((char *)s, (size_t)(count + 1));
		//@ ghost k++;
	}
	//@ ghost valid_strn_len(os, ocount);
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
