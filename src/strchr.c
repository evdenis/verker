#include "strchr.h"

char *strchr(const char *s, int c)
{
	//@ ghost char *os = (char *)s;
	//@ ghost size_t k = 0;
	/*@ loop invariant valid:   valid_str(s);
	    loop invariant idx:     s == os + k;
	    loop invariant bound:   0 <= k <= strlen(os);
	    loop invariant len:     strlen(os) == strlen(s) + k;
	    loop invariant nomatch: \forall integer i; 0 <= i < k ==> os[i] != (char) c;
	    loop invariant same:    strchr(s, (char) c) == strchr(os, (char) c);
	    loop assigns s, k;
	    loop variant strlen(os) - k;
	 */
	for (; *s != (char) c; ++s) {
		if (*s == '\0')
			return NULL;
		//@ ghost valid_str_shift((char *)s);
		//@ ghost k++;
	}
	//@ ghost valid_str_len(os);
	//@ ghost strchr_defn(os, (char) c, k);
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
