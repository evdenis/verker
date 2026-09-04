#include "strchrnul.h"

char *strchrnul(const char *s, int c)
{
	//@ ghost char *os = (char *)s;
	//@ ghost size_t k = 0;
	/*@ loop invariant valid:   valid_str(s);
	    loop invariant idx:     s == os + k;
	    loop invariant bound:   0 <= k <= strlen(os);
	    loop invariant len:     strlen(os) == strlen(s) + k;
	    loop invariant nomatch: \forall integer i; 0 <= i < k ==> os[i] != (char) c;
	    loop invariant same:    strchrnul(os, (char) c) == strchrnul(s, (char) c);
	    loop assigns s, k;
	    loop variant strlen(os) - k;
	 */
	while (*s && *s != (char) c) {
		//@ ghost valid_str_shift((char *)s);
		s++;
		//@ ghost k++;
	}
	//@ ghost valid_str_len(os);
	//@ ghost strchrnul_defn(os, (char) c, k);
	//@ ghost strchrnul_strlen(os);
	return (char *)s;
}


#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 1 && data[size-1] == '\0') {
		strchrnul((const char *)data + 1, *data);
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	const char *s = "123456788889";
	char *ptr;

	ptr = strchrnul(s, '6');
	ptr = strchrnul(s, '8');
	ptr = strchrnul(s, '\0');
	ptr = ptr;

	return 0;
}
#endif
