#include "strrchr.h"

char *strrchr(const char *s, int c)
{
	const char *last = NULL;
	//@ ghost char *os = (char *)s;
	//@ ghost size_t k = 0;
	//@ ghost size_t lastk = 0;

	/*@ loop invariant idx:    s == os + k;
	    loop invariant bound:  0 <= k <= strlen(os);
	    loop invariant len:    strlen(os) == strlen(s) + k;
	    loop invariant valid:  valid_str(s);
	    loop invariant nolast: last == \null <==>
	                           (\forall integer i; 0 <= i < k ==> os[i] != (char) c);
	    loop invariant lastok: last != \null ==>
	                           (last == os + lastk && lastk < k && os[lastk] == (char) c &&
	                            (\forall integer i; lastk < i < k ==> os[i] != (char) c));
	    loop assigns s, last, k, lastk;
	    loop variant strlen(os) - k;
	 */
	do {
		if (*s == (char) c) {
			last = s;
			//@ ghost lastk = k;
		}
		//@ ghost if (*s != '\0') valid_str_shift((char *)s);
		//@ ghost if (*s != '\0') k++;
	} while (*s++);
	//@ ghost valid_str_len(os);
	return (char *)last;
}

#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 1 && data[size-1] == '\0') {
		strrchr((const char *)data + 1, *data);
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	const char *s = "123456788889";
	char *ptr;

	ptr = strrchr(s, '6');
	ptr = strrchr(s, '8');
	ptr = strrchr(s, '\0');
	ptr = ptr;

	return 0;
}
#endif
