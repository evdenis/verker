#include "strrchr.h"

char *strrchr(const char *s, int c)
{
	const char *last = NULL;
	//@ ghost char *os = s;

	/*@ loop invariant os <= s <= os + strlen(os);
	    loop invariant last == \null ^^ ((os <= last < s) && (*last == (char %)c));
	    loop invariant (last != \null) <==> (\exists char *p; os <= p < s && *p == (char %) c);
	    loop invariant (last == \null) <==> (\forall char *p; os <= p < s ==> *p != (char %)c);
	    loop invariant last != \null ==> (\forall char *p; last < p < s ==> *p != (char %)c);
	    //loop invariant strrchr(s, (char %) c) == strrchr(os, (char %) c);
	    loop variant strlen(os) - (s - os);
	 */
	do {
		if (*s == (char)/*@%*/c)
			last = s;
	} while (*s++);
	//@ assert s[-1] == '\0';
	//@ assert s == os + strlen(os) + 1;
	//@ assert (\exists char *p; os <= p < os + strlen(os) && *p == (char %) c) ==> (last != \null);
	// assert strrchr(\at(s,Pre), (char %) c) == last;
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
