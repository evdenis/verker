#include "strnstr.h"

char *strnstr(const char *s1, const char *s2, size_t len)
{
	size_t l2;
	//@ ghost const char *start = s1;
	//@ ghost size_t limit = len;
	//@ ghost size_t offset = 0;

	l2 = strlen(s2);
	if (!l2)
		return (char *)s1;
	/*@ loop invariant bound: 0 <= offset <= limit;
	    loop invariant cursor: s1 == start + offset;
	    loop invariant remaining: len == limit - offset;
	    loop invariant valid: \valid_read(s1 + (0..len-1));
	    loop invariant needle_length: l2 == strlen(s2) && l2 > 0;
	    loop invariant skipped: \forall integer i; 0 <= i < offset ==>
	                            !strnstr_match(start, s2, i);
	    loop assigns s1, len, offset;
	    loop variant len;
	 */
	while (len >= l2) {
		len--;
		if (!memcmp(s1, s2, l2))
			//@ assert matched: strnstr_match(start, s2, offset);
			//@ assert nonnull: s1 != \null;
			return (char *)s1;
		s1++;
		//@ ghost offset++;
	}
	return NULL;
}

#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 0 && size % 2 == 0 && data[(size/2) - 1] == '\0' && data[size-1] == '\0') {
		strnstr((const char *)data, (const char *)(data + size / 2), size / 2);
	}
	return 0;
}
#endif


#ifdef DUMMY_MAIN

#include <string.h>

int main(int argc, char *argv[])
{
	const char *s1 = "1234567890";
	char *ptr;

	ptr = strnstr(s1, "789", strlen(s1));
	ptr = strnstr(s1, "789", strlen(s1) / 2);
	ptr = strnstr(s1, "000", strlen(s1));
	ptr = ptr;

	return 0;
}
#endif
