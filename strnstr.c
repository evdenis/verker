#include "strnstr.h"

char *strnstr(const char *s1, const char *s2, size_t len)
{
	size_t l2;

	l2 = strlen(s2);
	if (!l2)
		return (char *)s1;
	while (len >= l2) {
		len--;
		if (!memcmp(s1, s2, l2))
			return (char *)s1;
		s1++;
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
