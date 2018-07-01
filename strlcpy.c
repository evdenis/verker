#include "strlcpy.h"

size_t strlcpy(char *dest, const char *src, size_t size)
{
	size_t ret = strlen(src);

	if (size) {
		size_t len = (ret >= size) ? size - 1 : ret;
		memcpy(dest, src, len);
		//@ assert \forall integer i;  0 <= i < len ==> src[i] == dest[i];
		dest[len] = '\0';
		//@ assert valid_str(dest);
		//@ assert strlen(dest) == len;
	}
	return ret;
}

#ifdef DUMMY_MAIN
#include <string.h>

int main(int argc, char *argv[])
{
	const char *s = "1234567890";
	char d[strlen(s)];

	strlcpy(d, s, strlen(s));
	strlcpy(d, s, strlen(s) / 2);

	return 0;
}
#endif
