#include "strlcat.h"

size_t strlcat(char *dest, const char *src, size_t count)
{
	//@ ghost char *odest = dest;
	//@ ghost char *osrc = (char *)src;
	//@ ghost valid_str_len(odest);
	//@ ghost valid_str_len(osrc);
	size_t dsize = strlen(dest);
	size_t len = strlen(src);
	size_t res = dsize + len;

	dest += dsize;
	//@ assert cursor: dest == odest + dsize;
	//@ assert terminator: *dest == '\0';
	count -= dsize;
	if (len >= count)
		len = count-1;
	//@ assert room: len < count;
	memcpy(dest, src, len);
	//@ assert copied: \forall integer i; 0 <= i < len ==> odest[dsize + i] == \at(src[i], Pre);
	dest[len] = 0;
	//@ ghost intro_valid_str_len(dest, len);
	//@ ghost intro_valid_str_len(odest, (size_t)(dsize + len));
	return res;
}

#ifdef DUMMY_MAIN
#include <string.h>

int main(int argc, char *argv[])
{
	const char *s = "12345";
	char d[strlen(s) + 4];

	d[0] = '1'; d[1] = '1'; d[2] = '1'; d[3] = '\0';
	strlcat(d, s, strlen(s));
	strlcat(d, s, strlen(s) - 3);

	return 0;
}
#endif
