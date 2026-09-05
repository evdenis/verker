#include "strlcat.h"

/*@ requires valid_str(dest);
    requires valid_str(src);
    requires \valid(dest+(0..count));
    requires strlen(dest) + strlen(src) <= SIZE_MAX;
    requires strlen(dest) <= LONG_MAX && strlen(src) <= LONG_MAX;
    requires count > strlen(dest);
    requires \separated(dest+(0..count), src+(0..strlen(src)));
    terminates \true;
    assigns dest[strlen{Pre}(dest)..strlen{Pre}(dest) + strlen{Pre}(src)];
    exits \false;
    ensures \result == strlen{Pre}(dest) + strlen{Pre}(src);
    ensures valid_str(dest);
    ensures strlen{Pre}(dest) <= strlen(dest) <=
            strlen{Pre}(dest) + strlen{Pre}(src);
 */
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
	//@ assert dest == odest + dsize;
	//@ assert *dest == '\0';
	count -= dsize;
	if (len >= count)
		len = count-1;
	//@ assert len < count;
	memcpy(dest, src, len);
	//@ assert \forall integer i; 0 <= i < len ==> odest[dsize + i] == \at(src[i], Pre);
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
