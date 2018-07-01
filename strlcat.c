#include "strlcat.h"

/*@ requires valid_str(dest);
    requires valid_str(src);
    requires \valid(dest+(0..count));
    requires strlen(dest) + strlen(src) <= SIZE_MAX;
    requires count > strlen(dest);
    assigns dest[strlen{Old}(\old(dest))..strlen{Old}(\old(dest)) + strlen(src)];
    ensures strlen(dest) <= \result <= strlen(dest) + strlen(src);
    ensures valid_str(dest);
 */
size_t strlcat(char *dest, const char *src, size_t count)
{
	size_t dsize = strlen(dest);
	size_t len = strlen(src);
	size_t res = dsize + len;

	/* This would be a bug */
	//BUG_ON(dsize >= count);

	dest += dsize;
//@ ghost Mid:
	//@ assert valid_str(dest);
	//@ assert dest == \at(dest,Pre) + strlen(\at(dest,Pre));
	//@ assert *dest == '\0';
	count -= dsize;
	if (len >= count)
		len = count-1;
	//@ assert len < count;
	// assert \valid(dest+(0..len-1));
	memcpy(dest, src, len);
	//@ assert \forall integer i; 0 <= i < len ==> \at(dest,Mid)[i] == src[i];
	dest[len] = 0;
	//@ assert valid_str(dest);
	//@ assert valid_str(\at(dest,Pre));
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
