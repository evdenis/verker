#include "strncpy.h"

/*@ requires valid_str(src);
    requires \valid(dest+(0..strlen(src)));
    requires \base_addr(dest) != \base_addr(src);
    assigns dest[0..strlen(src)];
    ensures valid_str(\result);
    ensures \result == dest;
    ensures \forall integer i; 0 <= i <= strlen(src) ==> \result[i] == src[i];
 */
char *strncpy(char *dest, const char *src, size_t count)
{
	char *tmp = dest;

	while (count) {
		if ((*tmp = *src) != 0)
			src++;
		tmp++;
		count--;
	}
	return dest;
}