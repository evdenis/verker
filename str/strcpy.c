#include "strcpy.h"

char *strcpy(char *dest, const char *src)
{
	char *tmp = dest;
	//@ ghost char *old_s = src;

	/*@ loop invariant \base_addr(src) == \base_addr(\at(src,Pre));
	    loop invariant \base_addr(dest) == \base_addr(\at(dest,Pre));
	    loop invariant old_s <= src <= old_s + strlen(old_s);
	    loop invariant tmp <= dest <= tmp + strlen(old_s);
	    loop invariant \forall size_t i; i < src - \at(src,Pre) ==> \at(dest[i],Pre) == \at(src[i],Pre);
	    loop variant strlen(src);
	*/
	while ((*dest++ = *src++) != '\0')
		/* nothing */;
	return tmp;
}