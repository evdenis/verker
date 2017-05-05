#include "strcpy.h"


/*@ requires valid_str(src);
    requires \valid(dest+(0..strlen(src)));
    requires \base_addr(dest) != \base_addr(src);
    assigns dest[0..strlen(src)];
    ensures valid_str(dest);
    ensures \result == dest;
    ensures \forall size_t i; i <= strlen(src) ==> \result[i] == src[i];
 */
char *strcpy(char *dest, const char *src)
{
	char *tmp = dest;
	//@ ghost char *old_s = src;
	//@ assert valid_str(old_s);

	/*@ loop invariant old_s <= src <= old_s + strlen(old_s);
	    loop invariant tmp <= dest <= tmp + strlen(old_s);
	    loop invariant valid_str(src);
	    loop invariant dest - tmp == src - old_s;
	    loop invariant \forall size_t i; i < src - old_s ==> tmp[i] == old_s[i];
	    loop variant strlen(old_s) - (src - old_s);
	*/
	while ((*dest++ = *src++) != '\0')
		/* nothing */;
	//@ assert dest[-1] == '\0' && src[-1] == '\0';
	//@ assert valid_str(tmp);
	return tmp;
}
