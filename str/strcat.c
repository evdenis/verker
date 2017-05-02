#include "strcat.h"

/*@ requires valid_str(src);
    requires valid_str(dest);
    requires \valid(dest+(0..strlen(dest)+strlen(src)-1));
    assigns dest[strlen(dest)..strlen(dest)+strlen(src)-1];
    ensures \result == dest;
 */
char *strcat(char *dest, const char *src)
{
	char *tmp = dest;

	//@ assert valid_str(tmp);
	//@ ghost size_t dest_len = strlen(tmp);

	/*@ loop invariant \base_addr(dest) == \base_addr(tmp);
	    loop invariant tmp <= dest <= tmp + strlen(tmp);
	    loop invariant valid_str(dest);
	    loop variant strlen(tmp) - (dest - tmp);
	 */
	while (*dest)
		dest++;
	//@ assert *dest == '\0';
	//@ assert dest == tmp + strlen(tmp);
	//@ ghost Mid:

	/*@ loop invariant \base_addr(dest) == \base_addr(tmp);
	    loop invariant \base_addr(src) == \base_addr(\at(src,Pre));
	    loop invariant \at(src,Pre) <= src <= \at(src,Pre) + strlen(\at(src,Pre));
	    loop invariant \at(dest,Mid) <= dest <= \at(dest,Mid) + strlen(\at(src,Pre));
	    loop invariant src - \at(src,Pre) == dest - \at(dest,Mid);
	    loop invariant valid_str(src);
	    loop invariant \forall integer i; 0 <= i < src - \at(src,Pre) ==> tmp[dest_len + i] == \at(src,Pre)[i];
	    loop assigns \at(dest,Mid)[0..strlen(src)];
	    loop variant strlen(\at(src,Pre)) - (src - \at(src,Pre));
	 */
	while ((*dest++ = *src++) != '\0')
		;
	//@ assert dest[-1] == '\0' && src[-1] == '\0';
	//@ assert valid_str(tmp);
	return tmp;
}
