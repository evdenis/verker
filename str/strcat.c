#include "strcat.h"

/*@ requires valid_str(src);
    requires valid_str(dest)
	requires \valid(dest+(0..strlen(dest)+strlen(src)-1));
    assigns dest[strlen(dest)..strlen(dest)+strlen(src)-1];
	ensures \result == dest;
 */
char *strcat(char *dest, const char *src)
{
	char *tmp = dest;

	/*@ loop invariant \base_addr(dest) == \base_addr(tmp);
	    loop invariant tmp <= dest <= tmp + strlen(tmp);
		loop invariant valid_str(dest);
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
		loop invariant valid_str(dest);
	 */
	while ((*dest++ = *src++) != '\0')
		;
	//@ assert *dest == '\0' && *src == '\0';
	//@ assert valid_str(tmp);
	return tmp;
}