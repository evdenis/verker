#include "strncat.h"

/*@ requires valid_str(dest);
    requires \valid(dest+(0..strlen(dest)+strnlen(src, count)));
    requires valid_strn(src, count);
 */
char *strncat(char *dest, const char *src, size_t count)
{
	char *tmp = dest;

	if (count) {
		//@ assert count > 0;
		/*@ loop invariant tmp <= dest <= tmp + strlen(tmp);
		    loop invariant \base_addr(tmp) == \base_addr(dest);
		    loop invariant valid_str(dest);
		    loop variant strlen(tmp) - (dest - tmp);
		 */
		while (*dest)
			dest++;
		//@ ghost Mid:
		//@ assert dest == tmp + strlen(tmp);
		/*@ loop invariant count >= 0;
		    loop invariant \at(src,Pre) <= src <= \at(src,Pre) + strnlen(\at(src,Pre), \at(count,Pre));
		    loop invariant \at(dest,Mid) <= dest <= \at(dest,Mid) + strnlen(\at(src,Pre), \at(count,Pre));
		    loop invariant \base_addr(tmp) == \base_addr(dest);
		    loop invariant \base_addr(\at(src,Pre)) == \base_addr(src);
		    loop invariant valid_str(src);
		    //loop invariant \valid(dest);
		    loop invariant src - \at(src,Pre) == dest - \at(dest,Mid) == \at(count,Pre) - count;
		    loop variant count;
		 */
		while ((*dest++ = *src++) != 0) {
			if (--count == 0) {
				*dest = '\0';
				break;
			}
		}
	}
	return tmp;
}
