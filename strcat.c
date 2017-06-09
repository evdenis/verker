#include "strcat.h"

char *strcat(char *dest, const char *src)
{
	char *tmp = dest;
	//@ ghost size_t dest_len = strlen(tmp);

	/*@ loop invariant tmp <= dest <= tmp + dest_len;
	    loop invariant valid_str(dest);
	    loop variant dest_len - (dest - tmp);
	 */
	while (*dest)
		dest++;
	//@ assert *dest == '\0';
	//@ assert dest == tmp + dest_len;
	//@ ghost char *osrc = src;
	//@ ghost char *mdest = dest;

	/*@ loop invariant osrc <= src <= osrc + strlen(osrc);
	    loop invariant mdest <= dest <= mdest + strlen(osrc);
	    loop invariant src - osrc == dest - mdest;
	    loop invariant valid_str(src);
	    loop invariant \forall integer i; 0 <= i < src - osrc ==>
	                   mdest[i] == osrc[i];
	    loop assigns mdest[0..strlen(osrc)];
	    loop variant strlen(osrc) - (src - osrc);
	 */
	while ((*dest++ = *src++) != '\0')
		;
	//@ assert \forall integer i; 0 <= i < dest_len ==> \at(dest[i],Pre) == tmp[i];
	//@ assert dest[-1] == '\0' && src[-1] == '\0';
	//@ assert dest - 1 == tmp + dest_len + strlen(osrc);
	//@ assert strlen(osrc) == src - osrc - 1;
	//@ assert \exists size_t n; tmp[n] == '\0' && \valid(tmp+(0..n)) && n == (size_t) (dest_len + strlen(osrc));
	//@ assert valid_str(tmp);
	return tmp;
}
