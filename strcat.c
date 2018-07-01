#include "strcat.h"

char *strcat(char *dest, const char *src)
{
	char *tmp = dest;
	//@ ghost size_t dest_len = strlen(tmp);

	/*@ loop invariant tmp <= dest <= tmp + dest_len;
	    loop invariant valid_str(dest);
	    loop invariant \forall integer i; 0 <= i < dest - tmp ==> tmp[i] != '\0';
	    loop variant dest_len - (dest - tmp);
	 */
	while (*dest)
		dest++;
	//@ assert *dest == '\0';
	//@ assert dest == tmp + dest_len;
	//@ assert strlen(tmp) == dest_len;
	//@ ghost char *osrc = src;
	//@ ghost char *mdest = dest;

	/*@ loop invariant osrc <= src <= osrc + strlen(osrc);
	    loop invariant mdest <= dest <= mdest + strlen(osrc);
	    loop invariant src - osrc == dest - mdest;
	    loop invariant valid_str(src);
	    loop invariant \forall integer i; 0 <= i < src - osrc ==>
	                   mdest[i] == osrc[i];
	    loop invariant \forall integer i; 0 <= i < dest - tmp ==> tmp[i] != '\0';
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
	/*@ assert valid_str(tmp) &&
	    (tmp[(size_t)(dest_len + strlen(osrc))] == '\0') &&
	    (\forall integer i; 0 <= i < (size_t)(dest_len + strlen(osrc)) ==> tmp[i] != '\0');
	 */
	//@ assert strlen(tmp) == (size_t) (dest_len + strlen(osrc));
	return tmp;
}

#ifdef DUMMY_MAIN
#include <string.h>

int main(int argc, char *argv[])
{
	const char *s = "12345";
	char d[strlen(s) + 4];

	d[0] = '1'; d[1] = '1'; d[2] = '1'; d[3] = '\0';
	strcat(d, s);

	return 0;
}
#endif
