#include "strcpy.h"

char *strcpy(char *dest, const char *src)
{
	char *tmp = dest;
	//@ ghost char *osrc = src;
	//@ assert valid_str(osrc);

	/*@ loop invariant osrc <= src <= osrc + strlen(osrc);
	    loop invariant tmp <= dest <= tmp + strlen(osrc);
	    loop invariant valid_str(src);
	    loop invariant dest - tmp == src - osrc;
	    loop invariant strlen(src) == strlen(osrc) - (src - osrc);
	    loop invariant \forall integer i; 0 <= i < src - osrc ==> tmp[i] == osrc[i];
	    loop variant strlen(osrc) - (src - osrc);
	*/
	while ((*dest++ = *src++) != '\0')
		/* nothing */;
	//@ assert dest[-1] == '\0' && src[-1] == '\0';
	//@ assert valid_str(tmp);
	return tmp;
}

#ifdef DUMMY_MAIN
#include <string.h>

int main(int argc, char *argv[])
{
	const char *s = "1234567890";
	char d[strlen(s)];
	strcpy(d, s);
	return 0;
}
#endif
