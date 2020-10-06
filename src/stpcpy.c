#include "stpcpy.h"

char *stpcpy(char *__restrict__ dest, const char *__restrict__ src)
{
	//@ ghost char *osrc = src;
	//@ ghost char *odest = dest;
	//@ assert valid_str(osrc);

	/*@ loop invariant osrc <= src <= osrc + strlen(osrc);
	    loop invariant odest <= dest <= odest + strlen(osrc);
	    loop invariant valid_str(src);
	    loop invariant dest - odest == src - osrc;
	    loop invariant strlen(src) == strlen(osrc) - (src - osrc);
	    loop invariant \forall integer i; 0 <= i < src - osrc ==> odest[i] == osrc[i];
	    loop assigns src, dest, odest[0..strlen(osrc)];
	    loop variant strlen(osrc) - (src - osrc);
	*/
	while ((*dest++ = *src++) != '\0')
		/* nothing */;

	//@ assert dest[-1] == '\0' && src[-1] == '\0';
	//@ assert valid_str(odest);
	//@ assert (dest - 1) - odest == strlen(osrc);

	return --dest;
}

#ifdef DUMMY_MAIN
#include <string.h>

int main(int argc, char *argv[])
{
	const char *s = "1234567890";
	char d[strlen(s)];

	stpcpy(d, s);

	return 0;
}
#endif
