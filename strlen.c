#include "strlen.h"

size_t strlen(const char *s)
{
	const char *sc;
	/*@ loop invariant \base_addr(s) == \base_addr(sc);
	    loop invariant s <= sc <= s + strlen(s);
	    loop invariant valid_str(sc);
	    loop invariant strlen(s) == strlen(sc) + (sc - s);
	    loop variant strlen(s) - (sc - s);
	    //loop variant strlen(sc);
	 */
	for (sc = s; *sc != '\0'; ++sc)
		/* nothing */;
	return sc - s;
}