#include "strnlen.h"

size_t strnlen(const char *s, size_t count)
{
	const char *sc;
	/*@ loop invariant \base_addr(s) == \base_addr(sc);
	    loop invariant 0 <= count <= \at(count,Pre);
	    loop invariant s <= sc <= s + strnlen(s,\at(count,Pre));
	    loop invariant sc - s == (\at(count,Pre) - count);
	    loop invariant valid_strn(sc, count);
	    loop invariant strnlen(sc,count) <= strnlen(s,\at(count,Pre)) <= \at(count,Pre);
	    loop invariant \forall size_t i; 0 <= i < sc - s ==> s[i] != '\0';
	    loop invariant sc - s <= strnlen(s, \at(count,Pre));
	    loop variant count;
	 */
	for (sc = s; count--/*@%*/ && *sc != '\0'; ++sc)
		/* nothing */;
	//@ assert *sc == '\0' || count == ((size_t %)(-1));
	//@ assert sc - s <= \at(count,Pre);
	// assert strnlen(s, \at(count,Pre)) == strnlen(sc, \at(count,Pre)) + count;
	// assert (size_t)(sc - s) == sc - s;
	// assert (count == ((size_t %)(-1))) ==> ((size_t)(sc - s) == strnlen(s, (size_t)(sc - s)));
	// assert (count == ((size_t %)(-1))) ==> (\at(count,Pre) == (size_t)(sc - s));
	// assert (count == ((size_t %)(-1))) ==> (size_t)(sc - s) == strnlen(s, \at(count,Pre));
	// assert (count != ((size_t %)(-1))) ==> *sc == '\0';
	// assert (count != ((size_t %)(-1))) ==> count - 1 == s + \at(count,Pre) - sc;
	//@ assert (size_t)(sc - s) == strnlen(s, \at(count,Pre));
	return sc - s;
}