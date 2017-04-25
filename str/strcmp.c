#include "strcmp.h"

int strcmp(const char *cs, const char *ct)
{
	unsigned char c1, c2;

	/*@ loop invariant \base_addr(\at(cs,Pre)) == \base_addr(cs);
	    loop invariant \base_addr(\at(ct,Pre)) == \base_addr(ct);
	    loop invariant \at(cs,Pre) <= cs <= \at(cs,Pre) + strlen(\at(cs,Pre));
	    loop invariant \at(ct,Pre) <= ct <= \at(ct,Pre) + strlen(\at(ct,Pre));
	    loop invariant \forall size_t s; s < cs - \at(cs,Pre) ==> cs[s] == ct[s];
	    loop variant strlen(cs);
	*/
	while (1) {
		c1 = /*CODE_CHANGE:*/(unsigned char)/*@%*/ *cs++;
		c2 = /*CODE_CHANGE:*/(unsigned char)/*@%*/ *ct++;
		if (c1 != c2)
			return c1 < c2 ? -1 : 1;
		if (!c1)
			break;
	}
	//@ assert c1 == 0 && c2 == 0;
	return 0;
}