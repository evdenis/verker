#include "strcmp.h"

/*@ requires valid_str(cs);
    requires valid_str(ct);
    assigns \nothing;
    ensures \result == -1 || \result == 0 || \result == 1;
    behavior equal:
       assumes \forall integer i; 0 <= i <= strlen(cs) ==> cs[i] == ct[i];
       ensures \result == 0;
    behavior less:
       assumes \exists integer i; 0 <= i <= strlen(cs) && cs[i] < ct[i];
       ensures \result == -1;
    behavior greater:
       assumes \exists integer i; 0 <= i <= strlen(cs) && cs[i] > ct[i];
       ensures \result == 1;
    complete behaviors;
    disjoint behaviors;
 */
int strcmp(const char *cs, const char *ct)
{
	unsigned char c1, c2;

	/*@ loop invariant \base_addr(\at(cs,Pre)) == \base_addr(cs);
	    loop invariant \base_addr(\at(ct,Pre)) == \base_addr(ct);
	    loop invariant valid_str(cs);
	    loop invariant valid_str(ct);
	    loop invariant \at(cs,Pre) <= cs <= \at(cs,Pre) + strlen(\at(cs,Pre));
	    loop invariant \at(ct,Pre) <= ct <= \at(ct,Pre) + strlen(\at(ct,Pre));
	    loop invariant cs - \at(cs,Pre) == ct - \at(ct,Pre);
	    loop invariant \forall integer i; 0 <= i < cs - \at(cs,Pre) ==> \at(cs,Pre)[i] == \at(ct,Pre)[i];
	    loop variant strlen(\at(cs,Pre)) - (cs - \at(cs,Pre));
	*/
	while (1) {
		c1 = /*CODE_CHANGE:*/(unsigned char)/*@%*/ *cs++;
		c2 = /*CODE_CHANGE:*/(unsigned char)/*@%*/ *ct++;
		if (c1 != c2)
			return c1 < c2 ? -1 : 1;
		if (!c1)
			break;
		//@ assert *(cs-1) == *(ct-1);
	}
	//@ assert c1 == 0 && c2 == 0;
	return 0;
}