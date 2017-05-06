#include "strpbrk.h"

/*@ requires valid_str(cs);
    requires valid_str(ct);
    assigns \nothing;
    behavior found:
       ensures cs <= \result <= cs + strlen(cs);
       ensures \forall integer i; 0 <= i <= strlen(ct) ==> \result[i] == ct[i];
       //ensures \forall integer i; 
    behavior not_found:
       //assumes \forall integer i; 0 <= i <= 
       ensures \result == \null;
    complete behaviors;
    disjoint behaviors;
 */
char *strpbrk(const char *cs, const char *ct)
{
	const char *sc1, *sc2;

	/*@ loop invariant cs <= sc1 <= cs + strlen(cs);
	    loop invariant valid_str(sc1);
	    loop invariant \forall integer i; 0 <= i < sc1 - cs ==>
	                   (\forall integer j; 0 <= j < sc2 - ct ==> );
	    loop variant strlen(cs) - (sc1 - cs);
	 */
	for (sc1 = cs; *sc1 != '\0'; ++sc1) {
		/*@ loop invariant ct <= sc2 <= ct + strlen(ct);
		    loop invariant valid_str(sc2);
		    loop invariant \forall integer i; 0 <= i < sc2 - ct ==> cs[i] == ct[i];
		    loop variant strlen(ct) - (sc2 - ct);
		 */
		for (sc2 = ct; *sc2 != '\0'; ++sc2) {
			if (*sc1 == *sc2)
				return (char *)sc1;
		}
	}
	return NULL;
}