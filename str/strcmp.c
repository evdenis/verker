#include "strcmp.h"

/*@ axiomatic StrCmp {
    logic integer cmp(char a, char b) =
       a == b ? 0 : a > b ? 1 : -1;

    logic integer strncmp(char *cs, char *ct, integer n) =
       n == -1 ? 0 : (cs[n] == ct[n] ? strncmp(cs+1, ct+1, n-1) : cmp(cs[n], ct[n]));
    logic integer strcmp(char *cs, char *ct) = strncmp(cs, ct, strlen(cs));
    predicate equaln(char *cs, char *ct, size_t n) = strncmp(cs, ct, n) == 0;
    predicate equal(char *cs, char *ct) = strcmp(cs, ct) == 0;

    lemma range:
       \forall char *cs, *ct, size_t n;
       \valid(cs+(0..n)) && \valid(ct+(0..n)) ==>
          -1 <= strncmp(cs, ct, n) <= 1;

    lemma defn_equal:
       \forall char *cs, *ct, size_t n;
       \valid(cs+(0..n)) && \valid(ct+(0..n)) &&
       (\forall size_t i; i <= n ==> cs[i] == ct[i]) ==>
          strncmp(cs, ct, n) == 0;
    lemma defn_less:
       \forall char *cs, *ct, size_t n, k;
       \valid(cs+(0..n)) && \valid(ct+(0..n)) && k <= n &&
       (\forall size_t i; i < k ==> cs[i] == ct[i]) &&
       cs[k] < ct[k] ==>
          strncmp(cs, ct, n) == -1;
    lemma defn_greater:
       \forall char *cs, *ct, size_t n, k;
       \valid(cs+(0..n)) && \valid(ct+(0..n)) && k <= n &&
       (\forall size_t i; i < k ==> cs[i] == ct[i]) &&
       cs[k] > ct[k] ==>
          strncmp(cs, ct, n) == 1;

    lemma iter_one:
       \forall char *cs, *ct, size_t n;
       \valid(cs+(0..n)) && \valid(ct+(0..n)) &&
       n > 0 && *cs == *ct ==>
          strncmp(cs, ct, n) == strncmp(cs+1, ct+1, n-1);
    lemma at_end:
       \forall char *cs, *ct;
       \valid(cs) && \valid(ct) ==>
       strncmp(cs, ct, 0) == cmp(*cs, *ct);
    }
 */

/*@ requires valid_str(cs);
    requires valid_str(ct);
    assigns \nothing;
    ensures \result == strcmp(cs, ct);
 */
int strcmp(const char *cs, const char *ct)
{
	unsigned char c1, c2;

	/*@ loop invariant \base_addr(\at(cs,Pre)) == \base_addr(cs);
	    loop invariant \base_addr(\at(ct,Pre)) == \base_addr(ct);
	    loop invariant valid_str(cs) && valid_str(ct);
	    loop invariant \at(cs,Pre) <= cs <= \at(cs,Pre) + strlen(\at(cs,Pre));
	    loop invariant \at(ct,Pre) <= ct <= \at(ct,Pre) + strlen(\at(ct,Pre));
	    loop invariant cs - \at(cs,Pre) == ct - \at(ct,Pre);
	    loop invariant \forall size_t i; 0 <= i < cs - \at(cs,Pre) ==>
	       \at(cs,Pre)[i] == \at(ct,Pre)[i];
	    loop invariant strlen(\at(cs,Pre)) == strlen(cs) + (cs - \at(cs,Pre));
	    loop invariant strcmp(\at(cs,Pre), \at(ct,Pre)) == strcmp(cs, ct);
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
	//@ assert equal(\at(cs,Pre), \at(ct, Pre));
	return 0;
}
