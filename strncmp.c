#include "strncmp.h"

/*@ requires valid_strn(cs, count);
    requires valid_strn(ct, count);
    assigns \nothing;
    //ensures \result == strcmp(cs, ct);
    behavior equal:
       assumes \forall integer i; 0 <= i <= strnlen(cs, count) ==> (u8 %)cs[i] == (u8 %)ct[i];
       ensures \result == 0;
    //behavior not_equal:
    //   assumes \exists integer i; 0 <= i <= strnlen(cs) && (u8 %)cs[i] != (u8 %)ct[i];
    //   ensures \result == -1 || \result == 1;
    //   ensures \exists integer i; 0 <= i <= strnlen(cs) &&
    //           (\forall integer j; 0 <= j < i ==> cs[j] == ct[j]) &&
    //           (cs[i] != ct[i]) &&
    //           ((u8 %)cs[i] < (u8 %)ct[i] ? \result == -1 : \result == 1);
    //complete behaviors;
    //disjoint behaviors;
 */
int strncmp(const char *cs, const char *ct, size_t count)
{
	unsigned char c1, c2;
	//@ ghost char *ocs = cs;
	//@ ghost char *oct = ct;
	//@ ghost size_t ocount = count;

	/*@ loop invariant 0 <= count <= ocount;
	    loop invariant ocs <= cs <= ocs + strnlen(ocs, ocount);
	    loop invariant oct <= ct <= oct + strnlen(oct, ocount);
	    loop invariant cs - ocs == ct - oct == ocount - count;
	    loop invariant valid_strn(cs, count) && valid_strn(ct, count);
	    loop invariant \forall integer i; 0 <= i < cs - ocs ==>
	                   ocs[i] == oct[i];
	    loop invariant strnlen(cs, count) == strnlen(ocs, ocount) - (cs - ocs);
	    loop invariant strnlen(ct, count) == strnlen(oct, ocount) - (ct - oct);
	    loop variant count;
	*/
	while (count) {
		c1 = /*CODE_CHANGE:*/(unsigned char)/*@%*/*cs++;
		c2 = /*CODE_CHANGE:*/(unsigned char)/*@%*/*ct++;
		if (c1 != c2)
			return c1 < c2 ? -1 : 1;
		if (!c1)
			break;
		count--;
		//@ assert ocs[cs - ocs - 1] == oct[cs - ocs - 1];
	}
	return 0;
}

#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
   if (size > 0 && size % 2 == 0 && data[(size/2) - 1] == '\0' && data[size-1] == '\0') {
      strncmp((const char *)data, (const char *)(data + size / 2), size / 2);
   }
   return 0;
}
#endif
