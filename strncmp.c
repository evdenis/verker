#include "strncmp.h"

/*@ requires valid_strn(cs, count);
    requires valid_strn(ct, count);
    assigns \nothing;
    ensures \result == -1 || \result == 0 || \result == 1;
    behavior equal:
       assumes count == 0 ||
               count > 0  &&
               (\forall integer i; 0 <= i < strnlen(cs, count) ==> (cs[i] == ct[i])) &&
               strnlen(cs, count) == strnlen(ct, count);
       ensures \result == 0;
    behavior len_diff:
       assumes count > 0;
       assumes \forall integer i; 0 <= i < strnlen(cs, count) ==> (cs[i] == ct[i]);
       assumes strnlen(cs, count) != strnlen(ct, count);
       ensures strnlen(cs, count) < strnlen(ct, count) ==> \result == -1;
       ensures strnlen(cs, count) > strnlen(ct, count) ==> \result == 1;
    behavior not_equal:
       assumes count > 0;
       assumes \exists integer i; 0 <= i < strnlen(cs, count) && cs[i] != ct[i];
       ensures \exists integer i; 0 <= i < strnlen(cs, count) &&
               (\forall integer j; 0 <= j < i ==> cs[j] == ct[j]) &&
               (cs[i] != ct[i]) &&
               ((u8 AENO)cs[i] < (u8 AENO)ct[i] ? \result == -1 : \result == 1);
    complete behaviors;
    disjoint behaviors;
 */
int strncmp(const char *cs, const char *ct, size_t count)
{
	unsigned char c1, c2;
	//@ ghost char *ocs = cs;
	//@ ghost char *oct = ct;
	//@ ghost size_t ocount = count;

	/*@ assert \forall integer i; 0 <= i < strnlen(ocs, ocount) ==>
		((cs[i] == ct[i]) <==> (((u8 AENO)cs[i]) == ((u8 AENO)ct[i])));
	*/

	/*@ loop invariant 0 <= count <= ocount;
	    loop invariant ocs <= cs <= ocs + strnlen(ocs, ocount);
	    loop invariant oct <= ct <= oct + strnlen(oct, ocount);
	    loop invariant cs - ocs == ct - oct == ocount - count;
	    loop invariant valid_strn(cs, count) && valid_strn(ct, count);
	    loop invariant strnlen(cs, count) == strnlen(ocs, ocount) - (cs - ocs);
	    loop invariant strnlen(ct, count) == strnlen(oct, ocount) - (ct - oct);
	    loop invariant \forall integer i; 0 <= i < ocount - count ==> ocs[i] == oct[i];
	    loop assigns cs, ct, count;
	    loop variant count;
	*/
	while (count) {
		c1 = /*CODE_CHANGE:*/(unsigned char) AENOC *cs++;
		c2 = /*CODE_CHANGE:*/(unsigned char) AENOC *ct++;
		//@ assert c1 == 0 ==> valid_str(ocs) && strlen(ocs) == strnlen(ocs, ocount) == ocount - count;
		//@ assert c2 == 0 ==> valid_str(oct) && strlen(oct) == strnlen(oct, ocount) == ocount - count;
		if (c1 != c2)
			//@ ghost int res = c1 < c2 ? -1 : 1;
			/*@ for not_equal:
				assert \exists integer i; 0 <= i < strnlen(ocs, ocount) &&
				(\forall integer j; 0 <= j < i ==> ocs[j] == oct[j]) &&
				(ocs[i] != oct[i]) &&
				((u8 AENO)ocs[i] < (u8 AENO)oct[i] ? res == -1 : res == 1) &&
				((size_t) i) == ocount - count && i == ocount - count;
			*/
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

#ifdef DUMMY_MAIN
#include <string.h>

int main(int argc, char *argv[])
{
	int res;
	const char *s1 = "1234567895";
	const char *s2 = "123456789";
	const char *s3 = "1234567899";
	const char *s4 = "1234567890";

	res = strncmp(s1, s1, strlen(s1)+10);
	res = strncmp(s1, s1, strlen(s1) / 2);
	res = strncmp(s1, s2, strlen(s1)+10);
	res = strncmp(s1, s3, strlen(s1)+10);
	res = strncmp(s1, s4, strlen(s1)+10);
	res = res;

	return 0;
}
#endif
