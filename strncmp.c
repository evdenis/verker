#include "strncmp.h"

/*@ requires valid_strn(cs, count);
    requires valid_strn(ct, count);
    assigns \nothing;
    behavior equal:
       assumes count > 0;
       assumes strnlen(cs, count) == strnlen(ct, count);
       assumes \forall integer i; 0 <= i < strnlen(cs, count) ==> (cs[i] == ct[i]);
       ensures \result == 0;
    behavior not_equal:
       assumes count > 0;
       assumes strnlen(cs, count) != strnlen(ct, count) ||
               (\exists integer i; 0 <= i < strnlen(cs, count) && cs[i] != ct[i]);
       ensures \result == -1 || \result == 1;
       //ensures \exists integer i; 0 <= i < strnlen(cs, count) &&
       //        (\forall integer j; 0 <= j < i ==> cs[j] == ct[j]) &&
       //        (cs[i] != ct[i]) &&
       //        ((u8 %)cs[i] < (u8 %)ct[i] ? \result == -1 : \result == 1);
       //ensures strnlen(cs, count) < strnlen(ct, count) ==> \result == -1;
       //ensures strnlen(cs, count) > strnlen(ct, count) ==> \result == 1;
    behavior zero_count:
       assumes count == 0;
       ensures \result == 0;
    complete behaviors;
    disjoint behaviors;
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
	    loop invariant strnlen(cs, count) == strnlen(ocs, ocount) - (cs - ocs);
	    loop invariant strnlen(ct, count) == strnlen(oct, ocount) - (ct - oct);
	    loop invariant \forall integer i; 0 <= i < ocount - count ==>
	                   ((u8 %) ocs[i]) == ((u8 %) oct[i]);
	    loop variant count;
	*/
	while (count) {
		c1 = /*CODE_CHANGE:*/(unsigned char)/*@%*/*cs++;
		c2 = /*CODE_CHANGE:*/(unsigned char)/*@%*/*ct++;
      // assert c1 == 0 ==> valid_str(ocs) && strlen(ocs) == ocount - count;
      // assert c2 == 0 ==> valid_str(oct) && strlen(oct) == ocount - count;
		if (c1 != c2)
         // assert c1 == 0 ==> c2 > c1;
         // assert c2 == 0 ==> c1 > c2;
         // assert c1 == 0 ==> strnlen(ocs, ocount) < strnlen(oct, ocount);
         // assert c2 == 0 ==> strnlen(ocs, ocount) > strnlen(oct, ocount);
			return c1 < c2 ? -1 : 1;
		if (!c1)
         // assert strlen(ocs) == strlen(oct);
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
