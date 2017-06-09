#include "strcmp.h"

int strcmp(const char *cs, const char *ct)
{
	unsigned char c1, c2;

	/*@ loop invariant valid_str(cs) && valid_str(ct);
	    loop invariant \at(cs,Pre) <= cs <= \at(cs,Pre) + strlen(\at(cs,Pre));
	    loop invariant \at(ct,Pre) <= ct <= \at(ct,Pre) + strlen(\at(ct,Pre));
	    loop invariant cs - \at(cs,Pre) == ct - \at(ct,Pre);
	    loop invariant \forall integer i; 0 <= i < cs - \at(cs,Pre) ==>
	                   \at(cs,Pre)[i] == \at(ct,Pre)[i];
	    loop invariant strlen(cs) == strlen(\at(cs,Pre)) - (cs - \at(cs,Pre));
	    //loop invariant strcmp(\at(cs,Pre), \at(ct,Pre)) == strcmp(cs, ct);
	    loop variant strlen(\at(cs,Pre)) - (cs - \at(cs,Pre));
	*/
	while (1) {
		c1 = /*CODE_CHANGE:*/(unsigned char)/*@%*/ *cs++;
		c2 = /*CODE_CHANGE:*/(unsigned char)/*@%*/ *ct++;
		if (c1 != c2)
			//@ ghost int res = c1 < c2 ? -1 : 1;
			/*@ assert \exists integer i; 0 <= i <= strlen(\at(cs,Pre)) &&
			      (\forall integer j; 0 <= j < i ==> \at(cs,Pre)[j] == \at(ct,Pre)[j]) &&
			      (\at(cs,Pre)[i] != \at(ct,Pre)[i]) &&
			      ((u8 %)\at(cs,Pre)[i] < (u8 %)\at(ct,Pre)[i] ? res == -1 : res == 1) &&
			      i == cs - \at(cs,Pre)-1;
			 */
			return c1 < c2 ? -1 : 1;

		if (!c1)
			break;
		//@ assert \at(cs,Pre)[cs - \at(cs,Pre)-1] == \at(ct,Pre)[cs - \at(cs,Pre)-1];
	}

	return 0;
}

#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 0 && size % 2 == 0 && data[(size/2) - 1] == '\0' && data[size-1] == '\0') {
		strcmp((const char *)data, (const char *)(data + size / 2));
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	int res;
	const char *s1 = "1234567895";
	const char *s2 = "123456789";
	const char *s3 = "1234567899";
	const char *s4 = "1234567890";
	res = strcmp(s1, s1);
	res = strcmp(s1, s2);
	res = strcmp(s1, s3);
	res = strcmp(s1, s4);
	res = res;
	return 0;
}
#endif
