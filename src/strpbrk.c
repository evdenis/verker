#include "strpbrk.h"

char *strpbrk(const char *cs, const char *ct)
{
	const char *sc1, *sc2;

	//@ ghost size_t k = 0;
	//@ ghost size_t m = 0;
	/*@ loop invariant idx:      sc1 == cs + k;
	    loop invariant bound:    0 <= k <= strlen(cs);
	    loop invariant len:      strlen(cs) == strlen(sc1) + k;
	    loop invariant valid:    valid_str(sc1);
	    loop invariant rejected: \forall integer i; 0 <= i < k ==> !in_array(ct, cs[i]);
	    loop invariant same:     strpbrk(cs, ct) == strpbrk(sc1, ct);
	    loop assigns sc1, sc2, k, m;
	    loop variant strlen(cs) - k;
	 */
	for (sc1 = cs; *sc1 != '\0'; ++sc1) {
		//@ ghost m = 0;
		/*@ loop invariant iidx:   sc2 == ct + m;
		    loop invariant ibound: 0 <= m <= strlen(ct);
		    loop invariant ilen:   strlen(ct) == strlen(sc2) + m;
		    loop invariant ivalid: valid_str(sc2);
		    loop invariant inone:  \forall integer i; 0 <= i < m ==> ct[i] != *sc1;
		    loop assigns sc2, m;
		    loop variant strlen(ct) - m;
		 */
		for (sc2 = ct; *sc2 != '\0'; ++sc2) {
			if (*sc1 == *sc2) {
				//@ ghost valid_str_len((char *)sc2);
				//@ assert m < strlen(ct);
				//@ ghost in_array_intro((char *)ct, *sc1, m);
				//@ ghost valid_str_len((char *)cs);
				return (char *)sc1;
			}
			//@ ghost valid_str_shift((char *)sc2);
			//@ ghost m++;
		}
		//@ assert !in_array(ct, *sc1);
		//@ ghost valid_str_shift((char *)sc1);
		//@ ghost k++;
	}
	//@ ghost valid_str_len((char *)cs);
	//@ ghost valid_str_len((char *)ct);
	//@ ghost strpbrk_range((char *)cs, (char *)ct);
	return NULL;
}


#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 0 && size % 2 == 0 && data[(size/2) - 1] == '\0' && data[size-1] == '\0') {
		strpbrk((const char *)data, (const char *)(data + size / 2));
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	char * res;
	const char *find = "1234567890";

	res = strpbrk("abcbcd", find);
	res = strpbrk("123456", find);
	res = strpbrk("abc023", find);
	res = strpbrk("",       find);
	res = res;

	return 0;
}
#endif
