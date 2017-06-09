#include "strpbrk.h"

char *strpbrk(const char *cs, const char *ct)
{
	const char *sc1, *sc2;

	/*@ loop invariant cs <= sc1 <= cs + strlen(cs);
	    loop invariant valid_str(sc1);
	    loop invariant \forall char *p, *t;
	                   cs <= p < sc1 &&
	                   ct <= t < ct + strlen(ct) ==>
	                   *p != *t;
	    loop invariant strpbrk(cs, ct) == strpbrk(sc1, ct);
	    loop variant strlen(cs) - (sc1 - cs);
	 */
	for (sc1 = cs; *sc1 != '\0'; ++sc1) {
		/*@ loop invariant ct <= sc2 <= ct + strlen(ct);
		    loop invariant valid_str(sc2);
		    loop invariant \forall char *t; ct <= t < sc2 ==> *sc1 != *t;
		    loop invariant in_array(ct, *sc1) ==> in_array(sc2, *sc1);
		    loop variant strlen(ct) - (sc2 - ct);
		 */
		for (sc2 = ct; *sc2 != '\0'; ++sc2) {
			if (*sc1 == *sc2)
				/*@ assert \exists char *p, *t;
				   cs <= p < cs + strlen(cs) &&
				   ct <= t < ct + strlen(ct) &&
				   *p == *t &&
				   p == sc1 && t == sc2;
				*/
				/*@ assert \forall char *p, *t;
				   cs <= p < sc1 &&
				   ct <= t < ct + strlen(ct) ==>
				   *p != *t;
				*/
				return (char *)sc1;
		}
		//@ assert \forall char *t; ct <= t < ct + strlen(ct) ==> *sc1 != *t;
		//@ assert \forall char *p, *t; cs <= p <= sc1 && ct <= t < ct + strlen(ct) ==> *p != *t;
	}
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
