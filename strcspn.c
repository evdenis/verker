#include "strcspn.h"

size_t strcspn(const char *s, const char *reject)
{
	const char *p;
	const char *r;
	size_t count = 0;

	/*@ loop invariant s <= p <= s + strlen(s);
	    loop invariant 0 <= count <= strlen(s);
	    loop invariant count == p - s;
	    loop invariant \forall char *c, *t;
	                   s <= c < p && reject <= t < reject + strlen(reject) ==>
	                   *c != *t;
	    loop invariant valid_str(p);
	    loop invariant strcspn(s, reject) == strcspn(p, reject) + count;
	    loop variant strlen(s) - (p - s);
	 */
	for (p = s; *p != '\0'; ++p) {
		/*@ loop invariant reject <= r <= reject + strlen(reject);
		    loop invariant \forall char *c; reject <= c < r ==> *c != *p;
		    loop invariant valid_str(r);
		    loop invariant in_array(reject, *p) ==> in_array(r, *p);
		    loop variant strlen(reject) - (r - reject);
		 */
		for (r = reject; *r != '\0'; ++r) {
			if (*p == *r)
				//@ assert in_array(reject, *p);
				return count;
		}
		//@ assert !in_array(reject, *p);
		++count;
	}
	return count;
}


#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
   if (size > 0 && size % 2 == 0 && data[(size/2) - 1] == '\0' && data[size-1] == '\0') {
      strcspn((const char *)data, (const char *)(data + size / 2));
   }
   return 0;
}
#endif
