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
	    loop variant strlen(s) - (p - s);
	 */
	for (p = s; *p != '\0'; ++p) {
		/*@ loop invariant reject <= r <= reject + strlen(reject);
		    loop invariant \forall char *c; reject <= c < r ==> *c != *p;
		    loop variant strlen(reject) - (r - reject);
		 */
		for (r = reject; *r != '\0'; ++r) {
			if (*p == *r)
				return count;
		}
		++count;
	}
	return count;
}