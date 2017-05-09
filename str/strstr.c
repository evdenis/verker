#include "strstr.h"

/*@ requires valid_str(s1);
    requires valid_str(s2);
    assigns \nothing;
 */
char *strstr(const char *s1, const char *s2)
{
	size_t l1, l2;

	l2 = strlen(s2);
	if (!l2)
		return (char *)s1;
	l1 = strlen(s1);
	/*@ loop invariant l2 <= l1;
	    loop invariant \at(s1,Pre) <= s1 <= \at(s1,Pre) + strlen(\at(s1,Pre));
	    loop invariant valid_str(s1);
	    loop variant l1;
	 */
	while (l1 >= l2) {
		l1--;
		if (!memcmp(s1, s2, l2))
			return (char *)s1;
		s1++;
	}
	return NULL;
}