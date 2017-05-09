#include "strim.h"

/*@ requires valid_str(s);
    behavior zero_len:
       assumes strlen(s) == 0;
       assigns \nothing;
       ensures \result == s;
    behavior len:
       assumes strlen(s) > 0;
       ensures valid_str(\result);
       ensures !isspace(*\result);
       ensures !isspace(\result[strlen(\result)-1]);
    complete behaviors;
    disjoint behaviors;
 */
char *strim(char *s)
{
	size_t size;
	char *end;

	size = strlen(s);
	if (!size)
		return s;
	//@ assert strlen(s) > 0;
	//@ assert s[strlen(s) - 1] != '\0';

	end = s + size - 1;
	//@ ghost char *oend = end;
	/*@ loop invariant s - 1 <= end <= s + strlen(s) - 1;
	    loop invariant \forall char *p; end < p <= oend ==> isspace(*p);
	    loop variant end - s;
	 */
	while (end >= s && isspace(*end))
		end--;
	//@ assert !isspace(*end) || end == s - 1;
	*(end + 1) = '\0';
	//@ assert valid_str(s);

	return skip_spaces(s);
}