#include "skip_spaces.h"

char *skip_spaces(const char *str)
{
	/*@ loop invariant \base_addr(str) == \base_addr(\at(str,Pre));
	    loop invariant valid_str(str);
	    loop invariant \at(str,Pre) <= str <= \at(str,Pre) + strlen(\at(str,Pre));
	    loop invariant \forall char *p; \at(str,Pre) <= p < str ==> isspace(*p);
	    loop variant strlen(\at(str,Pre)) - (str - \at(str,Pre));
	 */
	while (isspace(*str))
		++str;
	return (char *)str;
}