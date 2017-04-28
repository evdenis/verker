#include "skip_spaces.h"

char *skip_spaces(const char *str)
{
	/*@ loop invariant \base_addr(str) == \base_addr(\at(str,Pre));
	    loop invariant \at(str,Pre) <= str <= \at(str,Pre) + strlen(\at(str,Pre));
	    loop invariant \forall size_t s; s < str - \at(str, Pre) ==> isspace(str[s]);
	    loop variant strlen(\at(str,Pre)) - (str - \at(str,Pre));
	 */
	while (isspace(*str))
		++str;
	return (char *)str;
}