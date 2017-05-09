#include "skip_spaces.h"

char *skip_spaces(const char *str)
{
	//@ ghost char *ostr = str;
	/*@ loop invariant valid_str(str);
	    loop invariant ostr <= str <= ostr + strlen(ostr);
	    loop invariant \forall char *p; ostr <= p < str ==> isspace(*p);
	    loop variant strlen(ostr) - (str - ostr);
	 */
	while (isspace(*str))
		++str;
	return (char *)str;
}