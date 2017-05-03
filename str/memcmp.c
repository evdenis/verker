#include "memcmp.h"

__visible int memcmp(const void *cs, const void *ct, size_t count)
{
	const unsigned char *su1, *su2;
	int res = 0;

	/*@ loop invariant 0 <= count <= \at(count,Pre);
	    loop invariant (u8 *)cs <= su1 <= (u8 *)cs + \at(count,Pre);
	    loop invariant (u8 *)ct <= su2 <= (u8 *)ct + \at(count,Pre);
	    loop invariant \base_addr((u8 *)cs) == \base_addr(su1);
	    loop invariant \base_addr((u8 *)ct) == \base_addr(su2);
	    loop invariant su1 - (u8 *)cs ==
	                   su2 - (u8 *)ct ==
	                   \at(count,Pre) - count;
	    loop invariant \forall integer i; 0 <= i < \at(count,Pre) - count ==>
	                   ((u8 *)cs)[i] == ((u8 *)ct)[i];
	    loop invariant res == 0;
	    loop assigns res;
	    loop variant count;
	 */
	for (su1 = cs, su2 = ct; 0 < count; ++su1, ++su2, count--)
		if ((res = *su1 - *su2) != 0)
			break;

	return res;
}
