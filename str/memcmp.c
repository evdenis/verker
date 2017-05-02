#include "memcmp.h"

/*@ requires \typeof(cs) <: \type(unsigned char *);
    requires \typeof(ct) <: \type(unsigned char *);
    requires \valid(((unsigned char *)cs)+(0..count));
    requires \valid(((unsigned char *)ct)+(0..count));
    requires \base_addr((unsigned char *)cs) == \base_addr((unsigned char *)ct) ^^
             \base_addr((unsigned char *)cs) != \base_addr((unsigned char *)ct);
    assigns \nothing;
 */
__visible int memcmp(const void *cs, const void *ct, size_t count)
{
	const unsigned char *su1, *su2;
	int res = 0;

	/*@ loop invariant 0 <= count <= \at(count,Pre);
	    loop invariant (unsigned char *)cs <= su1 <= (unsigned char *)cs + \at(count,Pre);
	    loop invariant (unsigned char *)ct <= su2 <= (unsigned char *)ct + \at(count,Pre);
	    loop invariant \base_addr((unsigned char *)cs) == \base_addr(su1);
	    loop invariant \base_addr((unsigned char *)ct) == \base_addr(su2);
	    loop invariant su1 - (unsigned char *)cs ==
	                   su2 - (unsigned char *)ct ==
	                   \at(count,Pre) - count;
	    loop invariant \forall integer i; 0 <= i < su1 - (unsigned char *)cs ==>
	                   ((unsigned char *)cs)[i] == ((unsigned char *)ct)[i];
	    loop variant count;
	 */
	for (su1 = cs, su2 = ct; 0 < count; ++su1, ++su2, count--)
		if ((res = *su1 - *su2) != 0)
			break;
	//@ assert *su1 == *su2 ==> count == 0;
	return res;
}
