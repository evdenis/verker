#include "memcmp.h"

/*@ requires \typeof(cs) <: \type(u8 *);
    requires \typeof(ct) <: \type(u8 *);
    requires \valid(((u8 *)cs)+(0..count-1));
    requires \valid(((u8 *)ct)+(0..count-1));
    requires \base_addr((u8 *)cs) == \base_addr((u8 *)ct) ^^
             \base_addr((u8 *)cs) != \base_addr((u8 *)ct);
    assigns \nothing;
    behavior equal:
       assumes \forall integer i; 0 <= i < count ==> ((u8 *)cs)[i] == ((u8 *)ct)[i];
       ensures \result == 0;
    behavior diff:
       assumes \exists integer i; 0 <= i < count && ((u8 *)cs)[i] != ((u8 *)ct)[i];
       ensures \exists integer i; 0 <= i < count &&
               (\forall integer j; 0 <= j < i ==> ((u8 *)cs)[j] == ((u8 *)ct)[j]) &&
               ((u8 *)cs)[i] != ((u8 *)ct)[i] &&
               \result == ((u8 *)cs)[i] - ((u8 *)ct)[i];
    complete behaviors;
    disjoint behaviors;
 */
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
