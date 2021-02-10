#include "strlcat.h"
/*@ predicate eqstr{L1, L2}(char *s1, char *s2, size_t len) =
	\forall size_t i; 0 <= i < len ==> \at(s1[i], L1) == \at(s2[i], L2);
*/

/*@ requires valid_str(dest);
    requires valid_str(src);
    requires \valid(dest+(0..count));
    requires strlen(dest) + strlen(src) <= SIZE_MAX;
    requires count > strlen(dest);
    ensures \result == strlen{Pre}(\at(dest, Pre)) + strlen(src);
	ensures \forall size_t i; 0 <= i < strlen{Pre}(\at(dest, Pre)) ==>
		dest[i] == \at(dest[i], Pre);
    ensures valid_str(dest);

	behavior count_len:
		assumes (strlen(dest) + strlen(src)) < count;
    	assigns dest[strlen{Old}(\old(dest))..strlen{Old}(\old(dest)) + strlen(src)];
		ensures eqstr{Post, Pre}(dest + strlen{Pre}(dest), src, strlen(src));
	behavior len_count:
		assumes (strlen(dest) + strlen(src)) >= count;
    	assigns dest[strlen{Old}(\old(dest))..(count - 1)];
		ensures eqstr{Post, Pre}(dest+strlen{Pre}(dest), src, (size_t)(count - 1 - strlen{Pre}(dest)));
	complete behaviors;
	disjoint behaviors;
		
 */
size_t strlcat(char *dest, const char *src, size_t count)
{
	size_t dsize = strlen(dest);
	size_t len = strlen(src);
	size_t res = dsize + len;
	//@ ghost char *odest = dest;
	//@ ghost size_t olen = len;
	//@ ghost size_t ocount = count;
	//@ assert res <= strlen(dest) + strlen(src);
	//@ assert dsize == strlen{Pre}(\at(dest, Pre));
	//@ assert \valid(dest+(0..dsize));

	/* This would be a bug */
	//BUG_ON(dsize >= count);

	//@ assert eqstr{Here, Pre}(odest, dest, dsize);
	dest += dsize;
	//@ assert eqstr{Here, Pre}(odest, \at(dest, Pre), dsize);

//@ ghost Mid:
	//@ assert valid_str(dest);
	//@ assert dest == \at(dest,Pre) + strlen(\at(dest,Pre));
	//@ assert *dest == '\0';

	//@ assert eqstr{Here, Here}(dest - dsize, odest, dsize);
	count -= dsize;
	if (len >= count)
		//@ assert dsize + olen >= ocount;
	  //count = len+1;
		len = count-1;
	//@ assert len < count;
	// assert \valid(dest+(0..len-1));
	//@ assert \at(dest, Pre) == dest - dsize;

	
	//@ assert dsize == strlen{Pre}(\at(dest, Pre));
	//@ assert eqstr{Here, Pre}(odest, \at(dest, Pre), dsize);
	memcpy(dest, src, len);
	//@ assert eqstr{Here, Pre}(odest, \at(dest, Pre), dsize);
	//@ assert dsize == strlen{Pre}(\at(dest, Pre));


	//@ assert \at(dest, Pre) == dest - dsize;
	//@ assert len == 0 || odest[dsize] != '\0';
	//@ assert \valid(dest+(-dsize..0));
	dest[len] = 0;
	//@ assert dest[len] == '\0';
	//@ assert \exists size_t n; dest[n] == '\0' && \valid(dest+(0..n)) && n == len;
	//@ assert odest[len + dsize] == '\0';
	//@ assert \valid(odest+(0..(ocount - 1)));
	//@ assert (len + dsize) < ocount;
	//@ assert \exists size_t n; odest[n] == '\0' && \valid(odest+(0..n)) && n <= ocount - 1;
	
	

	//@ assert eqstr{Here, Pre}(odest, \at(dest, Pre), dsize);
	//@ assert dsize == strlen{Pre}(\at(dest, Pre));
	/*@ assert \forall size_t i; 0 <= i < dsize ==>
		odest[i] == \at(dest[i], Pre);
	*/
	/*@ assert (dsize + olen) >= ocount ||
		\forall size_t i; 0 <= i < len ==>
			\at(dest,Mid)[i] == src[i];
	*/
	/*@ assert (dsize + olen) <  ocount ||
		\forall size_t i; 0 <= i < count - 1 ==>
			\at(dest,Mid)[i] == src[i];
	*/

	/*@ assert (dsize + olen) >= ocount ||
		eqstr{Here, Pre}(odest + dsize, src, strlen(src));
	*/
	/*@ assert (dsize + olen) <  ocount ||
		 eqstr{Here, Pre}(odest + dsize, src, (size_t)(ocount - 1 - dsize));
	*/

	return res;
}

#ifdef DUMMY_MAIN
#include <string.h>

int main(int argc, char *argv[])
{
	const char *s = "12345";
	char d[strlen(s) + 4];

	d[0] = '1'; d[1] = '1'; d[2] = '1'; d[3] = '\0';
	strlcat(d, s, strlen(s));
	strlcat(d, s, strlen(s) - 3);

	return 0;
}
#endif
