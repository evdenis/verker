#include "strncat.h"

/*@ requires valid_strn(src, count);
    requires valid_str(dest);
    requires strlen(dest) + count <= SIZE_MAX;
    requires \valid(dest+(0..strlen(dest)+count));
    assigns dest[strlen(dest)..strlen(dest)+count];
    ensures \result == dest;
    ensures valid_str(\result);
    ensures \forall integer i; 0 <= i < strlen{Old}(\old(dest)) ==>
            \old(dest[i]) == \result[i];
    ensures \forall integer i;
            strlen{Old}(dest) <= i < strlen{Old}(dest) + strnlen(src, count) ==>
            src[i - strlen{Old}(dest)] == \result[i];
 */
char *strncat(char *dest, const char *src, size_t count)
{
	char *tmp = dest;

	if (count) {
		//@ ghost size_t dest_len = strlen(tmp);
		//@ ghost size_t ocount = count;
		//@ ghost char *osrc = src;
		//@ ghost size_t src_len = strnlen(osrc, ocount);

		/*@ loop invariant tmp <= dest <= tmp + dest_len;
		    loop invariant valid_str(dest);
		    loop variant dest_len - (dest - tmp);
		 */
		while (*dest)
			dest++;
		//@ assert *dest == '\0';
		//@ assert dest == tmp + dest_len;
		//@ ghost char *mdest = dest;

		/*@ loop invariant 0 <= count <= ocount;
		    loop invariant osrc <= src <= osrc + src_len;
		    loop invariant mdest <= dest <= mdest + src_len;
		    loop invariant valid_str(src);
		    loop invariant src - osrc == dest - mdest == ocount - count;
		    loop invariant \forall integer i; 0 <= i < src - osrc ==>
		                   mdest[i] == osrc[i];
		    loop assigns mdest[0..src_len];
		    loop variant count;
		 */
		while ((*dest++ = *src++) != 0) {
			if (--count == 0) {
				*dest = '\0';
				break;
			}
		}
		//@ assert \forall integer i; 0 <= i < dest_len ==> \at(dest[i],Pre) == tmp[i];
		/*@ assert (count > 0) ==>
		              (dest[-1] == '\0' && src[-1] == '\0') &&
		              (src_len == src - osrc - 1);
		 */
		/*@ assert (count == 0) ==>
		              (src_len == ocount) &&
		              (*dest == '\0');
		 */
		// assert count > 0 ==> dest - 1 == tmp + dest_len + strlen(osrc);
		//@ assert \exists size_t n; tmp[n] == '\0' && \valid(tmp+(0..n)) && n == (size_t) (dest_len + 	src_len);
		//(\exists size_t n; (n < cnt) && s[n] == '\0' && \valid(s+(0..n))) ||
		//\valid(s+(0..cnt));
		//@ assert valid_str(tmp);
	}
	return tmp;
}

#ifdef DUMMY_MAIN
#include <string.h>

int main(int argc, char *argv[])
{
	const char *s = "12345";
	char d[strlen(s) + 4];
	d[0] = '1'; d[1] = '1'; d[2] = '1'; d[3] = '\0';
	strncat(d, s, strlen(s));
	strncat(d, s, strlen(s) - 3);
	return 0;
}
#endif
