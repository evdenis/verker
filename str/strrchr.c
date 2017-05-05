#include "strrchr.h"

/* axiomatic Strrchr {
    logic char *strrchr_helper(char *s, char c, char *pos) =
       *s == c ? (*s ? strrchr_helper(s+1,c,s) : pos) : (*s ? strrchr_helper(s+1,c,pos) : pos);
    logic char *strrchr(char *s, char c) = strrchr_helper(s, c, \null);

    lemma mem:
       \forall char *str, char c;
       valid_str(str) ==>
          (str <= strrchr(str, c) <= str + strlen(str) &&
           \base_addr(str) == \base_addr(strrchr(str, c))) ^^
          strrchr(str, c) == \null;
    lemma defn:
       \forall char *str, char c;
       valid_str(str)
    }
 */

/*@ requires valid_str(s);
    requires ((char %)c) == c;
    assigns \nothing;
    behavior found:
       assumes \exists integer i; 0 <= i <= strlen(s); s[i] == c;
       ensures s <= \result <= s + strlen(s);
       ensures \forall integer i; \result < i < s + strlen(s) ==> s[i] != c;
       ensures *\result == c;
    behavior not_found:
       assumes \exists integer i; 0 <= i <= strlen(s); s[i] == c;
       ensures \result == \null;
    complete behaviors;
    disjoint behaviors;
 */
char *strrchr(const char *s, int c)
{
	const char *last = NULL;
	/*@ loop invariant \base_addr(s) == \base_addr(\at(s,Pre));
	    loop invariant \at(s,Pre) <= s <= \at(s,Pre) + strlen(\at(s,Pre));
	    loop invariant valid_str(s);
	    loop invariant last == \null || *last == c;
	    loop variant strlen(\at(s,Pre)) - (s - \at(s,Pre));
	 */
	do {
		if (*s == (char)c)
			last = s;
	} while (*s++);
	//@ assert s[-1] == '\0';
	return (char *)last;
}
