#include "strrchr.h"


/* axiomatic Strrchr {
    logic char *strrchr_helper(char *s, char c, char *pos) =
       *pos == c ? pos : (pos == s ? (char *) \null : strrchr_helper(s,c,pos-1));
    logic char *strrchr(char *s, char c) = strrchr_helper(s, c, s + strlen(s));

    lemma strrchr_mem:
       \forall char *str, c;
       valid_str(str) ==>
          (str <= strrchr(str, c) <= str + strlen(str)) ^^
          strrchr(str, c) == \null;
    lemma strrchr_res:
       \forall char *str, c;
       valid_str(str) ==>
          strrchr(str, c) == \null ^^ *strrchr(str, c) == c;
    lemma strrchr_at_end_found:
       \forall char *str;
       valid_str(str) && strlen(str) == 0 ==>
       strrchr(str, '\0') == str;
    lemma strrchr_at_end:
       \forall char *str, char c;
       valid_str(str) && strlen(str) == 0 && c != '\0' ==>
       strrchr(str, '\0') == \null;
    lemma defn_non_exists:
       \forall char *str, char c;
       valid_str(str) ==>
          (\forall char *p; str <= p <= str + strlen(str) ==> *p != c) <==>
          (strrchr(str, c) == \null);

    lemma strrchr_defn:
       \forall char *str, c, integer i;
       valid_str(str) && 0 <= i <= strlen(str) &&
       (\forall integer j; i < j <= strlen(str) ==> str[j] != c) &&
       str[i] == c ==>
          str + i == strrchr(str, c);
    lemma strrchr_skipped:
       \forall char *str, c, integer i;
       valid_str(str) &&
       strrchr(str, c) - str < i <= strlen(str) ==>
          str[i] != c;

    lemma strrchr_iter_one:
       \forall char *str, char c;
       valid_str(str) && strlen(str) > 0 && *str != c ==>
          strrchr(str, c) == strrchr(str + 1, c);
    }
 */

/*@ requires valid_str(s);
    assigns \nothing;
    //ensures \result == strrchr(s, (char %) c);
    behavior found:
       assumes \exists char *p; s <= p <= s + strlen(s) && *p == (char %)c;
       ensures s <= \result <= s + strlen(s);
       ensures *\result == (char %)c;
       ensures \forall char *p; \result < p <= s + strlen(s) ==>
               *p != (char %)c;
    behavior not_found:
       assumes \forall char *p; s <= p <= s + strlen(s) ==> *p != (char %)c;
       ensures \result == \null;
    complete behaviors;
    disjoint behaviors;
 */
char *strrchr(const char *s, int c)
{
	const char *last = NULL;
	//@ ghost char *os = s;

	/*@ loop invariant os <= s <= os + strlen(os);
	    loop invariant last == \null ^^ ((os <= last < s) && (*last == (char %)c));
	    loop invariant (last != \null) <==> (\exists char *p; os <= p < s && *p == (char %) c);
	    loop invariant (last == \null) <==> (\forall char *p; os <= p < s ==> *p != (char %)c);
	    loop invariant last != \null ==> (\forall char *p; last < p < s ==> *p != (char %)c);
	    //loop invariant strrchr(s, (char %) c) == strrchr(os, (char %) c);
	    loop variant strlen(os) - (s - os);
	 */
	do {
		if (*s == (char)/*@%*/c)
			last = s;
	} while (*s++);
	//@ assert s[-1] == '\0';
	//@ assert s == os + strlen(os) + 1;
	//@ assert (\exists char *p; os <= p < os + strlen(os) && *p == (char %) c) ==> (last != \null);
	// assert strrchr(\at(s,Pre), (char %) c) == last;
	return (char *)last;
}

#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 1 && data[size-1] == '\0') {
		strrchr((const char *)data + 1, *data);
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	const char *s = "123456788889";
	char *ptr;
	ptr = strrchr(s, '6');
	ptr = strrchr(s, '8');
	ptr = strrchr(s, '\0');
	ptr = ptr;
	return 0;
}
#endif
