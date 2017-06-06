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
    assigns \nothing;
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
	    loop variant strlen(os) - (s - os);
	 */
	do {
		if (*s == (char)/*@%*/c)
			last = s;
	} while (*s++);
	//@ assert s[-1] == '\0';
	//@ assert s == os + strlen(os) + 1;
	//@ assert (\exists char *p; os <= p < os + strlen(os) && *p == (char %) c) ==> (last != \null);
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
