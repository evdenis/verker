#include "strim.h"

/* axiomatic StrimAxiom {
    logic integer left_strim{L}(char *str) reads str;
    logic integer right_strim{L}(char *str) reads str;

    axiom left_strim_range{L}:
       \forall char *str;
          valid_str(str) ==> 0 <= left_strim(str) <= strlen(str);
    axiom right_strim_range{L}:
       \forall char* str;
          valid_str(str) ==> -1 <= right_strim(str) < strlen(str);

    axiom left_strim_spaces{L}:
       \forall char *str, integer i;
          valid_str(str) &&
          0 <= i < strlen(str) &&
          i < left_strim(str) ==>
             isspace(str[i]);
    axiom right_strim_spaces{L}:
       \forall char *str, integer i;
          valid_str(str) &&
          0 <= i < strlen(str) &&
          i > right_strim(str) ==>
             isspace(str[i]);

    axiom left_strim_not_space{L}:
       \forall char *str;
          valid_str(str) &&
          left_strim(str) < strlen(str) ==>
             !isspace(str[left_strim(str)]);
    axiom right_strimNotSpace{L}:
       \forall char *str;
          valid_str(str) &&
          0 <= right_strim(str) ==>
             !isspace(str[right_strim(str)]);

    axiom left_strim_all_space{L}:
       \forall char *str;
          valid_str(str) ==>
             (left_strim(str) == strlen(str) <==> \forall integer i; 0<=i<strlen(str) ==> isspace(str[i]) );
    axiom right_strim_all_space{L}:
       \forall char *str;
          valid_str(str) ==>
             (right_strim(str)==-1 <==> \forall integer i; 0<=i<strlen(str) ==> isspace(str[i]));

    lemma right_strim_is_not_changed_by_skip_spaces:
       \forall char *str;
          valid_str(str) ==>
             right_strim(str) + str == right_strim(skip_spaces(str)) + skip_spaces(str);

    lemma good_string:
       \forall char *str;
          valid_str(str) &&
          (!isspace(str[strlen(str)-1])) ==>
             right_strim(str)==strlen(str)-1;
    }
*/


/* axiomatic SkipSpacesRight {
    logic char *skip_spaces_right(char *str) ;//=
       //isspace(*str) ? skip_spaces(str + 1) : str;
    lemma defn:
       \forall char *str, size_t i;
       valid_str(str) && i <= strlen(str) &&
       (\forall size_t j; j < i ==> isspace(str[j])) &&
       !isspace(str[i]) ==>
          str + i == skip_spaces(str);
    lemma deref:
       \forall char *str; valid_str(str) ==>
          !isspace(*skip_spaces_right(str));
    lemma range:
       \forall char *str;
       valid_str(str) ==>
          str - 1 <= skip_spaces_right(str) < str + strlen(str);
    lemma iter_one:
       \forall char *str;
       valid_str(str) && !isspace(*str) ==>
       skip_spaces(str) == skip_spaces(str+1);
    lemma base_addr:
       \forall char *str;
       valid_str(str) ==>
          \base_addr(str) == \base_addr(skip_spaces(str));
    lemma same:
       \forall char *str;
       \valid(str) && !isspace(*str) ==>
          str == skip_spaces(str);
    lemma skipped_are_spaces:
       \forall char *str, size_t i;
       valid_str(str) &&
       i < skip_spaces(str) - str ==>
          isspace(str[i]);
    }
 */

/*@ requires valid_str(s);
    requires strlen(s) <= LONG_MAX;
    terminates \true;
    exits \false;
    behavior zero_len:
       assumes strlen(s) == 0;
       assigns \result \from s;
       ensures \result == s;
    behavior len:
       assumes strlen(s) > 0;
       assigns s[0..strlen{Pre}(s)];
       assigns \result \from s;
       ensures 0 <= \result - s <= strlen{Pre}(s);
       ensures valid_str(\result);
       ensures \forall integer i; 0 <= i < \result - s ==> isspace(\at(s[i], Pre));
       ensures \forall integer i;
          \result - s + strlen(\result) <= i < strlen{Pre}(s) ==>
          isspace(\at(s[i], Pre));
    complete behaviors;
    disjoint behaviors;
 */
char *strim(char *s)
{
	size_t size;
	char *end;

	//@ ghost valid_str_len(s);
	size = strlen(s);
	if (!size)
		return s;
	//@ assert strlen(s) > 0;
	//@ assert s[strlen(s) - 1] != '\0';

	end = s + size - 1;
	//@ ghost char *oend = end;
	//@ ghost long e = (long)(size - 1);
	//@ assert end + 1 == s + strlen(s);
	//@ assert *(oend + 1) == '\0';

	/*@ loop invariant idx:    end == s + e;
	    loop invariant bound:  -1 <= e <= oend - s;
	    loop invariant spaces: \forall integer i; e < i <= oend - s ==>
	                           isspace(\at(s[i], Pre));
	    loop invariant kept:   \forall integer i; 0 <= i <= oend - s ==>
	                           s[i] == \at(s[i], Pre);
	    loop assigns end, e;
	    loop variant e + 1;
	 */
	while (end >= s && isspace(*end)) {
		end--;
		//@ ghost e--;
	}
	//@ assert !isspace(*end) || end == s - 1;
	*(end + 1) = '\0';
	//@ ghost intro_valid_str_len(s, (size_t)(e + 1));
	char *res = skip_spaces(s);
	//@ ghost long r = res - s;
	//@ assert strlen(s) == e + 1;
	//@ assert 0 <= res - s <= e + 1;
	//@ assert \valid(s+(0..e + 1));
	//@ assert s[e + 1] == '\0';
	//@ assert \forall integer j; 0 <= j < e + 1 ==> s[j] != '\0';
	//@ ghost intro_valid_str_len(s + r, (size_t)(e + 1 - r));
	return res;
}

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	char s1[] = "   test   ";
	char s2[] = " ";
	char s3[] = "";
	char s4[] = "test   ";
	char s5[] = "   test";
	char s6[] = "test";

	strim(s1); strim(s2); strim(s3);
	strim(s4); strim(s5); strim(s6);

	return 0;
}
#endif
