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
    behavior zero_len:
       assumes strlen(s) == 0;
       assigns \nothing;
       ensures \result == s;
    behavior len:
       assumes strlen(s) > 0;
       assigns s[0..strlen(s)];
       ensures valid_str(\result);
       ensures \forall char *p; s <= p < \result ==> isspace(*p);
       ensures !isspace(*\result);
       ensures \forall char *p;
          \result + strlen(\result) <= p < s + strlen{Old}(s) ==> isspace(*p);
       ensures !isspace(\result[strlen(\result)-1]);
    complete behaviors;
    disjoint behaviors;
 */
char *strim(char *s)
{
	size_t size;
	char *end;

	size = strlen(s);
	if (!size)
		return s;
	//@ assert strlen(s) > 0;
	//@ assert s[strlen(s) - 1] != '\0';

	end = s + size - 1;
	//@ ghost char *oend = end;
	//@ assert end + 1 == s + strlen(s);
	//@ assert oend + 1 == '\0';

	/*@ loop invariant s - 1 <= end <= oend;
	    loop invariant \forall char *p; end < p <= oend ==> isspace(*p);
	    loop variant end - s;
	 */
	while (end >= s && isspace(*end))
		end--;
	//@ assert !isspace(*end) || end == s - 1;
	*(end + 1) = '\0';
	//@ assert end + 1 == '\0';
	//@ assert end > s ==> strlen(end) == 1;
	//@ assert end == s - 1 ==> strlen(s) == 0;
	//@ assert \forall char *p; end + 1 < p <= oend ==> isspace(*p);
	//@ assert valid_str(s);

	return skip_spaces(s);
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
