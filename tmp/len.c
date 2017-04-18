
/*@ predicate is_string(char *s) =
      \exists integer n;
         n >= 0 &&
         \valid(s + (0..n)) &&
         s[n] == 0 &&
         (\forall integer i; 0 <= i < n ==> s[i] != 0);
 */

/*@ axiomatic StrLength {
    logic size_t length(char *s) reads s[..];

    axiom length_non_negative :
      \forall char *s; is_string(s) ==> 0 <= length(s);

    axiom length_not_zero :
      \forall char *s; is_string(s) ==> 
      \forall integer i; 0 <= i < length(s) ==> s[i] != 0;

    axiom length_zero :
      \forall char *s; is_string(s) ==> s[length(s)] == 0;

    axiom is_string_valid :
      \forall char *s; is_string(s) ==>
      \forall integer i; 0 <= i <= length(s) ==> \valid(s+i);
    }
 */

/*@ requires is_string(s);
    assigns \nothing;
    ensures \result == length(s);
    ensures s[\result] == 0; 
    ensures \forall integer i; 0 <= i < \result ==> s[i] != 0;
 */
size_t strlen(char * s) {
  size_t len = 0;
  /*@ loop invariant 0 <= len <= length(s);
      loop invariant \forall integer i; 0 <= i < len ==> s[i] != 0;
      loop variant length(s) - len;
   */
  while (s[len] != 0) len++;
  return len;
}

