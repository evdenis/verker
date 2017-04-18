
/*@ axiomatic String {
    logic integer strlen(char *s) reads s[0..];
    axiom strlen_pos_or_null:
      \forall char* s; \forall integer i;
          (0 <= i <= 2147483647
          && (\forall integer j; 0 <= j < i ==> s[j] != '\0')
          && s[i] == '\0') ==> strlen(s) == i;
   
    axiom strlen_neg:
      \forall char* s;
          (\forall integer i; 0 <= i <= 2147483647 ==> s[i] != '\0')
          ==> strlen(s) < 0;
    }
   
    lemma strlen_upper_bound:
       \forall char* s; strlen(s) <= 2147483647;
     
    lemma strlen_before_null:
       \forall char* s; \forall integer i; 0 <= i < strlen(s) ==> s[i] != '\0';
   
    lemma strlen_at_null:
       \forall char* s; 0 <= strlen(s) ==> s[strlen(s)] == '\0';
   
    lemma strlen_not_zero:
    \forall char* s; \forall integer i;
       0 <= i <= strlen(s) && s[i] != '\0' ==> i < strlen(s);
   
    lemma strlen_zero:
    \forall char* s; \forall integer i;
       0 <= i <= strlen(s) && s[i] == '\0' ==> i == strlen(s);
   
    lemma strlen_sup:
    \forall char* s; \forall integer i;
       0 <= i <= 2147483647 && s[i] == '\0' ==> 0 <= strlen(s) <= i;
   
    lemma strlen_shift:
    \forall char* s; \forall integer i;
       0 <= i <= strlen(s) ==> strlen(s + i) == strlen(s) − i;
   
    lemma strlen_create:
    \forall char* s; \forall integer i;
       0 <= i <= 2147483647 && s[i] == '\0' ==> 0 <= strlen(s) <= i;
   
    lemma strlen_create_shift:
    \forall char* s; \forall integer i; \forall integer k;
       0 <= k <= i <= 2147483647 && s[i] == '\0'
          ==> 0 <= strlen(s+k) <= i − k;
   
    predicate valid_string(char *s) =
       0 <= strlen(s) && \valid(s+(0..strlen(s)));
 */

/*@ requires valid_string(str);
    ensures \result == strlen(str);
 */
size_t cstrlen(const char *str) {
  const char *s;
  //@ ghost int i = 0;

  /*@ loop invariant 0 <= i <= strlen(str);
      loop invariant s == str + i;
      loop variant strlen(str) - i;
   */
  for (s = str; *s; s+=1) /*@ ghost i++;*/  ;
  return (s - str);
}
