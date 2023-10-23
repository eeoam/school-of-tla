----------------------------- MODULE duplicates -----------------------------
EXTENDS Integers, Sequences, TLC

S == 1..10

(*--algorithm dup
  variable seq \in S \X S \X S  \X S;
  index = 1;
  seen = {};
  is_unique = TRUE;

begin
  Iterate:
    while index <= Len(seq) do
      if seq[index] \notin seen then
        seen := seen \union {seq[index]};
      else
        is_unique := FALSE;
      end if;
      index := index + 1;
    end while;

end algorithm; *)

=============================================================================
\* Modification History
\* Last modified Mon Oct 23 16:54:08 BST 2023 by eric
\* Created Mon Oct 23 16:53:41 BST 2023 by eric
