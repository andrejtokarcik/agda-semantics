require "agda-syntax-pretty.k"

module AGDA-SEMANTICS
  imports AGDA-SYNTAX-PRETTY

  rule Module _ _ Decls => Decls
  rule Syntax _ _ => .
  rule Postulate Sigs => Sigs
  rule <k> N : E => . ...</k>     // E should be already processed via strictness (type-checked)
       <ctx>... . => N |-> E ...</ctx>
  rule <k> L = R => . ...</k>     // both L and R should be processed via strictness (type-checked)
       <sig>... . => L |-> R ...</sig>
endmodule
