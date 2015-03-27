require "agda-syntax.k"

module AGDA-SEMANTICS
  imports AGDA-SYNTAX

  rule Module _ _ Decls => Decls
  rule Syntax _ _ => .
  rule Postulate Sigs => Sigs
  rule <k> TypeSig AInf N E => . ...</k>
       <tenv> Gamma (. => N |-> E) </tenv>
    when notBool (N in keys(Gamma))
  //rule Pi (TypedBindings _ (Arg AInf (TBind _ ((BName N _ _) BndNs => BndNs)))) (E => Pi () E)  when size(BndNs) >Int 1
  rule TypedBindings ATypdBnd => ATypdBnd
  rule Arg AInf TypdBnd => TypdBnd

  /*
  // don't have to check whether N is already bound or that the new type
  // is compatible with previous one, do we?
  rule <k> TBind _ ((BName N _ _) BndNs => BndNs) E => (N -> E) ...</k>
       <tenv>... N |-> (_ => E) ...</tenv>
  rule TBind _ .BoundNameL _ => .  [structural]
  */
endmodule
