require "agda-syntax-pretty.k"

module AGDA-SEMANTICS
  imports AGDA-SYNTAX-PRETTY

  syntax K ::= removeMetaData(K) [function]
  rule removeMetaData(annotated _ K => K)
  rule removeMetaData(KLabel:KLabel(KList:KList)) => KLabel(removeMetaDataL(KList)) when KLabel =/=KLabel 'annotated__
  syntax KList ::= removeMetaDataL(KList)
  rule removeMetaDataL(.KList) => .KList
  rule removeMetaDataL(K:K,,KList:KList) => removeMetaData(K),,removeMetaDataL(KList)



  rule Module _ _ Decls => Decls
  rule Syntax _ _ => .
  rule Postulate Sigs => Sigs
  /*
  rule <k> TypeSig AInf N E => . ...</k>    // E should be already processed via strictness
       <ctx> Gamma (. => N |-> E) </ctx>
    when notBool (N in keys(Gamma))
  */
  rule <k> N:Name : E:Expr => . ...</k>
       <ctx>... . => N |-> E ...</ctx>
  //rule Pi (TypedBindings _ (Arg AInf (TBind _ ((BName N _ _) BndNs => BndNs)))) (E => Pi () E)  when size(BndNs) >Int 1
  rule TypedBindings ATypdBnd => ATypdBnd
  rule Arg AInf TypdBnd => TypdBnd

  /*
  // don't have to check whether N is already bound or that the new type
  // is compatible with previous one, do we?
  rule <k> TBind _ ((BName N _ _) BndNs => BndNs) E => (N -> E) ...</k>
       <ctx>... N |-> (_ => E) ...</ctx>
  rule TBind _ .BoundNameL _ => .  [structural]
  */
endmodule
