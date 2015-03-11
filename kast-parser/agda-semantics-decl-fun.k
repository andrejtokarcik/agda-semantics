require "agda-syntax.k"
require "agda-semantics-normal.k"

module AGDA-SEMANTICS-DECL-FUN
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-NORMAL

  syntax Expr ::= closure(Map, Expr)

  rule <k> X:Variable = (E:Expr, T:Whnf) => . ...</k>
       //<fun> Fun (. => X |-> closure(Fun, E)) </fun>
       <fun> Fun (. => X |-> (E[Fun])) </fun>
       <tenv> TEnv (. => X |-> T) </tenv>
         when notBool (X in keys(Fun)) andBool notBool (X in keys(TEnv))

  // TODO: generate closures only for binders?
  /*
  syntax Binder
  rule isBinder(Lambda _ _ _) => true
  rule isBinder(Pi _ _ _) => true
  syntax Whnf ::= Binder
  */
endmodule
