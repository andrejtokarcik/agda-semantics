require "modules/unification.k"
require "agda-syntax.k"
require "agda-semantics-normal.k"

module AGDA-SEMANTICS-TYPESYSTEM
  imports UNIFICATION
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-NORMAL

  rule <k> X:Variable => (X, T) ...</k>
       <tenv>... X |-> T ...</tenv>

  rule <k> X:Name => (X, T) ...</k>
       <data>... X |-> T ...</data>

  rule Set I:Int => (Set I, Set (I +Int 1))

  rule <k> Pi X:Variable (T1:Expr, _) _ ~> (. => tenv(TEnv)) ...</k>
       <tenv> TEnv => TEnv[T1/X] </tenv>  //[structural]
  context Pi _ _ (HOLE:Expr => whnf21(HOLE)) ~> tenv(_)  [result(TypeT)]
  rule Pi X:Variable (T1:Expr, Set I1:Int) (T2:Expr, Set I2:Int) => (Pi X T1 T2, Set maxInt(I1, I2))

  rule <k> Lambda X:Variable (T:Expr, _) _ ~> (. => tenv(TEnv)) ...</k>
       <tenv> TEnv => TEnv[T/X] </tenv>  //[structural]
  context Lambda _ _ (HOLE:Expr => whnf2(HOLE)) ~> tenv(_)  [result(Whnf2ExprT)]
  rule Lambda X:Variable (T:Expr, _:Universe) (E:Expr, T':Expr) => (Lambda X T E, Pi X T T')

  rule (E1:Expr, T1:Whnf) (E2:Expr, T2:Expr) => T1 == Pi X T T' ~> T2 == T ~> (E1 E2, T') ~> tsubst(E2/X)
    when fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr)

  syntax KItem ::= Expr "==" Expr
  rule <k> T == T' => . ...</k>
       <mgu> Theta => updateMgu(Theta, T, T') </mgu> //[transition]

  rule <k> (_, T:Expr => applyMgu(Theta, T)) ...</k>
       <meta> Meta => applyMgu(Theta, Meta) </meta>
       <mgu> Theta => .Mgu </mgu>
    when Theta =/=K .Mgu   // <-- necessary, else infinite recursion

  syntax KItem ::= "tsubst" "(" Expr "/" Variable ")"
  rule <k> (_, T:Expr => T[E/X]) ~> (tsubst(E/X) => .) ...</k>
       <mgu> Theta </mgu>   // <mgu> .Mgu </mgu> doesn't work properly; the [anywhere] rule expanding .Mgu isn't anywhere enough, eh?
    when Theta ==K .Mgu     // hence, need this to guarantee that <mgu /> has been applied on the ExprT

  syntax KItem ::= tenv(Map)
  rule <k> _:ExprT ~> (tenv(TEnv) => .) ...</k>
       <tenv> _ => TEnv </tenv> //[transition]

  // special rules for unification
  rule eqns((eqn(((Lambda X:Variable _:Expr E1:Expr) E2:Expr),,E':Expr) => eqn(E1[E2/X],,E')),,_)   [anywhere]
  rule eqns((eqn(E':Expr,,((Lambda X:Variable _:Expr E1:Expr) E2:Expr)) => eqn(E1[E2/X],,E')),,_)   [anywhere]
endmodule
