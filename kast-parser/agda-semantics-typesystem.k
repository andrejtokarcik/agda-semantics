require "modules/unification.k"
require "agda-syntax.k"
require "agda-semantics-normal.k"
require "agda-semantics-decl-fun.k"   // FIXME

module AGDA-SEMANTICS-TYPESYSTEM
  imports UNIFICATION
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-NORMAL
  imports AGDA-SEMANTICS-DECL-FUN

  rule <k> X:Variable => (X, T) ...</k>
       <tenv>... X |-> T ...</tenv>
    //   <fun> Fun </fun>
    //when notBool (X in keys(Fun))

  rule <k> X:Name => (X, T) ...</k>
       <data>... X |-> T ...</data>

  rule Set I:Int => (Set I, Set (I +Int 1))

  rule <k> Pi X:Variable (T1:Expr, _) T2 ~> (. => env(TEnv, Fun)) ...</k>
       <tenv> TEnv => TEnv[T1/X] </tenv>
       <fun> Fun:Map => Fun[undef/X] </fun>       // also see http://lists.cs.uiuc.edu/pipermail/k-user/2012-February/000131.html for undef
     when isExprT(T2) =/=K true     // << toto (+ zakomentovany TypeT nizsie) ku krajsiemu vystupu pre pripadu, ked konstruktor targetuje novy
                                    // parametricky datatyp ale bez parametru a teda nevie otypovat vysledny Pi
  context Pi _ _ (HOLE:Expr => whnf2(HOLE)) ~> env(_, _)        [result(TypeT)]   //[result(Whnf21ExprT)]  // << bolo whnf21
  rule Pi X:Variable (T1:Expr, Set I1:Int) (T2:Expr, Set I2:Int) => (Pi X T1 T2, Set maxInt(I1, I2))

  //context Lambda _ (HOLE:Expr => whnf2(HOLE)) _         [result(TypeT)]
  //context Lambda _ ((HOLE:Expr => eval(HOLE)), _:Whnf) _  [result(Val)]
  //context Lambda _ (HOLE:Val => whnf(HOLE), _:Whnf) _   [result(Whnf)]
  rule <k> Lambda X:Variable (T:Expr, _) _ ~> (. => env(TEnv, Fun)) ...</k>
       <tenv> TEnv => TEnv[T/X] </tenv>  //[structural]
       <fun> Fun => Fun[undef/X] </fun>
  context Lambda _ _ (HOLE:Expr => eval2(HOLE)) ~> env(_, _)  [result(Whnf2ExprT)]
  rule Lambda X:Variable (T:Expr, _:Universe) (E:Expr, T':Expr) => (Lambda X T E, Pi X T T')

  // TODO: replace tsubst with a Fun update?
  rule (E1:Expr, T1:Whnf) (E2:Expr, T2:Expr) => T1 == Pi X T T' ~> T2 == T ~> (E1 E2, T') ~> tsubst(E2/X)
    when fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr)

  // NOTE: not every updateMgu is guaranteed to actually update the mgu.
  // e.g. if T is identical to T', no update occurs.
  syntax KItem ::= Expr "==" Expr   //[strict(all(context('eval)))]
  rule <k> T == T' => . ...</k>
       <mgu> Theta => updateMgu(Theta, T, T') </mgu>  [transition]

  rule <k> (_, T:Expr => applyMgu(Theta, T)) ...</k>
       <meta> Meta => applyMgu(Theta, Meta) </meta>
       <tenv> TEnv => applyMgu(Theta, TEnv) </tenv>    // FIXME?
       <mgu> Theta => .Mgu </mgu>
    when Theta =/=K .Mgu    // <-- necessary, else infinite recursion

  syntax KItem ::= "tsubst" "(" Expr "/" Variable ")"
  rule <k> (_, T:Expr => T[E/X]) ~> (tsubst(E/X) => .) ...</k>
       <mgu> Theta </mgu>   // <mgu> .Mgu </mgu> doesn't work properly; the [anywhere] rule expanding .Mgu isn't anywhere enough, eh?
    when Theta ==K .Mgu     // hence, need this to guarantee that <mgu /> has been applied on the ExprT

  syntax EnvRecovery ::= ExprT

  // TODO: move to some generic utils module
  syntax KItem ::= env(Map, Map)
  rule <k> _:EnvRecovery ~> (env(TEnv, Fun) => .) ...</k>
       <tenv> _ => TEnv </tenv>
       <fun> _ => Fun </fun>

  // special rules for unification
  // TODO: remove, should be taken care of as part of eval [within whnf2eval1]
  rule eqns((eqn(((Lambda X:Variable _:Expr E1:Expr) E2:Expr),,E':Expr) => eqn(E1[E2/X],,E')),,_)   [anywhere]
  rule eqns((eqn(E':Expr,,((Lambda X:Variable _:Expr E1:Expr) E2:Expr)) => eqn(E1[E2/X],,E')),,_)   [anywhere]
endmodule
