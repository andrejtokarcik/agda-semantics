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

  // TODO: move into generic
  rule M:Map[undef/X:Variable] => M when notBool(X in keys(M))  [structural, anywhere]

  rule <k> Pi X:Variable (T1:Expr, _) T2 ~> (. => tenv(TEnv) ~> fenv(Fun)) ...</k>
       <tenv> TEnv => TEnv[T1/X] </tenv>
       <fun> Fun:Map => Fun[undef/X] </fun>       // also see http://lists.cs.uiuc.edu/pipermail/k-user/2012-February/000131.html for undef
     when isExprT(T2) =/=K true     // << toto (+ zakomentovany TypeT nizsie) ku krajsiemu vystupu pre pripadu, ked konstruktor targetuje novy
                                    // parametricky datatyp ale bez parametru a teda nevie otypovat vysledny Pi
  context Pi _ _ (HOLE:Expr => eval2(HOLE)) ~> tenv(_) ~> fenv(_)        [result(TypeT)]   //[result(Whnf21ExprT)]  // << bolo whnf21
  rule Pi X:Variable (T1:Expr, Set I1:Int) (T2:Expr, Set I2:Int) => (Pi X T1 T2, Set maxInt(I1, I2))

  //context Lambda _ (HOLE:Expr => whnf2(HOLE)) _         [result(TypeT)]
  //context Lambda _ ((HOLE:Expr => eval(HOLE)), _:Whnf) _  [result(Val)]
  //context Lambda _ (HOLE:Val => whnf(HOLE), _:Whnf) _   [result(Whnf)]
  rule <k> Lambda X:Variable (T:Expr, _) _ ~> (. => tenv(TEnv) ~> fenv(Fun)) ...</k>
       <tenv> TEnv => TEnv[T/X] </tenv>  //[structural]
       <fun> Fun => Fun[undef/X] </fun>
  context Lambda _ _ (HOLE:Expr => eval2(HOLE)) ~> tenv(_) ~> fenv(_)  [result(Whnf2ExprT)]
  rule Lambda X:Variable (T:Expr, _:Universe) (E:Expr, T':Expr) => (Lambda X T E, Pi X T deval(T'))

  syntax Bool ::= condChich(Expr, Expr)  [function]
  //rule condChich(E:Expr, _:Expr) => #parseToken("Name", "Cons") ==K E
  //rule condChich(_:Expr, E:Expr) => #parseToken("Name", "Succ") #parseToken("Name", "Zero") ==K E

  rule condChich(_:Expr, #symExpr(_)) => true
  //rule condChich(_:Expr, E:Expr) => #parseToken("Name", "Zero") ==K E

  //rule condChich(E:Expr, _:Expr) => #parseToken("Variable", "f2") ==K E
  //rule condChich(_:Expr, E:Expr) => #parseToken("Name", "E") ==K E

  syntax KItem ::= "Chich"
  rule <k> (E1:Expr, T1:Whnf@Fun) (E2:Expr, T2:Expr) => /*Chich ~>*/ T1@Fun == Pi X T T' ~> T2 == T@Fun ~> applyMguT((E1 E2, T')) ~> fenv(Fun') ...</k>
       //<tenv> TEnv => TEnv[T2/X] </tenv>
       <fun> Fun' => Fun[E2/X] </fun>
    when fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr) andBool true //condChich(E1, E2) ==K true


  // TODO: replace tsubst with a Fun update?
  rule <k> (E1, T1@Fun) (E2, T2) => T1@Fun == Pi X T T' ~> T2 == T@Fun ~> applyMguT((E1 E2, T')) ~> fenv(Fun') ...</k> //~> tenv(TEnv) ~> fenv(Fun) ...</k>  //~> tsubst(E2/X)
       //<tenv> TEnv => TEnv[T2/X] </tenv>
       <fun> Fun' => Fun[E2/X] </fun>
    when fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr) andBool false //condChich(E1, E2) =/=K true

  // NOTE: not every updateMgu is guaranteed to actually update the mgu.
  // e.g. if T is identical to T', <mgu /> content remains the same
  // TODO: turn whnf into a deval'ing context and use here?
  syntax KItem ::= Expr "==" Expr   [strict(all(context('eval)))]
  rule <k> T == T' => . ...</k>
       <mgu> Theta => updateMgu(Theta, deval(T), deval(T')) </mgu>    //[transition]

  syntax KItem ::= applyMguT(ExprT)
  /*
  rule <k> applyMguT((E, T)) => (E, eval(applyMgu(Theta, T))) ...</k>
       <meta> Meta => applyMgu(Theta, Meta) </meta>
       <tenv> TEnv => applyMgu(Theta, TEnv) </tenv>    // remove?
       <mgu> Theta => .Mgu </mgu>
  */

  rule <k> applyMguT((E, T)) => (E, applyMgu(Theta, T)) ...</k>
       <meta> Meta => applyMgu(Theta, Meta) </meta>
       <tenv> TEnv => applyMgu(Theta, TEnv) </tenv>    // remove?
       <mgu> Theta => .Mgu </mgu>        //[transition]
       <fun> Fun </fun>

  syntax EnvRecovery ::= ExprT

  // TODO: move to some generic utils module
  syntax KItem ::= tenv(Map)
  context (HOLE:ExprT => eval2(HOLE)) ~> tenv(_)   [result(ValWhnf2ExprT)]
  rule <k> _:EnvRecovery ~> (tenv(TEnv) => .) ...</k>
       <tenv> _ => TEnv </tenv>

  syntax KItem ::= Muh(EnvRecovery) | "Muh"
  syntax KItem ::= fenv(Map)
  context (HOLE:ExprT => eval2(HOLE)) ~> fenv(_)   [result(ValWhnf2ExprT)]
  rule <k> _:EnvRecovery ~> (fenv(Fun) => .) ...</k>
       <fun> _ => Fun </fun>

  // special rules for unification
  // TODO: remove, should be taken care of as part of eval [within whnf2eval1]
  rule eqns((eqn(((Lambda X:Variable _:Expr E1:Expr) E2:Expr),,E':Expr) => eqn(E1[E2/X],,E')),,_)   [anywhere]
  rule eqns((eqn(E':Expr,,((Lambda X:Variable _:Expr E1:Expr) E2:Expr)) => eqn(E1[E2/X],,E')),,_)   [anywhere]


  /*
  rule eqns((eqn([E:Expr],,E':Expr) => eqn(E,,E')),,_)   [anywhere]
  rule eqns((eqn(E:Expr,,[E':Expr]) => eqn(E,,E')),,_)   [anywhere]
  */

endmodule
