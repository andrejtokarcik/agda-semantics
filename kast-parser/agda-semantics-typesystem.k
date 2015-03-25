require "modules/unification.k"
require "agda-syntax.k"
require "agda-semantics-normal.k"
require "agda-semantics-decl-fun.k"   // FIXME

module AGDA-SEMANTICS-TYPESYSTEM
  imports UNIFICATION
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-NORMAL
  imports AGDA-SEMANTICS-DECL-FUN

  rule <k> X:Variable => (X, T) /*~> false*/ ...</k>
       <tenv>... X |-> T ...</tenv>
    when #parseToken("Variable", "expr") =/=K X andBool #parseToken("Variable", "x") ==K X //andBool #parseToken("Variable", "x") =/=K X


  rule <k> X:Variable => (X, T) ...</k>
       <tenv>... X |-> T ...</tenv>
    when #parseToken("Variable", "x") =/=K X
    //   <fun> Fun </fun>
    //when notBool (X in keys(Fun))

  rule <k> X:Name => (X, T) ...</k>
       <data>... X |-> T ...</data>

  rule Set I:Int => (Set I, Set (I +Int 1))

  // TODO: move into generic
  rule M:Map[undef/X:Variable] => M when notBool(X in keys(M))  [structural, anywhere]

  rule <k> Pi X:Variable (T1:Expr, _) T2 ~> (. => tenv(TEnv) ~> fenv(Fun)) ...</k>
       <tenv> TEnv => TEnv[T1/X] </tenv>
       <fun> Fun => Fun[^/X] </fun>       // also see http://lists.cs.uiuc.edu/pipermail/k-user/2012-February/000131.html for undef
     when isExprT(T2) =/=K true     // << toto (+ zakomentovany TypeT nizsie) ku krajsiemu vystupu pre pripadu, ked konstruktor targetuje novy
                                    // parametricky datatyp ale bez parametru a teda nevie otypovat vysledny Pi
  context Pi _ _ (HOLE => evalWhnf2(HOLE)) ~> tenv(_) ~> fenv(_)        [result(TypeT)]   //[result(Whnf21ExprT)]  // << bolo whnf21
  rule <k> Pi X:Variable (T1:Expr, Set I1:Int) (T2:Expr, Set I2:Int)
           => freeVariables(T2) <=Set SetItem(X) keys(Fun) ~> true? ~> (Pi X T1 T2, Set maxInt(I1, I2)) ...</k>
       <fun> Fun </fun>   // asi treba zmenit freeVariables na freeVariablesM (postarat sa o meta), zatial necham tak

  rule <k> Lambda X:Variable (T:Expr, _) E ~> (. => tenv(TEnv) ~> fenv(Fun)) ...</k>
       <tenv> TEnv => TEnv[T/X] </tenv>
       <fun> Fun => Fun[^/X] </fun>
    when isExprT(E) =/=K true
  // I guess the following doesn't have to be evalNf2 as the target type of Pi gets fully evaluated
  // when needed after application.
  // actually do we need evalWhnf2 even, according to the same reasoning?
  //context Lambda _ _ (HOLE:Expr => evalWhnf2(HOLE)) ~> tenv(_) ~> fenv(_)  [result(Whnf2ExprT)]
  context Lambda _ _ HOLE ~> tenv(_) ~> fenv(_)
  rule <k> Lambda X:Variable (T:Expr, _:Universe) (E:Expr, T':Expr)
           => freeVariables(E) <=Set SetItem(X) keys(Fun) ~> true? ~> (Lambda X T E, Pi X T T') ...</k>
       <fun> Fun </fun>

  syntax Bool ::= condChich(Expr, Expr)  [function]
  //rule condChich(E:Expr, _:Expr) => #parseToken("Name", "Cons") ==K E
  //rule condChich(_:Expr, E:Expr) => #parseToken("Name", "Succ") #parseToken("Name", "Zero") ==K E

  rule condChich(_:Expr, #symExpr(_)) => true
  //rule condChich(_:Expr, E:Expr) => #parseToken("Name", "Zero") ==K E

  //rule condChich(E:Expr, _:Expr) => #parseToken("Variable", "f2") ==K E
  //rule condChich(_:Expr, E:Expr) => #parseToken("Name", "E") ==K E

  syntax KItem ::= "Chich"
  rule <k> (E1:Expr, T1:Whnf) (E2:Expr, T2:Expr) => T1 == Pi X T T' ~> T2 == T ~> applyMguT((E1 E2, T')) ~> /*tenv(TEnv) ~>*/ fenv(Fun) /*~> Chich*/ ...</k>
       //<tenv> TEnv => TEnv[T2/X] </tenv>    // < we wanna keep all changes to TEnv yet just remove X from the map afterwards, make tenv(Variable) which indacates what to _remove_?
       <fun> Fun => Fun[E2/X] </fun>
    when fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr) andBool condChich(E1, E2) ==K true


  // TODO: replace tsubst with a Fun update?
  rule <k> (E1, T1) (E2, T2) => T1 == Pi X T T' ~> T2 == T ~> applyMguT((E1 E2, T')) ~> /*tenv(TEnv) ~>*/ fenv(Fun) ...</k> //~> tenv(TEnv) ~> fenv(Fun) ...</k>  //~> tsubst(E2/X)
       //<tenv> TEnv => TEnv[T2/X] </tenv>
       <fun> Fun => Fun[E2/X] </fun>
    when fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr) andBool condChich(E1, E2) =/=K true

  // NOTE: not every updateMgu is guaranteed to actually update the mgu.
  // e.g. if T is identical to T', <mgu /> content remains the same
  syntax KItem ::= Expr "==" Expr   //[strict(all(context('eval)))]
  rule <k> T == T' => . ...</k>
       <mgu> Theta => updateMgu(Theta, T, T') </mgu>    //[transition]

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

  syntax FunRestore ::= Nf2ExprT

  // TODO: move to some generic utils module
  syntax KItem ::= tenv(Map)
  //context (HOLE:ExprT => evalNf2(HOLE)) ~> tenv(_)   [result(Nf2ExprT)]
  rule <k> _:ExprT ~> (tenv(TEnv) => .) ...</k>
       <tenv> _ => TEnv </tenv>

  syntax KItem ::= fenv(Map)
  // T@Fun below to enforce evaluation, else evalWhnf may return immediately (in case T is already in Whnf) without any evaluation whatsoever
  rule <k> ((E, T:Expr) => evalNf(T@Fun) ~> (E, HOLE)) ~> fenv(_) ...</k>
       <fun> Fun </fun>
       <dbg>... . => ListItem(T) </dbg>
    when needEval(T, Fun) //[heat]
  rule <k> (evalNf(T:Nf) ~> (E, HOLE) => (E, T)) ~> (fenv(Fun') => .) ...</k>
       <fun> Fun => Fun' </fun>
    when notBool needEval(T, Fun) //[cool]
  syntax KItem ::= l(Map) | s(Set) // need wrappersssz
  rule <k> R:FunRestore ~> (fenv(Fun') => .) ...</k>
       <fun> Fun => Fun' </fun>
       //<dbg>... . => ListItem(R) ListItem(l(Fun)) ListItem(isNf2ExprT(R)) ListItem(needEval(R, Fun)) </dbg>
    when isNf2ExprT(R) ==K true impliesBool notBool needEval(R, Fun)   // prevent bypassing of the specialised rules above

  syntax Bool ::= needEval(K, Map)  [function]
  rule needEval((_, T:Expr) => T, _)
  rule needEval(E:Expr, _) => true when isNf(E) =/=K true
  // do *not* want freeVariablesM here
  rule needEval(E, Rho) => notBool isEmptySet(intersectSet(freeVariables(E), keys(Rho) -Set boundKeys(Rho))) [owise]
  // -Set boundKeys not necessary because binder takes care of it?
  // -- it *is* necessary since the var may have been bound in a 'higher' bounder, not in this one,
  //    i.e. it will be superfluous only for the var bound just now

  // special rules for unification
  // TODO: remove, should be taken care of as part of eval [within whnf2eval1]
  rule eqns((eqn(((Lambda X:Variable _:Expr E1:Expr) E2:Expr),,E':Expr) => eqn(E1[E2/X],,E')),,_)   [anywhere]
  rule eqns((eqn(E':Expr,,((Lambda X:Variable _:Expr E1:Expr) E2:Expr)) => eqn(E1[E2/X],,E')),,_)   [anywhere]


  /*
  rule eqns((eqn([E:Expr],,E':Expr) => eqn(E,,E')),,_)   [anywhere]
  rule eqns((eqn(E:Expr,,[E':Expr]) => eqn(E,,E')),,_)   [anywhere]
  */

endmodule
