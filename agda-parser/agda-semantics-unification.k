require "modules/unification.k"
require "agda-semantics-common.k"

module AGDA-SEMANTICS-UNIFICATION
  //imports AGDA-SEMANTICS-DECL-FUN  // for debug

  imports UNIFICATION
  imports AGDA-SEMANTICS-COMMON

  // Not every updateMgu is actually guaranteed to update the mgu;
  // e.g. if T is identical to T', <mgu /> content remains the same.

  syntax KItem ::= Expr "==" Expr | K "#==" K
  rule E == E' => nf(E) #== nf(E')
  rule <k> nf(E) #== E' => nf(applyMgu(Theta, E)) ~> HOLE #== E' ...</k>
       <mgu> Theta </mgu>
  rule nf(E) ~> HOLE #== E' => E #== E'  when isNf(E)
  rule <k> E #== nf(E') => nf(applyMgu(Theta, E')) ~> E #== HOLE ...</k>
       <mgu> Theta </mgu>
  rule nf(E') ~> E #== HOLE => E #== E'  when isNf(E')
  rule <k> E #== E' => . ...</k>
       <mgu> Theta => updateMgu(Theta, E, E') </mgu>
    when getKLabel(E) =/=KLabel 'nf andBool getKLabel(E') =/=KLabel 'nf andBool
         isMguError(updateMgu(Theta, E, E')) =/=K true
  syntax KItem ::= "BREAK"
  // FIXME tu Theta a updateMgu si viem zistit aj potom v resolveFunClauses, nemusim predavat ako arg
  rule <k> E #== E' => resolveFunClauses(Theta, updateMgu(Theta, E, E'), ListItem(E), ListItem(E')) ...</k>
       <mgu> Theta </mgu>  //=> resolveFunClauses(Theta, updateMgu(Theta, E, E'), E, E') </mgu>
    when getKLabel(E) =/=KLabel 'nf andBool getKLabel(E') =/=KLabel 'nf andBool
         isMguError(updateMgu(Theta, E, E')) andBool
         troublesomeFunClauses(updateMgu(Theta, E, E'))

  syntax KItem ::= "unifyConf"
  rule R:KResult ~> unifyConf => unifyConf ~> R  [structural]
  rule <k> unifyConf => . ...</k>
       <sig> Sigma => applyMgu(Theta, Sigma) </sig>
       <tenv> Gamma => applyMguKeys(Theta, Gamma) </tenv>
       <tenvRestore> TEnvR => applyMguKeysL(Theta, TEnvR) </tenvRestore>
       <fenv> Rho => applyMgu(Theta, Rho) </fenv>
       <metavars> Meta => applyMgu(Theta, Meta) </metavars>
       <mgu> Theta => .Mgu </mgu>
    when isMguError(Theta) =/=K true

  syntax KItem ::= unify(K)
  rule <k> unify(K:K) => applyMgu(Theta, K) ...</k>
       <mgu> Theta </mgu>

  syntax Bool ::= troublesomeFunClauses(Mgu)  [function]
  rule troublesomeFunClauses(clash(C1,,C2)) => true
    when isFunClauses(leftmost(C1)) orElseBool isFunClauses(leftmost(C2))

  syntax KItem ::= "TUSOM" K K //Int LHS Map
  syntax KItem ::= "MguXX" Mgu
  syntax KItem ::= resolveFunClauses(Mgu, Mgu, List, List)     //[function]
  syntax List ::= "stop"

  // nepozeraj len na leftmost v E1 ale na leftmost v kazdom argu E1
  rule resolveFunClauses(_, _, ListItem(E1 => E2) _, ListItem(E2 => E1) _)
    when isFunClauses(leftmost(E1)) =/=K true andBool isFunClauses(leftmost(E2))
  rule resolveFunClauses(_, clash((C1 => C2),,(C2 => C1)), _, _)
    when isFunClauses(leftmost(C1)) =/=K true andBool isFunClauses(leftmost(C2))
  rule resolveFunClauses(Theta, clash(C1,,C2), ListItem(E1) _, ListItem(E2) _) => /*TUSOM 
    freshFunName(E1) freshFunName(subExpr(numReqArgs(leftmost(E1)), E1)) numReqArgs(leftmost(E1))
    suitableLHS(Theta, leftmost(E1), C2)
    getMatching(freshFunName(subExpr(numReqArgs(leftmost(E1)), E1)), suitableLHS(Theta, leftmost(E1), C2)) ~> */
    //TUSOM subExpr(numReqArgs(leftmost(E1)), E1) suitableLHS(Theta, leftmost(E1), C2) ~>
    //MguXX updateMgu(Theta, subExpr(numReqArgs(leftmost(E1)), E1), suitableLHS(Theta, leftmost(E1), C2)) ~>
    //MguXX updateMgu(updateMgu(Theta, freshFunName(subExpr(numReqArgs(leftmost(E1)), E1)), suitableLHS(Theta, leftmost(E1), C2)), E1, E2) ~>
    subExpr(numReqArgs(leftmost(E1)), E1) #== suitableLHS(Theta, leftmost(E1), C2) ~> E1 == E2 ~> chich
    //updateMgu(Theta, freshFunName(E1)[getMatching(freshFunName(subExpr(numReqArgs(leftmost(E1)), E1)), suitableLHS(Theta, leftmost(E1), C2))], E2)
    when isFunClauses(leftmost(C1)) andBool isFunClauses(leftmost(E1)) andBool
         leftmost(C1) ==K leftmost(E1) //////andBool
         //(any(isVariable, args(E1)) orBool any(isSymbolicExpr, args(E1))) andBool
         //matchable(C2
         // reverted isMatching should be a sufficient test...? (normally LHS is the first argument of isMatching)
    ////////isMatching(freshFunName(subExpr(numReqArgs(leftmost(E1)), E1)), suitableLHS(Theta, leftmost(E1), C2))
    // when: updateMgu so suitableLHS neurobi MguError
  rule resolveFunClauses(Theta, clash(C1,,C2), (. => stop args(E1)) (ListItem(E1) => .) _, (. => stop args(E2)) (ListItem(E2) => .) _) //=> TUSOM l(args(E1)) l(args(E2))
    when isFunClauses(leftmost(C1)) andBool
         ((isFunClauses(leftmost(E1)) ==K true andBool leftmost(C1) =/=K leftmost(E1)) orBool
          (isFunClauses(leftmost(E1)) =/=K true andBool isFunClauses(leftmost(E2)) =/=K true))


  syntax Expr ::= subExpr(Int, Expr)   [function]
  rule subExpr(I, E) => E when lengthList(args(E)) <=Int I
  rule subExpr(I, E _ => E)  [owise]

  syntax LHS ::= suitableLHS(Mgu, FunClauses, Expr)  [function]
  //rule suitableLHS(Theta, FunClauses(_, .List), _) => false
  rule suitableLHS(Theta, FunClauses(_, ListItem(L = R) _), T) => renameVariables(L)
    when isMguError(updateMgu(Theta, leftmost(R), leftmost(T))) =/=K true
  rule suitableLHS(_, FunClauses(_, (_:ListItem => .) _), _)  [owise]


  /*
  syntax MetaVariable
  rule isMetaVariable(K) => true  when getKLabel(K) ==KLabel #symExpr
  // it holds that Variable ::= MetaVariable  (i.e., #symExpr's are also Variable)
  */

  syntax List ::= applyMguKeysL(Mgu, List)   [function]
  rule applyMguKeysL(Theta, .List) => .List
  rule applyMguKeysL(Theta, _ (ListItem(m(TEnv)) => .List)) (.List => ListItem(m(applyMguKeys(Theta, TEnv))))

  syntax Map ::= applyMguKeys(Mgu, Map)  [function]
  rule applyMguKeys(_, .Map) => .Map
  rule applyMguKeys(Theta, _ (K |-> V => .Map)) (.Map => (K |-> applyMgu(Theta, V)) (applyMgu(Theta, K) |-> applyMgu(Theta, V)))
    when isVariable(K) andThenBool isVariable(applyMgu(Theta, K)) andThenBool applyMgu(Theta, K) =/=K K
  rule applyMguKeys(Theta, _ (K |-> V => .Map)) (.Map => K |-> applyMgu(Theta, V))  [owise]

  // The LHS of eqn() below gets replaced with the RHS: swapping the sides
  // when necessary.
  // - Metavariables should be always substituted *for*, not vice versa.
  rule eqns((eqn(K,,#symExpr(I)) => eqn(#symExpr(I),,K)),,_)
    when getKLabel(K) =/=KLabel #symExpr  [structural, anywhere]
  //rule eqns((eqn(K,,K') => .KList),,_)
  //  when isVariable(K) andBool isVariable(K')  [structural, anywhere]

  rule eqns((eqn(X:Variable,,#symVariable(I)) => eqn(#symVariable(I),,X)),,_)
    when getKLabel(X) =/=KLabel #symVariable  [structural, anywhere]
  //rule eqns((eqn(#symExpr(I),,#symVariable(J)) => eqn(#symVariable(J),,#symExpr(I))),,_)  [structural, anywhere]

endmodule
