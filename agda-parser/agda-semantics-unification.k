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
  // TODO? dat nf(E:Nf)?
  rule nf(E) ~> HOLE #== E' => E #== E'  when isNf(E)
  rule <k> E #== nf(E') => nf(applyMgu(Theta, E')) ~> E #== HOLE ...</k>
       <mgu> Theta </mgu>
  rule nf(E') ~> E #== HOLE => E #== E'  when isNf(E')
  rule L:LHS ~> E #== HOLE => E #== L //~> BREAKx E L
  rule <k> E #== E' => . ...</k>
       <mgu> Theta => updateMgu(Theta, E, E') </mgu>
    when getKLabel(E) =/=KLabel 'nf andBool getKLabel(E') =/=KLabel 'nf andBool
         isMguError(updateMgu(Theta, E, E')) =/=K true
  // FIXME tu Theta a updateMgu si viem zistit aj potom v resolveFunClauses, nemusim predavat ako arg
  rule <k> E #== E' => resolveFunClauses(Theta, updateMgu(Theta, E, E'), ListItem(E), ListItem(E')) ...</k>
       <mgu> Theta </mgu>  //=> resolveFunClauses(Theta, updateMgu(Theta, E, E'), E, E') </mgu>
    when getKLabel(E) =/=KLabel 'nf andBool getKLabel(E') =/=KLabel 'nf andBool
         isMguError(updateMgu(Theta, E, E')) andBool
         troublesomeFunClauses(updateMgu(Theta, E, E'))


  syntax KItem ::= "BREAKx" K K
  syntax KItem ::= K "errx#==" K
  rule <k> nf(E) errx#== E' => nf(applyMgu(Theta, E)) ~> HOLE errx#== E' ...</k>
       <mgu> Theta </mgu>
  rule nf(E) ~> HOLE errx#== E' => E errx#== E'  when isNf(E)
  rule <k> E errx#== nf(E') => nf(applyMgu(Theta, E')) ~> E errx#== HOLE ...</k>
       <mgu> Theta </mgu>
  rule nf(E') ~> E errx#== HOLE => E errx#== E'  when isNf(E')
  rule L:LHS ~> E errx#== HOLE => E errx#== L //~> BREAKx E L
  rule <k> E errx#== E' => . ...</k>
       <mgu> Theta => updateMgu(Theta, E, E') </mgu>
    when getKLabel(E) =/=KLabel 'nf andBool getKLabel(E') =/=KLabel 'nf andBool
         isMguError(updateMgu(Theta, E, E')) =/=K true
  rule <k> E errx#== E' => resolveFunClauses(Theta, updateMgu(Theta, E, E'), ListItem(E), ListItem(E')) ...</k>
       <mgu> Theta </mgu>
    when getKLabel(E) =/=KLabel 'nf andBool getKLabel(E') =/=KLabel 'nf andBool
         isMguError(updateMgu(Theta, E, E')) andBool
         troublesomeFunClauses(updateMgu(Theta, E, E'))


  syntax KItem ::= "unifyConf"
  rule R:KResult ~> unifyConf => unifyConf ~> R  [structural]
  rule <k> unifyConf => . ...</k>
       <sig> Sigma => applyMgu(Theta, Sigma) </sig>
       <tenv> Gamma => applyMgu/*Keys*/(Theta, Gamma) </tenv>
       <tenvRestore> TEnvR => applyMguL/*KeysL*/(Theta, TEnvR) </tenvRestore>
       <fenv> Rho => applyMgu(Theta, Rho) </fenv>
       <metavars> Meta => extendMeta(applyMgu(Theta, Meta)) </metavars>
       //<metavars> Meta => applyMgu(Theta, Meta) </metavars>
       <mgu> Theta => .Mgu </mgu>

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

  rule resolveFunClauses(_, _, ListItem(E1 => E2) _, ListItem(E2 => E1) _)
    when isFunClauses(leftmost(E1)) =/=K true andBool isFunClauses(leftmost(E2))
  rule resolveFunClauses(_, clash((C1 => C2),,(C2 => C1)), _, _)
    when isFunClauses(leftmost(C1)) =/=K true andBool isFunClauses(leftmost(C2))
  rule resolveFunClauses(Theta, clash(C1,,C2), ListItem(E1) _, ListItem(E2) _) =>
    renameVariablesConf(suitableLHS(Theta, leftmost(E1), C2)) ~> subExpr(numReqArgs(leftmost(E1)), E1) #== HOLE ~> nf(E1) #== nf(E2) //~> chich
    when isFunClauses(leftmost(C1)) andBool isFunClauses(leftmost(E1)) andBool
         leftmost(C1) ==K leftmost(E1) andBool leftmost(C2) ==K leftmost(E2)
         //andBool condit(E2) =/=K true

  syntax Cond ::= condit(Expr)  [function]
  rule condit(E) => true when leftmost(leftmost(leftmost(E))) ==K Data("_+_")

  rule //(. => TUSOM 3 3 ~> isFunClauses(leftmost(C1)) ~> isFunClauses(leftmost(E1)) ~> leftmost(C1) ==K leftmost(E1) ~> leftmost(C2) ==K leftmost(E2)) ~>
       resolveFunClauses(Theta, clash(C1,,C2), ListItem(E1) _, ListItem(E2) _)
       => //nf(applyMgu(updateMgu(Theta, subExpr(numReqArgs(leftmost(E1)), E1), suitableLHS(Theta, leftmost(E1), C2)), E1)) ~>
          //MguXX updateMgu(Theta, subExpr(numReqArgs(leftmost(E1)), E1), suitableLHS(Theta, leftmost(E1), C2)) ~>
          renameVariablesConf(suitableLHS(Theta, leftmost(E1), C2)) ~> subExpr(numReqArgs(leftmost(E1)), E1) #== HOLE ~> nf(E1) errx#== nf(E2) //~> chich
    when isFunClauses(leftmost(C1)) andBool isFunClauses(leftmost(E1)) andBool
         leftmost(C1) ==K leftmost(E1) andBool leftmost(C2) ==K leftmost(E2)
         andBool
         condit(E2) ==K true
 
  rule resolveFunClauses(Theta, clash(C1,,C2), ListItem(E1) L1, ListItem(E2) L2)
       => resolveFunClauses(Theta, clash(C1,,C2), args(E1) L1, args(E2) L2) ~> E1 == E2 //~> chich
    when isFunClauses(leftmost(C1)) andBool
         ((isFunClauses(leftmost(E1)) ==K true andBool (leftmost(C1) =/=K leftmost(E1) orBool leftmost(C2) =/=K leftmost(E2))) orBool
          (isFunClauses(leftmost(E1)) =/=K true andBool isFunClauses(leftmost(E2)) =/=K true))
         andBool condit(E2) =/=K true


  syntax Expr ::= subExpr(Int, Expr)   [function]
  rule subExpr(I, E) => E when lengthList(args(E)) <=Int I
  rule subExpr(I, E _ => E)  [owise]

  syntax LHS ::= suitableLHS(Mgu, FunClauses, Expr)  [function]
  rule suitableLHS(Theta, FunClauses(_, ListItem(L = R) _), T) => L
    when isMguError(updateMgu(Theta, leftmost(R), leftmost(T))) =/=K true
  rule suitableLHS(_, FunClauses(_, (_:ListItem => .) _), _)  [owise]


  syntax MetaVariable
  rule isMetaVariable(K) => true  when getKLabel(K) ==KLabel #symExpr
  // it holds that Variable ::= MetaVariable  (i.e., #symExpr's are also Variable)

  // move to -common or -utils or something
  syntax KItem ::= renameVariablesConf(K) | #renameVarsConf(K, K)
  rule renameVariablesConf(K) => #renameVarsConf(getAlpha(K), K)
  rule <k> #renameVarsConf(Alpha, K) => applySubst(Alpha, K) ...</k>
       <tenv> Gamma => Gamma[#renameVarsCtx(Gamma, Alpha)] </tenv>
  syntax Map ::= #renameVarsCtx(Map, K)  [function]
  rule #renameVarsCtx(_, subst(.KList)) => .Map
  rule #renameVarsCtx(_ (K |-> V), subst((eqn(K,,X) => .KList),,_)) (.Map => X |-> V)
  rule #renameVarsCtx(_, subst((eqn(_,,X) => .KList),,_)) (.Map => X |-> T)  when fresh(T:Expr)  [owise]


  syntax List ::= applyMguL(Mgu, List)   [function]
  rule applyMguL(Theta, .List) => .List
  rule applyMguL(Theta, _ (ListItem(m(TEnv)) => .List)) (.List => ListItem(m(applyMgu(Theta, TEnv))))


  syntax List ::= applyMguKeysL(Mgu, List)   [function]
  rule applyMguKeysL(Theta, .List) => .List
  rule applyMguKeysL(Theta, _ (ListItem(m(TEnv)) => .List)) (.List => ListItem(m(applyMguKeys(Theta, TEnv))))

  syntax Map ::= applyMguKeys(Mgu, Map)  [function]
  rule applyMguKeys(_, .Map) => .Map
  rule applyMguKeys(Theta, _ (K |-> V => .Map)) (.Map => (K |-> applyMgu(Theta, V)) (applyMgu(Theta, K) |-> applyMgu(Theta, V)))
    when isVariable(applyMgu(Theta, K)) andBool applyMgu(Theta, K) =/=K K
  rule applyMguKeys(Theta, _ (K |-> V => .Map)) (.Map => K |-> applyMgu(Theta, V))  [owise]

  syntax Map ::= extendMeta(Map)  [function]
               | #extendMeta(Map, Map)  [function]
  rule extendMeta(M) => #extendMeta(M, .Map)
  rule #extendMeta(.Map, M') => M'
  rule #extendMeta(M (X |-> t(E, T)), M' (.Map => E |-> t(E, T)))
    when isMetaVariable(E) andBool E =/=K X andBool notBool (E in keys(M) keys(M'))
  rule #extendMeta(_ (X |-> V => .Map), _ (.Map => X |-> V))  [owise]

  // The LHS of eqn() below gets replaced with the RHS: swapping the sides
  // when necessary.
  // - Metavariables should be always substituted *for*, not vice versa.
  /*
  rule eqns((eqn(K,,#symExpr(I)) => eqn(#symExpr(I),,K)),,_)
    when getKLabel(K) =/=KLabel #symExpr  [structural, anywhere]
  */
  //rule eqns((eqn(K,,K') => .KList),,_)
  //  when isVariable(K) andBool isVariable(K')  [structural, anywhere]

  // NOTE ked zakomentujem tak cykli
  rule eqns((eqn(K,,#symVariable(I)) => eqn(#symVariable(I),,K)),,_)
    when getKLabel(K) =/=KLabel #symVariable  [structural, anywhere]
  //rule eqns((eqn(#symExpr(I),,#symVariable(J)) => eqn(#symVariable(J),,#symExpr(I))),,_)  [structural, anywhere]

endmodule
