require "agda-semantics-common.k"
require "agda-semantics-unification.k"

module AGDA-SEMANTICS-TYPESYSTEM
  imports AGDA-SEMANTICS-COMMON
  imports AGDA-SEMANTICS-UNIFICATION

  // The offic typechecker reports a variable identifier
  // with underscores as a [function] name in some cases,
  // e.g., in LibVec.agda, foldr's _⊕_.
  rule <k> Name(S) => Var(S) ...</k>  <ctx> Gamma </ctx>  <ncat> NCat </ncat>
    when notBool (Name(S) in keys(NCat)) andBool Var(S) in keys(Gamma)
  rule [infer-variable]:
       <k> X:Variable => t(X, renameBoundVariables(T)) ...</k>
       <ctx>... X |-> T ...</ctx>

  rule <k> N:Name => Nc ...</k>  <ncat>... N |-> Nc ...</ncat>
  rule [infer-name]:
       <k> N:Name => t(N, renameBoundVariables(T)) ...</k>
       <sig>... N |-> T ...</sig>
  rule <k> FunClauses(F, _) => t(F, renameBoundVariables(T)) ...</k>
       <sig>... F |-> T ...</sig>

  rule [infer-universe]:
       Set(Alpha) => t(Set(Alpha), Set(Alpha +Int 1))

  rule [infer-meta]:
       <k> %meta => E ...</k>
       <meta>... . => E |-> t(E, T) ...</meta>
    when fresh(E:Expr) andBool fresh(T:Expr)
    //ensures isMetaVariable(E)
  rule [infer-meta]:
       <k> X:MetaVariable => t(E, renameBoundVariables(T)) ...</k>
       <meta>... X |-> t(E, T) ...</meta>


  // implicit args
  context {HOLE}
  rule {t(E, T)} => t({E}, {T})

  // inaccessible patterns
  syntax Expr ::= DotP(Pattern)
  //rule DotP(E) => Dot(E)
  context DotP(HOLE)::Expr
  rule DotP(t(E, T))::Expr => t(DotP(E), T)


  // for the binders' semantics
  syntax KItem ::= "bound!"

  // XXX: what about putting all the Pi-related rules into a separate module?
  // ... as suggested in the funkons paper

  context (_ : (HOLE => checkSetType(HOLE))) -> _  [infer-pi-arg1, result(SetTypedExpr)]
  rule [bind-pi]:
       <k> (. => saveCtx(Gamma) ~> bound!) ~> (X : t(T1, Set(_))) -> _ ~>
           (. => loadCtx) ...</k>
       <ctx> Gamma => Gamma[T1/X] </ctx>
  context bound! ~> (_ : _) -> (HOLE => checkSetType(HOLE))    [infer-pi-arg2, result(SetTypedExpr)]
  rule [infer-pi]:
           (bound! => .) ~>
           ((X : t(T1, Set(Alpha))) -> t(T2, Set(Beta))
            => t((X : T1) -> T2, Set(maxInt(Alpha, Beta))))

  context {_ : (HOLE => checkSetType(HOLE))} -> _   [result(SetTypedExpr)]
  rule
       <k> (. => saveCtx(Gamma) ~> bound!) ~> {X : t(T1, Set(_))} -> _ ~>
           (. => loadCtx) ...</k>
       <ctx> Gamma => Gamma[T1/X] </ctx>
  context bound! ~> {_ : _} -> (HOLE => checkSetType(HOLE))    [result(SetTypedExpr)]
  rule
           (bound! => .) ~>
           ({X : t(T1, Set(Alpha))} -> t(T2, Set(Beta))
            => t({X : T1} -> T2, Set(maxInt(Alpha, Beta))))

  context \ (_ : (HOLE => checkSetType(HOLE))) -> _  [result(SetTypedExpr)]
  rule [bind-lambda]:
       <k> (. => saveCtx(Gamma) ~> bound!) ~> \ (X : t(T, Set(_))) -> _ ~>
           (. => loadCtx) ...</k>
       <ctx> Gamma => Gamma[T/X] </ctx>
  context bound! ~> \ (_ : _) -> HOLE
  rule [infer-lambda]:
           (bound! => .) ~>
           (\ (X : t(T, Set(_))) -> t(E, T')
            => t(\ (X : T) -> E, (X : T) -> T'))

  context \ {_ : (HOLE => checkSetType(HOLE))} -> _   [result(SetTypedExpr)]
  rule [bind-lambda]:
       <k> (. => saveCtx(Gamma) ~> bound!) ~> \ {X : t(T, Set(_))} -> _ ~>
           (. => loadCtx) ...</k>
       <ctx> Gamma => Gamma[T/X] </ctx>
  context bound! ~> \ {_ : _} -> HOLE
  rule [infer-lambda]:
           (bound! => . ) ~>
           (\ {X : t(T, Set(_))} -> t(E, T')
            => t(\ {X : T} -> E, {X : T} -> T'))


  context (HOLE::Expr => whnfType(HOLE)) _   [result(WhnfTypedExpr)]




  //context hold(_::Expr (HOLE => whnfType(HOLE)))   [result(WhnfTypedExpr)]
  //context hold(HOLE::Expr)


  syntax Bool ::= condz(Expr)   [function]
  rule condz(t(E, _)) => condz(E)
  //rule condz(Fun("map") _ _ _) => true
  //rule condz(Fun("foldr") _ _ _ _ _ (Var ( "_8853_" ) _:Arg)) => true
  //rule condz(((((Con (
  //     "_,_" ) _) _) Var ( "x" )) ((((Fun 
  //    ( "_,0691_" ) _) _) Var ( "xs" ))))) => true
  //rule condz(Con("_,_") _ _ _) => true //when leftmost(E) ==K Fun("_,0691_")
  //rule condz(Var("_8853_")) => true
  //rule condz(Name("_,0691_")) => true
  //rule condz(Fun("_,0691_")) => true
  //rule condz(Fun("foldl") _ _ _ _ _ _ _) => true


  context W::WhnfTypedExpr HOLE  when condz(W) =/=K true
  context W::WhnfTypedExpr (HOLE => HOLE)  when condz(W) ==K true

  context t(_, (_ : (HOLE => nf(HOLE))) -> _) _   [result(Nf)]
  context t(_, {_ : (HOLE => nf(HOLE))} -> _) _   [result(Nf)]
  context _ t(_, (HOLE => nf(HOLE)))              [result(Nf)]

  /*
  syntax Bool ::= needDot(Variable, Expr)  [function]
  rule needDot(X, T) => X in freeVariables(T)
  */

  // TODO TODO DODODO : Mozem tie <mgu> pomazat a testovt len canUnify(E1, E2)?


  // insert an implicit metavariable in front of an explicit arg when needed
  /*
  rule [insert-implicit1]:
       <k> t(E1, ({X : T1} -> T1')) t(E2, T2) => (E1 #if needDot(X, T1') #then Dot({X}) #else {%meta} #fi) E2 ...</k>
       <ctx>... . => X |-> T1 ...</ctx>  // check whether X not already in keys?
    when isImplicit(T2) =/=K true
  rule [insert-implicit2]:
       <k> t(E1:Expr, _) t(E2, {X : T2} -> T2') => E1 (E2 #if needDot(X, T2') #then Dot({X}) #else {%meta} #fi) ...</k>
       <ctx>... . => X |-> T2 ...</ctx>
    //when isImplicit(E2) =/=K true
  */
  rule [insert-implicit1]:
       <k> t(E1, {_ : _} -> _) t(E2, T2) => (E1 {%meta}) E2 ...</k>
       //<mgu> Theta </mgu>
    when isImplicit(T2) =/=K true
         //isImplicitPi(T1) andBool notBool canUnify(Theta, T1, T2)


  rule [insert-implicit0]:   // hackity hackity? --- just because of constructors (that don't accept parameters as arguments)
                             // this behaviour otherwise does not correspond to Agda
                             // WELL IT DOES CORRESPOND in other cases:
                             // Agda does not accept the parameter arguments for constructors in PATTERNS ONLY
       t(Con(C), {_ : T1} -> _) t({E2}, {T2}) => (Con(C) {%meta}) {E2}
    when notBool canUnify(T1, T2)

  /*
  rule [insert-implicit2]:
       t(E1, (_ : T1) -> _) t(E2, {_ : _} -> _) => E1 (E2 {%meta})
    when isImplicitPi(T1) =/=K true
  */

  rule [insert-implicit2]:
       t(E1:Expr, (_ : T1) -> _) t(E2, T2:ImplicitPi) => E1 (E2 {%meta})
    when notBool canUnify(T1, T2) andBool numPiArgs(T1) <Int numPiArgs(T2)
    //when shouldGetRidOfThatImplicitFunctionSpace(T1, T2)

  /*
  syntax Bool ::= shouldGetRidOfThatImplicitFunctionSpace(Expr, Expr)  [function]
  rule shouldGetRidOfThatImplicitFunctionSpace(T1, T2) => false  when canUnify(T1, T2)
  rule shouldGetRidOfThatImplicitFunctionSpace(T1, {X : T} -> T2) => true   when canUnify(
  */


  /*
  rule [insert-implicit2]:
       <k> t(_, (_ : (T1 => {X : T'} -> T1)) -> _) t(_, {_ : _} -> _) ...</k>
       <meta>... . => T' |-> t(T', T'') ...</meta>
    when isImplicitPi(T1) =/=K true andBool fresh(X:Variable) andBool fresh(T':Expr) andBool fresh(T'':Expr)
  */
  /*
  rule [insert-implicit3]:
       <k> t(E1, (_ : T1) -> _) t(E2, T2) => E1 (\ {X : %meta} -> E2) ...</k>
       <mgu> Theta </mgu>
    when isImplicitPi(T1) andBool notBool canUnify(Theta, T1, T2) andBool fresh(X:Variable)
         /*isMetaVariable(T2) =/=K true*/ /*andBool isImplicitPi(T2) =/=K true*/
  /*
  rule [insert-implicit4]:
       t(E1, (_ : {_ : _} -> _) -> _) t(E2, T2) => T2 == {X : %meta} -> %meta ~> E1 E2
    when isMetaVariable(T2) =/=K true isImplicitPi(T2) =/=K true andBool fresh(X:Variable)
  */



//  rule [infer-app-implicit]:
//       t(E1, T1) t({E2}, {T2}) => T1 == {X : T} -> T' ~> T2 == T ~> unify(t(E1 {E2}, T')) ~> tsubst(X |-> dedot(E2)) ~> unifyConf ~> killMgu
//    when fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr)
//    andBool condz(E1) =/=K true
//       //t(E1, {X : T} -> T') t(E2, {T2}) => T2 == T ~> unify(t(E1 E2, T')) ~> tsubst(X |-> E2) ~> unifyConf ~> killMgu
//  rule [infer-app-implicit]:
//       t(E1, T1) t({E2}, {T2}) => block 98 ~> T1 == {X : T} -> T' ~> T2 == T ~> unify(t(E1 {E2}, T')) ~> tsubst(X |-> dedot(E2)) ~> unifyConf ~> killMgu
//    when fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr)
//    andBool condz(E1) ==K true
//


  rule t(E1, T1) t({E2}, {T2}) => T1 == {X : T} -> T' ~> unify(t(E1, T1) t(E2, T2)) ~> unifyConf ~> killMgu
    when isImplicitPi(T1) =/=K true andBool canUnify(T1, {X : T} -> T') andBool
         fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr)

  rule t(E1, {X : T} -> T') t({E2}, {T2}) => T == T2 ~> unify(t(E1 {E2}, T')) ~> tsubst(X |-> dedot(E2)) ~> unifyConf ~> killMgu
    when canUnify(T, T2)

  rule t(E1, T1) t(E2, T2) => T1 == (X : T) -> T' ~> unify(t(E1, T1) t(E2, T2)) ~> unifyConf ~> killMgu
    when isPi(T1) =/=K true andBool isImplicit(T2) =/=K true andBool canUnify(T1, (X : T) -> T') andBool
         fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr)

  rule t(E1, (X : T) -> T') t(E2, T2) => T == T2 ~> unify(t(E1 E2, T')) ~> tsubst(X |-> dedot(E2)) ~> unifyConf ~> killMgu
     when isImplicit(T2) =/=K true andBool canUnify(T, T2)



//  rule [infer-app-explicit]:
//       t(E1:Expr, T1) t(E2:Expr, T2) => T1 == (X : T) -> T' ~> T2 == T ~> unify(t(E1 E2, T')) ~> tsubst(X |-> dedot(E2)) ~> unifyConf ~> killMgu
//    when //canUnifyApp(T1, T2) andBool
//         isImplicitPi(T1) =/=K true andBool isImplicit(T2) =/=K true andBool
//         fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr)
//         andBool condz(E1) =/=K true
//
//  rule [infer-app-explicit]:
//       t(E1:Expr, T1) t(E2:Expr, T2) => block 99 ~> T1 == (X : T) -> T' ~> T2 == T ~> unify(t(E1 E2, T')) ~> tsubst(X |-> dedot(E2)) ~> unifyConf ~> /*chich ~>*/ killMgu
//    when //canUnifyApp(T1, T2) andBool
//         isImplicitPi(T1) =/=K true andBool isImplicit(T2) =/=K true andBool
//         fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr)
//         andBool condz(E1) ==K true
//


  syntax Expr ::= dedot(Expr)  [function]
  rule dedot(E1 E2) => dedot(E1) dedot(E2)
  rule dedot(DotP(E)) => E
  rule dedot(E) => E   [owise]

  // TODO: reformulate the above condition with canUnify?

  /*
  rule [infer-inaccessible]:
       <k> (. => E == V) ~> t(_, _) t(Dot(E) => E, _) ...</k>
       <dot>... E |-> V ...</dot>
  */

  /*
  rule [infer-app-explicit]:
       t(E1:Expr, T1) t(waa E2:Expr, T2) => chich ~> T1 == (X : T) -> T' ~> T2 == T ~> unify(t(E1 E2, T')) ~> tsubst(X |-> E2) ~> unifyConf ~> killMgu
    when isImplicit(T2) =/=K true andBool fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr)
  */
endmodule
