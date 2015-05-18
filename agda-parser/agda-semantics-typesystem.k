require "agda-semantics-common.k"
require "agda-semantics-unification.k"

module AGDA-SEMANTICS-TYPESYSTEM
  imports AGDA-SEMANTICS-COMMON
  imports AGDA-SEMANTICS-UNIFICATION

  rule [infer-variable]:
       <k> X:Variable => t(X, T) ...</k>
       <ctx>... X |-> T ...</ctx>

  rule <k> N:Name => Nc ...</k>  <ncat>... N |-> Nc ...</ncat>
  rule [infer-name]:
       <k> N:Name => t(N, T) ...</k>
       <sig>... N |-> T ...</sig>

  rule <k> FunClauses(F, _) => t(F, T) ...</k>
       <sig>... F |-> T ...</sig>

  rule [infer-universe]:
       Set(Alpha) => t(Set(Alpha), Set(Alpha +Int 1))

  rule [infer-meta]:
       <k> %meta => E ...</k>
       <meta>... . => E |-> t(E, T) ...</meta>
    when fresh(E:Expr) andBool fresh(T:Expr)
    //ensures isMetaVariable(E)
  rule [infer-meta]:
       <k> X:MetaVariable => t(E, T) ...</k>
       <meta>... X |-> t(E, T) ...</meta>


  // implicit args
  context {HOLE}
  rule {t(E, T)} => t({E}, {T})

  // inaccessible patterns
  syntax Expr ::= DotP(Pattern)
  //rule DotP(E) => Dot(E)
  context DotP(HOLE)
  rule DotP(t(E, T)) => t(DotP(E), T)


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
  context chich ~> (HOLE::Expr => whnfType(HOLE)) _   [result(WhnfTypedExpr)]


  syntax Bool ::= condz(Expr)   [function]
  rule condz(t(E, _)) => condz(E)
  rule condz(Fun("map") _ _ _) => true

  context W::WhnfTypedExpr HOLE  when condz(W) =/=K true
  context W::WhnfTypedExpr (HOLE => HOLE)  when condz(W) ==K true


  /*
  syntax Bool ::= needDot(Variable, Expr)  [function]
  rule needDot(X, T) => X in freeVariables(T)
  */

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
       t(E1, ({X : T1} -> T1')) t(E2, T2) => (E1 {%meta}) E2
    when isImplicit(T2) =/=K true
  rule [insert-implicit2]:
       t(E1:Expr, _) t(E2, {X : T2} -> T2') => E1 (E2 {%meta})
    //when isImplicit(E2) =/=K true

  rule [infer-app-implicit]:
       t(E1, T1) t({E2}, {T2}) => T1 == {X : T} -> T' ~> T2 == T ~> unify(t(E1 {E2}, T')) ~> tsubst(X |-> dedot(E2)) ~> unifyConf ~> killMgu
    when fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr)
    andBool condz(E1) =/=K true
       //t(E1, {X : T} -> T') t(E2, {T2}) => T2 == T ~> unify(t(E1 E2, T')) ~> tsubst(X |-> E2) ~> unifyConf ~> killMgu
  rule [infer-app-implicit]:
       t(E1, T1) t({E2}, {T2}) => chich ~> T1 == {X : T} -> T' ~> T2 == T ~> unify(t(E1 {E2}, T')) ~> tsubst(X |-> dedot(E2)) ~> unifyConf ~> killMgu
    when fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr)
    andBool condz(E1) ==K true

  rule [infer-app-explicit]:
       t(E1:Expr, T1) t(E2:Expr, T2) => T1 == (X : T) -> T' ~> T2 == T ~> unify(t(E1 E2, T')) ~> tsubst(X |-> dedot(E2)) ~> unifyConf ~> killMgu
    when isImplicitPi(T1) =/=K true andBool isImplicit(T2) =/=K true andBool
         fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr)
         andBool condz(E1) =/=K true

  rule [infer-app-explicit]:
       t(E1:Expr, T1) t(E2:Expr, T2) => T1 == (X : T) -> T' ~> T2 == T ~> unify(t(E1 E2, T')) ~> tsubst(X |-> dedot(E2)) ~> unifyConf ~> killMgu //~> chich
    when isImplicitPi(T1) =/=K true andBool isImplicit(T2) =/=K true andBool
         fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr)
         andBool condz(E1) ==K true

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
