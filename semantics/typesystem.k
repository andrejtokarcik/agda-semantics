module AGDA-SEMANTICS-TYPESYSTEM
  imports AGDA-SEMANTICS-COMMON
  imports AGDA-SEMANTICS-UNIFICATION

  // TODO move to -common or elsewhere?
  // The offic typechecker reports a variable identifier
  // with underscores as a [function] name in some cases,
  // e.g., in LibVec.agda, foldr's _⊕_.
  rule <k> Name(S) => Var(S) ...</k>  <ctx> Gamma </ctx>  <ncat> NCat </ncat>
    when notBool (Name(S) in keys(NCat)) andBool Var(S) in keys(Gamma)

  // A dual problem occurs with let-bindings...
  rule <k> Var(S) => Name(S) ...</k>  <ctx> Gamma </ctx>  <ncat> NCat </ncat>
    when Name(S) in keys(NCat) andBool notBool (Var(S) in keys(Gamma))

  rule <k> N:Name => Nc ...</k>  <ncat>... N |-> Nc ...</ncat>

  rule <k> %meta => E ...</k>
       <meta>... . => E |-> t(E, T) ...</meta>
    when fresh(E:Expr) andBool fresh(T:Expr)

  rule <k> let Ds in E => Ds ~> E ~> globalNames(keys(Sigma)) ...</k>
       <sig> Sigma </sig>
  rule <k> t(E, T) ~> globalNames(GlobalKeys) => localNames(keys(Sigma) -Set GlobalKeys) ~> <t(E, T), Sigma(keys(Sigma) -Set GlobalKeys), Rho(keys(Rho) -Set GlobalKeys)>...</k>
       <sig> Sigma </sig>
       <fun> Rho </fun>

  rule <k> (<E, LocalSigs, LocalFuns> => E) ~> (. => localData(LocalSigs, LocalFuns)) ...</k>
       <sig> Sigma => Sigma[LocalSigs] </sig>
  rule (. => localNames(keys(LocalSigs))) ~> (t(E, T) => <t(E, T), LocalSigs, LocalFuns>) ~> (localData(LocalSigs, LocalFuns) => .)  [structural]

  /////////

  rule [infer-universe]:
       Set(Alpha) => t(Set(Alpha), Set(Alpha +Int 1))

  rule [infer-variable]:
       <k> X:Variable => t(X, renameBoundVariables(T)) ...</k>
       <ctx>... X |-> T ...</ctx>

  rule [infer-name]:
       <k> N:Name => t(N, renameBoundVariables(T)) ...</k>
       <sig>... N |-> T ...</sig>
  rule <k> FunClauses(F, _) => t(F, renameBoundVariables(T)) ...</k>
       <sig>... F |-> T ...</sig>

  rule [infer-meta]:
       <k> X:MetaVariable => t(E, renameBoundVariables(T)) ...</k>
       <meta>... X |-> t(E, T) ...</meta>

  // Implicit arguments.
  context {HOLE}
  rule {t(E, T)} => t({E}, {T})

  // Inaccessible patterns.
  syntax InaccessiblePattern ::= DotP(Expr)    [klabel('DotP)]
  syntax Expr ::= InaccessiblePattern
  context DotP(HOLE)::Expr
  rule DotP(t(E, T))::Expr => t(DotP(E), T)


  syntax KItem ::= "bound!"

  context (_ : (HOLE => checkSetType(HOLE))) -> _              [infer-pi-arg1, result(SetTypedExpr)]
  rule [bind-pi]:
       <k> (. => saveCtx(Gamma) ~> bound!) ~> (X : t(T1, Set(_))) -> _ ~>
           (. => loadCtx) ...</k>
       <ctx> Gamma => Gamma[T1/X] </ctx>
  context bound! ~> (_ : _) -> (HOLE => checkSetType(HOLE))    [infer-pi-arg2, result(SetTypedExpr)]
  rule [infer-pi]:
           (bound! => .) ~>
           ((X : t(T1, Set(Alpha))) -> t(T2, Set(Beta))
            => t((X : T1) -> T2, Set(maxInt(Alpha, Beta))))

  context {_ : (HOLE => checkSetType(HOLE))} -> _              [result(SetTypedExpr)]
  rule
       <k> (. => saveCtx(Gamma) ~> bound!) ~> {X : t(T1, Set(_))} -> _ ~>
           (. => loadCtx) ...</k>
       <ctx> Gamma => Gamma[T1/X] </ctx>
  context bound! ~> {_ : _} -> (HOLE => checkSetType(HOLE))    [result(SetTypedExpr)]
  rule
           (bound! => .) ~>
           ({X : t(T1, Set(Alpha))} -> t(T2, Set(Beta))
            => t({X : T1} -> T2, Set(maxInt(Alpha, Beta))))

  context \ (_ : (HOLE => checkSetType(HOLE))) -> _            [result(SetTypedExpr)]
  rule [bind-lambda]:
       <k> (. => saveCtx(Gamma) ~> bound!) ~> \ (X : t(T, Set(_))) -> _ ~>
           (. => loadCtx) ...</k>
       <ctx> Gamma => Gamma[T/X] </ctx>
  context bound! ~> \ (_ : _) -> HOLE
  rule [infer-lambda]:
           (bound! => .) ~>
           (\ (X : t(T, Set(_))) -> t(E, T')
            => t(\ (X : T) -> E, (X : T) -> T'))

  context \ {_ : (HOLE => checkSetType(HOLE))} -> _            [result(SetTypedExpr)]
  rule [bind-lambda]:
       <k> (. => saveCtx(Gamma) ~> bound!) ~> \ {X : t(T, Set(_))} -> _ ~>
           (. => loadCtx) ...</k>
       <ctx> Gamma => Gamma[T/X] </ctx>
  context bound! ~> \ {_ : _} -> HOLE
  rule [infer-lambda]:
           (bound! => . ) ~>
           (\ {X : t(T, Set(_))} -> t(E, T')
            => t(\ {X : T} -> E, {X : T} -> T'))


  // Applications.
  context (HOLE::Expr => whnfType(HOLE)) _                     [result(WhnfTypedExpr)]
  context _::WhnfTypedExpr HOLE
  context t(_, (_ : (HOLE => nf(HOLE))) -> _) _                [result(Nf)]
  context t(_, {_ : (HOLE => nf(HOLE))} -> _) _                [result(Nf)]
  context _ t(_, (HOLE => nf(HOLE)))                           [result(Nf)]

  // Agda does not accept the parameter arguments for constructors in patterns. Hack.
  rule [insert-implicit0]:
       t(Con(C), {_ : T1} -> _) t({E2}, {T2}) => (Con(C) {%meta}) {E2}
    when notBool canUnify(T1, T2)

  rule [insert-implicit1]:
       <k> t(E1, {_ : _} -> _) t(E2, T2) => (E1 {%meta}) E2 ...</k>
    when isImplicit(T2) =/=K true

  rule [insert-implicit2]:
       t(E1:Expr, (_ : T1) -> _) t(E2, T2:ImplicitPi) => E1 (E2 {%meta})
    when notBool canUnify(T1, T2) andBool numPiArgs(T1) <Int numPiArgs(T2)

  rule [unify-function-implicit]:
       t(E1, T1) t({E2}, {T2}) => T1 == {X : T} -> T' ~> unify(t(E1, T1) t(E2, T2)) ~> unifyConf ~> killMgu
    when isImplicitPi(T1) =/=K true andBool canUnify(T1, {X : T} -> T') andBool
         fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr)

  rule [infer-app-implicit]:
       t(E1, {X : T} -> T') t({E2}, {T2}) => T == T2 ~> unify(t(E1 {E2}, T')) ~> tsubst(X |-> dedot(E2)) ~> unifyConf ~> killMgu
    when canUnify(T, T2)

  rule [unify-function-explicit]:
       t(E1, T1) t(E2, T2) => T1 == (X : T) -> T' ~> unify(t(E1, T1) t(E2, T2)) ~> unifyConf ~> killMgu
    when isPi(T1) =/=K true andBool isImplicit(T2) =/=K true andBool canUnify(T1, (X : T) -> T') andBool
         fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr)

  rule [infer-app-explicit]:
       t(E1, (X : T) -> T') t(E2, T2) => T == T2 ~> unify(t(E1 E2, T')) ~> tsubst(X |-> dedot(E2)) ~> unifyConf ~> killMgu
     when isImplicit(T2) =/=K true andBool canUnify(T, T2)


  syntax KItem ::= tsubst(Map)
  rule <k> t(E, T) ~> tsubst(M) => t(E, T[applyMguKeys(Theta, M)]) ...</k>
       <mgu> Theta </mgu> [structural]

  syntax Expr ::= dedot(Expr)  [function]
  rule dedot(E1 E2) => dedot(E1) dedot(E2)
  rule dedot(DotP(E)) => E
  rule dedot(E) => E   [owise]
endmodule
