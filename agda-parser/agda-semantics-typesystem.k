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
       <k> Nc:Name => t(Nc, T) ...</k>
       <sig>... Nc |-> T ...</sig>

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


  // for the binders' semantics
  syntax KItem ::= "bound!"

  // XXX: what about putting all the Pi-related rules into a separate module?
  // ... as suggested in the funkons paper

  context (X : (HOLE => checkSetType(HOLE))) -> _  [infer-pi-arg1, result(SetTypedExpr)]
  rule [bind-pi]:
       <k> (. => saveCtx(Gamma) ~> bound!) ~> (X : t(T1, Set(_))) -> _ ~>
           (. => loadCtx) ...</k>
       <ctx> Gamma => Gamma[T1/X] </ctx>
    when fresh(I1:Int)
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
    when fresh(I1:Int)
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
  context _::WhnfTypedExpr HOLE

  // insert an implicit metavariable in front of an explicit arg when needed
  rule [insert-implicit1]:
       t(E1, ({_ : _} -> _)) t(E2, _) => (E1 {%meta}) E2  when isImplicit(E2) =/=K true
  rule [insert-implicit2]:
       t(E1, _) t(E2, ({_ : _} -> _)) => E1 (E2 {%meta})  when isImplicit(E2) =/=K true

  rule [infer-app-implicit]:
       t(E1, ({X : T} -> T')) t({E2}, {T2}) => T2 == T ~> unify(t(E1 {E2}, T')) ~> tsubst(X |-> E2) ~> unifyConf

  rule [infer-app-explicit]:
       t(E1:Expr, T1) t(E2:Expr, T2) => T1 == (X : T) -> T' ~> T2 == T ~> unify(t(E1 E2, T')) ~> tsubst(X |-> E2) ~> unifyConf
    when isImplicit(T2) =/=K true andBool fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr)
endmodule
