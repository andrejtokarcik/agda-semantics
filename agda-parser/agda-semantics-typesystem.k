require "agda-syntax.k"
require "agda-semantics-common.k"
require "agda-semantics-unification.k"
require "agda-semantics-metavariables.k"

module AGDA-SEMANTICS-TYPESYSTEM
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-COMMON
  imports AGDA-SEMANTICS-UNIFICATION
  imports AGDA-SEMANTICS-METAVARIABLES

  // TODO pomaz <k>...</k> tam kde nie je treba

  rule [infer-variable]:
       <k> X:Variable => t(X, T) ...</k>
       <tenv>... X |-> T ...</tenv>

  rule <k> N:Name => Nc ...</k>  <ncat>... N |-> Nc ...</ncat>
  rule [infer-name]:
       <k> Nc:Name => t(Nc, T) ...</k>
       <sig>... Nc |-> T ...</sig>

  rule [infer-universe]:
       Set(I) => t(Set(I), Set(I +Int 1))

  // implicit args
  context {HOLE}
  rule {t(E, T)} => t({E}, {T})


  // for the binders' semantics
  syntax KItem ::= "bound!"

  // XXX: what about putting all the Pi-related rules into a separate module?
  // ... as suggested in the funkons paper

  context (_ : (HOLE => checkSetType(HOLE))) -> _   [infer-pi-arg1, result(SetTypedExpr)]
  rule [bind-pi]:
       <k> (. => bound!) ~> (X : t(T1, Set(_))) -> _ ~>
           (. => tenv(Gamma)) ...</k>
       <tenv> Gamma => Gamma[T1/X] </tenv>
    when fresh(I1:Int)
  context bound! ~> (_ : _) -> (HOLE => checkSetType(HOLE))    [infer-pi-arg2, result(SetTypedExpr)]
  rule [infer-pi]:
       <k> (bound! => .) ~>
           ((X : t(T1, Set(I1))) -> t(T2, Set(I2))
            => t((X : T1) -> T2, Set(maxInt(I1, I2)))) ...</k>

  context {_ : (HOLE => checkSetType(HOLE))} -> _   [result(SetTypedExpr)]
  rule
       <k> (. => bound!) ~> {X : t(T1, Set(_))} -> _ ~>
           (. => tenv(Gamma)) ...</k>
       <tenv> Gamma => Gamma[T1/X] </tenv>
    when fresh(I1:Int)
  context bound! ~> {_ : _} -> (HOLE => checkSetType(HOLE))    [result(SetTypedExpr)]
  rule
       <k> (bound! => .) ~>
           ({X : t(T1, Set(I1))} -> t(T2, Set(I2))
            => t({X : T1} -> T2, Set(maxInt(I1, I2)))) ...</k>


  context \ (_ : (HOLE => checkSetType(HOLE))) -> _   [result(SetTypedExpr)]
  rule [bind-lambda]:
       <k> (. => bound!) ~> \ (X : t(T, Set(_))) -> _ ~>
           (. => tenv(Gamma)) ...</k>
       <tenv> Gamma => Gamma[T/X] </tenv>
  context bound! ~> \ (_ : _) -> HOLE
  rule [infer-lambda]:
       <k> (bound! => .) ~>
           (\ (X : t(T, Set(_))) -> t(E, T')
            => t(\ (X : T) -> E, ((X : T) -> T'))) ...</k>

  context \ {_ : (HOLE => checkSetType(HOLE))} -> _   [result(SetTypedExpr)]
  rule [bind-lambda]:
       <k> (. => bound!) ~> \ {X : t(T, Set(_))} -> _ ~>
           (. => tenv(Gamma)) ...</k>
       <tenv> Gamma => Gamma[T/X] </tenv>
  context bound! ~> \ {_ : _} -> HOLE
  rule [infer-lambda]:
       <k> (bound! => .) ~>
           (\ {X : t(T, Set(_))} -> t(E, T')
            => t(\ {X : T} -> E, ({X : T} -> T'))) ...</k>


  context (HOLE::Expr => whnfType(HOLE)) _   [result(WhnfTypedExpr)]
  context _::WhnfTypedExpr HOLE

  // insert an implicit metavariable in front of an explicit arg in application
  // NOTE forgetting the already inferred type... does it matter that much?
  // XXX this should be somehow related to convertibility of types
  rule [insert-implicit1]:
       t(E1, ({_ : _} -> _)) t(E2, _) => (E1 {%underscore}) E2  when isImplicit(E2) =/=K true
  rule [insert-implicit2]:
       t(E1, _) t(E2, ({_ : _} -> _)) => E1 (E2 {%underscore})  when isImplicit(E2) =/=K true

  rule [infer-app-implicit]:
       <k> t(E1, ({X : T} -> T')) t({E2}, {T2}) => T2 == T ~> t(E1 {E2}, unify(T')) ~> tsubst(X |-> E2) ...</k>

  rule [infer-app-explicit]:
       <k> t(E1:Expr, T1) t(E2:Expr, T2) => T1 == (X : T) -> T' ~> T2 == T ~> t(E1 E2, unify(T')) ~> tsubst(X |-> E2) ...</k>
    when isImplicit(T2) =/=K true andBool fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr) andBool cond(E1, E2) =/=K true

  syntax Bool ::= cond(Expr, Expr)  [function]
  rule cond(_, Name("zero")) => true
  rule <k> t(E1:Expr, T1) t(E2:Expr, T2) => chich ~> T1 == (X : T) -> T' ~> T2 == T ~> t(E1 E2, unify(T')) ~> tsubst(X |-> E2) ~> chich ...</k>
    when fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr) andBool cond(E1, E2) ==K true
endmodule
