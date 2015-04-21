require "modules/unification.k"
require "agda-syntax.k"
require "agda-semantics-common.k"
require "agda-semantics-metavariables.k"

module AGDA-SEMANTICS-TYPESYSTEM
  imports UNIFICATION
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-COMMON
  imports AGDA-SEMANTICS-METAVARIABLES

  rule [infer-variable]:
       <k> X:Variable => t(X, T) ...</k>
       <tenv>... X |-> T ...</tenv>

  rule [infer-name]:
       <k> N:Name => t(N, T) ...</k>
       <sig>... N |-> T ...</sig>

  rule [infer-universe]:
       Set(K) => t(Set(K), Set(K +Int 1))

  // implicit args
  context {HOLE}
  rule <k> {t(E, T)} => t({E}, {deval(T)}@Rho) ...</k>
       <fenv> Rho </fenv>

  // for the binders' semantics
  //syntax KItem ::= "envs!"
  syntax KItem ::= "bound!"

  // XXX: what about putting all the Pi-related rules into a separate module?
  // ... as suggested in the funkons paper


  // just duplicted rules for pis with implicit/hidden args
  context /*envs! ~>*/ {_ : (HOLE => checkSetType(HOLE))} -> _   [result(SetTypedExpr)]
  rule
       <k> (. => bound!) ~> {X : t(T1, Set(_))} -> _ ~> //...</k>
           (. => tenv(Gamma) ~> fenv(Rho)) ...</k>
       <tenv> Gamma => Gamma[T1@(Rho[^/X])/X] </tenv>
       <fenv> Rho => Rho[^/X] </fenv>
    when fresh(I1:Int)
  context bound! ~> {_ : _} -> (HOLE => checkSetType(HOLE))    [result(SetTypedExpr)]
  rule
       <k> (bound! => .) ~>
           ({X : t(T1, Set(I1))} -> t(T2, Set(I2))
            => //freeVariablesM(T2) <=Set keys(Rho) ~> pass? ~>    // AT commented just for latex  --- would fail with scope checking anyway, huh?
               t({X : T1} -> T2, Set(maxInt(I1, I2)))) ...</k>
       //<fenv> Rho </fenv>
    //when freeVariablesM(T2) <=Set keys(Rho)





  context /*envs! ~>*/ (_ : (HOLE => checkSetType(HOLE))) -> _   [infer-pi-arg1, result(SetTypedExpr)]
  /*
  rule <k> (. => envs!) ~>
           (_ : _) -> _ ~>
           (. => tenv(Gamma) ~> fenv(Rho)) ...</k>
       <tenv> Gamma </tenv>
       <fenv> Rho </fenv>
  */
  rule [bind-pi]:
       <k> (. => bound!) ~> (X : t(T1, Set(_))) -> _ ~> //...</k>
           (. => tenv(Gamma) ~> fenv(Rho)) ...</k>
       <tenv> Gamma => Gamma[T1@(Rho[^/X])/X] </tenv>
       <fenv> Rho => Rho[^/X] </fenv>
    when fresh(I1:Int)
  context bound! ~> (_ : _) -> (HOLE => checkSetType(HOLE))    [infer-pi-arg2, result(SetTypedExpr)]
  rule [infer-pi]:
       <k> (bound! => .) ~>
           ((X : t(T1, Set(I1))) -> t(T2, Set(I2))
            => //freeVariablesM(T2) <=Set keys(Rho) ~> pass? ~>    // AT commented just for latex  --- would fail with scope checking anyway, huh?
               t((X : T1) -> T2, Set(maxInt(I1, I2)))) ...</k>
       //<fenv> Rho </fenv>
    //when freeVariablesM(T2) <=Set keys(Rho)
    // vid FIXME v -metavariables.k k freeVariablesM()



  context \ {_ : (HOLE => checkSetType(HOLE))} -> _   [result(SetTypedExpr)]
  rule [bind-lambda]:
       <k> (. => bound!) ~> \ {X : t(T, Set(_))} -> _ ~> //...</k>
           (. => tenv(Gamma) ~> fenv(Rho)) ...</k>
       <tenv> Gamma => Gamma[T@(Rho[^/X])/X] </tenv>
       <fenv> Rho => Rho[^/X] </fenv>
  context //[infer-lam-arg2]:
          bound! ~> \ {_ : _} -> HOLE
  rule [infer-lambda]:
       <k> (bound! => .) ~>
           (\ {X : t(T, Set(_))} -> t(E, T')
            => t(\ {X : T} -> E, ((X : T) -> deval(T'))@Rho)) ...</k>
       <fenv> Rho </fenv>      // neviem ci dobre priradujem Rho.  celkovo je lambda problematicka, ofic. by som ju mal len checkovat, nie inferovat.



  context //[infer-lam-arg1]:
          /*envs! ~>*/ \ (_ : (HOLE => checkSetType(HOLE))) -> _   [result(SetTypedExpr)]
  /*
  rule <k> (. => envs!) ~>
           \ (_ : _) -> _ ~>
           (. => tenv(Gamma) ~> fenv(Rho)) ...</k>
       <tenv> Gamma </tenv>
       <fenv> Rho </fenv>
  */
  rule [bind-lambda]:
       <k> (. => bound!) ~> \ (X : t(T, Set(_))) -> _ ~> //...</k>
           (. => tenv(Gamma) ~> fenv(Rho)) ...</k>
       <tenv> Gamma => Gamma[T@(Rho[^/X])/X] </tenv>
       <fenv> Rho => Rho[^/X] </fenv>
  context //[infer-lam-arg2]:
          bound! ~> \ (_ : _) -> HOLE
  rule [infer-lambda]:
       <k> (bound! => .) ~>
           (\ (X : t(T, Set(_))) -> t(E, T')
            => //freeVariablesM(E) <=Set keys(Rho) ~> pass? ~>    // AT latex
               t(\ (X : T) -> E, ((X : T) -> deval(T'))@Rho)) ...</k>
       <fenv> Rho </fenv>      // neviem ci dobre priradujem Rho.  celkovo je lambda problematicka, ofic. by som ju mal len checkovat, nie inferovat.
    //when freeVariablesM(E) <=Set keys(Rho)

  // XXX: tieto contexty prehodit do -syntax.k ako strictness atributy?
  context //[infer-app-arg1]:
          (HOLE::Expr => whnfType(HOLE)) _   [result(WhnfTypedExpr)]
  context //[infer-app-arg2]:
          _::TypedExpr HOLE
  rule [infer-app-implicit]:
       <k> t(E1, ({X : T} -> T')@Rho) t({E2}, {T2}@_) => T2 == deval(T@Rho) ~> unifyType(t(E1 {E2}, T'@(Rho[Rho'[E2/X]]))) ~> fenv(Rho') ...</k>
       <fenv> Rho' => Rho'[E2/X] </fenv>

  // TODO move to a separate file also with the insertion from agda-semantics(-common, or where was it?).k
  // insert an implicit metavariable in front of an explicit arg in application
  // NOTE forgetting the already inferred type... does it matter that much?
  // XXX this should be somehow related to convertibility of types
  rule [insert-implicit1]:
       t(E1, ({_ : _} -> _)@_) t(E2, _) => (E1 {%underscore}) E2  when isImplicit(E2) =/=K true
  rule [insert-implicit2]:
       t(E1, _) t(E2, ({_ : _} -> _)@_) => E1 (E2 {%underscore})  when isImplicit(E2) =/=K true

  rule [infer-app]:
       <k> t(E1:Expr, T1@Rho) t(E2:Expr, T2) => T1 == (X : T) -> T' ~> deval(T2) == deval(T@Rho) ~> unifyType(t(E1 E2, T'@(Rho[Rho'[E2/X]]))) ~> fenv(Rho') ...</k>
       <fenv> Rho' => Rho'[E2/X] </fenv>
    when isImplicit(deval(T2)) =/=K true /*!*/ andBool fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr) andBool cond(E1, E2) =/=K true

  /*
  rule //[infer-app]:    // when the type of the function being applied isn't a closure directly
       <k> t(E1:Expr, T1) t(E2:Expr, T2) => deval(T1) == (X : T) -> T' ~> deval(T2) == T ~> unifyType(t(E1 E2, T'@(Rho'[E2/X]))) ~> fenv(Rho') ...</k>
       <fenv> Rho' => Rho'[E2/X] </fenv>
    when fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr) andBool cond(E1, E2) =/=K true
  */


  syntax Bool ::= cond(Expr, Expr)  [function]
  rule cond(_, Var("f")) => true
  rule //[infer-app]:
       <k> t(E1:Expr, T1@Rho) t(E2:Expr, T2) => T1 == (X : T) -> T' ~> deval(T2) == T ~> unifyType(t(E1 E2, T'@(Rho[Rho'[E2/X]]))) ~> fenv(Rho') ...</k>
       <fenv> Rho' => Rho'[E2/X] </fenv>
    when fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr) andBool cond(E1, E2) ==K true



  // TODO: move the unification machinery to a separate file
  // NOTE: not every updateMgu is actually guaranteed to update the mgu;
  // e.g. if T is identical to T', <mgu /> content remains the same.


  // when a mgu gets on top of <k />, extend the mgu cell with its contents
  // XXX may cause troubles, must test
  /*
  rule Theta':Mgu => extendMguCell(Theta')   [structural]
  syntax KItem ::= extendMguCell(Mgu)
                 | extendMguCell(Map)
  rule extendMguCell(Theta:Mgu => Mgu2Map(Theta))
  rule <k> extendMguCell(K1 |-> K2 Rest:Map => Rest) ...</k>
       <mgu> Theta => updateMgu(Theta, K1, K2) </mgu>
  */


  /*
  syntax KItem ::= "solve"
  rule <k> solve => noMguError ~> pass? ...</k>
       <tenv> Gamma => unify(Theta, Gamma) </tenv>
       <fenv> Rho => unify(Theta, Rho) </fenv>
       <metavars> Meta => unify(Theta, Meta) </metavars>
       <mgu> Theta => .Mgu </mgu>
  */

endmodule
