require "modules/unification.k"
require "agda-syntax.k"
require "agda-semantics-common.k"
require "agda-semantics-metavariables.k"

module AGDA-SEMANTICS-TYPESYSTEM
  imports UNIFICATION
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-COMMON
  imports AGDA-SEMANTICS-METAVARIABLES

  rule <k> X:Variable => t(X, T) ...</k>
       <tenv>... X |-> T ...</tenv>

  rule <k> X:Name => t(X, T) ...</k>
       <sig>... X |-> T ...</sig>

  rule Set(I) => t(Set(I), Set(I +Int 1))

  // for the binders' semantics
  //syntax KItem ::= "envs!"
  syntax KItem ::= "bound!"

  context /*envs! ~>*/ (_ : (HOLE => coerceSetType(HOLE))) -> _   [result(SetTypedExpr)]
  /*
  rule <k> (. => envs!) ~>
           (_ : _) -> _ ~>
           (. => tenv(Gamma) ~> fenv(Rho)) ...</k>
       <tenv> Gamma </tenv>
       <fenv> Rho </fenv>
  */
  rule <k> (. => bound!) ~> (X : t(T1, Set(_))) -> _ ~> //...</k>
           (. => tenv(Gamma) ~> fenv(Rho)) ...</k>
       <tenv> Gamma => Gamma[T1/X] </tenv>
       <fenv> Rho => Rho[^/X] </fenv>
    when fresh(I1:Int)
  context bound! ~> (_ : _) -> (HOLE => coerceSetType(HOLE))    [result(SetTypedExpr)]
  rule <k> (bound! => .) ~>
           ((X : t(T1, Set(I1))) -> t(T2, Set(I2))
            => freeVariablesM(T2) <=Set keys(Rho) ~> pass? ~>
               t((X : T1) -> T2, Set(maxInt(I1, I2)))) ...</k>
       <fenv> Rho </fenv>
    // vid FIXME v -metavariables.k k freeVariablesM()

  context /*envs! ~>*/ \ (_ : (HOLE => coerceSetType(HOLE))) -> _   [result(SetTypedExpr)]
  /*
  rule <k> (. => envs!) ~>
           \ (_ : _) -> _ ~>
           (. => tenv(Gamma) ~> fenv(Rho)) ...</k>
       <tenv> Gamma </tenv>
       <fenv> Rho </fenv>
  */
  rule <k> (. => bound!) ~> \ (X : t(T, Set(_))) -> _ ~> //...</k>
           (. => tenv(Gamma) ~> fenv(Rho)) ...</k>
       <tenv> Gamma => Gamma[T/X] </tenv>
       <fenv> Rho => Rho[^/X] </fenv>
  context bound! ~> \ (_ : _) -> HOLE
  rule <k> (bound! => .) ~>
           (\ (X : t(T, Set(_))) -> t(E, T')
           => freeVariablesM(E) <=Set keys(Rho) ~> pass? ~>
              t(\ (X : T) -> E, (X : T) -> T')) ...</k>
       <fenv> Rho </fenv>

  // XXX: tieto contexty prehodit do -syntax.k ako strictness atributy?
  context (HOLE::Expr => whnfType(HOLE)) _   [result(WhnfTypedExpr)]
  context _::Expr HOLE
  rule <k> t(E1:Expr, T1) t(E2:Expr, T2) => T1 == (X : T) -> T' ~> T2 == T ~> unifyType(t(E1 E2, T')) ~> fenv(Rho) ...</k>
       <fenv> Rho => Rho[E2/X] </fenv>
    when fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr)

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
