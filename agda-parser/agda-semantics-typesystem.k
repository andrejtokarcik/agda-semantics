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

  rule Set I:Int => t(Set I, Set (I +Int 1))

  // ... TypedType je zlo, lebo mna az tak nezaujima, ci je to identicke univerzu (co je to,
  // co sa checkuje v isTypedType, ale mna zaujima, ci sa to da *zunifikovat s nejakym univerzom
  //  ---- FIXED

  rule <k> (. => envs!) ~>
           (_ : _) -> _ ~>
           (. => tenv(Gamma) ~> fenv(Rho)) ...</k>
       <tenv> Gamma </tenv>
       <fenv> Rho </fenv>
  context envs! ~> (_ : (HOLE => unifyUniverse(HOLE))) -> _   [result(TypedType)]
  rule <k> (envs! => bound!) ~> (X : t(T1, Set _)) -> _ ...</k>
       <tenv> Gamma => Gamma[T1/X] </tenv>
       <fenv> Rho => Rho[^/X] </fenv>
    when fresh(I1:Int)
  context bound! ~> (_ : _) -> (HOLE => unifyUniverse(HOLE))    [result(TypedType)]
  rule <k> (bound! => .) ~>
           ((X : t(T1, Set I1)) -> t(T2, Set I2)
            => freeVariablesM(T2) <=Set keys(Rho) ~> true? ~>
               t((X : T1) -> T2, Set maxInt(I1, I2))) ...</k>
       <fenv> Rho </fenv>
    // vid FIXME v -metavariables.k k freeVariablesM()

  rule <k> (. => envs!) ~>
           \ (_ : _) -> _ ~>
           (. => tenv(Gamma) ~> fenv(Rho)) ...</k>
       <tenv> Gamma </tenv>
       <fenv> Rho </fenv>
  context envs! ~> \ (_ : (HOLE => unifyUniverse(HOLE))) -> _   [result(TypedType)]
  rule <k> (envs! => bound!) ~> \ (X : t(T, Set _)) -> _ ...</k>
       <tenv> Gamma => Gamma[T/X] </tenv>
       <fenv> Rho => Rho[^/X] </fenv>
  context bound! ~> \ (_ : _) -> HOLE
  rule <k> (bound! => .) ~>
           (\ (X : t(T, Set _)) -> t(E, T')
           => freeVariablesM(E) <=Set keys(Rho) ~> true? ~>
              t(\ (X : T) -> E, (X : T) -> T')) ...</k>
       <fenv> Rho </fenv>

  rule <k> t(E1, T1) t(E2, T2) => T1 == (X : T) -> T' ~> T2 == T ~> unifyType(t(E1 E2, T')) ~> fenv(Rho) ...</k>
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
  syntax Bool ::= "noMguError"
  rule <k> noMguError => isMguError(Theta) =/=K true ...</k>
       <mgu> Theta </mgu>
  */

  /*
  syntax KItem ::= "solve"
  rule <k> solve => noMguError ~> true? ...</k>
       <tenv> Gamma => applyMgu(Theta, Gamma) </tenv>
       <fenv> Rho => applyMgu(Theta, Rho) </fenv>
       <metavars> Meta => applyMgu(Theta, Meta) </metavars>
       <mgu> Theta => .Mgu </mgu>
  */

endmodule
