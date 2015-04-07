require "modules/unification.k"
require "agda-syntax.k"
require "agda-semantics-common.k"
require "agda-semantics-metavariables.k"

module AGDA-SEMANTICS-TYPESYSTEM
  imports UNIFICATION
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-COMMON
  imports AGDA-SEMANTICS-METAVARIABLES

  rule <k> X:Name => te(X, T) ...</k>
       <tenv>... X |-> T ...</tenv>

  rule Set I:Int => te(Set I, Set (I +Int 1))

  // TODO: envStored! pre pi-abstrakciu
  // ... TypedType je zlo, lebo mna az tak nezaujima, ci je to identicke univerzu (co je to,
  // co sa checkuje v isTypedType, ale mna zaujima, ci sa to da *zunifikovat s nejakym univerzom
  context (_ : (HOLE => whnfType(HOLE))) -> _   //[result(TypedType)]
  rule <k> (. => bound!) ~> (X : te(T:Expr, _)) -> _ ~> (. => tenv(Gamma) ~> fenv(Rho)) ...</k>
       <tenv> Gamma => Gamma[T/X] </tenv>
       <fenv> Rho => Rho[^/X] </fenv>
  context bound! ~> (_ : _) -> (HOLE => whnfType(HOLE))        //[result(TypedType)]
  rule <k> bound! ~> (X : te(T1:Expr, Set I1:Int)) -> te(T2:Expr, Set I2:Int)
        => freeVariablesM(T2) <=Set keys(Rho) ~> true?
           ~> te((X : T1) -> T2, Set maxInt(I1, I2)) ...</k>
       <fenv> Rho </fenv>   // vid FIXME v -metavariables.k k freeVariablesM()

  rule <k> (. => envStored!) ~> \ (_ : _) -> _ ~> (. => tenv(Gamma) ~> fenv(Rho)) ...</k>
       <tenv> Gamma </tenv>
       <fenv> Rho </fenv>
  context envStored! ~> \ (_ : (HOLE => whnfType(HOLE))) -> _
  rule <k> (envStored! => bound!) ~> \ (X : te(T:Expr, _)) -> _ ...</k>
       <tenv> Gamma => Gamma[T/X] </tenv>
       <fenv> Rho => Rho[^/X] </fenv>
  context bound! ~> \ (_ : _) -> HOLE
  rule <k> bound! ~> \ (X : te(T:Expr, U:Expr)) -> te(E:Expr, T':Expr)
        => U == Set I ~> solve
           ~> freeVariablesM(E) <=Set keys(Rho) ~> true?
           ~> te(\ (X : T) -> E, (X : T) -> T') ...</k>
       <fenv> Rho </fenv>
    when fresh(I:Int)

  rule <k> te(E1, T1) te(E2, T2) => T1 == (X : T) -> T' ~> T2 == T ~> solveType(te(E1 E2, T')) ~> fenv(Rho) ...</k>
       <fenv> Rho => Rho[E2/X] </fenv>
    when fresh(X:Name) andBool fresh(T:Expr) andBool fresh(T':Expr)

  // TODO: move the unification machinery to a separate file
  // NOTE: not every updateMgu is actually guaranteed to update the mgu;
  // e.g. if T is identical to T', <mgu /> content remains the same.
  syntax KItem ::= Expr "==" Expr
  rule <k> T == T' => . ...</k>
       <mgu> Theta => updateMgu(Theta, T, T') </mgu>

  syntax Bool ::= "noMguError"
  rule <k> noMguError => isMguError(Theta) =/=K true ...</k>
       <mgu> Theta </mgu>

  syntax KItem ::= "solve"
  rule <k> solve => noMguError ~> true? ...</k>
       <tenv> Gamma => applyMgu(Theta, Gamma) </tenv>
       <fenv> Rho => applyMgu(Theta, Rho) </fenv>
       <metavars> Meta => applyMgu(Theta, Meta) </metavars>
       <mgu> Theta => .Mgu </mgu>

  syntax KItem ::= solveType(TypedExpr)
  rule <k> solveType(te(E, T)) => noMguError ~> true? ~> te(E, applyMgu(Theta, T)) ...</k>
       <tenv> Gamma => applyMgu(Theta, Gamma) </tenv>
       <fenv> Rho => applyMgu(Theta, Rho) </fenv>
       <metavars> Meta => applyMgu(Theta, Meta) </metavars>
       <mgu> Theta => .Mgu </mgu>
endmodule
