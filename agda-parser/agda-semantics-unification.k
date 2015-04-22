require "modules/unification.k"
require "agda-semantics-common.k"

module AGDA-SEMANTICS-UNIFICATION
  imports UNIFICATION
  imports AGDA-SEMANTICS-COMMON

 // NOTE: not every updateMgu is actually guaranteed to update the mgu;
  // e.g. if T is identical to T', <mgu /> content remains the same.
  syntax KItem ::= Expr "==" Expr
  rule <k> E == E' => . ...</k>
       <mgu> Theta => updateMgu(Theta, E, E') </mgu>

  syntax KItem ::= "unify"
  rule <k> unify => . ...</k>
       <sig> Sigma => applyMgu(Theta, Sigma) </sig>
       <tenv> Gamma => applyMgu(Theta, Gamma) </tenv>
       <fenv> Rho => applyMgu(Theta, Rho) </fenv>
       <metavars> Meta => applyMgu(Theta, Meta) </metavars>
       <mgu> Theta => .Mgu </mgu>
    when isMguError(Theta) =/=K true

  syntax KItem ::= unify(Expr)
  rule <k> unify(E:Expr) => unify ~> applyMgu(Theta, E) ...</k>
       <mgu> Theta </mgu>
  rule <k> t(E, unify(T:Expr)) => unify ~> t(E, applyMgu(Theta, T)) ...</k>
       <mgu> Theta </mgu>
endmodule
