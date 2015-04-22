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
       <tenv> Gamma => updateClosures(applyMgu(Theta, Rho), applyMgu(Theta, Gamma)) </tenv>
       <fenv> Rho => updateClosures(applyMgu(Theta, Rho), applyMgu(Theta, Rho)) </fenv>
       <metavars> Meta => updateClosures(applyMgu(Theta, Rho), applyMgu(Theta, Meta)) </metavars>
       <mgu> Theta => .Mgu </mgu>
    when isMguError(Theta) =/=K true

  syntax KItem ::= unify(Expr)
  rule <k> unify(E:Expr) => unify ~> applyMgu(Theta, E) ...</k>
       <mgu> Theta </mgu>

  syntax KItem ::= unifyType(Expr, Expr, Map)
  rule <k> unifyType(E, T, Rho) => unify ~> t(E, applyMgu(Theta, T)@Rho) ...</k>
       <mgu> Theta </mgu>



  // these functions exist only because unnecessary keys get removed in -common
  syntax Val ::= updateClosure(Val, Map)  [function]
  rule updateClosure(V1 V2, Rho) => updateClosure(V1, Rho) updateClosure(V2, Rho)
  rule updateClosure(E@Rho', Rho) => E@(Rho'[Rho])
  rule updateClosure(E, Rho) => E@Rho  [owise]

  syntax Map ::= updateClosures(Map, Map)  [function]
  rule updateClosures(_, .Map) => .Map
  rule updateClosures(Rho, (K |-> V => .) _) (.Map => K |-> updateClosure(V, Rho))
  rule updateClosures(Rho, (K |-> t(E, T) => .) _) (.Map => K |-> t(E, updateClosure(T, Rho)))
  rule updateClosures(_, (K |-> V => .) _) (.Map => K |-> V)  [owise]
endmodule
