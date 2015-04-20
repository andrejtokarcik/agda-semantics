require "agda-syntax.k"
require "agda-semantics-common.k"

module AGDA-SEMANTICS-DECL-DATA
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-COMMON

  context data _ _ : (HOLE => checkSetType(HOLE)) where _   [result(SetTypedExpr)]
  rule data N:Name Ps:Telescope : t(T, Set(_)@_) where Cs:TypeSignatures
    => //I >=Int 1 ~> pass? ~>        // << FIXME   (the `-Int 1' guard below is sufficient?)
       addDataSig(N, Pi(Ps, T)) ~>
       addConSigs(applyParams(Ps, N), prependParams(Ps, Cs))      // TODO: replace prependParams with: turn Ps into a hidden-args telescope and use the Pi trick as in addDataSig

  syntax KItem ::= addDataSig(Name, Expr)              [strict(2(context('checkSetType)))]
  rule <k> addDataSig(N, t(T, Set(I)@_)) => T constructorOf Set(I -Int 1) ~> pass? ...</k>   // << FIXME not sure if the condition is correct: what universe must the datatype fit in?
       <sig> Sigma (. => N |-> T@Rho) </sig>
       <fenv> Rho </fenv>
    when notBool (N in keys(Sigma))

  syntax KItem ::= addConSigs(Expr, TypeSignatures)
  rule addConSigs(D:Expr, .TypeSignatures) => . [structural]
  rule addConSigs(D:Expr, (C:Name : T:Expr) Cs:TypeSignatures) => addConSig(D, C, T) ~> addConSigs(D, Cs)  [structural]

  // TODO: check the constructor's universe whether it fits into the datatype
  syntax KItem ::= addConSig(Expr, Name, Expr)  [strict(3(context('checkSetType)))]
  rule <k> addConSig(D:Expr, C:Name, t(T:Expr, Set(_)@_)) => T constructorOf D ~> pass? ...</k>
       <sig> Sigma (. => C |-> T@Rho) </sig>
       <fenv> Rho </fenv>
    when notBool (C in keys(Sigma))

  syntax KItem ::= Expr "constructorOf" Expr          [strict(all(context('whnf)))]
  rule ((_ : _) -> T => T) constructorOf _
  rule ({_ : _} -> T => T) constructorOf _
  rule D:Name constructorOf D => true
  rule Set(I) constructorOf Set(I) => true
  rule (T:Expr V:Variable => T) constructorOf (D:Expr V => D)
  rule (T:Expr E:Expr => T) constructorOf _:Expr  [owise]

  syntax Expr ::= prependParams(Telescope, Expr) [function]
  rule prependParams(.Telescope, T:Expr) => T
  rule prependParams((X:Variable : Tp:Expr) Ps:Telescope, T:Expr) => {X : Tp} -> prependParams(Ps, T)

  syntax TypeSignatures ::= prependParams(Telescope, TypeSignatures) [function]
  rule prependParams(Ps:Telescope, .TypeSignatures) => .TypeSignatures
  rule prependParams(Ps:Telescope, (C:Name : T:Expr) Cs:TypeSignatures) => (C : prependParams(Ps, T)) prependParams(Ps, Cs)

  syntax Expr ::= applyParams(Telescope, Expr) [function]
  rule applyParams(.Telescope, E:Expr) => E
  rule applyParams(((X:Variable : _:Expr) Ps:Telescope => Ps), (E:Expr => E X))
endmodule
