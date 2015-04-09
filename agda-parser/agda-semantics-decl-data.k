require "agda-syntax.k"
require "agda-semantics-common.k"

module AGDA-SEMANTICS-DECL-DATA
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-COMMON

  // TODO: need to check whether params are well-typed and (not necessarily?) whether prependParams(Ps, T) yields a type as well
  context data _ _ : (HOLE => unifyUniverse(HOLE)) where _   [result(SetTypedExpr)]
  rule <k> data N:Name Ps:Telescope : t(T:Expr, Set I) where Cs:TypeSignatures => T constructorOf Set (I -Int 1) ~> true? ~> processCons(applyParams(Ps, N), prependParams(Ps, Cs)) ...</k>
       <sig> Sigma (. => N |-> prependParams(Ps, T)) </sig>
    when notBool (N in keys(Sigma)) andBool /* FIXME? --> */ I >=Int 1

  syntax KItem ::= processCons(Expr, TypeSignatures)
  rule processCons(D:Expr, .TypeSignatures) => . [structural]
  rule processCons(D:Expr, (C:Name : T:Expr) Cs:TypeSignatures) => processCon(D, C, T) ~> processCons(D, Cs)

  syntax KItem ::= processCon(Expr, Name, Expr)  [strict(3(context('unifyUniverse)))]
  rule <k> processCon(D:Expr, C:Name, t(T:Expr, Set _)) => T constructorOf D ~> true? ...</k>
       <sig> Sigma (. => C |-> T) </sig>
    when notBool (C in keys(Sigma))

  syntax Bool ::= Expr "constructorOf" Expr          [strict(all(context('whnf)))]
  rule ((_ : _) -> T => T) constructorOf _
  rule D:Name constructorOf D => true
  rule Set I constructorOf Set I => true
  rule (T:Expr V:Variable => T) constructorOf (D:Expr V => D)
  rule (T:Expr E:Expr => T) constructorOf _:Expr  [owise]

  syntax Expr ::= prependParams(Telescope, Expr) [function]
  rule prependParams(.Telescope, T:Expr) => T
  rule prependParams((X:Variable : Tp:Expr) Ps:Telescope, T:Expr) => (X : Tp) -> prependParams(Ps, T)

  syntax TypeSignatures ::= prependParams(Telescope, TypeSignatures) [function]
  rule prependParams(Ps:Telescope, .TypeSignatures) => .TypeSignatures
  rule prependParams(Ps:Telescope, (C:Name : T:Expr) Cs:TypeSignatures) => (C : prependParams(Ps, T)) prependParams(Ps, Cs)

  syntax Expr ::= applyParams(Telescope, Expr) [function]
  rule applyParams(.Telescope, E:Expr) => E
  rule applyParams(((X:Variable : _:Expr) Ps:Telescope => Ps), (E:Expr => E X))
endmodule
