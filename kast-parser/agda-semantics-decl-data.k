require "agda-syntax.k"
require "agda-semantics-normal.k"

module AGDA-SEMANTICS-DECL-DATA
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-NORMAL

  syntax Expr ::= piTarget(Expr) [function]
  rule piTarget((Pi _ _ E:Expr) => E)
  rule piTarget(E:Expr) => E [owise]

  syntax Expr ::= prependParams(Params, Expr) [function]
  rule prependParams(.Params, T:Expr) => T
  rule prependParams(((X:Variable : Tp:Expr), Ps:Params), T:Expr) => Pi X Tp prependParams(Ps, T)

  syntax Constrs ::= prependParams(Params, Constrs) [function]
  rule prependParams(Ps:Params, .Constrs) => .Constrs
  rule prependParams(Ps:Params, ((C:Name : T:Expr), Cs:Constrs)) => (C : prependParams(Ps, T)), prependParams(Ps, Cs)

  syntax Expr ::= applyParams(Params, Expr) [function]
  rule applyParams(.Params, E:Expr) => E
  rule applyParams((((X:Variable : _:Expr), Ps:Params) => Ps), (E:Expr => E X))

  syntax KItem ::= processConstrs(Expr, Constrs)
  rule processConstrs(D:Expr, .Constrs) => . [structural]
  rule processConstrs(D:Expr, ((C:Name : T:Expr), Cs:Constrs)) => processConstr(D, C, T) ~> processConstrs(D, Cs)

  syntax Bool ::= constructsType(Expr, Expr) [function]
  rule constructsType(D:Name, D) => true
  rule constructsType((D1:Expr D2:Variable) => D1, (T:Expr D2) => T)
  rule constructsType(_:Expr, (T:Expr _:Expr) => T)  [owise]

  syntax KItem ::= processConstr(Expr, Name, Expr)  [strict(3(context('whnf21),result(TypeT)))]
  // Constr's target may also be a function that computes the data type
  // --- already being handled since T is in whnf?
  rule <k> processConstr(D:Expr, C:Name, (T:Expr, _:Universe)) => constructsType(D, piTarget(T)) ~> true? ...</k>
       <data> Data (. => C |-> T) </data>
         when notBool (C in keys(Data))

  rule <k> data N:Name Ps:Params : (T:Expr, Set I:Int) where Cs:Constrs => isUniverse(piTarget(T)) ~> true? ~> processConstrs(applyParams(Ps, N), prependParams(Ps, Cs)) ...</k>
       <data> Data (. => N |-> prependParams(Ps, T)) </data>
         when notBool (N in keys(Data)) andBool /* FIXME? --> */ I >=Int 1

  syntax KItem ::= "true?"
  rule true ~> true? => .

  // TODO: error handling/reporting as in:
  //  rule E ~> true? => error(_) when E =/=K true
endmodule
