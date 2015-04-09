require "agda-syntax.k"
require "agda-semantics-normal.k"

module AGDA-SEMANTICS-DECL-DATA
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-NORMAL

  // TODO: need to check whether params are well-typed and (not necessarily?) whether prependParams(Ps, T) yields a type as well
  rule <k> data N:Name Ps:Params : (T:Expr, Set I:Int) where Cs:Constrs => T constructorOf Set (I -Int 1) ~> true? ~> processConstrs(applyParams(Ps, N), prependParams(Ps, Cs)) ...</k>
       <data> Data (. => N |-> prependParams(Ps, T)) </data>
         when notBool (N in keys(Data)) andBool /* FIXME? --> */ I >=Int 1

  syntax KItem ::= processConstrs(Expr, Constrs)
  rule processConstrs(D:Expr, .Constrs) => . [structural]
  rule processConstrs(D:Expr, ((C:Name : T:Expr), Cs:Constrs)) => processConstr(D, C, T) ~> processConstrs(D, Cs)

  syntax KItem ::= processConstr(Expr, Name, Expr)  [strict(3(context('evalWhnf2),result(TypeT)))]   // << bolo whnf21
  rule <k> processConstr(D:Expr, C:Name, (T:Expr, _:Universe)) => T constructorOf D ~> true? ...</k>
       <data> Data (. => C |-> T) </data>
         when notBool (C in keys(Data))

  // this is bad, the bool arg has to be a function which is too restrictive
  /*
  syntax KItem ::= Bool "?"
  rule true ? => .
  */
  syntax KItem ::= "true?"
  rule true ~> true? => .

  // TODO: error handling/reporting like:
  //  rule E ~> true? => error(E) when E =/=K true

  //syntax KItem ::= Expr "constructorOf" Expr   [strict(1(context('piTarget)))]
  //syntax KItem ::= Expr "constructorOf" Expr          [strict(all(context('whnf), result(Whnf)))]
  syntax Bool ::= Expr "constructorOf" Expr          [strict(all(context('evalWhnf), result(Whnf)))]
  rule (Pi _ _ T => T) constructorOf _:Expr
  rule D:Name constructorOf D => true
  rule Set I:Int constructorOf Set I => true
  rule (T:Expr V:Variable => T) constructorOf (D:Expr V => D)
  rule (T:Expr E:Expr => T) constructorOf _:Expr  [owise]

  syntax Expr ::= prependParams(Params, Expr) [function]
  rule prependParams(.Params, T:Expr) => T
  rule prependParams(((X:Variable : Tp:Expr), Ps:Params), T:Expr) => Pi X Tp prependParams(Ps, T)

  syntax Constrs ::= prependParams(Params, Constrs) [function]
  rule prependParams(Ps:Params, .Constrs) => .Constrs
  rule prependParams(Ps:Params, ((C:Name : T:Expr), Cs:Constrs)) => (C : prependParams(Ps, T)), prependParams(Ps, Cs)

  syntax Expr ::= applyParams(Params, Expr) [function]
  rule applyParams(.Params, E:Expr) => E
  rule applyParams((((X:Variable : _:Expr), Ps:Params) => Ps), (E:Expr => E X))

  /*
  syntax Bool ::= notPi(Expr)   [function]
  rule notPi(Pi _ _ _) => false
  rule notPi(_:Expr) => true  [owise]
  */

  /*
  syntax K ::= piTarget(Expr)   [context(result('notPi))]
  rule piTarget(Pi _ _ E:Expr => E)
  */
  syntax Expr ::= piTarget(Expr) [function]
  rule piTarget(Pi _ _ E:Expr => E)
  rule piTarget(E:Expr) => E [owise]
endmodule
