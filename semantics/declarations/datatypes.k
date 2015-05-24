module AGDA-SEMANTICS-DECLARATIONS-DATATYPES
  imports AGDA-SEMANTICS-COMMON

  rule [process-data-decl]:
       <k> data Name(N) Ps : T where Cons
           => addTypeCon(Data(N), App(Data(N), Ps), Pi(Ps, T)) ~>
              addDataCons(App(Data(N), Ps), Ps, Cons) ...</k>
       <ncat> NCat (. => Name(N) |-> Data(N)) </ncat>
    when notBool (Name(N) in keys(NCat))

  syntax KItem ::= addTypeCon(Name, Expr, Expr)              [strict(3(context('checkSetType)))]
  context addTypeCon(_, _, t(HOLE => whnf(HOLE), _))         [result(Whnf)]
  // not sure if the condition is correct: what universe must the datatype fit in?
  rule [add-type-con]:
       <k> addTypeCon(D, DPs, t(T, Set(Alpha))) => . ...</k>
       <sig>... . => D |-> renameBoundVariables(T) ...</sig>
    when T constructorOf Set(Alpha -Int 1)

  syntax KItem ::= addDataCons(Expr, Telescope, TypeSignatures)
  rule addDataCons(DPs, Ps, .TypeSignatures) => .    [structural]
  rule addDataCons(DPs, Ps, C : T ; Cons) => addDataCon(DPs, C, Pi(makeHidden(Ps), T)) ~> addDataCons(DPs, Ps, Cons)  [structural]

  syntax KItem ::= addDataCon(Expr, Name, Expr)              [strict(3(context('checkSetType)))]
  context addDataCon(_, _, t(HOLE => whnf(HOLE), _))         [result(Whnf)]
  // TODO check the constructor's universe whether it fits into the datatype's
  rule [add-data-con]:
       <k> addDataCon(DPs, Name(C), t(T, Set(_))) => . ...</k>
       <ncat> NCat (. => Name(C) |-> Con(C)) </ncat>
       <sig>... . => Con(C) |-> renameBoundVariables(T) ...</sig>
    when notBool (Name(C) in keys(NCat)) andBool T constructorOf DPs

  syntax KItem ::= Expr "constructorOf" Expr  [function]
  rule ((_ : _) -> T => T) constructorOf _
  rule ({_ : _} -> T => T) constructorOf _
  rule D:Name constructorOf D => true
  rule Set(Alpha) constructorOf Set(Alpha) => true
  rule (T:Expr _:Variable => T) constructorOf (D:Expr _:Variable => D)
  rule _:Expr E:Expr constructorOf (D:Expr {_} => D)
    when isImplicit(E) =/=K true
  rule (T:Expr _:Expr => T) constructorOf _:Expr  [owise]

  syntax Telescope ::= makeHidden(Telescope)  [function]
  rule makeHidden(.Telescope) => .Telescope
  rule makeHidden((X : T) Tel) => {X : T} makeHidden(Tel)
  rule makeHidden({X : T} Tel) => {X : T} makeHidden(Tel)
endmodule
