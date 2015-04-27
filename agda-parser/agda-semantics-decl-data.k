require "agda-semantics-common.k"

module AGDA-SEMANTICS-DECL-DATA
  imports AGDA-SEMANTICS-COMMON

  syntax KItem ::= "params!"
  rule (. => params!) ~> data _ Ps : (T => Pi(Ps, T)) where _   [structural]
  context params! ~> data _ _ : (HOLE => checkSetType(HOLE)) where _   [result(SetTypedExpr)]
  rule <k> params! ~> data Name(N) Ps : t(T, Set(_)) where Cons
           => //I >=Int 1 ~> pass? ~>        // << FIXME   (the `-Int 1' guard below is sufficient?)
              addDataSig(Data(N), App(Data(N), Ps), T) ~>
              addConSigs(App(Data(N), Ps), Ps, Cons) ...</k>
       <ncat> NCat (. => Name(N) |-> Data(N)) </ncat>
    when notBool (Name(N) in keys(NCat))     // this may be already guaranteed by the external parser

  syntax KItem ::= addDataSig(Name, Expr, Expr)              [strict(3(context('checkSetType)))]
  // FIXME not sure if the condition is correct: what universe must the datatype fit in?
  rule <k> addDataSig(D, DPs, t(T, Set(I))) => T constructorOf Set(I -Int 1) ~> pass? ...</k>
       <sig> Sigma (. => D |-> T) </sig>
       <con>... . => DPs |-> l(.List) ...</con>

  syntax KItem ::= addConSigs(Expr, Telescope, TypeSignatures)
  rule addConSigs(DPs, Ps, .TypeSignatures) => .    [structural]
  rule addConSigs(DPs, Ps, (C : T) Cons) => addConSig(DPs, C, Pi(makeHidden(Ps), T)) ~> addConSigs(DPs, Ps, Cons)  [structural]

  syntax KItem ::= addConSig(Expr, Name, Expr)  [strict(3(context('checkSetType)))]
  // TODO: check the constructor's universe whether it fits into the datatype's
  rule <k> addConSig(DPs, Name(C), t(T:Expr, Set(_))) => T constructorOf DPs ~> pass? ...</k>
       <ncat> NCat (. => Name(C) |-> Con(C)) </ncat>
       <sig> Sigma (. => Con(C) |-> T) </sig>
       <con>... DPs |-> l(_ (. => ListItem(Con(C)))) ...</con>
    when notBool (Name(C) in keys(NCat))     // this may be already guaranteed by the external parser

  syntax KItem ::= Expr "constructorOf" Expr          [strict(all(context('whnf)))]
  rule ((_ : _) -> T => T) constructorOf _
  rule ({_ : _} -> T => T) constructorOf _
  rule D:Name constructorOf D => true
  rule Set(I) constructorOf Set(I) => true
  rule (T:Expr _:Variable => T) constructorOf (D:Expr _:Variable => D)
  rule _:Expr E:Expr constructorOf (D:Expr {_} => D)
    when isImplicit(E) =/=K true
  rule (T:Expr _:Expr => T) constructorOf _:Expr  [owise]

  syntax Telescope ::= makeHidden(Telescope)  [function]
  rule makeHidden(.Telescope) => .Telescope
  rule makeHidden((X : T) Tel) => {X : T} makeHidden(Tel)
  rule makeHidden({X : T} Tel) => {X : T} makeHidden(Tel)

  /*
  syntax Expr ::= applyParams(Expr, Telescope) [function]
  rule applyParams(E, .Telescope) => E
  rule applyParams(E => E X, (X:Variable : _:Expr) Ps:Telescope => Ps)
  // TODO: hidden bindings
  */
endmodule
