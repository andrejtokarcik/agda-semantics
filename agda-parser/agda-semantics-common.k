require "agda-syntax.k"//-pretty.k"

module AGDA-SEMANTICS-COMMON
  imports AGDA-SYNTAX//-PRETTY

  syntax KResult ::= TypedExpr

  /*
  // TODO: if we defined ValNf, we could reduce needEval() to a check
  // of belonging to the syntactic sort ValNf
  syntax Bool ::= needEval(K, Map)  [fenvction]
  rule needEval((_, T:Expr) => T, _)
  rule needEval(E:Expr, _) => true when isNf(E) =/=K true
  // do *not* want freeVariablesM here
  rule needEval(E, Rho) => notBool isEmptySet(intersectSet(freeVariables(E), keys(Rho) -Set boundKeys(Rho))) [owise]
  // `-Set boundKeys` not necessary because binder takes care of it?
  // -- it *is* necessary since the var may have been bound in a 'higher' bounder, not in this one,
  //    i.e. it will be superfluous only for the var bound just now
  */

  syntax TEnvRestore
  rule isTEnvRestore(_:TypedExpr) => true
  syntax KItem ::= tenv(Map)
  rule <k> _:TEnvRestore ~> (tenv(Gamma) => .) ...</k>
       <tenv> _ => Gamma </tenv>
  syntax KItem ::= sig(Map)
  rule <k> _:TEnvRestore ~> (sig(Sigma) => .) ...</k>
       <sig> _ => Sigma </sig>

  syntax FEnvRestore
  rule isFEnvRestore(_:NfTypedExpr) => true
  syntax KItem ::= fenv(Map)
  context (HOLE:TypedExpr => nfType(HOLE)) ~> fenv(_)
  rule <k> _:FEnvRestore ~> (fenv(Rho) => .) ...</k>
       <fenv> _ => Rho </fenv>

  syntax KItem ::= "true?"
  rule true ~> true? => .

  syntax Expr ::= leftmost(Expr)  [function]
  rule leftmost(E _ => E)
  rule leftmost(E) => E [owise]

  // for the binders' semantics
  syntax KItem ::= "envStored!"
  syntax KItem ::= "bound!"

  syntax Bool ::= matches(K, K)  [function]
  rule matches(Set I1 => I1, Set I2 => I2)
  rule matches(K1, K2) => true
    when K1 ==K K2 orBool
         isVariable(K1) orBool
         isVariable(K2)
    [owise]





  /*
  // this causes LOTS of ambiguities
  syntax TypedExpr ::= "(" TypedExpr ")" [bracket]
                     | Expr ":" Expr  [klabel('te)]      // ~ expr : type    // XXX: kedze dvojbodka je aj na type signature, tak sa tie anotacie mozu chaoticky zanorovat...
  */
  syntax TypedExpr ::= te(Expr, Expr)
  //syntax TypedExpr ::= PrettyBinding
  //syntax priorities 'bnd > 'te
  //syntax priorities 'te > 'tsig
  syntax Expr ::= TypedExpr


  // XXX: should these be in a separate file -normal.k as before...?

  syntax Whnf ::= "(" Whnf ")" [bracket]
                | WhNeut
                /*
                | "Set" Int
                | "(" Name ":" Expr ")" "->" Expr        [binder(2 -> 4)]
                | "\\" "(" Name ":" Expr ")" "->" Expr   [binder(2 -> 4)]
                */
  syntax WhNeut ::= Name     // considered neutral only if cannot be evaluted
                  | WhNeut Expr [left]
  rule isWhnf(Set _) => true
  rule isWhnf((_ : _) -> _) => true
  rule isWhnf(\ (_ : _) -> _) => true
  
  syntax Nf ::= "(" Nf ")" [bracket]
                | Neut
                /*
                | "Set" Int
                | "(" Name ":" Nf ")" "->" Nf        [binder(2 -> 4)]
                | "\\" "(" Name ":" Nf ")" "->" Nf   [binder(2 -> 4)]
                */
  syntax Neut ::= Name       // considered neutral only if cannot be evaluated
                | Neut Nf [left]
  rule isNf(Set _) => true
  rule isNf((_ : _:Nf) -> _:Nf) => true
  rule isNf(\ (_ : _:Nf) -> _:Nf) => true

  syntax WhNeut ::= Neut
  syntax Whnf ::= Nf
  syntax Expr ::= Whnf

  syntax NfTypedExpr
  rule isNfTypedExpr(te(_:Expr, _:Nf)) => true
  syntax WhnfTypedExpr ::= NfTypedExpr
  rule isWhnfTypedExpr(te(_:Expr, _:Whnf)) => true
  syntax TypedExpr ::= WhnfTypedExpr | NfTypedExpr

  /*
  syntax TypedType
  rule isTypedType(te(_:Expr, _:MetaVariable)) => true   // XXX hack
  rule isTypedType(te(_:Expr, Set _)) => true
  syntax NfTypedExpr ::= TypedType
  */


  syntax Val ::= "(" Val ")" [bracket]
               | Expr "@" Map   [klabel('closure)]
               | Val Val  [left]

  syntax Val ::= "^"   // bound -- vraj aj historicky symbol na oznacenie prave bound premennych

  syntax Set ::= boundKeys(Map)  [function]
  rule boundKeys(.Map) => .Set   [structural]
  rule boundKeys((E |-> ^ => .) _) (. => SetItem(E)) [structural]
  rule boundKeys((_ |-> _ => .) _) [owise, structural]

  // The following rules are where most of the evaluation magic happens...
  rule X:Name@Rho => #if X in keys(Rho) andBool Rho(X) =/=K ^ #then Rho(X)@Rho #else X #fi  [structural, anywhere]
  rule (Set I:Int)@_ => Set I [structural, anywhere]
  rule N:WhNeut@_ => N   [structural, anywhere]
  rule (E1:Expr E2:Expr)@Rho => E1@Rho E2@Rho [structural, anywhere]
  // handle (E@R1)@R2 --- have to take advantage of abstract syntax here, or else K complains about E@RhoOrig's not being an Expr but a Val
  // (the more immediate context, closer to the expression, has higher priority, its values are just extended not modified)
  rule 'closure(E:Expr@RhoOrig,, Map2KLabel(RhoNew:Map)(.KList)) => E@(RhoNew[RhoOrig]) [structural, anywhere]

  syntax ValNf ::= Neut
                 | Neut ValNf [left]
  rule isValNf(E:Nf@Rho) => true when isEmptySet(intersectSet(freeVariables(E), keys(Rho) -Set boundKeys(Rho)))

  syntax ValWhnf ::= WhNeut
                   | WhNeut Val [left]
  rule isValWhnf(E:Whnf@Rho) => true when isName(leftmost(E)) impliesBool notBool (leftmost(E) in keys(Rho) -Set boundKeys(Rho))


  syntax ValWhnf ::= ValNf
  syntax Val ::= ValWhnf


  syntax K ::= eval(K)  [context(result(Val))]
  rule <k> eval(E:Expr => E@Rho) ...</k>
       <fenv> Rho </fenv>

  syntax K ::= whnf(K)  [strict(all(context('eval))), context(result(Whnf))]
  context whnf(HOLE:Val => evalWhnf(HOLE)) [result(ValWhnf)]
  context whnf(HOLE:ValWhnf => deval(HOLE)) [result(Whnf)]

  syntax K ::= whnfType(K) [strict, context(result(WhnfTypedExpr))]
  context whnfType(te(_, HOLE:Expr => whnf(HOLE)))  [result(Whnf)]

  syntax K ::= nf(K)  [strict(all(context('eval))), context(result(Nf))]
  context nf(HOLE:Val => evalNf(HOLE)) [result(ValNf)]
  context nf(HOLE:ValNf => deval(HOLE)) [result(Nf)]

  syntax K ::= nfType(K) [strict, context(result(NfTypedExpr))]
  context nfType(te(_, (HOLE:Expr => nf(HOLE))))  [result(Nf)]









  rule isFEnvRestore(evalWhnf(_:ValWhnf)) => true


  syntax K ::= evalWhnf(Val)     [context(result(ValWhnf))]
  // XXX !!! HOLE:<sort> does NOT enforce dynamic checks that HOLE is of sort <sort>,
  // possibly A BUG IN K (check newer versions before reporting),
  // it might be just an indication how to _parse_ the item [as with ::]
  // TODO: create a test for this!
  /*
  context evalWhnf((HOLE:Expr => nft ~> isExpr(HOLE) ~> evalWhnf(HOLE)) _)
      when isExpr(HOLE)    [result(ValWhnf)]  // << 'when' clause necessary due to the bug mentioned above
  */
  context evalWhnf((HOLE:Val => evalWhnf(HOLE)) _)   [result(ValWhnf)]

  rule <k> evalWhnf((\ (_ X : _) -> E:Expr)@Rho V:Val => E@(Rho[V/X])) ~> (. => fenv(Rho')) ...</k>
       <fenv> Rho' </fenv>

  // see the NOTE in agda-semantics.k on how to try to implement pattern matching
  //rule <k> evalWhnf(fun(Cs:List)@Fun V:Val => matchCase(Cs, V, Fun)) ~> (. => fenv(Fun')) ...</k>
  //     <fun> Fun' </fun>
  // TODO: add rules ^ for general P -> C:Case, not just when isExpr(C)



  syntax K ::= evalNf(Val)     [strict(all(context('evalWhnf))), context(result(ValNf))]
  context evalNf((HOLE:Val => evalNf(HOLE)) _:Val)  [result(Nf)]
  context evalNf(_:Val (HOLE:Val => evalNf(HOLE)))  [result(Nf)]
  // TODO !!!!!!
  /*
  context evalNf((_ : (HOLE:Val => evalNf(HOLE))) -> _)  [result(Nf)]
  context evalNf((X : _)-> (HOLE:Expr@Rho => evalNf(HOLE@(Rho[^/X]))))  [result(Nf)]
  context evalNf(\ (_ : (HOLE:Val => evalNf(HOLE))) -> _)  [result(Nf)]
  context evalNf(\ (X : _)-> (HOLE:Expr@Rho => evalNf(HOLE@(Rho[^/X]))))  [result(Nf)]
  */



  syntax K ::= deval(K) [context(result(Expr))]
  rule deval(E:Expr@_ => E)
  rule deval((E1:Expr => deval(E1)) (E2:Expr => deval(E2)))

endmodule
