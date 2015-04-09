require "agda-syntax.k"//-pretty.k"

require "modules/unification.k"

module AGDA-SEMANTICS-COMMON
  imports AGDA-SYNTAX//-PRETTY
  imports UNIFICATION

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

  syntax TenvRestore
  rule isTenvRestore(_:TypedExpr) => true
  syntax KItem ::= tenv(Map)
  rule <k> _:TenvRestore ~> (tenv(Gamma) => .) ...</k>
       <tenv> _ => Gamma </tenv>
  syntax KItem ::= sig(Map)
  rule <k> _:TenvRestore ~> (sig(Sigma) => .) ...</k>
       <sig> _ => Sigma </sig>

  syntax KItem ::= "chich"
  syntax FenvRestore
  rule isFenvRestore(_:NfTypedExpr) => true
  syntax KItem ::= fenv(Map)
  // XXX: must use 'isTypedExpr(HOLE)' instead of 'HOLE:TypedExpr'
  // due to the possible K BUG described below  (the latter doesn't
  // generate the dynamic sort check as intended).
  context (HOLE => nfType(HOLE)) ~> fenv(_) when isTypedExpr(HOLE)  [result(NfTypedExpr)]
  rule <k> _:FenvRestore ~> (fenv(Rho) => .) ...</k>
       <fenv> _ => Rho </fenv>

  syntax KItem ::= "true?"
  rule true ~> true? => .
  // TODO: error handling/reporting like:
  //  rule E ~> true? => error(E) when E =/=K true

  syntax Expr ::= leftmost(Expr)  [function]
  rule leftmost(E _ => E)
  rule leftmost(E) => E [owise]

  // for the binders' semantics
  syntax KItem ::= "envs!"
  syntax KItem ::= "bound!"




  syntax TypedExpr ::= t(Expr, Expr)
  syntax Expr ::= TypedExpr


  // XXX: should these be in a separate file -normal.k as before...?

  syntax Whnf ::= "(" Whnf ")" [bracket]
                | WhNeut
                /*
                | "Set" Int
                | "(" Name ":" Expr ")" "->" Expr        [binder(2 -> 4)]
                | "\\" "(" Name ":" Expr ")" "->" Expr   [binder(2 -> 4)]
                */
  syntax WhNeut /*::= Variable     // considered neutral only if cannot be evaluted
                  | Name
                  | WhNeut Expr [left]
                  */
  rule isWhNeut(_:WhNeut _:Expr) => true
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
  syntax Neut /*::= Variable       // considered neutral only if cannot be evaluated
                | Name
                | Neut Nf [left]
                */
  rule isNeut(_:Variable) => true
  rule isNeut(_:Name) => true
  rule isNeut(_:Neut _:Nf) => true
  rule isNf(Set _) => true
  rule isNf((_ : _:Nf) -> _:Nf) => true
  rule isNf(\ (_ : _:Nf) -> _:Nf) => true

  syntax WhNeut ::= Neut
  syntax Whnf ::= Nf
  syntax Expr ::= Whnf

  syntax NfTypedExpr
  rule isNfTypedExpr(t(_, _:Nf)) => true
  syntax WhnfTypedExpr ::= NfTypedExpr
  rule isWhnfTypedExpr(t(_, _:Whnf)) => true
  syntax TypedExpr ::= WhnfTypedExpr | NfTypedExpr

  syntax SetTypedExpr
  //rule isSetTypedExpr(t(_:Expr, _:MetaVariable)) => true   // XXX hack
  rule isSetTypedExpr(t(_, Set _)) => true
  syntax NfTypedExpr ::= SetTypedExpr




  /*
  syntax KItem ::= Expr "==" Expr
             | Mgu "&&" Expr "==" Expr
  rule T1 == T2 => .Mgu && T1 == T2   [macro]
  rule Theta:Mgu && T1 == T2 => updateMgu(Theta, T1, T2)  [macro]
  */

  syntax KItem ::= Expr "==" Expr
  rule <k> T == T' => . ...</k>
       <mgu> Theta => updateMgu(Theta, T, T') </mgu>

  syntax KItem ::= "unify"
  rule <k> unify => . ...</k>
       <sig> Sigma => applyMgu(Theta, Sigma) </sig>
       <tenv> Gamma => applyMgu(Theta, Gamma) </tenv>
       <fenv> Rho => applyMgu(Theta, Rho) </fenv>
       <metavars> Meta => applyMgu(Theta, Meta) </metavars>
       <mgu> Theta => .Mgu </mgu>
    when isMguError(Theta) =/=K true

  /*
  syntax KItem ::= unify(K)         [context(result(Unified))]   //[strict(all(context('whnf)))]
  syntax Unified ::= unified(K)
  rule <k> (. => unify) ~> unify(K => unified(unify(Theta, K))) ...</k>
       <mgu> Theta </mgu>
    when getKLabel(K) =/=KLabel 'unified
  */

  syntax KItem ::= unify(Expr)
  rule <k> unify(E:Expr) => unify ~> applyMgu(Theta, E) ...</k>
       <mgu> Theta </mgu>

  syntax KItem ::= unifyType(TypedExpr)     //[context(result(Unified))]
  rule <k> unifyType(t(E, T)) => unify ~> t(E, applyMgu(Theta, T)) ...</k>
       <mgu> Theta </mgu>

  /*
  context unifyType(t(_, HOLE => unify(HOLE)))   [result(Unified)]
  rule unifyType(t(E, unified(T)) => unified(t(E, T)))
  */

  syntax KItem ::= coerceSetType(Expr)  [strict(all(context('whnfType))), context(result(SetTypedExpr))]
  rule coerceSetType(t(E, T)) => T == Set I ~> unifyType(t(E, T)) ~> coerceSetType(HOLE)  //[heat]
    when isSetTypedExpr(t(E, T)) =/=K true andBool fresh(I:Int)
  rule Te:SetTypedExpr ~> coerceSetType(HOLE) => coerceSetType(Te)
  /*
  rule coerceSetType(t(E, T:Expr)) => T == Set I ~> unifyType(t(E, T)) ~> coerceSetType(HOLE)
    when isSetTypedExpr(t(E, T)) =/=K true andBool fresh(I:Int)
  rule Set I ~> coerceSetType(t(E, HOLE)) => coerceSetType(t(E, Set I))
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
  rule X:Variable@Rho => #if X in keys(Rho) andBool Rho(X) =/=K ^ #then Rho(X)@Rho #else X #fi  [structural, anywhere]
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


  syntax KItem ::= eval(K)  [context(result(Val))]
  rule <k> eval(E:Expr => E@Rho) ...</k>
       <fenv> Rho </fenv>

  syntax KItem ::= whnf(K)  [strict(all(context('eval))), context(result(Whnf))]
  context whnf(HOLE => evalWhnf(HOLE))  when isVal(HOLE)      [result(ValWhnf)]
  context whnf(HOLE => deval(HOLE))     when isValWhnf(HOLE)  [result(Whnf)]

  syntax KItem ::= whnfType(K) [strict, context(result(WhnfTypedExpr))]
  context whnfType(t(_, HOLE::Expr => whnf(HOLE)))  [result(Whnf)]

  syntax KItem ::= nf(K)  [strict(all(context('eval))), context(result(Nf))]
  context nf(HOLE => evalNf(HOLE))    when isVal(HOLE)      [result(ValNf)]
  context nf(HOLE => deval(HOLE))     when isValNf(HOLE)    [result(Nf)]

  syntax KItem ::= nfType(K) [strict, context(result(NfTypedExpr))]
  context nfType(t(_, (HOLE::Expr => nf(HOLE))))  [result(Nf)]









  rule isFenvRestore(evalWhnf(_:ValWhnf)) => true


  syntax KItem ::= evalWhnf(Val)     [context(result(ValWhnf))]
  // XXX !!! HOLE:<sort> does NOT enforce dynamic checks that HOLE is of sort <sort>,
  // possibly A BUG IN K (check newer versions before reporting),
  // it might be just an indication how to _parse_ the item [as with ::]
  // TODO: create a test for this!
  /*
  context evalWhnf((HOLE:Expr => nft ~> isExpr(HOLE) ~> evalWhnf(HOLE)) _)
      when isExpr(HOLE)    [result(ValWhnf)]  // << 'when' clause necessary due to the bug mentioned above
  */
  context evalWhnf((HOLE::Val => evalWhnf(HOLE)) _)   [result(ValWhnf)]

  rule <k> evalWhnf((\ (X : _) -> E:Expr)@Rho V:Val => E@(Rho[V/X])) ~> (. => fenv(Rho')) ...</k>
       <fenv> Rho' </fenv>

  // see the NOTE in agda-semantics.k on how to try to implement pattern matching
  //rule <k> evalWhnf(fun(Cs:List)@Fun V:Val => matchCase(Cs, V, Fun)) ~> (. => fenv(Fun')) ...</k>
  //     <fun> Fun' </fun>
  // TODO: add rules ^ for general P -> C:Case, not just when isExpr(C)



  syntax KItem ::= evalNf(Val)     [strict(all(context('evalWhnf))), context(result(ValNf))]
  context evalNf((HOLE::Val => evalNf(HOLE)) _)  [result(Nf)]
  context evalNf(_::Val (HOLE => evalNf(HOLE)))  [result(Nf)]
  // TODO !!!!!!
  /*
  context evalNf((_ : (HOLE:Val => evalNf(HOLE))) -> _)  [result(Nf)]
  context evalNf((X : _)-> (HOLE:Expr@Rho => evalNf(HOLE@(Rho[^/X]))))  [result(Nf)]
  context evalNf(\ (_ : (HOLE:Val => evalNf(HOLE))) -> _)  [result(Nf)]
  context evalNf(\ (X : _)-> (HOLE:Expr@Rho => evalNf(HOLE@(Rho[^/X]))))  [result(Nf)]
  */



  syntax KItem ::= deval(K) [context(result(Expr))]
  rule deval(E:Expr@_ => E)
  rule deval((E1:Expr => deval(E1)) (E2:Expr => deval(E2)))

endmodule
