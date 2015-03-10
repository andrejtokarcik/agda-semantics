require "modules/unification.k"
require "modules/substitution.k"

module LAMBDA-SYNTAX
  syntax Variable ::= Token{[a-z][a-zA-Z0-9\_]*}  [onlyLabel]
  syntax Name ::= Token{[A-Z][a-zA-Z0-9\_]*}     [onlyLabel]

  syntax Universe ::= "Set" Int
  syntax Expr ::= "(" Expr ")" [bracket]
                | Variable
                | Name
                | "Set"
                | Universe
                > Expr Expr [left, strict(1(context('whnf2)), 2)]
                > "Pi" Variable Expr Expr [binder, strict(2(context('whnf21),result(TypeT)))]
                | "Lambda" Variable Expr Expr [binder, strict(2(context('whnf21),result(TypeT)))]
                | "?"
  rule Set => Set 0 [macro]

  syntax DataDecl ::= "(" DataDecl ")" [bracket]
                    | "data" Name Params ":" Expr "where" Constrs [strict(3)]

  syntax Param ::= "(" Param ")" [bracket]
                 | Variable ":" Expr
  // TODO: this should be just standard application, not a list (Expr to contain telescopes)
  //       --- then remove applyParams() function
  syntax Params ::= List{Param,","}

  syntax Constr ::= "(" Constr ")" [bracket]
                  | Name ":" Expr
  // TODO: make Constrs newline-separated to match Agda's syntax
  syntax Constrs ::= List{Constr,","}

  // klabel below necessary in order to avoid "Cannot use '__ as a right
  // child of '__" errors (which is due to [left] attribute assigned
  // to application above)
  syntax Program ::= "expr" "=" Expr
                   | DataDecl Program  [klabel(p)]
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
  imports UNIFICATION
  imports SUBSTITUTION

  syntax ExprT ::= (Expr, Expr)
  syntax Expr ::= ExprT
  syntax KResult ::= ExprT

  syntax Whnf ::= "(" Whnf ")" [bracket]
                | WhNeut
                | Universe
                | "Pi" Variable Expr Expr [binder]
                | "Lambda" Variable Expr Expr [binder]
  syntax WhNeut ::= Name
                  | WhNeut Whnf [left]
  rule isWhnf(#symExpr(_)) => true
  syntax Expr ::= Whnf

  syntax Whnf2ExprT
  rule isWhnf2ExprT((_:Expr, _:Whnf)) => true
  syntax ExprT ::= Whnf2ExprT

  syntax K ::= whnf(Expr)                   [context(result(Whnf))]
  // TODO: (contextual) closures for evaluation
  rule whnf((Lambda X _ E1) E2 => E1[E2/X])
  syntax K ::= whnf2(Expr)                  [strict, context(result(Whnf2ExprT))]
  context whnf2((_, (HOLE => whnf(HOLE))))  [result(Whnf)]

  syntax Whnf21ExprT
  rule isWhnf21ExprT((_:Whnf, _:Whnf)) => true
  syntax Whnf2ExprT ::= Whnf21ExprT

  syntax K ::= whnf21(Expr)            [strict(all(context('whnf2))), context(result(Whnf21ExprT))]
  context whnf21(((HOLE => whnf(HOLE)), _:Whnf))   [result(Whnf)]

  syntax KItem ::= parseProgram(Program) [function]
  rule parseProgram(expr = E:Expr) => E
  rule parseProgram(D:DataDecl P:Program) => D ~> parseProgram(P)

  configuration <k color="green"> parseProgram($PGM:Program) </k>
                <tenv color="red"> .Map </tenv>
                <data> .Map </data>   // signatures
                <meta> .Map </meta>
                <mgu color="blue"> .Mgu </mgu>
                //<orig> $PGM </orig>

  // dependent type system

  rule <k> ? => (E, T) ...</k>
       <meta>... . => E |-> (E, T) ...</meta>
    when fresh(E:Expr) andBool fresh(T:Expr)

  rule <k> E => Et ...</k>
       <meta>... E |-> Et ...</meta>
    when isSymExpr(E)

  rule <k> X:Variable => (X, T) ...</k>
       <tenv>... X |-> T ...</tenv>

  rule <k> X:Name => (X, T) ...</k>
       <data>... X |-> T ...</data>

  rule Set I:Int => (Set I, Set (I +Int 1))

  rule <k> Pi X:Variable (T1:Expr, _) _ ~> (. => tenv(TEnv)) ...</k>
       <tenv> TEnv => TEnv[T1/X] </tenv>  //[structural]
  context Pi _ _ (HOLE:Expr => whnf2(HOLE)) ~> tenv(_)  [result(TypeT)]
  rule Pi X:Variable (T1:Expr, Set I1:Int) (T2:Expr, Set I2:Int) => (Pi X T1 T2, Set maxInt(I1, I2))

  rule <k> Lambda X:Variable (T:Expr, _) _ ~> (. => tenv(TEnv)) ...</k>
       <tenv> TEnv => TEnv[T/X] </tenv>  //[structural]
  context Lambda _ _ HOLE:Expr ~> tenv(_)
  rule Lambda X:Variable (T:Expr, _:Universe) (E:Expr, T':Expr) => (Lambda X T E, Pi X T T')

  rule (E1:Expr, T1:Whnf) (E2:Expr, T2:Expr) => T1 = Pi X T T' ~> T2 = T ~> (E1 E2, T') ~> tsubst(E2/X)
    when fresh(X:Variable) andBool fresh(T:Expr) andBool fresh(T':Expr)

  // datatypes

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
         when notBool(C in keys(Data))

  rule <k> data N:Name Ps:Params : (T:Expr, Set I:Int) where Cs:Constrs => isUniverse(piTarget(T)) ~> true? ~> processConstrs(applyParams(Ps, N), prependParams(Ps, Cs)) ...</k>
       <data> Data (. => N |-> prependParams(Ps, T)) </data>
         when notBool(N in keys(Data)) andBool /* FIXME? --> */ I >=Int 1

  // misc

  // special rules for unification
  // TODO: make it more formal in accordance with Norell's thesis, guarded constants etc.
  rule eqns((eqn(((Lambda X:Variable _:Expr E1:Expr) E2:Expr),,E':Expr) => eqn(E1[E2/X],,E')),,_)   [anywhere]
  rule eqns((eqn(E':Expr,,((Lambda X:Variable _:Expr E1:Expr) E2:Expr)) => eqn(E1[E2/X],,E')),,_)   [anywhere]

  syntax Expr ::= leftMost(Expr) [function]
  rule leftMost(E:Expr _:Expr) => leftMost(E)
  rule leftMost(E:Expr) => E [owise] 

  rule eqns((eqn((E1:Expr E2:Expr),,E':Expr) => eqn(E1,,Lambda X T E')),,_)
    when isSymExpr(leftMost(E1)) andBool fresh(X:Variable) andBool fresh(T:Expr)   [anywhere]
  rule eqns(E':Expr,,(eqn((E1:Expr E2:Expr)) => eqn(E1,,Lambda X T E')),,_)
    when isSymExpr(leftMost(E1)) andBool fresh(X:Variable) andBool fresh(T:Expr)   [anywhere]

  syntax KItem ::= Expr "=" Expr
  rule <k> T = T' => . ...</k>
       <mgu> Theta => updateMgu(Theta, T, T') </mgu> //[transition]

  rule <k> (_, T:Expr => applyMgu(Theta, T)) ...</k>
       <meta> Meta => applyMgu(Theta, Meta) </meta>
       <mgu> Theta => .Mgu </mgu>
    when Theta =/=K .Mgu   // <-- necessary, else infinite recursion

  syntax KItem ::= "tsubst" "(" Expr "/" Variable ")"
  rule <k> (_, T:Expr => T[E/X]) ~> (tsubst(E/X) => .) ...</k>
       <mgu> Theta </mgu>   // <mgu> .Mgu </mgu> doesn't work properly; the [anywhere] rule expanding .Mgu isn't anywhere enough, eh?
    when Theta ==K .Mgu     // hence, need this to guarantee that <mgu /> has been applied on the ExprT

  syntax KItem ::= tenv(Map)
  rule <k> _:ExprT ~> (tenv(TEnv) => .) ...</k>
       <tenv> _ => TEnv </tenv> //[transition]

  // normalise result
  syntax Nf ::= "(" Nf ")" [bracket]
                | Neut
                | Universe
                | "Pi" Variable Nf Nf [binder]
                | "Pi" Variable Variable Nf [binder]
                | "Lambda" Variable Nf Nf [binder]
  syntax Neut ::= Name
                | Variable   // FIXME?
                | Neut Nf [left]
  rule isNf(#symExpr(_)) => true
  syntax Whnf ::= Nf

  syntax Nf2ExprT
  rule isNf2ExprT((_:Expr, _:Nf)) => true
  syntax Whnf2ExprT ::= Nf2ExprT

  syntax K ::= nf(Expr)                   [strict(all(context('whnf))), context(result(Nf))]
  context nf(Pi _ (HOLE => nf(HOLE)) _)   [result(Nf)]
  context nf(Pi _ _ (HOLE => nf(HOLE)))   [result(Nf)]
  context nf(Lambda _ (HOLE => nf(HOLE)) _)   [result(Nf)]
  context nf(Lambda _ _ (HOLE => nf(HOLE)))   [result(Nf)]
  context nf((HOLE => nf(HOLE)) _:Expr)   [result(Nf)]
  context nf(_:Expr (HOLE => nf(HOLE)))   [result(Nf)]

  syntax K ::= nf2(Expr)                [strict, context(result(Nf2ExprT))]
  context nf2((_, (HOLE => nf(HOLE))))  [result(Nf)]

  /*
  // consider a separate tag <solution /> as in logik.k
  syntax KItem ::= "Solution" ExprT [strict(all(context('nf2)))]
  rule <k> S:ExprT => Solution S </k>
  */
  rule <k> T:ExprT => nf2(T) </k>

  syntax TypeT
  rule isTypeT((_:Expr, _:Universe)) => true
  syntax Nf2ExprT ::= TypeT

  // ---
  syntax Bool ::= isSymExpr(Expr) [function]
  rule isSymExpr(#symExpr(_)) => true
  rule isSymExpr(#symWhnf(_)) => true
  rule isSymExpr(#symNf(_)) => true

  syntax KItem ::= "true?"
  rule true ~> true? => .
endmodule
