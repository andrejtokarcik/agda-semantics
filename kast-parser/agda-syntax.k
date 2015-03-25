module AGDA-SYNTAX
  syntax Variable ::= Token{[a-z][a-zA-Z0-9\_]*}  [onlyLabel]
  syntax Name ::= Token{[A-Z][a-zA-Z0-9\_]*}      [onlyLabel]
  // XXX: use Id instead of Variable?

  syntax Universe ::= "Set" Int

  // use getKLabel in checks instead of these Binder/ExprApp sorts
  /*
  syntax Binder ::= "Pi" Variable Expr Expr         [binder(1 -> 3), strict(2(context('eval2),result(TypeT)))]  // << bolo whnf21  -- daj whnf2eval1?
                  | "Lambda" Variable Expr Expr     [binder(1 -> 3), strict(2(context('eval2),result(TypeT)))]  // << bolo whnf21
  syntax ExprApp ::= Expr Expr                       [left, strict(1(context('evalWhnf2)), 2)]  // << bolo whnf2
  */

  // the [binder] attribute is useless for environment-based semantics
  // --- well not really it gets utilised within freeVariables()
  syntax Expr ::= "(" Expr ")" [bracket]
                | Variable | Name | "?"
                | Universe | "Set"
                > Expr Expr                       [left, strict(1(context('evalWhnf2)), 2)]  // << bolo whnf2
                > "Pi" Variable Expr Expr         [binder(1 -> 3), strict(2(context('evalWhnf2),result(TypeT)))]  // << bolo whnf21  -- daj whnf2eval1?
                | "Lambda" Variable Expr Expr     [binder(1 -> 3), strict(2(context('evalWhnf2),result(TypeT)))]  // << bolo whnf21


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

  syntax Pattern ::= "(" Pattern ")" [bracket]
    | Variable    //[klabel('autotype)]
    //| patvar(Variable)
    //| pat(Variable)  [strict(all(context('patvar)))]
    //| Variable ":" Expr
    | Name
    | Name Pattern  [left]
  //syntax Patterns ::= List{Pattern, ""}          //[strict] //[strict(all(context('pattype)))]
  syntax LHS ::= Variable   //[klabel('autotype)]
               | LHS Pattern  [left]  //, klabel(lhspat)]
  syntax FunDecl ::= LHS "=" Expr    [binder]
  //[strict(2(context('pattype2)))] //, 3(context('whnf21)))]
  //rule F:Variable = E:Expr => F .Patterns = E    [macro]

  /*
  syntax Program ::= FunDecl
                   | DataDecl
                   | Program Program  [assoc, id('.Program)]   // << doesn't work
                   //| DataDecl Program [klabel(p)]
  */

  syntax Decl ::= DataDecl | FunDecl

  // Explicit klabel below is necessary to avoid the "Cannot use '__ as a right
  // a right child of '__" error (which is apparently due to [left] attribute
  // assigned to Expr application and identical auto-generated klabels).
  // TODO: rename to Decls
  syntax Program ::= List{Decl, ";"}  [klabel(dl)]
endmodule
