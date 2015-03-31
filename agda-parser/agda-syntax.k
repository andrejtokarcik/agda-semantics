module AGDA-SYNTAX
  // perhaps I don't have to include ranges at all? is it good for anything
  // besides error reporting?

  // TODO: get rid of Color as done for Range...
  // TODO: convert all of those into functions (i.e. klabels without underscores)
  // and then mark everything as [onlyLabel] -> we should refer to -pretty.k terms exclusively

  // output z `agda` je teraz dvakrat zabaleny zoznam (neviem preco)
  syntax Program ::= List{DeclarationL, ","}

  // elementom DeclarationL moze byt aj samotne DeclarationL, kedze
  // K automaticky zoznam nastavi ako subsort toho sortu elementov,
  // t. j. DeclarationL < Declaration
  syntax DeclarationL ::= List{Declaration, ","}

  // TODO: skus to urobit tak ze tu v K budem pracovat s peknou beznou citatelnou syntaxou
  // Agda programov, ale z K parsera dostanem Concrete
  // tak zachovam vyhody (scope checking, spracovane operatory atd.) i budem mat
  // pekne pravidla v semantike.

  syntax Declaration ::= "(" Declaration ")" [bracket]
    | "TypeSig" ArgInfo AgdaName Expr
    | "FunClause" LHS RHS WhereClause
    | "DataSig" Induction AgdaName LamBindingL Expr
    | "Data" Induction AgdaName LamBindingL ExprM TypeSignatureOrInstanceBlockL
    | "Syntax" AgdaName Notation
    | "Postulate" TypeSignatureOrInstanceBlockL
    | "Module" QName Telescope DeclarationL

  syntax Expr ::= "(" Expr ")" [bracket]
    | "Ident" AgdaName
    | "Lam" LamBindingL Expr
    | "App" Expr ArgExpr
    | "Fun" Expr Expr
    | "Pi" Telescope Expr
    | "Set"  [onlyLabel]
    | "Set" Int
  rule 'Set => 'Set_(0) [macro]

  syntax LHS ::= "(" LHS ")" [bracket]
    | "LHS" Pattern PatternL RewriteEqnL WithExprL      // LHS lhsOriginalPattern lhsWithPattern lhsRewriteEqn lhsWithExpr
    //| "Ellipsis" ...
  syntax PatternL ::= List{Pattern, ","}
  syntax Pattern ::= "(" Pattern ")" [bracket]
    | "IdentP" QName
    | "QuoteP"
    //| ... etc, TODO
  syntax RewriteEqnL ::= List{RewriteEqn, ","}
  syntax RewriteEqn ::= Expr
  syntax WithExprL ::= List{WithExpr, ","}
  syntax WithExpr ::= Expr

  syntax RHS ::= "(" RHS ")" [bracket]
    | "AbsurdRHS"
    | "RHS" Expr

  syntax WhereClause ::= "(" WhereClause ")" [bracket]
    | "NoWhere"
    | "AnyWhere" DeclarationL
    | "SomeWhere" AgdaName DeclarationL

  syntax Induction ::= "Inductive"   // don't support "CoInductive"

  syntax LamBindingL ::= List{LamBinding, ","}
  syntax LamBinding ::= "(" LamBinding ")" [bracket]
    | "DomainFree" ArgInfo BoundName
    | "DomainFull" TypedBindings

  syntax Telescope ::= "(" Telescope ")" [bracket]
    | List{TypedBindings, ","}
  syntax TypedBindings ::= "(" TypedBindings ")" [bracket]
    | "TypedBindings" ArgTypedBinding
  syntax ArgTypedBinding ::= "(" ArgTypedBinding ")" [bracket]
    | "Arg" ArgInfo TypedBinding
  syntax TypedBinding ::= "(" TypedBinding ")" [bracket]
    | "TBind" BoundNameL Expr
    | "TLet" DeclarationL Expr
  syntax BoundNameL ::= List{BoundName, ","}
  syntax BoundName ::= "(" BoundName ")" [bracket]
    | "BName" AgdaName AgdaName FixityP
  syntax FixityP ::= "(" FixityP ")" [bracket]
    | "Fixity'" Fixity Notation
  syntax Fixity ::= "(" Fixity ")" [bracket] 
    | "LeftAssoc" Int
    | "RightAssoc" Int
    | "NonAssoc" Int
  syntax Notation ::= GenPartL [bracket]
  syntax GenPartL ::= List{Bool, ","}   // FIXME

  syntax ArgExpr ::= "(" ArgExpr ")" [bracket]
                   | "Arg" ArgInfo Expr

  // ---
  // preliminaries:

  syntax Variable ::= Token{[a-zA-Z][a-zA-Z0-9\_]*}  [onlyLabel]
  syntax AgdaName ::= Variable
  syntax QName ::= AgdaName | AgdaName"."QName
  // See c-semantics/cil-semantics/cil-syntax.k for Char syntax, including EscapeString.
  syntax Literal ::= Int | Float | "\""String"\"" | "'"Char"'" | QName

  syntax Hiding ::= "Hidden" | "NotHidden"
  syntax Relevance ::= "Relevant" | "Irrelevant" | "UnusedArg"
  syntax Color ::= Expr
  syntax ColorL ::= List{Color, ","}
  syntax ArgInfo ::= "(" ArgInfo ")" [bracket] 
    | "ArgInfo" Hiding Relevance ColorL

  syntax TypeSignatureOrInstanceBlockL ::= List{TypeSignatureOrInstanceBlock, ","}
  syntax TypeSignatureOrInstanceBlock ::= Declaration

  syntax ExprM ::= "Just" Expr | "Nothing"

  syntax Range ::= "@noRange"
    | Token{([a-zA-Z0-9\/\-]+ "." "l"? "agda" ":")? [0-9]+ "," [0-9]+ "-" ([0-9]+ ",")? [0-9]+}  [notInRules]
    | "@someRange"
  syntax K ::= m(Range, K)    // generic metadata wrapper

// the following set of rules doesn't work, from which follows that the problem is *not*
// restricted to dynamic sort checks -- the 'annotated' keyword apparently has to be moved
// from (generic) K sort to the particular sorts as in
//    syntax Declaration ::= annotated Range Declaration
// TODO: the change should also allow mentioning DeclarationL directly in agda.k in the rules
// for sequentialising the input declaration lists etc.
/*
rule isDeclarationL(annotated _ K) => isDeclarationL(K)
rule isDeclaration(annotated _ K) => isDeclaration(K)
rule isExpr(annotated _ K) => isExpr(K)
// etc.   -- generated via x.py
*/

/*
  // WAAAT this doesn't appear to work either...
  // metadata wrappers for every syntax sort
  //syntax DeclarationL ::= m(MetaData, DeclarationL)
  syntax Declaration ::= m(MetaData, Declaration)
  syntax Expr ::= m(MetaData, Expr)
  syntax LHS ::= m(MetaData, LHS)
  //syntax PatternL ::= m(MetaData, PatternL)
  syntax Pattern ::= m(MetaData, Pattern)
  //syntax RewriteEqnL ::= m(MetaData, RewriteEqnL)
  //syntax RewriteEqn ::= m(MetaData, RewriteEqn)
  //syntax WithExprL ::= m(MetaData, WithExprL)
  //syntax WithExpr ::= m(MetaData, WithExpr)
  syntax RHS ::= m(MetaData, RHS)
  syntax WhereClause ::= m(MetaData, WhereClause)
  //syntax Induction ::= m(MetaData, Induction)
  //syntax LamBindingL ::= m(MetaData, LamBindingL)
  syntax LamBinding ::= m(MetaData, LamBinding)
  //syntax Telescope ::= m(MetaData, Telescope)
  //syntax Telescope ::= m(MetaData, Telescope)
  syntax TypedBindings ::= m(MetaData, TypedBindings)
  syntax ArgTypedBinding ::= m(MetaData, ArgTypedBinding)
  syntax TypedBinding ::= m(MetaData, TypedBinding)
  //syntax BoundNameL ::= m(MetaData, BoundNameL)
  syntax BoundName ::= m(MetaData, BoundName)
  syntax FixityP ::= m(MetaData, FixityP)
  syntax Fixity ::= m(MetaData, Fixity)
  //syntax Notation ::= m(MetaData, Notation)
  //syntax GenPartL ::= m(MetaData, GenPartL)
  //syntax QName ::= m(MetaData, QName)
  //syntax AgdaName ::= m(MetaData, AgdaName)
  //syntax Literal ::= m(MetaData, Literal)
  //syntax Hiding ::= m(MetaData, Hiding)
  //syntax Relevance ::= m(MetaData, Relevance)
  //syntax Color ::= m(MetaData, Color)
  //syntax ColorL ::= m(MetaData, ColorL)
  syntax ArgInfo ::= m(MetaData, ArgInfo)
  //syntax TypeSignatureOrInstanceBlockL ::= m(MetaData, TypeSignatureOrInstanceBlockL)
  //syntax TypeSignatureOrInstanceBlock ::= m(MetaData, TypeSignatureOrInstanceBlock)
  //syntax ExprM ::= m(MetaData, ExprM)
  //syntax Range ::= m(MetaData, Range)
*/
endmodule
