require "agda-syntax.k"
require "agda-semantics-unification.k"
require "agda-semantics-normal.k"

module AGDA-SEMANTICS-COMMON
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS-UNIFICATION
  imports AGDA-SEMANTICS-NORMAL

  syntax KItem ::= "chich"

  syntax TypedExpr ::= t(Expr, Expr)    [latex(\ktyped{#1}{#2})]
  syntax Expr ::= TypedExpr


  //syntax Expr ::= Dot(Expr)

  syntax Name ::= Data(Identifier) | Con(Identifier) | Fun(Identifier) | Postulate(Identifier)
  syntax Name ::= Name "@" Map

  /*
  syntax Name ::= ncatLookup(Map, Name)  [function]
  rule ncatLookup((N |-> Nc) _, N) => Nc
  rule ncatLookup(_, N) => N  [owise]
  */
  /*
  syntax K ::= ncatReplace(Map, K)     [function]
  syntax KList ::= ncatReplace(Map, KList) [function]
  rule ncatReplace(NCat, N:Name) => #if N in keys(NCat) #then NCat(N) #else N #fi
       //<ncat>... N |-> Nc ...</ncat>
  rule ncatReplace(NCat, L:KLabel(Ks:KList)) => L(ncatReplace(NCat, Ks))
    when isName(L(Ks)) =/=K true
  rule ncatReplace(NCat, K:K,,Ks:KList) => ncatReplace(NCat, K),,ncatReplace(NCat, Ks)
  rule ncatReplace(_, .KList) => .KList
  */

  // XXX move to a better location?
  syntax K ::= K "@" Map
  rule L:KLabel(Ks:KList)@Fs => L(Ks@Fs)  when isName(L(Ks)) =/=K true  [structural, anywhere]
  rule N:Name@Fs => N  when notBool N in keys(Fs)  [structural, anywhere]
  //rule K@_ => K    [owise]
  syntax KList ::= KList "@" Map  //[function]
  rule .KList@_ => .KList  [structural, anywhere]
  rule (K,,Ks:KList)@Fs => (K@Fs),,(Ks@Fs)   [structural, anywhere]



  /*
  // XXX move to a better location?
  syntax Declarations ::= Declarations "@" Name
  rule ((module M Tel where MDs) ; Ds)@N => module M Tel where MDs@N ; (Ds@N)
  rule (postulate M : T ; Ds)@N => postulate M@N : T //; (Ds@N)
  rule (L = R ; Ds)@N => replaceLeftmost(L, leftmost(L)@N) = R ; (Ds@N)
  rule .Declarations@_ => .Declarations
  */

  /*
  syntax KItem ::= "saveMgu" | "loadMgu" | "cleanMgu"
  rule <k> saveMgu => . ...</k>
       <mgu> Mgu </mgu>
       <mgu-stack> (.List => ListItem(Mgu)) _ </mgu-stack>   // TODO replace m() with <ctx /> cell  -- doesn't work
  rule <k> loadMgu => . ...</k>
       <mgu> _ => Mgu </mgu>
       <mgu-stack> (ListItem(Mgu) => .List) _ </mgu-stack>
  rule <k> cleanMgu => . ...</k>
       <mgu> _ => .Mgu </mgu>
  */


  syntax KItem ::= saveCtx(Map) | "loadCtx"      // TODO no arg for saveCtx
  rule <k> saveCtx(Gamma) => . ...</k>
       <ctxstack> L => ListItem(#map(Gamma)) L </ctxstack>   // TODO replace m() with <ctx /> cell  -- doesn't work
  rule <k> loadCtx => . ...</k>
       <ctx> _ => Gamma </ctx>
       <ctxstack> ListItem(#map(Gamma)) L => L </ctxstack>
  rule (. => loadCtx) ~> R:KResult ~> (loadCtx => .)  [structural]

  syntax KItem ::= "pass?" | error(String)
  syntax GuardPass
  rule isGuardPass(true) => true
  rule _:GuardPass ~> pass? => .

  syntax KItem ::= "cleanMetas"
  rule <k> cleanMetas => . ...</k>
       <meta> _ => .Map </meta>

  syntax KItem ::= checkType(Expr, Expr)  [strict(1)]
  rule checkType(t(_, T1), T2) => renameBoundVariables(T1) == renameBoundVariables(T2) /*unifyConf ~>* killMgu*/
    when isPi(T1) =/=K true
  rule checkType(t(_, T1), T2) => T1 ~> renameBoundVariables(T1) ~> T2 ~> renameBoundVariables(T2) ~> renameBoundVariables(T1) == renameBoundVariables(T2) /*unifyConf ~>* killMgu*/
    when isPi(T1) ==K true

  // perform unification in order to obtain a universe type
  syntax KItem ::= checkSetType(Expr)  [strict, context(result(SetTypedExpr))]
  rule checkSetType(t(E, T)) => T == Set(Alpha) ~> unify(t(E, T)) ~> unifyConf ~> killMgu ~> checkSetType(HOLE)
    when isSetTypedExpr(t(E, T)) =/=K true andBool fresh(Alpha:Int)
  rule Te:SetTypedExpr ~> checkSetType(HOLE) => checkSetType(Te)

  syntax KItem ::= tsubst(Map)
  rule <k> t(E, T) ~> tsubst(M) => t(E, T[applyMguKeys(Theta, M)]) ...</k>
       <mgu> Theta </mgu> [structural]


  /* General auxiliary functions. */

  syntax Expr ::= lhs2expr(LHS)  [function] // appears to be needed in very special cases only, can't K's built-in casts be (ab)used?
  rule lhs2expr(E) => E

  syntax Expr ::= unhide(Expr)  [function]
  rule unhide({E}) => E
  rule unhide(E) => E   [owise]

  syntax K ::= leftmost(Expr)  [function]
  rule leftmost({E} => E) [structural]     // FIXME
  rule leftmost(E _ => E) [structural]
  rule leftmost(E) => E   [owise, structural]

  syntax Expr ::= replaceLeftmost(Expr, Expr)  [function]
  rule replaceLeftmost(E E', R) => replaceLeftmost(E, R) E'
  rule replaceLeftmost(_, R) => R    [owise]

  syntax List ::= args(Expr)  [function]
  rule args({E} => E)                      // FIXME
  rule args(E E' => E) (.List => ListItem(E'))
  rule args(_) => .List [owise]

  syntax Int ::= numPiArgs(Pi)   [function]
               | #numPiArgs(Pi, Int)  [function]
  rule numPiArgs(E) => #numPiArgs(E, 0)
  rule #numPiArgs((_ : _) -> E => E, I => I +Int 1)
  rule #numPiArgs({_ : _} -> E => E, I => I +Int 1)
  rule #numPiArgs(_, I) => I   [owise]

  syntax List ::= "List" KList  [function]
  rule List .KList => .List
  rule List K,,Ks => ListItem(K) (List Ks)

  syntax KList ::= "KList" List    [function]
  rule KList .List => .KList
  rule KList (ListItem(K) Ls) => K,, (KList Ls)

  syntax List ::= "List" Set    [function]
  rule List .Set => .List
  rule List (_ (SetItem(K) => .Set)) (.List => ListItem(K))

  syntax Set ::= "Set" List    [function]
  rule Set .List => .Set
  rule Set (_ (ListItem(K) => .List)) (.Set => SetItem(K))

  syntax KList ::= "KList" Set [function]
  rule KList S:Set => KList (List S)

  syntax Set ::= "Set" KList [function]
  rule Set Ks:KList => Set (List Ks)


  syntax Bool ::= all(KLabel, List)  [function]
  rule all(_, .List) => true      [structural]
  rule all(Pred, ListItem(K) L) => Pred(K) ==K true andBool all(Pred, L)  [structural]
  syntax Bool ::= any(KLabel, List)  [function]
  rule any(_, .List) => false     [structural]
  rule any(Pred, ListItem(K) L) => Pred(K) ==K true orBool any(Pred, L)   [structural]

  syntax List ::= filter(KLabel, List)  [function]
  rule filter(_, .List) => .List
  rule filter(Pred, _ (ListItem(K) => .List)) (.List => ListItem(K))  when Pred(K) ==K true
  rule filter(_, _ (ListItem(_) => .List))   [owise]

  syntax Set ::= filter(KLabel, Set)  [function]
  rule filter(Pred, S) => Set filter(Pred, List S)

  syntax List ::= map(KLabel, List)  [function]
  rule map(_, .List) => .List
  rule map(F, _ (ListItem(K) => .List)) (.List => ListItem(F(K)))

  syntax KList ::= map(KLabel, KList)  [function]
  rule map(F, Ks) => KList map(F, List Ks)

  // if length of the given list is less than the desired number,
  // the whole list is returned
  syntax List ::= take(Int, List)    [function]
  rule take(_, .List) => .List
  rule take(0, _) => .List
  rule take(I => I -Int 1, _ (ListItem(K) => .List)) (.List => ListItem(K))  [owise]

  syntax K ::= List "(" Int ")"  [function]
  rule (ListItem(K) _)(0) => K
  rule ((ListItem(K) => .List) _)(I => I -Int 1) [owise]

  syntax K ::= index(KLabel, List)        [function]
             | #index(KLabel, List, Int)  [function]
  rule index(Pred, L) => #index(Pred, L, 0)
  rule #index(Pred, ListItem(K) _, I) => I  when Pred(K)
  rule #index(Pred, (ListItem(K) => .List) _, I +Int 1)   [owise]

  syntax K ::= head(List)   [function]
  rule head(ListItem(K) _) => K

  /*
  syntax Map ::= Map "[" "undef" "/" Set "]"  [function]
  rule M[undef/.Set] => M
  rule ((K |-> _ => .Map) _)[undef/(SetItem(K) => .Set) _]
  rule _[undef/(SetItem(_) => .Set) _]    [owise]
  */

  syntax Map ::= Map "(" Set ")"   [function]
  rule _(.Set) => .Map
  rule ((K |-> V => .Map) _)((SetItem(K) => .Set) _) (.Map => K |-> V)
  rule _:Map((SetItem(_) => .Set) _)   [owise]

  /*
  // wrappers for containers (that do not belong to sort K)
  // NOTE: module K-WRAPPERS-LABELS in k-prelude.k seems to provide similar functionality
  syntax K ::= l(List)   [latex({#1})]
  syntax List ::= unl(K) [function]
  rule unl(l(L)) => L  [structural]
  // k-prelude defines #map + #getMapFromK s tymto istym ucelom
  syntax K ::= m(Map)    [latex({#1})]
  syntax Map ::= unm(K)  [function]
  rule unm(m(M)) => M  [structural]
  */

  /*
  syntax Set ::= boundVariables(K)   [function]
  rule boundVariables(K) => getVariables(K) -Set freeVariables(K)
  */
endmodule
