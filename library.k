module LIBRARY
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
  rule all(_, .List) => true
  rule all(Pred, ListItem(K) L) => Pred(K) ==K true andBool all(Pred, L)
  syntax Bool ::= any(KLabel, List)  [function]
  rule any(_, .List) => false
  rule any(Pred, ListItem(K) L) => Pred(K) ==K true orBool any(Pred, L)

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
endmodule
