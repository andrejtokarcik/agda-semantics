module AGDA-SEMANTICS-DECLARATIONS-LOCAL
  syntax KItem ::= globalNames(Set) | globalNames(Name, Set)

  syntax KItem ::= localNames(Set) | localData(Map, Map)
  rule <k> localNames(.Set) => . ...</k>
  rule <k> localNames(SetItem(N) _) ...</k>
       <ncat>... _ |-> N => . ...</ncat>
  rule <k> localNames(SetItem(N) _) ...</k>
       <sig>... N |-> _ => . ...</sig>
  rule <k> localNames(SetItem(N) _) ...</k>
       <fun>... N |-> _ => . ...</fun>
  rule <k> localNames((SetItem(N) => .Set) _) ...</k>
       <ncat> NCat </ncat>
       <sig> Sigma </sig>
       <fun> Rho </fun>
    when notBool ((N in keys(NCat)) orBool (N in keys(Sigma)) orBool (N in keys(Rho)))

  syntax Name ::= "<" Name "," Map "," Map ">"    // <N, Sigma, Rho>
  syntax K ::= "<" K "," Map "," Map ">"
  rule <L:KLabel(Ks:KList), Ts, Fs> => L(<Ks, Ts, Fs>)  when isName(L(Ks)) =/=K true  [structural, anywhere]
  rule <N:Name, Ts, _> => N  when notBool N in keys(Ts)  [structural, anywhere]
  syntax KList ::= "<" KList "," Map "," Map ">"
  rule <.KList, _, _> => .KList  [structural, anywhere]
  rule <K,,Ks:KList, Ts, Fs> => <K, Ts, Fs>,,<Ks, Ts, Fs>   [structural, anywhere]
endmodule
