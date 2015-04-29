require "agda-syntax.k"
require "agda-semantics.k"

// TODO: closures (@Fun) like metadata wrappers by passing
// cell fragments as in kool-typed-dynamic.k

module AGDA
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS

  // sequentialise any whitespace-separated list that gets on top
  // (don't I want to deal with declaration lists *only*?)
  rule 'Cons(D,, Ds) => D ~> Ds           [structural]
  rule '.List`{""`}(.KList) => .          [structural]

  /*
  // metadata bureaucracy
  syntax K ::= md(MetadataCellFragment, K)
             | md(MetadataCellFragment)
  rule [R:Range] K => md(<range> R </range>, K)  [macro]
  rule <k> md(M, K) => K ~> md(M') ...</k>
       <metadata> M' => M </metadata>   [structural]
  //rule <k> _:KResult ~> md(M') => . ...</k>
  //     <metadata> _ => M' </metadata>   [structural]
  rule <k> md(M') => . ...</k>
       <metadata> _ => M' </metadata>   [structural]
  */

  configuration //<T>
                  <k> $PGM:Program </k>
                  <ctx> .Map </ctx>
                  <ctxstack> .List </ctxstack>
                  <sig> .Map </sig>
                  <meta> .Map </meta>
                  <fun> .Map </fun>
                  <con> .Map </con>
                  <ncat> .Map </ncat>
                  <mgu> .Mgu </mgu>
                  /*
                  <md>                    // <md> [?]
                    <range> .K </range>
                  </md>
                  */
                //</T>
endmodule
