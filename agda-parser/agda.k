require "agda-syntax.k"
require "agda-semantics.k"

// TODO: closures (@Fun) like metadata wrappers by passing
// cell fragments as in kool-typed-dynamic.k

module AGDA
  imports AGDA-SYNTAX
  imports AGDA-SEMANTICS

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

  syntax K ::= ff(K)  [function]
  //rule ff(E) => matches(leftmost(E), subExpr(numReqArgs(leftmost(E)), E)) //andBool
  rule ff(E) => isFunClausesApp(E)


  syntax K ::= l(List)
  configuration //<T>
                  <k>
                  $PGM:Program  //</k>
                  ~> nf(Fun("t1")) </k>
                  //<br />
                  /*
                  <mods>
                    <mod multiplicity="*">
                      <name> Name </name>
                      <sig> .Map </sig>
                    </mod>
                  </mods>  // ako urcite to ma svoje vyhody ze mam vsetky signatury pokope
                  */
                  // obsah nasledujucich je staly
                  <sig> .Map </sig>
                  <meta> .Map </meta>
                  <fun> .Map </fun>  // ak to spravim <funs> a bude obsahovat <fun> a v tom List tak sa zbavim FunClauses (vid cil-semantics funs)
                  <ncat> .Map </ncat>   // <defs>?
                  //<br />
                  // obsa sa meni
                  <ctx> .Map </ctx>
                  <ctxstack> .List </ctxstack>    // <ctx-stack> a podobne aj ostatne
                  <fenv> .Map </fenv>
                  <fenv-stack> .List </fenv-stack>
                  <mgu> .Mgu </mgu>
                  <dbg> 0 </dbg>
                  /*
                  <md>                    // <md> [?]
                    <range> .K </range>
                  </md>
                  */
                //</T>
endmodule
