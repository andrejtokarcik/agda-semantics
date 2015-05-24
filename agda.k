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
                  /*
hold(dummyVarsInBinders({ 
      #symVariable(675) : #symExpr(190) } -> ( #symVariable(678) : (Var ( "b" 
      ) (Con ( "suc" ) #symVariable(675))) ) -> ( #symVariable(677) : #symExpr
      (651) ) -> (Var ( "b" ) (Con ( "suc" ) (Con ( "suc" ) #symVariable(675))
      )))) ~> 

updateMgu(.Mgu,
  { 
      #symVariable(675) : #symExpr(190) } -> ( #symVariable(678) : (Var ( "b" 
      ) (Con ( "suc" ) #symVariable(675))) ) -> ( #symVariable(677) : #symExpr
      (651) ) -> (Var ( "b" ) (Con ( "suc" ) (Con ( "suc" ) #symVariable(675))
      )) ,
      
     
	dummyVarsInBinders({ #symVariable(71111) 
      : #symExpr(190) } -> ( #symVariable(707) : (Var ( "b" ) #symVariable(709
      )) ) -> ( #symVariable(708) : #symExpr(410) ) -> (Var ( "b" ) (Con ( 
      "suc" ) #symVariable(709)))) ) ~>

      */
                  $PGM:Program  </k>
                  //~> nf(Fun("t1")) </k>
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
                  //<br />
                  // obsah sa meni
                  <ctx> .Map </ctx>
                  <ctx-stack> .List </ctx-stack>    // <ctx-stack> a podobne aj ostatne
                  <fun> .Map </fun>  // ak to spravim <funs> a bude obsahovat <fun> a v tom List tak sa zbavim FunClauses (vid cil-semantics funs)
                  <meta> .Map </meta>
                  //<mgu-stack> .List </mgu-stack>
                  //<dbg> 0 </dbg>
                  <ncat> .Map </ncat>
                  <mgu> .Mgu </mgu>
                  /*
                  <md>                    // <md> [?]
                    <range> .K </range>
                  </md>
                  */
                //</T>
endmodule
