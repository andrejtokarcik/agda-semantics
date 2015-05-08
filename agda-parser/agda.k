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
    ff ( 'FunClauses(((#symFunClauses(182) Con ( "zero" )) #symVariable(183)
      ) = #symVariable(183),, ((#symFunClauses(184) (Con ( "suc" ) 
      #symVariable(185))) #symVariable(186)) = (Con ( "suc" ) ((Fun ( "plus" )
       #symVariable(185)) #symVariable(186)))) ) ~>
*/
                  /*
  canUnify('FunClauses(.KList), #symFunClauses(3000)) ~>


  canUnify('FunClauses((((((#symFunClauses(170) { #symExpr
      (487) }) { #symExpr(120) }) { Con ( "zero" ) }) Var ( "f" )) (Con ( "[]"
       ) { #symExpr(112) })) = (Con ( "[]" ) { #symExpr(159) }),, (((((
      #symFunClauses(287) { #symExpr(488) }) { #symExpr(182) }) { (Con ( "suc"
       ) #symExpr(489)) }) Var ( "f" )) ((((Con ( "_::_" ) { #symExpr(174) }) 
      { #symExpr(209) }) Var ( "x" )) Var ( "xs" ))) = ((((Con ( "_::_" ) { 
      #symExpr(246) }) { #symExpr(237) }) (Var ( "f" ) Var ( "x" ))) (((((Fun 
      ( "map" ) { #symExpr(248) }) { #symExpr(246) }) { #symExpr(237) }) Var (
       "f" )) Var ( "xs" )))), #symFunClauses(3001)) ~>

ff((((('FunClauses((((
      ((#symFunClauses(170) { #symExpr(487) }) { #symExpr(120) }) { Con ( 
      "zero" ) }) Var ( "f" )) (Con ( "[]" ) { #symExpr(112) })) = (Con ( "[]"
       ) { #symExpr(159) }),, (((((#symFunClauses(287) { #symExpr(488) }) { 
      #symExpr(182) }) { (Con ( "suc" ) #symExpr(489)) }) Var ( "f" )) ((((Con
       ( "_::_" ) { #symExpr(174) }) { #symExpr(209) }) Var ( "x" )) Var ( 
      "xs" ))) = ((((Con ( "_::_" ) { #symExpr(246) }) { #symExpr(237) }) (Var
       ( "f" ) Var ( "x" ))) (((((Fun ( "map" ) { #symExpr(248) }) { #symExpr(
      246) }) { #symExpr(237) }) Var ( "f" )) Var ( "xs" )))) { #symExpr(248) 
      }) { #symExpr(246) }) { #symExpr(237) }) ('FunClauses(((#symFunClauses(
      18) Con ( "zero" )) Var ( "m" )) = Var ( "m" ),, ((#symFunClauses(41) (
      Con ( "suc" ) Var ( "n" ))) Var ( "m" )) = (Con ( "suc" ) ((Fun ( "_+_" 
      ) Var ( "n" )) Var ( "m" )))) (Con ( "suc" ) (Con ( "suc" ) (Con ( "suc"
       ) Con ( "zero" )))))) ((((Con ( "_::_" ) { Data ( "Nat" ) }) { Con ( 
      "zero" ) }) (Con ( "suc" ) (Con ( "suc" ) (Con ( "suc" ) (Con ( "suc" ) 
      Con ( "zero" )))))) (Con ( "[]" ) { Data ( "Nat" ) }))) ~>
    isNf ( ((((Con ( "_::_" ) { #symExpr(246) }) { #symExpr(237) }) (Con ( "suc"
       ) (Con ( "suc" ) (Con ( "suc" ) Con ( "zero" ))))) ((((('FunClauses((((
      ((#symFunClauses(170) { #symExpr(487) }) { #symExpr(120) }) { Con ( 
      "zero" ) }) Var ( "f" )) (Con ( "[]" ) { #symExpr(112) })) = (Con ( "[]"
       ) { #symExpr(159) }),, (((((#symFunClauses(287) { #symExpr(488) }) { 
      #symExpr(182) }) { (Con ( "suc" ) #symExpr(489)) }) Var ( "f" )) ((((Con
       ( "_::_" ) { #symExpr(174) }) { #symExpr(209) }) Var ( "x" )) Var ( 
      "xs" ))) = ((((Con ( "_::_" ) { #symExpr(246) }) { #symExpr(237) }) (Var
       ( "f" ) Var ( "x" ))) (((((Fun ( "map" ) { #symExpr(248) }) { #symExpr(
      246) }) { #symExpr(237) }) Var ( "f" )) Var ( "xs" )))) { #symExpr(248) 
      }) { #symExpr(246) }) { #symExpr(237) }) ('FunClauses(((#symFunClauses(
      18) Con ( "zero" )) Var ( "m" )) = Var ( "m" ),, ((#symFunClauses(41) (
      Con ( "suc" ) Var ( "n" ))) Var ( "m" )) = (Con ( "suc" ) ((Fun ( "_+_" 
      ) Var ( "n" )) Var ( "m" )))) (Con ( "suc" ) (Con ( "suc" ) (Con ( "suc"
       ) Con ( "zero" )))))) ((((Con ( "_::_" ) { Data ( "Nat" ) }) { Con ( 
      "zero" ) }) (Con ( "suc" ) (Con ( "suc" ) (Con ( "suc" ) (Con ( "suc" ) 
      Con ( "zero" )))))) (Con ( "[]" ) { Data ( "Nat" ) })))) ) ~>
*/
                  /*
ff(((
      'FunClauses(((#symFunClauses(18) Con ( "zero" )) Var ( "m" )) = Var ( 
      "m" ),, ((#symFunClauses(41) (Con ( "suc" ) Var ( "n" ))) Var ( "m" )) =
       (Con ( "suc" ) ((Fun ( "_+_" ) Var ( "n" )) Var ( "m" )))) (Con ( "suc"
       ) (Con ( "suc" ) (Con ( "suc" ) Con ( "zero" ))))) Con ( "zero" ))) ~>
   isNf ( ((((Con ( "_::_" ) { #symExpr(246) }) { #symExpr(237) }) ((
      'FunClauses(((#symFunClauses(18) Con ( "zero" )) Var ( "m" )) = Var ( 
      "m" ),, ((#symFunClauses(41) (Con ( "suc" ) Var ( "n" ))) Var ( "m" )) =
       (Con ( "suc" ) ((Fun ( "_+_" ) Var ( "n" )) Var ( "m" )))) (Con ( "suc"
       ) (Con ( "suc" ) (Con ( "suc" ) Con ( "zero" ))))) Con ( "zero" ))) (((
      (('FunClauses((((((#symFunClauses(170) { #symExpr(487) }) { #symExpr(120
      ) }) { Con ( "zero" ) }) Var ( "f" )) (Con ( "[]" ) { #symExpr(112) })) 
      = (Con ( "[]" ) { #symExpr(159) }),, (((((#symFunClauses(287) { #symExpr
      (488) }) { #symExpr(182) }) { (Con ( "suc" ) #symExpr(489)) }) Var ( "f"
       )) ((((Con ( "_::_" ) { #symExpr(174) }) { #symExpr(209) }) Var ( "x" )
      ) Var ( "xs" ))) = ((((Con ( "_::_" ) { #symExpr(246) }) { #symExpr(237)
       }) (Var ( "f" ) Var ( "x" ))) (((((Fun ( "map" ) { #symExpr(248) }) { 
      #symExpr(246) }) { #symExpr(237) }) Var ( "f" )) Var ( "xs" )))) { 
      #symExpr(248) }) { #symExpr(246) }) { #symExpr(237) }) ('FunClauses(((
      #symFunClauses(18) Con ( "zero" )) Var ( "m" )) = Var ( "m" ),, ((
      #symFunClauses(41) (Con ( "suc" ) Var ( "n" ))) Var ( "m" )) = (Con ( 
      "suc" ) ((Fun ( "_+_" ) Var ( "n" )) Var ( "m" )))) (Con ( "suc" ) (Con 
      ( "suc" ) (Con ( "suc" ) Con ( "zero" )))))) ((((Con ( "_::_" ) { Data (
       "Nat" ) }) { Con ( "zero" ) }) (Con ( "suc" ) (Con ( "suc" ) (Con ( 
      "suc" ) (Con ( "suc" ) Con ( "zero" )))))) (Con ( "[]" ) { Data ( "Nat" 
      ) })))) ) ~>*/
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
