require "agda-syntax-pretty.k"
require "agda-semantics-common.k"
require "agda-semantics-typesystem.k"

module AGDA-SEMANTICS
  imports AGDA-SYNTAX-PRETTY
  imports AGDA-SEMANTICS-COMMON
  imports AGDA-SEMANTICS-TYPESYSTEM

  rule Module _ _ Decls => Decls
  rule Syntax _ _ => .
  rule Postulate Sigs => Sigs

  context _ : (HOLE => whnfType(HOLE))  //[result(TypedType)]
  rule <k> N : te(E, Set _) => . ...</k>
       <tenv>... . => N |-> E ...</tenv>

  /*
  syntax Map ::= loadTelescope(Map, Expr) [function]
  rule loadTelescope(Sigma, (X : T) -> E) => (X |-> T) loadTelescope(Sigma, E)
  rule loadTelescope(Sigma, _) => Sigma [owise]

  rule <k> (. => bound!) ~> L = _ ~> (. => sig(Sigma)) </k>
       <sig> Sigma => loadTelescope(Sigma, Sigma(leftMost(L))) </sig>
  context bound! ~> HOLE = _
  context bound! ~> _ = HOLE
  */
  context HOLE = _
  context _ = HOLE
  rule <k> te(L, Tl) = te(R, Tr) => Tl == Tr ~> solve ...</k>
       <fenv>... . => L |-> R ...</fenv>   // << ako kluc chcem mat len fun name, kvoli partial application
                                         // ALTERNATIVA: ale asi by slo vymysliet, zeby som si vytvaral fresh funkcie
                                         // co by len lambda abstrakciou zaobalili tu pattern matching funkciu
                                         // (typu map = \a -> \b -> map a b spolu s pattern-matching-based definiciami mapu)
                                         // vyhol by som sa takto tomu fun() konstruktu
                                         // kazdopadne, <fenv /> by potom musel byt list (lebo nas zaujima poradie
                                         // fun klauzuli v orig kode) a nie map
endmodule
