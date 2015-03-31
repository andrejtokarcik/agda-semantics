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

  rule <k> N : E => . ...</k>
       <tenv>... . => N |-> E ...</tenv>   // TODO: this should go into <sig /> (was called <data /> in kast-parser version)
  rule <k> L = R => . ...</k>     // both L and R should be preprocessed via strictness (type-checked)
       <fenv>... . => L |-> R ...</fenv>   // << ako kluc chcem mat len fun name, kvoli partial application
                                         // ale asi by slo vymysliet, zeby som si vytvaral fresh funkcie
                                         // co by len lambda abstrakciou zaobalili tu pattern matching funkciu
                                         // (typu map = \a -> \b -> map a b spolu s pattern-matching-based definiciami mapu)
                                         // vyhol by som sa takto tomu fun() konstruktu
                                         // kazdopadne, <fenv /> by potom musel byt list (lebo nas zaujima poradie
                                         // fun klauzuli v orig kode) a nie map
endmodule
