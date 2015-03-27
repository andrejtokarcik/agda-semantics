// TODO: import agda-syntax here so that it doesn't have to be in each -semantics- module separately
// ^ this doesn't work that way I think
require "agda-semantics-normal.k"
require "agda-semantics-typesystem.k"
require "agda-semantics-decl-data.k"
require "agda-semantics-decl-fun.k"
require "agda-semantics-metavariables.k"

module AGDA-SEMANTICS
  imports AGDA-SEMANTICS-NORMAL
  imports AGDA-SEMANTICS-TYPESYSTEM
  imports AGDA-SEMANTICS-DECL-DATA
  imports AGDA-SEMANTICS-DECL-FUN
  imports AGDA-SEMANTICS-METAVARIABLES
endmodule
