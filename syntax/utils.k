module AGDA-SYNTAX-UTILS
  imports AGDA-SYNTAX

  syntax Telescope ::= castTelescope(LamBindings)  [function, notInPrograms]
  rule castTelescope(LamBind(Relevant, NotHidden, X:Variable) Bs:LamBindings) => (X : %meta) castTelescope(Bs)
  rule castTelescope(LamBind(Relevant, Hidden, X:Variable) Bs:LamBindings) => {X : %meta} castTelescope(Bs)
  rule castTelescope(B:TypedBinding Bs:LamBindings) => B castTelescope(Bs)
  rule castTelescope(.LamBindings) => .Telescope

  syntax Telescope ::= castTelescope(List)  [function, notInPrograms]
  rule castTelescope(ListItem(X) Xs) => (X : %meta) castTelescope(Xs)
  rule castTelescope(.List) => .Telescope
endmodule
