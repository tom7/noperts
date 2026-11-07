module

public import Septopert.ArcCap
public import Septopert.AxisCap
public import Septopert.IsNopert

@[expose] public section

/-!
# Septopert

Septopert = permutations of (-27, 15, 15), (27, 6, 6), (-13, -13, -13) over 64. The caps of its
certificates in Lean: `Septopert.ArcCap` (the U cap and the arc, `Septopert.arc_not_rupert`) and
`Septopert.AxisCap` (the axis cap), and `Septopert.IsNopert` (`Septopert.isNopert_of_certificatesValid`, with the
tables of `Septopert.SolutionTree`; cap 3 is the P cap certificate of `Septopert.PCap`).
-/
