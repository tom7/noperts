module

public import M7.ArcCap
public import M7.AxisCap
public import M7.IsNopert

@[expose] public section

/-!
# M7

M7 = permutations of (-27, 15, 15), (27, 6, 6), (-13, -13, -13) over 64. The caps of its
certificates in Lean: `M7.ArcCap` (the U cap and the arc, `M7.arc_not_rupert`) and
`M7.AxisCap` (the axis cap), and `M7.IsNopert` (`M7.isNopert_of_certificatesValid`, with the
tables of `M7.SolutionTree`; cap 3 is the P cap certificate of `M7.PCap`).
-/
