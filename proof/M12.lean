module

public import M12.ArcCap
public import M12.AxisCap
public import M12.IsNopert

@[expose] public section

/-!
# M12

M12 = permutations of (-11, 7, 7), (12, 3, 3), (-5, -5, -5) over 16. The caps of its
certificates in Lean: `M12.ArcCap` (the U cap and the arc, `M12.arc_not_rupert`) and
`M12.AxisCap` (the axis cap), and `M12.IsNopert` (`M12.isNopert_of_certificatesValid`, with the
tables of `M12.SolutionTree`; cap 3 is the hypothesis `M12.PCapClaim`).
-/
