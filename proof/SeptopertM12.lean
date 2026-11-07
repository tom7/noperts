module

public import SeptopertM12.ArcCap
public import SeptopertM12.AxisCap
public import SeptopertM12.IsNopert

@[expose] public section

/-!
# SeptopertM12

SeptopertM12 = permutations of (-11, 7, 7), (12, 3, 3), (-5, -5, -5) over 16. The caps of its
certificates in Lean: `SeptopertM12.ArcCap` (the U cap and the arc, `SeptopertM12.arc_not_rupert`) and
`SeptopertM12.AxisCap` (the axis cap), and `SeptopertM12.IsNopert` (`SeptopertM12.isNopert_of_certificatesValid`, with the
tables of `SeptopertM12.SolutionTree`; cap 3 is the hypothesis `SeptopertM12.PCapClaim`).
-/
