module

public import M7.IsNotRupert
public import Nopert

@[expose] public section

/-!
# M7 is a nopert, given valid certificate data

M7 is the convex polyhedron whose vertices are the permutations of (-27, 15, 15)/64 and
(27, 6, 6)/64, and (-13, -13, -13)/64 (`M7.vertexQ`, `M7.verts` its vertex set, `M7.solid` its
hull). As for the Septopert (`Septopert.lean`), the Lean proof `isNopert_of_certificatesValid`
shows that valid certificate data give `IsNopert verts`, and the program `constructM7` checks the
data natively (the tables and the cap, arc cap and axis cap certificates).

One claim is still a hypothesis: cap 3, `PCapClaim` (the strip of views around (2, 1, 0) with
rotations within 1/46), has no certificate yet.
-/

namespace M7

open Noperts Noperts.Pipeline

/-- The certificate data is valid: four solution tables (one per chart, each passing the validity
check), the cap certificate at the mirror normal, the arc cap certificate (cap 1), the axis cap
certificate (cap 2), and the claim of cap 3. -/
def CertificatesValid : Prop :=
  ∃ table : CayleyAtlas.ChartIndex → SolutionTree.Table,
    (∀ chart, (table chart).chart = chart) ∧
    (∀ chart, (table chart).Valid) ∧
    SolutionTree.CapOk ∧
    SolutionTree.ArcOk ∧
    SolutionTree.AxisOk ∧
    PCapClaim

/-- If the certificate data is valid, M7 is not Rupert. -/
theorem not_isRupert_of_certificatesValid (h : CertificatesValid) : ¬ IsRupert verts := by
  obtain ⟨table, hchart, hvalid, hcap, harc, haxis, hpc⟩ := h
  exact not_rupert_of_valid_tables table hchart hvalid hcap harc haxis hpc

/-- M7 is a genuine solid: its vertices 0, 1, 2 and 6 span a tetrahedron. -/
theorem not_coplanar_verts : ¬ Coplanar ℝ (verts : Set ℝ³) := by
  refine not_coplanar_of_det3_ne_zero
    (a := toR3 (vertexQ 0)) (b := toR3 (vertexQ 1)) (c := toR3 (vertexQ 2)) (d := toR3 (vertexQ 6))
    (by simp [verts]) (by simp [verts]) (by simp [verts]) (by simp [verts]) ?_
  simp [det3, Matrix.det_fin_three, toR3, vertexQ]
  norm_num

/-- **M7 is a nopert**, given valid certificate data. -/
theorem isNopert_of_certificatesValid (h : CertificatesValid) : IsNopert verts :=
  ⟨not_coplanar_verts, not_isRupert_of_certificatesValid h⟩

end M7

end
