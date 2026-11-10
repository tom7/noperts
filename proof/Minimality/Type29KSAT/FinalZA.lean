module

public import Minimality.Type29KSAT.LinkZA
public import Minimality.Type29KSAT.NfZA
public import Minimality.Type29TSAT.FinalBoundary

@[expose] public section

/-!
# Type 29, class K2a on the stratum `Z1`, case A: `NF29.isRupert_K2a_Z1_caseA`

On the stratum `Z1 = {s = t = 1, a0 + h0 = 0}` (the quadrilateral `1456` a parallelogram and the facets `015`, `346`
parallel), every normal form of class K2a (`a2 < 0`, `b0 < 0`, `V < 0`) in which the edge direction `x1 - x4` is not
orthogonal to the plane of the facet `B = 015` is Rupert.  Here "not orthogonal to both of the edges `x0 - x1` and
`x0 - x5` of that facet" is the hypothesis `CaseA`; its geometric form is that `x1 - x4` is not parallel to the facet
normal.  The proof is the kernel-checked unsatisfiability of a trimmed core of 1,012 clauses of the tie view encoding,
with the stratum `Z1` and the case clause "`<x0 - x1, x1 - x4>` or `<x0 - x5, x1 - x4>` is nonzero" as class literals
(`rupert_of_coreZA`).  The core was found by CaDiCaL on the sign encoding and shrunk; every row is checked here.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H29K.SAT

/-- **Class K2a on `Z1`, case A, from the core theorem**: if every type 29 facet family with the brackets
`[0123]+ [0134]- [0245]- [1235]-`, the three atoms `KF1456`, `KF1546`, `B:34` zero and `CaseA` is Rupert, every normal
form with `a2 < 0`, `b0 < 0`, `V < 0` on `Z1` with `CaseA` is Rupert. -/
theorem nf29_K2a_Z1_caseA_of_core
    (hcore : ∀ {y : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 y),
      0 < det3 (y 1 - y 0) (y 2 - y 0) (y 3 - y 0) → det3 (y 1 - y 0) (y 3 - y 0) (y 4 - y 0) < 0 →
      det3 (y 2 - y 0) (y 4 - y 0) (y 5 - y 0) < 0 → det3 (y 2 - y 1) (y 3 - y 1) (y 5 - y 1) < 0 →
      (det3 (y 1 - y 4) (y 5 - y 6) (F.N 5) = 0 ∧ det3 (y 1 - y 5) (y 4 - y 6) (F.N 5) = 0 ∧
        ⟪F.N 1, y 3 - y 4⟫ = 0) → CaseA y → IsRupert (univ.image y))
    {x : Fin 7 → ℝ³} (N : NF29 x) (ha2 : N.a2 < 0) (hb0 : N.b0 < 0) (hV : N.V < 0)
    (hZ : N.s = 1 ∧ N.t = 1 ∧ N.a0 + N.h0 = 0) (hA : CaseA x) :
    IsRupert (univ.image x) := by
  obtain ⟨i0, i1, i2, i3⟩ := nf29_brackets N
  have hDD := N.hDD
  let F := s0x_fac29 N.facets
  have hz := z1_atoms N F hZ
  rcases lt_or_gt_of_ne N.hD with hD | hD
  · refine isRupert_of_mir (hcore (mirFac F) ?_ ?_ ?_ ?_ ?_ ?_)
    · show 0 < det3 (mir (x 1) - mir (x 0)) (mir (x 2) - mir (x 0)) (mir (x 3) - mir (x 0))
      rw [mir_br, i0]; have := mul_neg_of_neg_of_pos hD hDD; linarith
    · show det3 (mir (x 1) - mir (x 0)) (mir (x 3) - mir (x 0)) (mir (x 4) - mir (x 0)) < 0
      rw [mir_br, i1]; have := mul_pos_of_neg_of_neg hD hb0; linarith
    · show det3 (mir (x 2) - mir (x 0)) (mir (x 4) - mir (x 0)) (mir (x 5) - mir (x 0)) < 0
      rw [mir_br, i2]; have := mul_pos_of_neg_of_neg hD hV; linarith
    · show det3 (mir (x 2) - mir (x 1)) (mir (x 3) - mir (x 1)) (mir (x 5) - mir (x 1)) < 0
      rw [mir_br, i3]; have := mul_pos_of_neg_of_neg hD ha2; linarith
    · obtain ⟨a, b, c⟩ := hz
      simp only [mirFac, ← mir_sub, mir_det3, mir_inner]
      refine ⟨?_, ?_, c⟩ <;> linarith
    · unfold CaseA at hA ⊢
      simp only [← mir_sub, mir_inner]
      exact hA
  · exact hcore F (by rw [i0]; exact mul_pos hD hDD) (by rw [i1]; exact mul_neg_of_pos_of_neg hD hb0)
      (by rw [i2]; exact mul_neg_of_pos_of_neg hD hV) (by rw [i3]; exact mul_neg_of_pos_of_neg hD ha2) hz hA

end Minimality.H29K.SAT

/-- **Class K2a on `Z1`, case A, is closed.**  Every type 29 normal form with `a2 < 0`, `b0 < 0`, `V < 0` on the stratum
`s = 1 ∧ t = 1 ∧ a0 + h0 = 0` in which `x1 - x4` is not orthogonal to both `x0 - x1` and `x0 - x5` (the two edges of the
facet `015`) is Rupert.  No hypothesis of general position. -/
theorem Minimality.NF29.isRupert_K2a_Z1_caseA {x : Fin 7 → EuclideanSpace ℝ (Fin 3)} (N : NF29 x) (ha2 : N.a2 < 0)
    (hb0 : N.b0 < 0) (hV : N.V < 0) (hZ : N.s = 1 ∧ N.t = 1 ∧ N.a0 + N.h0 = 0)
    (hA : inner ℝ (x 1 - x 4) (x 0 - x 1) ≠ 0 ∨ inner ℝ (x 1 - x 4) (x 0 - x 5) ≠ 0) :
    IsRupert (Finset.univ.image x) :=
  Minimality.H29K.SAT.nf29_K2a_Z1_caseA_of_core
    (fun F h0 h1 h2 h3 hz hA => Minimality.H29K.SAT.rupert_of_coreZA Minimality.H29K.SAT.coreUnsatZA F h0 h1 h2 h3 hz hA)
    N ha2 hb0 hV hZ hA

/-- **Case A in geometric form.**  The same, with the hypothesis that the edge direction `x1 - x4` is not parallel to the
normal of the facet `B = 015` (that is, not orthogonal to the plane of `B`). -/
theorem Minimality.NF29.isRupert_K2a_Z1_caseA_geom {x : Fin 7 → EuclideanSpace ℝ (Fin 3)} (N : NF29 x)
    (ha2 : N.a2 < 0) (hb0 : N.b0 < 0) (hV : N.V < 0) (hZ : N.s = 1 ∧ N.t = 1 ∧ N.a0 + N.h0 = 0)
    (hA : ¬ ∃ c : ℝ, x 1 - x 4 = c • (s0x_fac29 N.facets).N 1) :
    IsRupert (Finset.univ.image x) :=
  N.isRupert_K2a_Z1_caseA ha2 hb0 hV hZ (Minimality.H29K.SAT.caseA_of_not_parallel N _ hA)

/-- **Class K2b on `σ(Z1)`, case A, is closed** (the `σ`-image of K2a: `σ = (0 2)(4 5)`).  Every normal form with
`a2 < 0`, `b0 < 0`, `0 < V` on `t = 1 ∧ s = 1 ∧ b2 + h2 = 0` in which `x1 - x5` is not orthogonal to both `x2 - x1` and
`x2 - x4` is Rupert. -/
theorem Minimality.NF29.isRupert_K2b_Z1_caseA {x : Fin 7 → EuclideanSpace ℝ (Fin 3)} (N : NF29 x) (ha2 : N.a2 < 0)
    (hb0 : N.b0 < 0) (hV : 0 < N.V) (hZ : N.t = 1 ∧ N.s = 1 ∧ N.b2 + N.h2 = 0)
    (hA : inner ℝ (x 1 - x 5) (x 2 - x 1) ≠ 0 ∨ inner ℝ (x 1 - x 5) (x 2 - x 4) ≠ 0) :
    IsRupert (Finset.univ.image x) := by
  have hv : N.sigma.V = -N.V := by simp only [NF29.sigma, NF29.V]; ring
  have := N.sigma.isRupert_K2a_Z1_caseA (by exact hb0) (by exact ha2) (by linarith) (by exact hZ) (by exact hA)
  rwa [image_sigma29] at this

#print axioms Minimality.NF29.isRupert_K2a_Z1_caseA
#print axioms Minimality.NF29.isRupert_K2a_Z1_caseA_geom
#print axioms Minimality.NF29.isRupert_K2b_Z1_caseA
