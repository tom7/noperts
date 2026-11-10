module

public import Minimality.Type29KSAT.LinkZB
public import Minimality.Type29KSAT.NfZA
public import Minimality.Type29TSAT.FinalBoundary

@[expose] public section

/-!
# Type 29, class K2a on the stratum `Z1`, case B, the residue of the Slide leaf: `NF29.isRupert_K2a_Z1_caseB_residue`

On the stratum `Z1 = {s = t = 1, a0 + h0 = 0}`, in case B (the edge direction `x1 - x4` orthogonal to `x0 - x1` and
`x0 - x5`, i.e. to the plane of the facet `B = 015`), the Slide leaf `NF29.isRupert_Z1_caseB_slide` covers the shapes
whose deep vertices `0, 2, 3` all lie beyond one end plane of the edge `15`.  The residue is "overhang at both ends":
some deep vertex `p` has `<x p - x1, x5 - x1> ≤ 0` and some deep vertex `q` has `<x q - x5, x1 - x5> ≤ 0`.  Every
normal form of class K2a (`a2 < 0`, `b0 < 0`, `V < 0`) in the residue is Rupert.  The proof is the kernel-checked
unsatisfiability of a trimmed core of 453 clauses of the tie view encoding, with the stratum `Z1`, the two case-B zeros
`T(d01, d14) = T(d05, d14) = 0` (four negated T units) and the two residue clauses as class literals
(`rupert_of_coreZB`).
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H29K.SAT

/-- **Class K2a on `Z1`, case B residue, from the core theorem**: if every type 29 facet family with the brackets
`[0123]+ [0134]- [0245]- [1235]-`, the three atoms `KF1456`, `KF1546`, `B:34` zero, `CaseB` and `CaseBRes` is Rupert,
every normal form with `a2 < 0`, `b0 < 0`, `V < 0` on `Z1` with `CaseB` and `CaseBRes` is Rupert. -/
theorem nf29_K2a_Z1_caseB_res_of_core
    (hcore : ∀ {y : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 y),
      0 < det3 (y 1 - y 0) (y 2 - y 0) (y 3 - y 0) → det3 (y 1 - y 0) (y 3 - y 0) (y 4 - y 0) < 0 →
      det3 (y 2 - y 0) (y 4 - y 0) (y 5 - y 0) < 0 → det3 (y 2 - y 1) (y 3 - y 1) (y 5 - y 1) < 0 →
      (det3 (y 1 - y 4) (y 5 - y 6) (F.N 5) = 0 ∧ det3 (y 1 - y 5) (y 4 - y 6) (F.N 5) = 0 ∧
        ⟪F.N 1, y 3 - y 4⟫ = 0) → CaseB y → CaseBRes y → IsRupert (univ.image y))
    {x : Fin 7 → ℝ³} (N : NF29 x) (ha2 : N.a2 < 0) (hb0 : N.b0 < 0) (hV : N.V < 0)
    (hZ : N.s = 1 ∧ N.t = 1 ∧ N.a0 + N.h0 = 0) (hB : CaseB x) (hR : CaseBRes x) :
    IsRupert (univ.image x) := by
  obtain ⟨i0, i1, i2, i3⟩ := nf29_brackets N
  have hDD := N.hDD
  let F := s0x_fac29 N.facets
  have hz := z1_atoms N F hZ
  rcases lt_or_gt_of_ne N.hD with hD | hD
  · refine isRupert_of_mir (hcore (mirFac F) ?_ ?_ ?_ ?_ ?_ ?_ ?_)
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
    · unfold CaseB at hB ⊢
      simp only [← mir_sub, mir_inner]
      exact hB
    · unfold CaseBRes at hR ⊢
      simp only [← mir_sub, mir_inner]
      exact hR
  · exact hcore F (by rw [i0]; exact mul_pos hD hDD) (by rw [i1]; exact mul_neg_of_pos_of_neg hD hb0)
      (by rw [i2]; exact mul_neg_of_pos_of_neg hD hV) (by rw [i3]; exact mul_neg_of_pos_of_neg hD ha2) hz hB hR

end Minimality.H29K.SAT

/-- **Class K2a on `Z1`, case B, overhang at both ends of `15`, is closed.**  Every type 29 normal form with `a2 < 0`,
`b0 < 0`, `V < 0` on the stratum `s = 1 ∧ t = 1 ∧ a0 + h0 = 0` in which `x1 - x4` is orthogonal to `x0 - x1` and
`x0 - x5` (case B), some deep vertex `p ∈ {0, 2, 3}` has `<x p - x1, x5 - x1> ≤ 0` and some deep vertex
`q ∈ {0, 2, 3}` has `<x q - x5, x1 - x5> ≤ 0`, is Rupert.  No hypothesis of general position.  Together with the Slide
leaf (`isRupert_Z1_caseB_slide`, the negation of the residue) this closes case B. -/
theorem Minimality.NF29.isRupert_K2a_Z1_caseB_residue {x : Fin 7 → EuclideanSpace ℝ (Fin 3)} (N : NF29 x)
    (ha2 : N.a2 < 0) (hb0 : N.b0 < 0) (hV : N.V < 0) (hZ : N.s = 1 ∧ N.t = 1 ∧ N.a0 + N.h0 = 0)
    (hB : inner ℝ (x 1 - x 4) (x 0 - x 1) = 0 ∧ inner ℝ (x 1 - x 4) (x 0 - x 5) = 0)
    (hR1 : ∃ p ∈ ({0, 2, 3} : Finset (Fin 7)), inner ℝ (x p - x 1) (x 5 - x 1) ≤ 0)
    (hR2 : ∃ q ∈ ({0, 2, 3} : Finset (Fin 7)), inner ℝ (x q - x 5) (x 1 - x 5) ≤ 0) :
    IsRupert (Finset.univ.image x) :=
  Minimality.H29K.SAT.nf29_K2a_Z1_caseB_res_of_core
    (fun F h0 h1 h2 h3 hz hB hR => Minimality.H29K.SAT.rupert_of_coreZB Minimality.H29K.SAT.coreUnsatZB F h0 h1 h2 h3
      hz hB hR)
    N ha2 hb0 hV hZ hB ⟨hR1, hR2⟩

/-- **Class K2b on `σ(Z1)`, case B residue, is closed** (the `σ`-image of K2a: `σ = (0 2)(4 5)`).  Every normal form
with `a2 < 0`, `b0 < 0`, `0 < V` on `t = 1 ∧ s = 1 ∧ b2 + h2 = 0` in which `x1 - x5` is orthogonal to `x2 - x1` and
`x2 - x4`, some `p ∈ {0, 2, 3}` has `<x p - x1, x4 - x1> ≤ 0` and some `q ∈ {0, 2, 3}` has `<x q - x4, x1 - x4> ≤ 0`,
is Rupert. -/
theorem Minimality.NF29.isRupert_K2b_Z1_caseB_residue {x : Fin 7 → EuclideanSpace ℝ (Fin 3)} (N : NF29 x)
    (ha2 : N.a2 < 0) (hb0 : N.b0 < 0) (hV : 0 < N.V) (hZ : N.t = 1 ∧ N.s = 1 ∧ N.b2 + N.h2 = 0)
    (hB : inner ℝ (x 1 - x 5) (x 2 - x 1) = 0 ∧ inner ℝ (x 1 - x 5) (x 2 - x 4) = 0)
    (hR1 : ∃ p ∈ ({0, 2, 3} : Finset (Fin 7)), inner ℝ (x p - x 1) (x 4 - x 1) ≤ 0)
    (hR2 : ∃ q ∈ ({0, 2, 3} : Finset (Fin 7)), inner ℝ (x q - x 4) (x 1 - x 4) ≤ 0) :
    IsRupert (Finset.univ.image x) := by
  have key : ∀ (P : Fin 7 → Prop), (∃ p ∈ ({0, 2, 3} : Finset (Fin 7)), P p) →
      ∃ p ∈ ({0, 2, 3} : Finset (Fin 7)), P (sigma29 p) := by
    rintro P ⟨p, hp, h⟩
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨2, by decide, h⟩
    · exact ⟨0, by decide, h⟩
    · exact ⟨3, by decide, h⟩
  have hv : N.sigma.V = -N.V := by simp only [NF29.sigma, NF29.V]; ring
  have := N.sigma.isRupert_K2a_Z1_caseB_residue (by exact hb0) (by exact ha2) (by linarith) (by exact hZ)
    (by exact hB) (key (fun p => inner ℝ (x p - x 1) (x 4 - x 1) ≤ 0) hR1)
    (key (fun q => inner ℝ (x q - x 4) (x 1 - x 4) ≤ 0) hR2)
  rwa [image_sigma29] at this

#print axioms Minimality.NF29.isRupert_K2a_Z1_caseB_residue
#print axioms Minimality.NF29.isRupert_K2b_Z1_caseB_residue
