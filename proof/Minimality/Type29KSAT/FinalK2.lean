module

public import Minimality.Type29KSAT.LinkK2
public import Minimality.Type29KSAT.NfK2
public import Minimality.Type29TSAT.FinalBoundary

@[expose] public section

/-!
# Type 29, class K2 off `Z1`: `NF29.isRupert_K2a_offZ1`, `NF29.isRupert_K2b_offZ1`

Every normal form of class K2a (`a2 < 0`, `b0 < 0`, `V < 0`) that is not on the stratum `Z1 = {s = t = 1, a0 + h0 = 0}` is
Rupert, and every normal form of class K2b (`a2 < 0`, `b0 < 0`, `0 < V`) off `{t = s = 1, b2 + h2 = 0}`.  No genericity
hypothesis: the proof is the kernel-checked unsatisfiability of the trimmed core `K2` of 4,888 clauses (`coreUnsatK2`, the tie
view encoding with the class clause "not all of `KF1456`, `KF1546`, `B:34` vanish"), every row of which is checked against
the real data (`rupert_of_coreK2`).
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H29K.SAT

/-- **Class K2a from the core theorem**: if every type 29 facet family with the brackets
`[0123]+ [0134]- [0245]- [1235]-` and the class clause is Rupert, every normal form with `a2 < 0`, `b0 < 0`, `V < 0` off `Z1`
is Rupert. -/
theorem nf29_K2a_of_core
    (hcore : ∀ {y : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 y),
      0 < det3 (y 1 - y 0) (y 2 - y 0) (y 3 - y 0) → det3 (y 1 - y 0) (y 3 - y 0) (y 4 - y 0) < 0 →
      det3 (y 2 - y 0) (y 4 - y 0) (y 5 - y 0) < 0 → det3 (y 2 - y 1) (y 3 - y 1) (y 5 - y 1) < 0 →
      K2NZ F → IsRupert (univ.image y))
    {x : Fin 7 → ℝ³} (N : NF29 x) (ha2 : N.a2 < 0) (hb0 : N.b0 < 0) (hV : N.V < 0)
    (hZ : ¬ (N.s = 1 ∧ N.t = 1 ∧ N.a0 + N.h0 = 0)) :
    IsRupert (univ.image x) := by
  obtain ⟨i0, i1, i2, i3⟩ := nf29_brackets N
  have hDD := N.hDD
  let F := s0x_fac29 N.facets
  have hz : K2NZ F := k2nz_of_nf N F hZ
  rcases lt_or_gt_of_ne N.hD with hD | hD
  · refine isRupert_of_mir (hcore (mirFac F) ?_ ?_ ?_ ?_ (k2nz_mir F hz))
    · show 0 < det3 (mir (x 1) - mir (x 0)) (mir (x 2) - mir (x 0)) (mir (x 3) - mir (x 0))
      rw [mir_br, i0]; have := mul_neg_of_neg_of_pos hD hDD; linarith
    · show det3 (mir (x 1) - mir (x 0)) (mir (x 3) - mir (x 0)) (mir (x 4) - mir (x 0)) < 0
      rw [mir_br, i1]; have := mul_pos_of_neg_of_neg hD hb0; linarith
    · show det3 (mir (x 2) - mir (x 0)) (mir (x 4) - mir (x 0)) (mir (x 5) - mir (x 0)) < 0
      rw [mir_br, i2]; have := mul_pos_of_neg_of_neg hD hV; linarith
    · show det3 (mir (x 2) - mir (x 1)) (mir (x 3) - mir (x 1)) (mir (x 5) - mir (x 1)) < 0
      rw [mir_br, i3]; have := mul_pos_of_neg_of_neg hD ha2; linarith
  · refine hcore F ?_ ?_ ?_ ?_ hz
    · rw [i0]; exact mul_pos hD hDD
    · rw [i1]; exact mul_neg_of_pos_of_neg hD hb0
    · rw [i2]; exact mul_neg_of_pos_of_neg hD hV
    · rw [i3]; exact mul_neg_of_pos_of_neg hD ha2

end Minimality.H29K.SAT

/-- **Class K2a off `Z1` is closed.**  Every type 29 normal form with `a2 < 0`, `b0 < 0`, `V < 0` that is not on the stratum
`s = 1 ∧ t = 1 ∧ a0 + h0 = 0` (the quadrilateral `1456` a parallelogram and the facets `015`, `346` parallel) is Rupert, with
no hypothesis of general position. -/
theorem Minimality.NF29.isRupert_K2a_offZ1 {x : Fin 7 → EuclideanSpace ℝ (Fin 3)} (N : NF29 x) (ha2 : N.a2 < 0)
    (hb0 : N.b0 < 0) (hV : N.V < 0) (hZ : ¬ (N.s = 1 ∧ N.t = 1 ∧ N.a0 + N.h0 = 0)) :
    IsRupert (Finset.univ.image x) :=
  Minimality.H29K.SAT.nf29_K2a_of_core
    (fun F h0 h1 h2 h3 hz => Minimality.H29K.SAT.rupert_of_coreK2 Minimality.H29K.SAT.coreUnsatK2 F h0 h1 h2 h3 hz)
    N ha2 hb0 hV hZ

/-- **Class K2b off `σ(Z1)` is closed** (the `σ`-image of K2a: `σ` swaps `(a2, b0, V, s, t, a0, h0)` with
`(b0, a2, -V, t, s, b2, h2)`).  Every normal form with `a2 < 0`, `b0 < 0`, `0 < V` that is not on
`t = 1 ∧ s = 1 ∧ b2 + h2 = 0` is Rupert. -/
theorem Minimality.NF29.isRupert_K2b_offZ1 {x : Fin 7 → EuclideanSpace ℝ (Fin 3)} (N : NF29 x) (ha2 : N.a2 < 0)
    (hb0 : N.b0 < 0) (hV : 0 < N.V) (hZ : ¬ (N.t = 1 ∧ N.s = 1 ∧ N.b2 + N.h2 = 0)) :
    IsRupert (Finset.univ.image x) := by
  have hv : N.sigma.V = -N.V := by simp only [NF29.sigma, NF29.V]; ring
  have := N.sigma.isRupert_K2a_offZ1 (by exact hb0) (by exact ha2) (by linarith) (by exact hZ)
  rwa [image_sigma29] at this

#print axioms Minimality.NF29.isRupert_K2a_offZ1
#print axioms Minimality.NF29.isRupert_K2b_offZ1

/-- **Class K2 is closed off `Z1`** (all three signs of `V`): every type 29 normal form with `a2 < 0`, `b0 < 0` is Rupert
unless it is in the residual set `{V < 0, s = t = 1, a0 + h0 = 0} ∪ {0 < V, t = s = 1, b2 + h2 = 0}` (`V = 0` is the class
boundary, `NF29.isRupert_boundary`). -/
theorem Minimality.NF29.isRupert_K2_offZ1 {x : Fin 7 → EuclideanSpace ℝ (Fin 3)} (N : NF29 x) (ha2 : N.a2 < 0)
    (hb0 : N.b0 < 0)
    (hZ : ¬ ((N.V < 0 ∧ N.s = 1 ∧ N.t = 1 ∧ N.a0 + N.h0 = 0) ∨ (0 < N.V ∧ N.t = 1 ∧ N.s = 1 ∧ N.b2 + N.h2 = 0))) :
    IsRupert (Finset.univ.image x) := by
  rcases lt_trichotomy N.V 0 with hV | hV | hV
  · exact N.isRupert_K2a_offZ1 ha2 hb0 hV (fun h => hZ (Or.inl ⟨hV, h⟩))
  · exact N.isRupert_boundary (Or.inr (Or.inr hV))
  · exact N.isRupert_K2b_offZ1 ha2 hb0 hV (fun h => hZ (Or.inr ⟨hV, h⟩))

#print axioms Minimality.NF29.isRupert_K2_offZ1
