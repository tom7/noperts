module

public import Minimality.Type08S.P2NP5

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a, T4 `K_b` and `K_2`: `np_Kb`, `np_K2`.
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem np_Kb {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegT4 N.F)
    (hF : Fr e1 e2 e3) {κ κv : ℝ} (hκ : κ ≠ 0) (hκv : κv = κ ∨ κv = -κ) (hxe : b - d = κ • e3)
    (hf2 : ⟪c - d, e2⟫ = 0) (hL : 0 < ⟪c - d, e1⟫) (hr : 0 < ⟪b' - d, e2⟫)
    {k' : ℕ} [NeZero k'] (hk3 : 3 ≤ k') (σ : ZMod k' → ZMod 4) (u e : ℝ³)
    (hu : u = κv • e3) (he : e = ⟪c - d, e1⟫ • e1)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3 (quad b c' b' c (σ (i + 1)) - quad b c' b' c (σ i))
      (quad b c' b' c (σ j) - quad b c' b' c (σ i)) u)
    (hleft : ∀ (i : ZMod k') (a_ : ZMod 4), 0 ≤ det3 (quad b c' b' c (σ (i + 1)) - quad b c' b' c (σ i))
      (quad b c' b' c a_ - quad b c' b' c (σ i)) u)
    (hz : IsRobustUnimodal (fun i => ⟪quad b c' b' c (σ i), u⟫))
    (hbad : NoPersistHDN (fun i => quad b c' b' c (σ i)) u e) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨hcr, hcg, hXd0, hXdL, hlam⟩ := pic_Kb N hreg hF hκ hxe hf2 hL hr
  obtain ⟨hYg, hYp, hDp, hYq, hYlt, hcop, hchord⟩ := extra_Kb N hreg hF hκ hxe hf2 hL hr hcg hlam
  have hκv0 : κv ≠ 0 := by rcases hκv with h | h <;> rw [h] <;> simp [hκ]
  have hxx : b = fpt e1 e2 e3 d 0 0 κ := by
    rw [fpt, ← pc_smul_e3 hF, ← hxe]; abel
  have hxf : c = fpt e1 e2 e3 d ⟪c - d, e1⟫ 0 ⟪c - d, e3⟫ := by
    have := pc_coords hF d c; rw [hf2] at this; exact this
  have hxr : b' = fpt e1 e2 e3 d ⟪b' - d, e1⟫ ⟪b' - d, e2⟫ ⟪b' - d, e3⟫ := pc_coords hF d b'
  have hxg : c' = fpt e1 e2 e3 d ⟪c' - d, e1⟫ ⟪c' - d, e2⟫ ⟪c' - d, e3⟫ := pc_coords hF d c'
  have hxp : a' = fpt e1 e2 e3 d ⟪a' - d, e1⟫ 0 ⟪a' - d, e3⟫ := by
    have := pc_coords hF d a'; rw [hYp] at this; exact this
  have hxw : a = fpt e1 e2 e3 d ⟪a - d, e1⟫ ⟪a - d, e2⟫ ⟪a - d, e3⟫ := pc_coords hF d a
  have n1 : -(1 : ZMod 4) = 3 := by decide
  have n2 : -(2 : ZMod 4) = 2 := by decide
  have n3 : -(3 : ZMod 4) = 1 := by decide
  have hP : ∀ j, quad b c' b' c j = Qg e1 e2 e3 d κ ⟪c - d, e1⟫ ⟪c - d, e3⟫ ⟪b' - d, e1⟫ ⟪b' - d, e2⟫
      ⟪b' - d, e3⟫ ⟪c' - d, e1⟫ ⟪c' - d, e2⟫ ⟪c' - d, e3⟫ (-j) := by
    intro j
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
      simp only [Qg, n1, n2, n3, neg_zero, quad, Matrix.cons_val, ← hxx, ← hxf, ← hxr, ← hxg]
  have hw := rows_T4 hF d (κ := κ) (κv := κv) (L := ⟪c - d, e1⟫) (zf := ⟪c - d, e3⟫)
    (Xr := ⟪b' - d, e1⟫) (Yr := ⟪b' - d, e2⟫) (zr := ⟪b' - d, e3⟫) (Xg := ⟪c' - d, e1⟫)
    (Yg := ⟪c' - d, e2⟫) (zg := ⟪c' - d, e3⟫) (Xq := ⟪a - d, e1⟫) (Yq := ⟪a - d, e2⟫)
    (zq := ⟪a - d, e3⟫) hκ hκv0 hL hr hYg hcr hcg hYq hYlt hcop hchord
  have key := close_np_frame hF d (fpt e1 e2 e3 d ⟪a - d, e1⟫ ⟪a - d, e2⟫ ⟪a - d, e3⟫) hκ hκv0 hL hr
    hYg hcr hcg hXd0 hXdL hDp hw (quad b c' b' c) (fun j => -j) (fun x => neg_neg x) hP hk3 σ u e hu
    (by rw [he]) hcyc hleft hz hbad
  rw [← hxx, ← hxf, ← hxr, ← hxg, ← hxp, ← hxw] at key
  convert key using 1
  ext y
  simp only [mem_insert, mem_singleton]
  tauto

theorem np_K2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegT4 N.F)
    (hF : Fr e1 e2 e3) {κ κv : ℝ} (hκ : κ ≠ 0) (hκv : κv = κ ∨ κv = -κ) (hxe : d - b = κ • e3)
    (hf2 : ⟪c' - b, e2⟫ = 0) (hL : 0 < ⟪c' - b, e1⟫) (hr : 0 < ⟪b' - b, e2⟫)
    {k' : ℕ} [NeZero k'] (hk3 : 3 ≤ k') (σ : ZMod k' → ZMod 4) (u e : ℝ³)
    (hu : u = κv • e3) (he : e = ⟪c' - b, e1⟫ • e1)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3 (quad d c' b' c (σ (i + 1)) - quad d c' b' c (σ i))
      (quad d c' b' c (σ j) - quad d c' b' c (σ i)) u)
    (hleft : ∀ (i : ZMod k') (a_ : ZMod 4), 0 ≤ det3 (quad d c' b' c (σ (i + 1)) - quad d c' b' c (σ i))
      (quad d c' b' c a_ - quad d c' b' c (σ i)) u)
    (hz : IsRobustUnimodal (fun i => ⟪quad d c' b' c (σ i), u⟫))
    (hbad : NoPersistHDN (fun i => quad d c' b' c (σ i)) u e) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨hcr, hcg, hXd0, hXdL, hlam⟩ := pic_K2 N hreg hF hκ hxe hf2 hL hr
  obtain ⟨hYg, hYp, hDp, hYq, hYlt, hcop, hchord⟩ := extra_K2 N hreg hF hκ hxe hf2 hL hr hcg hlam
  have hκv0 : κv ≠ 0 := by rcases hκv with h | h <;> rw [h] <;> simp [hκ]
  have hxx : d = fpt e1 e2 e3 b 0 0 κ := by
    rw [fpt, ← pc_smul_e3 hF, ← hxe]; abel
  have hxf : c' = fpt e1 e2 e3 b ⟪c' - b, e1⟫ 0 ⟪c' - b, e3⟫ := by
    have := pc_coords hF b c'; rw [hf2] at this; exact this
  have hxr : b' = fpt e1 e2 e3 b ⟪b' - b, e1⟫ ⟪b' - b, e2⟫ ⟪b' - b, e3⟫ := pc_coords hF b b'
  have hxg : c = fpt e1 e2 e3 b ⟪c - b, e1⟫ ⟪c - b, e2⟫ ⟪c - b, e3⟫ := pc_coords hF b c
  have hxp : a = fpt e1 e2 e3 b ⟪a - b, e1⟫ 0 ⟪a - b, e3⟫ := by
    have := pc_coords hF b a; rw [hYp] at this; exact this
  have hxw : a' = fpt e1 e2 e3 b ⟪a' - b, e1⟫ ⟪a' - b, e2⟫ ⟪a' - b, e3⟫ := pc_coords hF b a'
  have hP : ∀ j, quad d c' b' c j = Qg e1 e2 e3 b κ ⟪c' - b, e1⟫ ⟪c' - b, e3⟫ ⟪b' - b, e1⟫ ⟪b' - b, e2⟫
      ⟪b' - b, e3⟫ ⟪c - b, e1⟫ ⟪c - b, e2⟫ ⟪c - b, e3⟫ (id j) := by
    intro j
    simp only [Qg, id]
    rw [← hxx, ← hxf, ← hxr, ← hxg]
  have hw := rows_T4 hF b (κ := κ) (κv := κv) (L := ⟪c' - b, e1⟫) (zf := ⟪c' - b, e3⟫)
    (Xr := ⟪b' - b, e1⟫) (Yr := ⟪b' - b, e2⟫) (zr := ⟪b' - b, e3⟫) (Xg := ⟪c - b, e1⟫)
    (Yg := ⟪c - b, e2⟫) (zg := ⟪c - b, e3⟫) (Xq := ⟪a' - b, e1⟫) (Yq := ⟪a' - b, e2⟫)
    (zq := ⟪a' - b, e3⟫) hκ hκv0 hL hr hYg hcr hcg hYq hYlt hcop hchord
  have key := close_np_frame hF b (fpt e1 e2 e3 b ⟪a' - b, e1⟫ ⟪a' - b, e2⟫ ⟪a' - b, e3⟫) hκ hκv0 hL hr
    hYg hcr hcg hXd0 hXdL hDp hw (quad d c' b' c) id (fun _ => rfl) hP hk3 σ u e hu
    (by rw [he]) hcyc hleft hz hbad
  rw [← hxx, ← hxf, ← hxr, ← hxg, ← hxp, ← hxw] at key
  convert key using 1
  ext y
  simp only [mem_insert, mem_singleton]
  tauto

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.np_Kb
#print axioms Minimality.Type08Sp.np_K2
