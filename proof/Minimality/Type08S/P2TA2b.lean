module

public import Minimality.Type08S.P2TA2a

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / A2b: `pers_KbT` (copy of `pers_Kb` with `pic_KbT`/`extra_KbT` and `triCert_cornerF` for `a'`).
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

set_option maxHeartbeats 4000000 in
/-- **T4 `K_b` with a persistent HDN.** -/
theorem pers_KbT {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d)
    (hF : Fr e1 e2 e3) {κ κv : ℝ} (hκ : κ ≠ 0) (hκv : κv = κ ∨ κv = -κ) (hxe : b - d = κ • e3)
    (hf2 : ⟪c - d, e2⟫ = 0) (hL : 0 < ⟪c - d, e1⟫) (hr : 0 < ⟪b' - d, e2⟫)
    {k' : ℕ} [NeZero k'] (hk3 : 3 ≤ k') (σ : ZMod k' → ZMod 4) (u e : ℝ³)
    (hu : u = κv • e3) (he : e = ⟪c - d, e1⟫ • e1)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3 (quad b c' b' c (σ (i + 1)) - quad b c' b' c (σ i))
      (quad b c' b' c (σ j) - quad b c' b' c (σ i)) u)
    (hleft : ∀ (i : ZMod k') (a_ : ZMod 4), 0 ≤ det3 (quad b c' b' c (σ (i + 1)) - quad b c' b' c (σ i))
      (quad b c' b' c a_ - quad b c' b' c (σ i)) u)
    (hz : IsRobustUnimodal (fun i => ⟪quad b c' b' c (σ i), u⟫))
    (hp : ¬ NoPersistHDN (fun i => quad b c' b' c (σ i)) u e)
    (hLE : LemE3 d b c b' c') (hSC2 : SC2Kb a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨hcr, hcg, hXp, hYp', hDp', hlam⟩ := pic_KbT N hT hF hκ hxe hf2 hL hr
  obtain ⟨hYg, hYp, -, hYq, hYlt, hcop, hchord⟩ := extra_KbT N hT hF hκ hxe hf2 hL hr hcg hlam
  have hκv0 : κv ≠ 0 := by rcases hκv with h | h <;> rw [h] <;> simp [hκ]
  have hxx : b = d + pc e1 e2 e3 0 0 κ := by
    rw [← pc_smul_e3 hF, ← hxe]; abel
  have hxf : c = d + pc e1 e2 e3 ⟪c - d, e1⟫ 0 ⟪c - d, e3⟫ := by
    have := pc_coords hF d c; rw [hf2] at this; exact this
  have hxr : b' = d + pc e1 e2 e3 ⟪b' - d, e1⟫ ⟪b' - d, e2⟫ ⟪b' - d, e3⟫ := pc_coords hF d b'
  have hxg : c' = d + pc e1 e2 e3 ⟪c' - d, e1⟫ ⟪c' - d, e2⟫ ⟪c' - d, e3⟫ := pc_coords hF d c'
  have hxp : a' = d + pc e1 e2 e3 ⟪a' - d, e1⟫ 0 ⟪a' - d, e3⟫ := by
    have := pc_coords hF d a'; rw [hYp] at this; exact this
  have hxw : a = d + pc e1 e2 e3 ⟪a - d, e1⟫ ⟪a - d, e2⟫ ⟪a - d, e3⟫ := pc_coords hF d a
  have n1 : -(1 : ZMod 4) = 3 := by decide
  have n2 : -(2 : ZMod 4) = 2 := by decide
  have n3 : -(3 : ZMod 4) = 1 := by decide
  have hP : ∀ j, quad b c' b' c j = Qg e1 e2 e3 d κ ⟪c - d, e1⟫ ⟪c - d, e3⟫ ⟪b' - d, e1⟫ ⟪b' - d, e2⟫
      ⟪b' - d, e3⟫ ⟪c' - d, e1⟫ ⟪c' - d, e2⟫ ⟪c' - d, e3⟫ (-j) := by
    intro j
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
      simp only [Qg, fpt, n1, n2, n3, neg_zero, quad, Matrix.cons_val, ← hxx, ← hxf, ← hxr, ← hxg]
  set E : Finset ℝ³ := {d + pc e1 e2 e3 ⟪a' - d, e1⟫ 0 ⟪a' - d, e3⟫,
    d + pc e1 e2 e3 ⟪a - d, e1⟫ ⟪a - d, e2⟫ ⟪a - d, e3⟫} with hEdef
  set V5 := rim5 e1 e2 e3 d ⟪c - d, e1⟫ 0 κ ⟪c - d, e3⟫ ⟪b' - d, e1⟫ ⟪b' - d, e2⟫ ⟪b' - d, e3⟫
    ⟪c' - d, e1⟫ ⟪c' - d, e2⟫ ⟪c' - d, e3⟫ E with hV5
  have m1 : d + pc e1 e2 e3 0 0 0 ∈ V5 := by simp [hV5, rim5]
  have m0 : d + pc e1 e2 e3 0 0 κ ∈ V5 := by simp [hV5, rim5]
  have m2 : d + pc e1 e2 e3 ⟪c - d, e1⟫ 0 ⟪c - d, e3⟫ ∈ V5 := by simp [hV5, rim5]
  have m4 : d + pc e1 e2 e3 ⟪c' - d, e1⟫ ⟪c' - d, e2⟫ ⟪c' - d, e3⟫ ∈ V5 := by simp [hV5, rim5]
  have hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert V5 (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (κ * s) (-κ) 0) y := by
    filter_upwards [triCert_midG' hF d V5 hL hYg hYq hYlt hcop hchord m4 m0 m2,
      triCert_cornerF (σ := κ) hF d V5 hL hYg m1 m2 m4 (zd := ⟪a' - d, e3⟫) (by nlinarith [hDp'])] with s hs hs' y hy
    rw [hEdef, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · rw [hXp]; exact hs'
    · exact hs
  have hLem : ⟪b' - d, e2⟫ = ⟪c' - d, e2⟫ → LemEF 0 ⟪c - d, e1⟫ κ ⟪c - d, e3⟫ ⟪b' - d, e1⟫
      ⟪b' - d, e3⟫ ⟪c' - d, e1⟫ ⟪c' - d, e3⟫ := by
    intro hY
    refine lemEF_of_3 hF d hY hr ?_
    rw [← hxx, ← hxf, ← hxr, ← hxg]; exact hLE
  rcases pers_frame hF d E hκ hκv0 hL hr hYg hcr hcg hE hLem (quad b c' b' c) (fun j => -j)
      (fun x => neg_neg x) hP hk3 σ u e hu he hcyc hleft hz hp with hR | ⟨hrob, hcase⟩
  · simp only [rim5, hEdef] at hR
    rw [show d + pc e1 e2 e3 0 0 0 = d by simp [pc], ← hxx, ← hxf, ← hxr, ← hxg, ← hxp, ← hxw] at hR
    have hset : insert d ({a, a', b, b', c, c'} : Finset ℝ³) = ({d, b, c, b', c'} : Finset ℝ³) ∪ {a', a} := by
      ext y; simp only [mem_insert, mem_singleton, mem_union]
      constructor
      · rintro (h | h | h | h | h | h | h) <;> subst h <;> simp only [true_or, or_true]
      · rintro ((h | h | h | h | h) | (h | h)) <;> subst h <;> simp only [true_or, or_true]
    rw [hset]; exact hR
  · exact hSC2 e1 e2 e3 κ hF hκ hxe hf2 hL hr hrob hcase

end Type08Sp
end Minimality
