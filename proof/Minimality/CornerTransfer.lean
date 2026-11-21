module

public import Mathlib
public import Minimality.CornerLift
public import Minimality.HiddenCapFree
public import Minimality.Type08S.P2RR0

/-!
# Lift transfer: a leaf at the lifted apex is a leaf at `x₆`

Source: `notes/LIFT-TRANSFER-DESIGN.md`.  Namespace `Minimality.CornerEQ`.

* `TiltWeak`, the closed version of `TiltSign`, with `TiltSign.add_weak`, `TiltWeak.add`, `TiltWeak.smul`.
* `lexCell_replace` (apex replacement): a lex cell of `insert p O` whose rim lies in `O` and avoids `p` is a
  lex cell of `insert q O` whenever `(1 + N) q = p + ∑ ν_a z_a`, `z_a ∈ O`, `ν ≥ 0`.  No cone and no
  obtuseness: each tilt row of `q` is a positive combination of the row of `p` (`TiltSign`) and rows of points
  of `O` (`TiltWeak`).  `lexCell_replace_ne` records that then the rim also avoids `q`.
* `CornerLeaf O z p`: a lex cell of `insert p O` with rim in `O` avoiding `p`, or a free view of `O` in the
  open cone of the edges `z a - p`.
* `cornerLeaf_lift`: `CornerLeaf O z x'` gives `CornerLeaf O z x₆` (`x' = liftPoint x₆ (z - x₆) ν`, `ν ≥ 0`).
* `isRupert_of_cornerLeaf`: `CornerLeaf O z x₆` and independent edges give `IsRupert (insert x₆ O)`.
* `cornerLeaf_of_freeAt`: the split-leaf adapter.
-/

set_option autoImplicit false

namespace Minimality.CornerEQ

open Finset Matrix
open scoped RealInnerProductSpace

@[expose] public section

/-- Weak lex sign: the closed version of `TiltSign`. -/
def _root_.Minimality.TiltWeak (a b u₀ v : ℝ³) : Prop := 0 < det3 a b u₀ ∨ (det3 a b u₀ = 0 ∧ 0 ≤ det3 a b v)

theorem _root_.Minimality.TiltSign.weak {a b u₀ v : ℝ³} (h : TiltSign a b u₀ v) : TiltWeak a b u₀ v := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2.le⟩

theorem _root_.Minimality.TiltWeak.zero (a u₀ v : ℝ³) : TiltWeak a 0 u₀ v := by
  have h : ∀ w : ℝ³, det3 a 0 w = 0 := fun w => by simpa using det3_smul_mid a 0 w 0
  exact Or.inr ⟨h u₀, (h v).ge⟩

theorem _root_.Minimality.TiltWeak.self (a u₀ v : ℝ³) : TiltWeak a a u₀ v :=
  Or.inr ⟨det3_self_left a u₀, (det3_self_left a v).ge⟩

theorem _root_.Minimality.TiltSign.add_weak {a b b' u₀ v : ℝ³} (h : TiltSign a b u₀ v) (h' : TiltWeak a b' u₀ v) :
    TiltSign a (b + b') u₀ v := by
  unfold TiltSign TiltWeak at *
  rw [det3_add_mid, det3_add_mid]
  rcases h with h | ⟨h1, h2⟩ <;> rcases h' with h' | ⟨h1', h2'⟩
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by linarith, by linarith⟩

theorem _root_.Minimality.TiltWeak.add {a b b' u₀ v : ℝ³} (h : TiltWeak a b u₀ v) (h' : TiltWeak a b' u₀ v) :
    TiltWeak a (b + b') u₀ v := by
  unfold TiltWeak at *
  rw [det3_add_mid, det3_add_mid]
  rcases h with h | ⟨h1, h2⟩ <;> rcases h' with h' | ⟨h1', h2'⟩
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by linarith, by linarith⟩

theorem _root_.Minimality.TiltWeak.smul {a b u₀ v : ℝ³} {t : ℝ} (ht : 0 ≤ t) (h : TiltWeak a b u₀ v) :
    TiltWeak a (t • b) u₀ v := by
  unfold TiltWeak at *
  rw [det3_smul_mid, det3_smul_mid]
  rcases ht.eq_or_lt with rfl | ht
  · exact Or.inr ⟨by simp, by simp⟩
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl (mul_pos ht h)
  · exact Or.inr ⟨by rw [h1, mul_zero], mul_nonneg ht.le h2⟩

theorem _root_.Minimality.TiltSign.smul {a b u₀ v : ℝ³} {t : ℝ} (ht : 0 < t) (h : TiltSign a b u₀ v) :
    TiltSign a (t • b) u₀ v := by
  unfold TiltSign at *
  rw [det3_smul_mid, det3_smul_mid]
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl (mul_pos ht h)
  · exact Or.inr ⟨by rw [h1, mul_zero], mul_pos ht h2⟩

/-- The tilt row of the new apex `q` at every rim edge. -/
theorem tiltSign_replace {O : Finset ℝ³} {p q u₀ v : ℝ³} {k : ℕ} [NeZero k] {y : ZMod k → ℝ³}
    (hyp : ∀ i, y i ≠ p) (z : Fin 3 → ℝ³) (hz : ∀ a, z a ∈ O)
    (ν : Fin 3 → ℝ) (hν : 0 ≤ ν) (hq : (1 + ∑ a, ν a) • q = p + ∑ a, ν a • z a)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → TiltSign (y (i + 1) - y i) (y j - y i) u₀ v)
    (hrest : ∀ w ∈ insert p O, (∀ j, w ≠ y j) → ∀ i, TiltSign (y (i + 1) - y i) (w - y i) u₀ v)
    (i : ZMod k) : TiltSign (y (i + 1) - y i) (q - y i) u₀ v := by
  have hN : 0 ≤ ∑ a, ν a := Finset.sum_nonneg fun a _ => hν a
  have hc : 0 < 1 + ∑ a, ν a := by linarith
  have hqy : q - y i = (1 + ∑ a, ν a)⁻¹ • ((p - y i) + ∑ a, ν a • (z a - y i)) := by
    have : (1 + ∑ a, ν a) • (q - y i) = (p - y i) + ∑ a, ν a • (z a - y i) := by
      rw [smul_sub, hq]
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, add_smul, one_smul]
      abel
    rw [← this, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  have hp : TiltSign (y (i + 1) - y i) (p - y i) u₀ v :=
    hrest p (Finset.mem_insert_self _ _) (fun j => (hyp j).symm) i
  have hw : ∀ a, TiltWeak (y (i + 1) - y i) (ν a • (z a - y i)) u₀ v := fun a => by
    refine TiltWeak.smul (hν a) ?_
    by_cases hj : ∃ j, z a = y j
    · obtain ⟨j, hj⟩ := hj
      rw [hj]
      by_cases h1 : j = i
      · rw [h1, sub_self]; exact TiltWeak.zero _ _ _
      by_cases h2 : j = i + 1
      · rw [h2]; exact TiltWeak.self _ _ _
      exact (hcyc i j h1 h2).weak
    · push Not at hj
      exact (hrest (z a) (Finset.mem_insert_of_mem (hz a)) hj i).weak.elim Or.inl fun h => Or.inr h
  have hs := (hp.add_weak (((hw 0).add (hw 1)).add (hw 2)))
  rw [hqy]
  refine TiltSign.smul (inv_pos.2 hc) ?_
  simpa [Fin.sum_univ_three, add_assoc] using hs

/-- **Apex replacement.**  A lex cell of `insert p O` with rim in `O`, avoiding `p`, is a lex cell of
`insert q O` when `(1 + N) q = p + ∑ ν_a z_a` with `z_a ∈ O`, `ν ≥ 0`.  No cone, no obtuseness. -/
theorem lexCell_replace {O : Finset ℝ³} {p q u₀ v : ℝ³} {k : ℕ} [NeZero k] {y : ZMod k → ℝ³}
    (hyp : ∀ i, y i ≠ p) (z : Fin 3 → ℝ³) (hz : ∀ a, z a ∈ O)
    (ν : Fin 3 → ℝ) (hν : 0 ≤ ν) (hq : (1 + ∑ a, ν a) • q = p + ∑ a, ν a • z a)
    (hyO : ∀ i, y i ∈ O) (h : LexCell (insert p O) u₀ v y) : LexCell (insert q O) u₀ v y := by
  obtain ⟨hk, -, hcyc, hrest, hU⟩ := h
  refine ⟨hk, fun i => Finset.mem_insert_of_mem (hyO i), hcyc, fun w hw hwj i => ?_, hU⟩
  rcases Finset.mem_insert.1 hw with rfl | hwO
  · exact tiltSign_replace hyp z hz ν hν hq hcyc hrest i
  · exact hrest w (Finset.mem_insert_of_mem hwO) hwj i

/-- The rim of a replaced cell avoids the new apex too. -/
theorem lexCell_replace_ne {O : Finset ℝ³} {p q u₀ v : ℝ³} {k : ℕ} [NeZero k] {y : ZMod k → ℝ³}
    (hyp : ∀ i, y i ≠ p) (z : Fin 3 → ℝ³) (hz : ∀ a, z a ∈ O)
    (ν : Fin 3 → ℝ) (hν : 0 ≤ ν) (hq : (1 + ∑ a, ν a) • q = p + ∑ a, ν a • z a)
    (h : LexCell (insert p O) u₀ v y) (i : ZMod k) : y i ≠ q := by
  obtain ⟨-, -, hcyc, hrest, -⟩ := h
  intro hi
  have := tiltSign_replace hyp z hz ν hν hq hcyc hrest i
  rw [← hi, sub_self] at this
  have h0 : ∀ w : ℝ³, det3 (y (i + 1) - y i) 0 w = 0 := fun w => by
    simpa using det3_smul_mid (y (i + 1) - y i) 0 w 0
  rcases this with h1 | ⟨-, h2⟩
  · rw [h0] at h1; exact lt_irrefl _ h1
  · rw [h0] at h2; exact lt_irrefl _ h2

/-- A corner leaf of `insert p O` (frame points `z`): a lex cell with rim in `O` avoiding `p`, or a free
view of `O` in the open cone of the edges `z a - p`. -/
def CornerLeaf (O : Finset ℝ³) (z : Fin 3 → ℝ³) (p : ℝ³) : Prop :=
  (∃ (u₀ v : ℝ³) (k : ℕ) (_ : NeZero k) (y : ZMod k → ℝ³),
      u₀ ≠ 0 ∧ (∀ i, y i ∈ O) ∧ (∀ i, y i ≠ p) ∧ LexCell (insert p O) u₀ v y) ∨
  (∃ ρ : Fin 3 → ℝ, (∀ a, 0 < ρ a) ∧ Split.FreeAt O (∑ a, ρ a • (z a - p)))

/-- **Lift transfer.**  Needs only `ν ≥ 0` and `z a ∈ O`. -/
theorem cornerLeaf_lift (O : Finset ℝ³) (z : Fin 3 → ℝ³) (hz : ∀ a, z a ∈ O) (x6 : ℝ³)
    (ν : Fin 3 → ℝ) (hν : 0 ≤ ν) (h : CornerLeaf O z (liftPoint x6 (fun a => z a - x6) ν)) :
    CornerLeaf O z x6 := by
  rcases h with ⟨u₀, v, k, hk, y, hu, hyO, hyp, hlex⟩ | ⟨ρ', hρ', hfree⟩
  · left
    have := hk
    have hq : (1 + ∑ a, ν a) • x6 = liftPoint x6 (fun a => z a - x6) ν + ∑ a, ν a • z a := by
      simpa using lift_point x6 (fun a => z a - x6) ν
    exact ⟨u₀, v, k, hk, y, hu, hyO, lexCell_replace_ne hyp z hz ν hν hq hlex,
      lexCell_replace hyp z hz ν hν hq hyO hlex⟩
  · right
    refine ⟨liftM ν *ᵥ ρ', liftM_mulVec_pos ν ρ' hν hρ', ?_⟩
    have := lift_view x6 (fun a => z a - x6) ν ρ'
    simp only [add_sub_cancel] at this
    rw [← this]
    exact hfree

/-- Independent edges have a nonzero coordinate determinant. -/
theorem det3_ne_zero_of_linearIndependent (z : Fin 3 → ℝ³) (x6 : ℝ³)
    (hli : LinearIndependent ℝ (fun a => z a - x6)) :
    Split.det3 (z 0 - x6) (z 1 - x6) (z 2 - x6) ≠ 0 := by
  have h1 := hli.map' (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap
    (LinearMap.ker_eq_bot.2 (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).injective)
  have h2 := (Matrix.linearIndependent_row_iff_isUnit (A := Matrix.of fun a j => (z a - x6) j)).1 h1
  have h3 := (Matrix.isUnit_iff_isUnit_det _).1 h2
  have h4 := h3.ne_zero
  rw [Matrix.det_fin_three] at h4
  intro h0
  apply h4
  simp only [Split.det3] at h0
  simp only [Matrix.of_apply]
  linarith

theorem isRupert_of_cornerLeaf (O : Finset ℝ³) (z : Fin 3 → ℝ³) (hz : ∀ a, z a ∈ O) (x6 : ℝ³)
    (hli : LinearIndependent ℝ (fun a => z a - x6)) (h : CornerLeaf O z x6) :
    IsRupert (insert x6 O) := by
  rcases h with ⟨u₀, v, k, hk, y, hu, -, -, hlex⟩ | ⟨ρ, hρ, hfree⟩
  · have := hk
    exact isRupert_of_lexCell _ u₀ v hu y hlex
  · have hw : (∑ a, ρ a • (z a - x6)) ≠ 0 := fun h0 => by
      have := Fintype.linearIndependent_iff.1 hli ρ h0 0
      exact (hρ 0).ne' this
    refine Split.FreeAt.isRupert hw ?_
    have hD := det3_ne_zero_of_linearIndependent z x6 hli
    simp only [Fin.sum_univ_three] at hfree ⊢
    exact Split.freeAt_insert_of_cone O x6 (z 0) (z 1) (z 2) (hz 0) (hz 1) (hz 2) hD (ρ 0) (ρ 1) (ρ 2)
      (Or.inl ⟨hρ 0, hρ 1, hρ 2⟩) hfree

/-- Split-leaf adapter: a free view of `O` in the open cone is a corner leaf. -/
theorem cornerLeaf_of_freeAt (O : Finset ℝ³) (z : Fin 3 → ℝ³) (p : ℝ³) (ρ : Fin 3 → ℝ)
    (hρ : ∀ a, 0 < ρ a) (h : Split.FreeAt O (∑ a, ρ a • (z a - p))) : CornerLeaf O z p :=
  Or.inr ⟨ρ, hρ, h⟩

end

end Minimality.CornerEQ
