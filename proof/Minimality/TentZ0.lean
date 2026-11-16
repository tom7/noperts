module

public import Mathlib
public import Minimality.TentApex
public import Minimality.CornerTransferEQ

/-!
# Tent apex, Lemma Z0 and the tent closing

Source: `notes/ROOF-PROOF-OPUS2.md`, sections 2.1 (Lemma Z0) and 2.5 (step L4, closing).
Namespace `Minimality.TentApex`.  Shape-only: no Gram matrix, no obtuseness.

Setting: `F : Frame` (frame coordinates of the base `O`), a frame matrix `E` with `0 < det E` (columns
`e_a = x_a - x*`), and the tent apex `x* = p`.  The six base points are `p + E (F.pt j)`, `j < 6`
(`Frame.base`); the frame points are `z_a = p + e_a` (`Frame.zf`).

* `Frame.cornerLeaf_Q`, `cornerLeaf_P`, `cornerLeaf_R` (**Z0 at `x*`**): a view `q > 0` in the open cell
  `{Q}`, `{P}` or `{R}` gives `CornerLeaf O z x*`.  The rim is perturbed inside the open cell to have
  distinct depths; the quadrilateral `Q` is planar, so its diagonals overlap and distinct depths are
  unimodal.
* `Frame.cornerLeaf_tent`: `x*` lifts to every apex `x_6 = lam0 x* + sum lam_a z_a`, `lam0 > 0`, `lam >= 0`,
  `lam0 + sum lam = 1` (the open tent `conv(T, x*)`), with `nu_a = lam_a / lam0`.
* `Frame.isRupert_tent_Q/P/R` and `Frame.isRupert_tent` (**Lemma Z0**): `IsRupert (insert x_6 O)`.
-/

set_option autoImplicit false

namespace Minimality.TentApex

open Matrix Finset
open Minimality.RimCell Minimality.CornerEQ
open scoped RealInnerProductSpace

@[expose] public section

/-- The frame points `z_a = p + e_a` (vertices `3, 4, 5`). -/
noncomputable def zf (E : Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ³) (a : Fin 3) : ℝ³ :=
  p + emb E (Pi.single a 1)

namespace Frame

variable (F : Frame) (E : Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ³)

/-- The six base points `O` (all vertices but the apex `6`), in space. -/
noncomputable def base : Finset ℝ³ :=
  (Finset.univ.erase (6 : Fin 7)).image fun j => p + emb E (F.pt j)


theorem emb_zero' : emb E 0 = 0 := by ext i; simp [emb_apply]

theorem pt_six : F.pt 6 = 0 := by ext i; fin_cases i <;> simp [pt]

theorem pt_ne_zero {j : Fin 7} (hj : j ≠ 6) : F.pt j ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  fin_cases j <;> simp [pt] at h0 h1 h2 hj <;> linarith [F.ha0, F.hg0, F.hb1, F.hg1, F.ha2, F.hb2]

theorem insert_base :
    insert p (F.base E p) = F.Y.image fun w => p + emb E w := by
  classical
  have h1 : F.Y.image (fun w => p + emb E w) = Finset.univ.image fun j => p + emb E (F.pt j) := by
    simp only [Frame.Y, Finset.image_image]; rfl
  rw [h1, ← Finset.insert_erase (Finset.mem_univ (6 : Fin 7)), Finset.image_insert, pt_six,
    emb_zero', add_zero]
  rfl

theorem zf_mem (a : Fin 3) : zf E p a ∈ F.base E p := by
  simp only [base, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true, zf]
  fin_cases a
  · exact ⟨3, by decide, by congr 2; ext i; fin_cases i <;> simp [pt]⟩
  · exact ⟨4, by decide, by congr 2; ext i; fin_cases i <;> simp [pt]⟩
  · exact ⟨5, by decide, by congr 2; ext i; fin_cases i <;> simp [pt]⟩


theorem cornerLeaf_of_cell {k : ℕ} [NeZero k] (hk : 3 ≤ k) (hE : 0 < E.det) (r : ZMod k → Fin 7)
    (hr : Function.Injective fun i => F.pt (r i)) (hr6 : ∀ i, r i ≠ 6) {q : Fin 3 → ℝ}
    (hq : q ∈ cellSet F.Y fun i => F.pt (r i))
    (hz : IsCyclicUnimodal fun i => ((Eᵀ * E) *ᵥ q) ⬝ᵥ F.pt (r i)) :
    CornerLeaf (F.base E p) (zf E p) p := by
  have hE0 : E.det ≠ 0 := hE.ne'
  have hq0 : q ≠ 0 := ne_zero_of_edge hk (fun i => F.pt (r i)) q
    (edge_of_cell hr (fun i => F.pt_mem_Y (r i)) hq)
  have hlex := lexCell_of_frameCell hk E hE p (fun i => F.pt (r i)) hr F.Y
    (fun i => F.pt_mem_Y (r i)) hq hz
  refine Or.inl ⟨emb E q, 0, k, inferInstance, fun j => p + emb E (F.pt (r j)), ?_, ?_, ?_, ?_⟩
  · intro h
    exact hq0 (emb_injective hE0 (h.trans (emb_zero' E).symm))
  · intro j
    exact Finset.mem_image.2 ⟨r j, by simp [hr6 j], rfl⟩
  · intro j h
    have h' : emb E (F.pt (r j)) = 0 := by simpa using h
    exact F.pt_ne_zero (hr6 j) (emb_injective hE0 (h'.trans (emb_zero' E).symm))
  · rw [insert_base]; exact hlex

/-- A view in an open cell can be moved inside it to have distinct depths on the (injective) rim. -/
theorem exists_injective_depth {k : ℕ} [NeZero k] (hE : 0 < E.det) (y : ZMod k → Fin 3 → ℝ)
    (hy : Function.Injective y) (Y : Finset (Fin 3 → ℝ)) {q : Fin 3 → ℝ} (hq : q ∈ cellSet Y y) :
    ∃ q' ∈ cellSet Y y, Function.Injective fun i => ((Eᵀ * E) *ᵥ q') ⬝ᵥ y i := by
  have hΓ : (Eᵀ * E).det ≠ 0 := by
    rw [det_mul, det_transpose]; exact (mul_pos hE hE).ne'
  obtain ⟨c, hc, hcS⟩ := exists_mem_forall_ne_zero
    (fun p : ZMod k × ZMod k => depthDiff (Eᵀ * E) (y p.1) (y p.2))
    (Finset.univ.filter fun p => p.1 ≠ p.2)
    (fun p hp => depthDiff_ne_zero hΓ fun h => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact hp (hy h)) _ (isOpen_cellSet Y y) ⟨q, hq⟩
  refine ⟨c, hc, fun i j h => ?_⟩
  by_contra hij
  apply hcS (i, j) (by simp [hij])
  simp only [depthDiff_apply]
  simp only at h
  linarith

/-- Distinct depths on a quadrilateral whose diagonals cross (planar, convex) are unimodal. -/
theorem quad_unimodal {z : ZMod 4 → ℝ} (hz : Function.Injective z) {s t : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (h : s * z 0 + (1 - s) * z 2 = t * z 1 + (1 - t) * z 3) : IsCyclicUnimodal z := by
  have n01 : z 0 ≠ z 1 := fun e => absurd (hz e) (by decide)
  have n03 : z 0 ≠ z 3 := fun e => absurd (hz e) (by decide)
  have n21 : z 2 ≠ z 1 := fun e => absurd (hz e) (by decide)
  have n23 : z 2 ≠ z 3 := fun e => absurd (hz e) (by decide)
  refine Minimality.RimCell.isCyclicUnimodal_four z hz ?_ ?_
  · by_contra hn
    push Not at hn
    obtain ⟨a, b, c, d⟩ := hn
    have a' := lt_of_le_of_ne a (Ne.symm n01)
    have b' := lt_of_le_of_ne b (Ne.symm n03)
    have c' := lt_of_le_of_ne c (Ne.symm n21)
    have d' := lt_of_le_of_ne d (Ne.symm n23)
    nlinarith [mul_pos (mul_pos hs0 ht0) (sub_pos.2 a'), mul_pos (mul_pos hs0 (sub_pos.2 ht1))
      (sub_pos.2 b'), mul_pos (mul_pos (sub_pos.2 hs1) ht0) (sub_pos.2 c'),
      mul_pos (mul_pos (sub_pos.2 hs1) (sub_pos.2 ht1)) (sub_pos.2 d')]
  · by_contra hn
    push Not at hn
    obtain ⟨a, b, c, d⟩ := hn
    have a' := lt_of_le_of_ne a n01
    have b' := lt_of_le_of_ne b n03
    have c' := lt_of_le_of_ne c n21
    have d' := lt_of_le_of_ne d n23
    nlinarith [mul_pos (mul_pos hs0 ht0) (sub_pos.2 a'), mul_pos (mul_pos hs0 (sub_pos.2 ht1))
      (sub_pos.2 b'), mul_pos (mul_pos (sub_pos.2 hs1) ht0) (sub_pos.2 c'),
      mul_pos (mul_pos (sub_pos.2 hs1) (sub_pos.2 ht1)) (sub_pos.2 d')]

theorem rimQ_inj : Function.Injective fun i => F.pt (rimQ i) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | (
    exfalso
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [rimQ, pt] at h0 h1 h2
    all_goals linarith [F.ha0, F.hg0, F.hb1, F.hg1, F.ha2, F.hb2])

theorem rimP_inj : Function.Injective fun i => F.pt (rimP i) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | (
    exfalso
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [rimP, pt] at h0 h1 h2; linarith [F.ha0, F.hg0, F.hb1, F.hg1, F.ha2, F.hb2])

theorem rimR_inj : Function.Injective fun i => F.pt (rimR i) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | (
    exfalso
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [rimR, pt] at h0 h1 h2; linarith [F.ha0, F.hg0, F.hb1, F.hg1, F.ha2, F.hb2])

/-- The diagonals of the planar quadrilateral `Q` (rim `3 2 1 0`) cross: `s e_3 + (1-s) y_1 =
t y_2 + (1-t) y_0` with `0 < s, t < 1`. -/
theorem quad_cross : ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
    s • F.pt (rimQ 0) + (1 - s) • F.pt (rimQ 2) = t • F.pt (rimQ 1) + (1 - t) • F.pt (rimQ 3) := by
  have hp := F.planar
  have hD : 0 < F.g0 * F.b1 + F.b2 * F.g1 := by
    have := F.hg0; have := F.hb1; have := F.hb2; have := F.hg1; positivity
  have hp' : (1 - F.a2) * F.b1 * F.g0 + (1 - F.a0) * F.g1 * F.b2 = F.b2 * F.g0 := by
    have := F.hb2; have := F.hg0
    field_simp at hp; linarith
  have hb1 := F.hb1; have hb2 := F.hb2; have hg0 := F.hg0; have hg1 := F.hg1
  have ha0 := F.ha0; have ha2 := F.ha2
  refine ⟨F.a2 * (F.g0 * F.b1) / (F.g0 * F.b1 + F.b2 * F.g1) +
      F.a0 * (F.b2 * F.g1) / (F.g0 * F.b1 + F.b2 * F.g1), F.g0 * F.b1 / (F.g0 * F.b1 + F.b2 * F.g1),
    ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · rw [← sub_pos]
    have : 1 - (F.a2 * (F.g0 * F.b1) / (F.g0 * F.b1 + F.b2 * F.g1) +
      F.a0 * (F.b2 * F.g1) / (F.g0 * F.b1 + F.b2 * F.g1)) =
      F.b2 * F.g0 / (F.g0 * F.b1 + F.b2 * F.g1) := by
      field_simp; linarith
    rw [this]; positivity
  · positivity
  · rw [div_lt_one hD]; nlinarith [mul_pos hb2 hg1]
  · ext i
    fin_cases i <;> simp [rimQ, pt] <;> field_simp <;>
      first | linarith | linear_combination F.g1 * hp'

/-! ### Lemma Z0 at `x*` -/

/-- **Z0, cell `{Q}`.** -/
theorem cornerLeaf_Q (hE : 0 < E.det) {q : Fin 3 → ℝ} (hq : ∀ i, 0 < q i) (hQ : 0 < F.nQ ⬝ᵥ q)
    (hP : F.nP ⬝ᵥ q < 0) (hR : F.nR ⬝ᵥ q < 0) :
    CornerLeaf (F.base E p) (zf E p) p := by
  obtain ⟨s, t, hs0, hs1, ht0, ht1, hst⟩ := F.quad_cross
  obtain ⟨q', hq', hinj⟩ := exists_injective_depth E hE _ F.rimQ_inj F.Y (F.cell_Q hq hQ hP hR)
  refine F.cornerLeaf_of_cell E p (by norm_num) hE rimQ F.rimQ_inj (by decide) hq' ?_
  refine quad_unimodal hinj hs0 hs1 ht0 ht1 ?_
  have := congrArg (fun v => ((Eᵀ * E) *ᵥ q') ⬝ᵥ v) hst
  simpa [dotProduct_add, dotProduct_smul] using this

/-- **Z0, cell `{P}`** (triangle rim `1 2 4`). -/
theorem cornerLeaf_P (hE : 0 < E.det) {q : Fin 3 → ℝ} (hq : ∀ i, 0 < q i) (hP : 0 < F.nP ⬝ᵥ q)
    (hQ : F.nQ ⬝ᵥ q < 0) : CornerLeaf (F.base E p) (zf E p) p := by
  obtain ⟨q', hq', hinj⟩ := exists_injective_depth E hE _ F.rimP_inj F.Y (F.cell_P hq hP hQ)
  exact F.cornerLeaf_of_cell E p (by norm_num) hE rimP F.rimP_inj (by decide) hq'
    (Minimality.isCyclicUnimodal_three hinj)

/-- **Z0, cell `{R}`** (triangle rim `0 1 5`). -/
theorem cornerLeaf_R (hE : 0 < E.det) {q : Fin 3 → ℝ} (hq : ∀ i, 0 < q i) (hR : 0 < F.nR ⬝ᵥ q)
    (hQ : F.nQ ⬝ᵥ q < 0) : CornerLeaf (F.base E p) (zf E p) p := by
  obtain ⟨q', hq', hinj⟩ := exists_injective_depth E hE _ F.rimR_inj F.Y (F.cell_R hq hR hQ)
  exact F.cornerLeaf_of_cell E p (by norm_num) hE rimR F.rimR_inj (by decide) hq'
    (Minimality.isCyclicUnimodal_three hinj)

end Frame

/-! ### The tent closing -/

/-- **Lift to the tent.**  For `x_6 = lam0 x* + sum lam_a z_a` (`lam0 > 0`, `lam >= 0`, weights summing to
`1`: the open tent `conv(T, x*)`), `x* = liftPoint x_6 (z - x_6) nu` with `nu_a = lam_a / lam0 >= 0`, so a
corner leaf at `x*` is one at `x_6`. -/
theorem cornerLeaf_tent (O : Finset ℝ³) (z : Fin 3 → ℝ³) (hz : ∀ a, z a ∈ O) {p x6 : ℝ³} {lam0 : ℝ}
    {lam : Fin 3 → ℝ} (h0 : 0 < lam0) (hl : 0 ≤ lam) (hsum : lam0 + ∑ a, lam a = 1)
    (hx6 : x6 = lam0 • p + ∑ a, lam a • z a) (h : CornerLeaf O z p) : CornerLeaf O z x6 := by
  refine cornerLeaf_lift O z hz x6 (fun a => lam a / lam0) (fun a => div_nonneg (hl a) h0.le) ?_
  have : liftPoint x6 (fun a => z a - x6) (fun a => lam a / lam0) = p := by
    ext i
    have hx := congrArg (fun v => v i) hx6
    simp only [Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hx hsum
    simp only [liftPoint, Fin.sum_univ_three, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]
    field_simp
    linear_combination hx + x6 i * hsum
  rw [this]; exact h

theorem zf_linearIndependent {E : Matrix (Fin 3) (Fin 3) ℝ} (hE : E.det ≠ 0) {p x6 : ℝ³} {lam0 : ℝ}
    {lam : Fin 3 → ℝ} (h0 : 0 < lam0) (hsum : lam0 + ∑ a, lam a = 1)
    (hx6 : x6 = lam0 • p + ∑ a, lam a • zf E p a) :
    LinearIndependent ℝ fun a => zf E p a - x6 := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hv : emb E (fun b => c b - (∑ a, c a) * lam b) = 0 := by
    ext i
    have hc' := congrArg (fun v => v i) hc
    have hx := congrArg (fun v => v i) hx6
    simp only [Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply,
      PiLp.zero_apply, zf, emb_apply, Matrix.mulVec, dotProduct, Pi.single_apply] at hc' hx hsum ⊢
    simp at hc' hx ⊢
    linear_combination hc' + (c 0 + c 1 + c 2) * hx + (c 0 + c 1 + c 2) * p.ofLp i * hsum
  have h1 := emb_injective hE (hv.trans (Frame.emb_zero' E).symm)
  have hb : ∀ b, c b = (∑ a, c a) * lam b := fun b => sub_eq_zero.1 (congrFun h1 b)
  have hS : (∑ a, c a) * lam0 = 0 := by
    have e : ∑ a, c a = (∑ a, c a) * ∑ a, lam a := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => hb b
    have : ∑ a, lam a = 1 - lam0 := by linarith
    rw [this] at e; linarith
  have hS0 : ∑ a, c a = 0 := by
    rcases mul_eq_zero.1 hS with h | h
    · exact h
    · exact absurd h h0.ne'
  intro i
  rw [hb i, hS0, zero_mul]

namespace Frame

variable (F : Frame) (E : Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ³)

section
variable {E p}

/-- **Lemma Z0, closing step.**  `lam0 x* + sum lam z` with `lam0 > 0`, `lam >= 0`. -/
theorem isRupert_of_cornerLeaf_tent (hE : 0 < E.det) {x6 : ℝ³} {lam0 : ℝ} {lam : Fin 3 → ℝ}
    (h0 : 0 < lam0) (hl : 0 ≤ lam) (hsum : lam0 + ∑ a, lam a = 1)
    (hx6 : x6 = lam0 • p + ∑ a, lam a • zf E p a) (h : CornerLeaf (F.base E p) (zf E p) p) :
    IsRupert (insert x6 (F.base E p)) :=
  isRupert_of_cornerLeaf _ _ (F.zf_mem E p) x6 (zf_linearIndependent hE.ne' h0 hsum hx6)
    (cornerLeaf_tent _ _ (F.zf_mem E p) h0 hl hsum hx6 h)

/-- **Lemma Z0.**  If a view `q > 0` of the zone lies in the open cell `{Q}`, `{P}` or `{R}`, every
solid over the base `O` with apex `x_6` in the open tent `conv(T, x*)` is Rupert. -/
theorem isRupert_tent (hE : 0 < E.det) {q : Fin 3 → ℝ} (hq : ∀ i, 0 < q i)
    (hcell : (0 < F.nQ ⬝ᵥ q ∧ F.nP ⬝ᵥ q < 0 ∧ F.nR ⬝ᵥ q < 0) ∨ (0 < F.nP ⬝ᵥ q ∧ F.nQ ⬝ᵥ q < 0) ∨
      (0 < F.nR ⬝ᵥ q ∧ F.nQ ⬝ᵥ q < 0))
    {x6 : ℝ³} {lam0 : ℝ} {lam : Fin 3 → ℝ} (h0 : 0 < lam0) (hl : 0 ≤ lam)
    (hsum : lam0 + ∑ a, lam a = 1) (hx6 : x6 = lam0 • p + ∑ a, lam a • zf E p a) :
    IsRupert (insert x6 (F.base E p)) := by
  refine F.isRupert_of_cornerLeaf_tent hE h0 hl hsum hx6 ?_
  rcases hcell with ⟨hQ, hP, hR⟩ | ⟨hP, hQ⟩ | ⟨hR, hQ⟩
  · exact F.cornerLeaf_Q E p hE hq hQ hP hR
  · exact F.cornerLeaf_P E p hE hq hP hQ
  · exact F.cornerLeaf_R E p hE hq hR hQ
end

end Frame

end

end Minimality.TentApex
