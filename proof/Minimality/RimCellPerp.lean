module

public import Mathlib
public import Minimality.RimCellVertex
public import Minimality.RobustUnimodal
public import Minimality.EdgeView

@[expose] public section

/-!
# The equator lemma and the perpendicular-pair certificate

* `IsCcwPolygon.isCyclicUnimodal_inner`: a linear functional with distinct values on the corners of
  a strictly convex polygon is cyclically unimodal.
* `IsCcwPolygon.comp_cyc`: a cyclic subsequence of a strictly convex polygon is one.
* `isCyclicUnimodal_perp_subseq`: **the equator lemma** (with subsequences).  If `c` satisfies the
  orientation inequalities of the rim `y` and `p` is Euclidean-perpendicular to `c`, the depths of
  `p` along any cyclic subsequence of the rim, if distinct, are cyclically unimodal.
* `isRupert_of_perp_pair`: **the perpendicular-pair certificate.**
-/

set_option autoImplicit false

namespace Minimality.RimCell

open Finset Matrix
open scoped RealInnerProductSpace

/-- A linear functional with distinct values on the corners of a strictly convex polygon is
cyclically unimodal. -/
theorem _root_.Minimality.IsCcwPolygon.isCyclicUnimodal_inner {k : ℕ} [NeZero k]
    {P : ZMod k → ℝ²} (hP : IsCcwPolygon P) (ν : ℝ²)
    (hinj : Function.Injective fun i => ⟪ν, P i⟫) :
    IsCyclicUnimodal (fun i => ⟪ν, P i⟫) := by
  have hk := hP.1
  have hν : ν ≠ 0 := by
    intro h
    apply zmod_ne_add_one (k := k) (by omega) 0
    apply hinj
    simp [h]
  refine ⟨hinj, ?_⟩
  obtain ⟨M, -, hM⟩ := (univ : Finset (ZMod k)).exists_max_image (fun i => ⟪ν, P i⟫)
    univ_nonempty
  have hM' : ∀ i, ⟪ν, P i⟫ ≤ ⟪ν, P M⟫ := fun i => hM i (mem_univ _)
  rw [Finset.card_eq_one]
  refine ⟨M, ?_⟩
  ext s
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hne
    have h3 : M ≠ s - 1 := by
      intro h; rw [← h] at h1; linarith [hM' s]
    have h4 : M ≠ s + 1 := by
      intro h; rw [← h] at h2; linarith [hM' s]
    have := hP.lt_of_localMax hν (s := s) (by rw [inner_sub_right]; linarith)
      (by rw [inner_sub_right]; linarith) h3 (Ne.symm hne) h4
    linarith [hM' s]
  · rintro rfl
    have e1 : s - 1 ≠ s := by
      have := zmod_ne_add_one (k := k) (by omega) (s - 1)
      rwa [sub_add_cancel] at this
    have e2 : s + 1 ≠ s := (zmod_ne_add_one (k := k) (by omega) s).symm
    exact ⟨lt_of_le_of_ne (hM' _) (fun h => e1 (hinj h)),
      lt_of_le_of_ne (hM' _) (fun h => e2 (hinj h))⟩

/-- Consecutive position and any other position are in cyclic order. -/
theorem cycBetween_succ {m : ℕ} [NeZero m] (hm : 3 ≤ m) (i j : ZMod m) (h1 : j ≠ i)
    (h2 : j ≠ i + 1) : CycBetween i (i + 1) j := by
  have e1 : (i + 1 - i).val = 1 := by
    rw [add_sub_cancel_left]
    exact ZMod.val_one'' (by omega)
  unfold CycBetween
  rw [e1]
  refine ⟨one_pos, ?_⟩
  have h0 : (j - i).val ≠ 0 := fun h => h1 (by
    have := (ZMod.val_eq_zero _).mp h
    exact sub_eq_zero.mp this)
  have h1' : (j - i).val ≠ 1 := fun h => h2 (by
    have : j - i = 1 := by rw [← ZMod.natCast_zmod_val (j - i), h]; simp
    rw [← this]; ring)
  omega

/-- A cyclic subsequence of a strictly convex polygon is a strictly convex polygon. -/
theorem _root_.Minimality.IsCcwPolygon.comp_cyc {k m : ℕ} [NeZero k] [NeZero m] {p : ZMod k → ℝ²}
    (hp : IsCcwPolygon p) (hm : 3 ≤ m) (σ : ZMod m → ZMod k)
    (hσ : ∀ i j l, CycBetween i j l → CycBetween (σ i) (σ j) (σ l)) :
    IsCcwPolygon (fun i => p (σ i)) :=
  ⟨hm, fun i j hj1 hj2 => hp.cross2_pos_of_cycBetween (hσ _ _ _ (cycBetween_succ hm i j hj1 hj2))⟩

/-- `c ≠ 0` for a view satisfying the orientation inequalities. -/
theorem ne_zero_of_hcell {k : ℕ} [NeZero k] (hk : 3 ≤ k) (y : ZMod k → Fin 3 → ℝ)
    (hy : Function.Injective y) (Y : Finset (Fin 3 → ℝ)) (hyY : ∀ i, y i ∈ Y)
    (c : Fin 3 → ℝ)
    (hcell : ∀ i : ZMod k, ∀ v ∈ Y, v ≠ y i → v ≠ y (i + 1) →
      0 < (Matrix.of ![y (i + 1) - y i, v - y i, c]).det) : c ≠ 0 := by
  intro h0
  have h2 : y 2 ≠ y 0 := fun h => by
    have := zmod_add_ne (k := k) (a := 2) (b := 0) (by omega) (by omega) (by omega) 0
    simp at this
    exact this (hy h)
  have h3 : y 2 ≠ y (0 + 1) := fun h => by
    rw [zero_add] at h
    have := zmod_add_ne (k := k) (a := 2) (b := 1) (by omega) (by omega) (by omega) 0
    simp at this
    exact this (hy h)
  have := hcell 0 _ (hyY _) h2 h3
  rw [h0] at this
  simp [Matrix.det_fin_three] at this

/-- **The equator lemma, with subsequences.**  Let `c` satisfy the orientation inequalities of the
rim `y` (`k ≥ 3`) and let `p` be Euclidean-perpendicular to `c`
(`((Eᵀ E) c) ⬝ᵥ p = 0`: the views `E c` and `E p` are orthogonal).  Along any cyclic subsequence
`σ` (`m ≥ 3`) of the rim the depths `((Eᵀ E) p) ⬝ᵥ y (σ i)`, if distinct, are cyclically
unimodal.  Reason: projecting along `c`, the rim is a strictly convex polygon and the depth of `p`
is a linear functional on its plane. -/
theorem isCyclicUnimodal_perp_subseq {k m : ℕ} [NeZero k] [NeZero m] (hk : 3 ≤ k) (hm : 3 ≤ m)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (y : ZMod k → Fin 3 → ℝ) (hy : Function.Injective y) (Y : Finset (Fin 3 → ℝ))
    (hyY : ∀ i, y i ∈ Y) (c : Fin 3 → ℝ)
    (hcell : ∀ i : ZMod k, ∀ v ∈ Y, v ≠ y i → v ≠ y (i + 1) →
      0 < (Matrix.of ![y (i + 1) - y i, v - y i, c]).det)
    (σ : ZMod m → ZMod k)
    (hσ : ∀ i j l, CycBetween i j l → CycBetween (σ i) (σ j) (σ l))
    (p : Fin 3 → ℝ) (hperp : ((Eᵀ * E) *ᵥ c) ⬝ᵥ p = 0)
    (hinj : Function.Injective fun i : ZMod m => ((Eᵀ * E) *ᵥ p) ⬝ᵥ y (σ i)) :
    IsCyclicUnimodal (fun i : ZMod m => ((Eᵀ * E) *ᵥ p) ⬝ᵥ y (σ i)) := by
  have hc : c ≠ 0 := ne_zero_of_hcell hk y hy Y hyY c hcell
  have hEne : E.det ≠ 0 := hE.ne'
  set w : ℝ³ := emb E c with hw
  have hw0 : w ≠ 0 := by
    intro h
    apply hc
    apply Matrix.eq_zero_of_mulVec_eq_zero hEne
    have h' : emb E c = 0 := h
    ext i; simpa [emb_apply] using congrArg (fun v : ℝ³ => v i) h'
  obtain ⟨R, hR, lam, hlam, hRw⟩ := exists_rotation_to_ez_pos w hw0
  have hor : ∀ a b : Fin 3 → ℝ, 0 < (Matrix.of ![a, b, c]).det →
      0 < cross2 (proj_xy (R.toEuclideanLin (emb E a))) (proj_xy (R.toEuclideanLin (emb E b))) := by
    intro a b h
    refine cross2_proj_rot_pos hR hlam hRw ?_
    rw [hw, det3_emb]; exact mul_pos hE h
  have hside : ∀ i : ZMod k, ∀ v ∈ Y, v ≠ y i → v ≠ y (i + 1) →
      0 < cross2 (proj_xy (R.toEuclideanLin (emb E (y (i + 1)))) -
          proj_xy (R.toEuclideanLin (emb E (y i))))
        (proj_xy (R.toEuclideanLin (emb E v)) - proj_xy (R.toEuclideanLin (emb E (y i)))) := by
    intro i v hv h1 h2
    rw [proj_rot_sub, proj_rot_sub, ← emb_sub, ← emb_sub]
    exact hor _ _ (hcell i v hv h1 h2)
  have hP : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (emb E (y i)))) := by
    refine ⟨hk, ?_⟩
    intro i j hj1 hj2
    exact hside i (y j) (hyY j) (fun h => hj1 (hy h)) (fun h => hj2 (hy h))
  have hP' := hP.comp_cyc hm σ hσ
  -- the third coordinate of `R (emb p)` vanishes
  set b : ℝ³ := R.toEuclideanLin (emb E p) with hb
  have hb2 : b 2 = 0 := by
    have h1 := inner_toEuclideanLin_SO3 hR (emb E p) w
    rw [hRw, real_inner_smul_right, inner_ez, hw, inner_emb] at h1
    rw [hperp] at h1
    -- h1 : lam * b 2 = 0
    exact (mul_eq_zero.mp h1).resolve_left hlam.ne'
  have hdepth : ∀ i : ZMod k, ((Eᵀ * E) *ᵥ p) ⬝ᵥ y i =
      ⟪proj_xy b, proj_xy (R.toEuclideanLin (emb E (y i)))⟫ := by
    intro i
    have h1 := inner_toEuclideanLin_SO3 hR (emb E (y i)) (emb E p)
    rw [inner_emb] at h1
    rw [← h1]
    simp only [PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_three, RCLike.inner_apply,
      conj_trivial, proj_xy]
    simp [hb]
    have h2 : (R *ᵥ (emb E p).ofLp) 2 = 0 := hb2
    rw [h2]
    ring
  have e : (fun i : ZMod m => ((Eᵀ * E) *ᵥ p) ⬝ᵥ y (σ i)) =
      fun i => ⟪proj_xy b, proj_xy (R.toEuclideanLin (emb E (y (σ i))))⟫ :=
    funext fun i => hdepth _
  rw [e] at hinj ⊢
  exact hP'.isCyclicUnimodal_inner _ hinj

/-- **The equator lemma.**  If `c` satisfies the orientation inequalities of the rim `y` and `p`
is Euclidean-perpendicular to `c`, distinct depths of `p` on the rim are cyclically unimodal. -/
theorem isCyclicUnimodal_perp {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (y : ZMod k → Fin 3 → ℝ) (hy : Function.Injective y) (Y : Finset (Fin 3 → ℝ))
    (hyY : ∀ i, y i ∈ Y) (c : Fin 3 → ℝ)
    (hcell : ∀ i : ZMod k, ∀ v ∈ Y, v ≠ y i → v ≠ y (i + 1) →
      0 < (Matrix.of ![y (i + 1) - y i, v - y i, c]).det)
    (p : Fin 3 → ℝ) (hperp : ((Eᵀ * E) *ᵥ c) ⬝ᵥ p = 0)
    (hinj : Function.Injective fun i : ZMod k => ((Eᵀ * E) *ᵥ p) ⬝ᵥ y i) :
    IsCyclicUnimodal (fun i : ZMod k => ((Eᵀ * E) *ᵥ p) ⬝ᵥ y i) :=
  isCyclicUnimodal_perp_subseq hk hk E hE y hy Y hyY c hcell id (fun _ _ _ h => h) p hperp hinj

/-- **The perpendicular-pair (PP) certificate.**  `c` satisfies the orientation inequalities of the
rim `y`; `p` satisfies those of the rim `y ∘ σ`, a cyclic subsequence of `y` (`σ` injective,
preserving the cyclic order of triples, `m ≥ 3`); the views `E c` and `E p` are orthogonal; the
depths of `p` on `y ∘ σ` are distinct.  Then `E Y` is Rupert. -/
theorem isRupert_of_perp_pair {k m : ℕ} [NeZero k] [NeZero m] (hk : 3 ≤ k) (hm : 3 ≤ m)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (y : ZMod k → Fin 3 → ℝ) (hy : Function.Injective y) (Y : Finset (Fin 3 → ℝ))
    (hyY : ∀ i, y i ∈ Y)
    (σ : ZMod m → ZMod k) (hσi : Function.Injective σ)
    (hσ : ∀ i j l, CycBetween i j l → CycBetween (σ i) (σ j) (σ l))
    (c : Fin 3 → ℝ)
    (hcell : ∀ i : ZMod k, ∀ v ∈ Y, v ≠ y i → v ≠ y (i + 1) →
      0 < (Matrix.of ![y (i + 1) - y i, v - y i, c]).det)
    (p : Fin 3 → ℝ)
    (hcell' : ∀ i : ZMod m, ∀ v ∈ Y, v ≠ y (σ i) → v ≠ y (σ (i + 1)) →
      0 < (Matrix.of ![y (σ (i + 1)) - y (σ i), v - y (σ i), p]).det)
    (hperp : ((Eᵀ * E) *ᵥ c) ⬝ᵥ p = 0)
    (hinj : Function.Injective fun i : ZMod m => ((Eᵀ * E) *ᵥ p) ⬝ᵥ y (σ i)) :
    IsRupert (Y.image (emb E)) := by
  have hz := isCyclicUnimodal_perp_subseq hk hm E hE y hy Y hyY c hcell σ hσ p hperp hinj
  have hp0 : p ≠ 0 := by
    intro h0
    have h2 : y (σ 2) ≠ y (σ 0) := fun h => by
      have := zmod_add_ne (k := m) (a := 2) (b := 0) (by omega) (by omega) (by omega) 0
      simp at this
      exact this (hσi (hy h))
    have h3 : y (σ 2) ≠ y (σ (0 + 1)) := fun h => by
      rw [zero_add] at h
      have := zmod_add_ne (k := m) (a := 2) (b := 1) (by omega) (by omega) (by omega) 0
      simp at this
      exact this (hσi (hy h))
    have := hcell' 0 _ (hyY _) h2 (by rw [zero_add] at h3 ⊢; exact h3)
    rw [h0] at this
    simp [Matrix.det_fin_three] at this
  exact isRupert_of_rimCell_zmod hm E hE (fun i => y (σ i)) (hy.comp hσi) Y
    (fun i => hyY _) p hp0 hcell' hz

end Minimality.RimCell
