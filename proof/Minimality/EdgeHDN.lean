module

public import Minimality.EdgeSlide

@[expose] public section

/-!
# Horizontal double normals perpendicular to a face (`FEWER-FACES-PROOFS.md` §22.0, §22.3)

A slide along `F_a`'s circle fails only for a double normal of the rim in space perpendicular to
`F_a` (`NoPersistHDN`).  Its ends are extremal for the face functional: one end lies on the side
`[v, a]` (where the functional is maximal), the other on the far set where it is minimal, a far
corner (class `c_a`) or a far edge parallel to `F_a` (class `d_a`).  This file proves the
classification and states the shape-level notions used for the codimension-2 conditions.

* `HDNDir V u ℓ`: a double normal of the shadow along `ℓ ⊥ u` (two points of the hull of `V`
  with difference `ℓ`, extremal for `⟪ℓ, ·⟫` over `V`); `OneHDNDir V u`: all such directions
  are parallel (two non-parallel horizontal double normals at one view: codimension 2).
* `hdnDir_of_rim`: a rim double normal with `SuppIn` is a shadow double normal.
* `classify_face`: a rim double normal along the normal of a face has one end on the side of the
  face and the other on the segment of the far minimizers.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **A horizontal double normal of the shadow of `V` at `u` along `ℓ`**: `ℓ ≠ 0`,
`ℓ ⊥ u`, and two points `Y, Y'` of the hull with `Y' − Y = ℓ`, `Y'` maximal and `Y` minimal for
`⟪ℓ, ·⟫` over `V`. -/
def HDNDir (V : Finset ℝ³) (u ℓ : ℝ³) : Prop :=
  ℓ ≠ 0 ∧ ⟪ℓ, u⟫ = 0 ∧ ∃ Y Y' : ℝ³, Y ∈ convexHull ℝ (V : Set ℝ³) ∧
    Y' ∈ convexHull ℝ (V : Set ℝ³) ∧ Y' - Y = ℓ ∧ ∀ z ∈ V, ⟪ℓ, z - Y'⟫ ≤ 0 ∧ 0 ≤ ⟪ℓ, z - Y⟫

/-- **At most one direction of horizontal double normals at `u`**: two horizontal double
normals at one view are two conditions on the shape. -/
def OneHDNDir (V : Finset ℝ³) (u : ℝ³) : Prop :=
  ∀ ℓ ℓ', HDNDir V u ℓ → HDNDir V u ℓ' → cross ℓ ℓ' = 0

theorem segment_subset_hull {V : Finset ℝ³} {p q : ℝ³} (hp : p ∈ V) (hq : q ∈ V) :
    segment ℝ p q ⊆ convexHull ℝ (V : Set ℝ³) :=
  segment_subset_convexHull (s := (V : Set ℝ³)) (by exact_mod_cast hp) (by exact_mod_cast hq)

/-- **A rim double normal is a shadow double normal** when every point of `V` lies in the
cylinder over the rim (`SuppIn`). -/
theorem hdnDir_of_rim {V : Finset ℝ³} {u : ℝ³} {k : ℕ} (R : ZMod k → ℝ³)
    (hRV : ∀ i, R i ∈ V) (hsupp : ∀ z ∈ V, SuppIn u R z) {i j : ZMod k} {Y Y' : ℝ³}
    (hY : Y ∈ segment ℝ (R i) (R (i + 1))) (hY' : Y' ∈ segment ℝ (R j) (R (j + 1)))
    (hne : Y' ≠ Y) (hu : ⟪Y' - Y, u⟫ = 0)
    (hext : ∀ m, ⟪Y' - Y, R m - Y'⟫ ≤ 0 ∧ ⟪Y - Y', R m - Y⟫ ≤ 0) :
    HDNDir V u (Y' - Y) := by
  refine ⟨sub_ne_zero.mpr hne, hu, Y, Y', segment_subset_hull (hRV i) (hRV (i + 1)) hY,
    segment_subset_hull (hRV j) (hRV (j + 1)) hY', rfl, fun z hz => ⟨?_, ?_⟩⟩
  · obtain ⟨m, hm⟩ := hsupp z hz (Y' - Y) hu
    have := (hext m).1
    rw [inner_sub_right] at this ⊢; linarith
  · have hu' : ⟪-(Y' - Y), u⟫ = 0 := by rw [inner_neg_left, hu, neg_zero]
    obtain ⟨m, hm⟩ := hsupp z hz _ hu'
    have := (hext m).2
    rw [inner_neg_left, inner_neg_left] at hm
    rw [show Y - Y' = -(Y' - Y) by abel, inner_neg_left, inner_sub_right] at this
    rw [inner_sub_right]; linarith

/-- A point of a segment maximal for a linear functional is an end, or both ends attain the
maximum. -/
theorem segment_ext {p q Y N : ℝ³} (hY : Y ∈ segment ℝ p q) (hp : ⟪N, p⟫ ≤ ⟪N, Y⟫)
    (hq : ⟪N, q⟫ ≤ ⟪N, Y⟫) : Y = p ∨ Y = q ∨ (⟪N, p⟫ = ⟪N, Y⟫ ∧ ⟪N, q⟫ = ⟪N, Y⟫) := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hY
  rcases hα.eq_or_lt with hα0 | hα0
  · right; left; rw [← hα0, show β = 1 by linarith]; simp
  rcases hβ.eq_or_lt with hβ0 | hβ0
  · left; rw [← hβ0, show α = 1 by linarith]; simp
  right; right
  simp only [inner_add_right, real_inner_smul_right] at hp hq ⊢
  obtain rfl : α = 1 - β := by linarith
  have h1 : β * ⟪N, p⟫ ≤ β * ⟪N, q⟫ := by linarith
  have h2 : (1 - β) * ⟪N, q⟫ ≤ (1 - β) * ⟪N, p⟫ := by linarith
  have h3 : ⟪N, p⟫ ≤ ⟪N, q⟫ := le_of_mul_le_mul_left h1 hβ0
  have h4 : ⟪N, q⟫ ≤ ⟪N, p⟫ := le_of_mul_le_mul_left h2 hα0
  have h5 : ⟪N, p⟫ = ⟪N, q⟫ := le_antisymm h3 h4
  rw [← h5]; constructor <;> ring

/-- The end of a rim double normal maximal for the face functional lies on the side `[v, a]`. -/
theorem face_end {V : Finset ℝ³} {k : ℕ} (hk : 2 ≤ k) (R : ZMod k → ℝ³)
    (hRinj : Function.Injective R) (hRV : ∀ i, R i ∈ V) {N : ℝ³} {κ : ℝ} {v a : ℝ³}
    (hle : ∀ z ∈ V, ⟪N, z⟫ ≤ κ) (hv : ⟪N, v⟫ = κ) (hvR : ∃ i, R i = v)
    (htop : ∀ m, ⟪N, R m⟫ = κ → R m = v ∨ R m = a) {i₀ : ZMod k} {P : ℝ³}
    (hP : P ∈ segment ℝ (R i₀) (R (i₀ + 1))) (hmax : ∀ m, ⟪N, R m⟫ ≤ ⟪N, P⟫) :
    P ∈ segment ℝ v a := by
  have hPκ : ⟪N, P⟫ = κ := by
    obtain ⟨iv, hiv⟩ := hvR
    have h1 := hmax iv
    rw [hiv, hv] at h1
    have h2 : ⟪N, P⟫ ≤ κ := by
      obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hP
      simp only [inner_add_right, real_inner_smul_right]
      have e1 := mul_le_mul_of_nonneg_left (hle _ (hRV i₀)) hα
      have e2 := mul_le_mul_of_nonneg_left (hle _ (hRV (i₀ + 1))) hβ
      have e3 : α * κ + β * κ = κ := by rw [← add_mul, hαβ, one_mul]
      linarith
    linarith
  have hne : R i₀ ≠ R (i₀ + 1) := hRinj.ne (zmod_ne_add_one hk i₀)
  rcases segment_ext hP (hmax i₀) (hmax (i₀ + 1)) with e | e | ⟨e1, e2⟩
  · rw [e] at hPκ ⊢
    rcases htop i₀ hPκ with e' | e' <;> rw [e']
    exacts [left_mem_segment ℝ v a, right_mem_segment ℝ v a]
  · rw [e] at hPκ ⊢
    rcases htop (i₀ + 1) hPκ with e' | e' <;> rw [e']
    exacts [left_mem_segment ℝ v a, right_mem_segment ℝ v a]
  · rw [hPκ] at e1 e2
    rcases htop i₀ e1 with e3 | e3 <;> rcases htop (i₀ + 1) e2 with e4 | e4
    · exact absurd (e3.trans e4.symm) hne
    · rw [e3, e4] at hP; exact hP
    · rw [e3, e4, segment_symm] at hP; exact hP
    · exact absurd (e3.trans e4.symm) hne

/-- The end of a rim double normal minimal for the face functional lies on `[c, b]`, at the
minimum of the functional over `c`, `b`. -/
theorem far_end {k : ℕ} (hk : 2 ≤ k) (R : ZMod k → ℝ³) (hRinj : Function.Injective R)
    {N : ℝ³} {c b : ℝ³} (hcR : ∃ i, R i = c) (hbR : ∃ i, R i = b)
    (hlow : ∀ m, R m ≠ c → R m ≠ b → min ⟪N, c⟫ ⟪N, b⟫ < ⟪N, R m⟫) {i₀ : ZMod k} {P : ℝ³}
    (hP : P ∈ segment ℝ (R i₀) (R (i₀ + 1))) (hmin : ∀ m, ⟪N, P⟫ ≤ ⟪N, R m⟫) :
    P ∈ segment ℝ c b ∧ ⟪N, P⟫ = min ⟪N, c⟫ ⟪N, b⟫ := by
  obtain ⟨ic, hic⟩ := hcR
  obtain ⟨ib, hib⟩ := hbR
  have hPc := hmin ic
  have hPb := hmin ib
  rw [hic] at hPc
  rw [hib] at hPb
  have hneg : ∀ m, min ⟪N, c⟫ ⟪N, b⟫ ≤ ⟪N, R m⟫ := by
    intro m
    by_cases h1 : R m = c
    · rw [h1]; exact min_le_left _ _
    by_cases h2 : R m = b
    · rw [h2]; exact min_le_right _ _
    exact (hlow m h1 h2).le
  have hlowP : ⟪N, P⟫ = min ⟪N, c⟫ ⟪N, b⟫ := by
    refine le_antisymm (le_min hPc hPb) ?_
    obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hP
    simp only [inner_add_right, real_inner_smul_right]
    have e1 := mul_le_mul_of_nonneg_left (hneg i₀) hα
    have e2 := mul_le_mul_of_nonneg_left (hneg (i₀ + 1)) hβ
    have e3 : α * min ⟪N, c⟫ ⟪N, b⟫ + β * min ⟪N, c⟫ ⟪N, b⟫ = min ⟪N, c⟫ ⟪N, b⟫ := by
      rw [← add_mul, hαβ, one_mul]
    linarith
  refine ⟨?_, hlowP⟩
  have hN : ∀ m, ⟪-N, R m⟫ ≤ ⟪-N, P⟫ := by
    intro m; rw [inner_neg_left, inner_neg_left]; linarith [hmin m]
  have hmembers : ∀ m, ⟪N, R m⟫ = ⟪N, P⟫ → R m = c ∨ R m = b := by
    intro m hm
    by_contra hcon
    push Not at hcon
    have := hlow m hcon.1 hcon.2
    rw [hm, hlowP] at this
    exact lt_irrefl _ this
  have hne : R i₀ ≠ R (i₀ + 1) := hRinj.ne (zmod_ne_add_one hk i₀)
  rcases segment_ext hP (hN i₀) (hN (i₀ + 1)) with e | e | ⟨e1, e2⟩
  · rcases hmembers i₀ (by rw [e]) with e' | e' <;> rw [e, e']
    exacts [left_mem_segment ℝ c b, right_mem_segment ℝ c b]
  · rcases hmembers (i₀ + 1) (by rw [e]) with e' | e' <;> rw [e, e']
    exacts [left_mem_segment ℝ c b, right_mem_segment ℝ c b]
  · rw [inner_neg_left, inner_neg_left, neg_inj] at e1 e2
    rcases hmembers i₀ e1 with e3 | e3 <;> rcases hmembers (i₀ + 1) e2 with e4 | e4
    · exact absurd (e3.trans e4.symm) hne
    · rw [e3, e4] at hP; exact hP
    · rw [e3, e4, segment_symm] at hP; exact hP
    · exact absurd (e3.trans e4.symm) hne

/-- **The classification of a rim double normal perpendicular to a face** (§22.0, class
`H_a`).  Let `R` be an injective cycle in `V` whose vertices on the face `⟪N, ·⟫ = κ` are among
`v, a` (all of `V` lies weakly below), with `v` a vertex, and whose vertices other than `c, b`
lie strictly above `min (⟪N, c⟫, ⟪N, b⟫)` (`c`, `b` vertices).  A rim double normal
`Y' − Y = r N` (`r ≠ 0`, extremal ends) has one end `Z` on `[v, a]` and the other `F` on
`[c, b]`, minimal for `⟪N, ·⟫` over `c`, `b`. -/
theorem classify_face {V : Finset ℝ³} {k : ℕ} (hk : 2 ≤ k) (R : ZMod k → ℝ³)
    (hRinj : Function.Injective R) (hRV : ∀ i, R i ∈ V) {N : ℝ³} {κ : ℝ} {v a c b : ℝ³}
    (hle : ∀ z ∈ V, ⟪N, z⟫ ≤ κ) (hv : ⟪N, v⟫ = κ) (hvR : ∃ i, R i = v)
    (htop : ∀ m, ⟪N, R m⟫ = κ → R m = v ∨ R m = a)
    (hcR : ∃ i, R i = c) (hbR : ∃ i, R i = b)
    (hlow : ∀ m, R m ≠ c → R m ≠ b → min ⟪N, c⟫ ⟪N, b⟫ < ⟪N, R m⟫)
    {i j : ZMod k} {Y Y' : ℝ³} (hY : Y ∈ segment ℝ (R i) (R (i + 1)))
    (hY' : Y' ∈ segment ℝ (R j) (R (j + 1))) {r : ℝ} (hr : r ≠ 0) (hYr : Y' - Y = r • N)
    (hext : ∀ m, ⟪Y' - Y, R m - Y'⟫ ≤ 0 ∧ ⟪Y - Y', R m - Y⟫ ≤ 0) :
    ∃ Z ∈ segment ℝ v a, ∃ F ∈ segment ℝ c b, ∃ r' : ℝ, r' ≠ 0 ∧ F - Z = r' • N ∧
      ⟪N, F⟫ = min ⟪N, c⟫ ⟪N, b⟫ := by
  have e1 : ∀ m, r * (⟪N, R m⟫ - ⟪N, Y'⟫) ≤ 0 := by
    intro m
    have := (hext m).1
    rw [hYr, real_inner_smul_left, inner_sub_right] at this; exact this
  have e2 : ∀ m, r * (⟪N, R m⟫ - ⟪N, Y⟫) ≥ 0 := by
    intro m
    have := (hext m).2
    rw [show Y - Y' = -(r • N) by rw [← hYr]; abel, inner_neg_left, real_inner_smul_left,
      inner_sub_right] at this
    linarith
  rcases lt_or_gt_of_ne hr with hr | hr
  · -- `Y` on the face, `Y'` far
    have hmax : ∀ m, ⟪N, R m⟫ ≤ ⟪N, Y⟫ := fun m => by nlinarith [e2 m]
    have hmin : ∀ m, ⟪N, Y'⟫ ≤ ⟪N, R m⟫ := fun m => by nlinarith [e1 m]
    obtain ⟨hF, hFmin⟩ := far_end hk R hRinj hcR hbR hlow hY' hmin
    exact ⟨Y, face_end hk R hRinj hRV hle hv hvR htop hY hmax, Y', hF, r, hr.ne, hYr, hFmin⟩
  · have hmax : ∀ m, ⟪N, R m⟫ ≤ ⟪N, Y'⟫ := fun m => by nlinarith [e1 m]
    have hmin : ∀ m, ⟪N, Y⟫ ≤ ⟪N, R m⟫ := fun m => by nlinarith [e2 m]
    obtain ⟨hF, hFmin⟩ := far_end hk R hRinj hcR hbR hlow hY hmin
    refine ⟨Y', face_end hk R hRinj hRV hle hv hvR htop hY' hmax, Y, hF, -r,
      neg_ne_zero.mpr hr.ne', ?_, hFmin⟩
    rw [neg_smul, ← hYr]; abel

end Minimality

end
