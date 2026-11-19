module

public import Mathlib

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace LemmaCA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Strict Cauchy-Schwarz for linearly independent vectors. -/
theorem inner_sq_lt {u w : E} (hlin : LinearIndependent ℝ ![u, w]) :
    ⟪u, w⟫ ^ 2 < ⟪u, u⟫ * ⟪w, w⟫ := by
  rw [LinearIndependent.pair_iff] at hlin
  have hu : u ≠ 0 := by
    intro h
    have := hlin 1 0 (by simp [h])
    simp at this
  have ha : 0 < ⟪u, u⟫ := real_inner_self_pos.2 hu
  set v : E := ⟪u, u⟫ • w - ⟪u, w⟫ • u with hv
  have hv0 : v ≠ 0 := by
    intro h
    have := hlin (-⟪u, w⟫) ⟪u, u⟫ (by rw [hv] at h; rw [← h]; module)
    exact ha.ne' this.2
  have hvv : 0 < ⟪v, v⟫ := real_inner_self_pos.2 hv0
  have : ⟪v, v⟫ = ⟪u, u⟫ * (⟪u, u⟫ * ⟪w, w⟫ - ⟪u, w⟫ ^ 2) := by
    rw [hv]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      real_inner_comm u w]
    simp only [conj_trivial]
    ring
  rw [this] at hvv
  have := (pos_iff_pos_of_mul_pos hvv).1 ha
  linarith

/-- Lemma CA (Cauchy-Schwarz). -/
theorem inner_pos_or_of_det {u w : E} (hlin : LinearIndependent ℝ ![u, w])
    {db dc eb ec : ℝ} (hdb : 0 ≤ db) (hdc : dc < 0) (heb : eb < 0)
    (hD : dc * eb ≤ db * ec) :
    0 < ⟪u, db • u + dc • w⟫ ∨ 0 < ⟪w, eb • u + ec • w⟫ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hcs := inner_sq_lt hlin
  have ha : 0 < ⟪u, u⟫ := by
    have : u ≠ 0 := by
      intro h; rw [LinearIndependent.pair_iff] at hlin
      have := hlin 1 0 (by simp [h]); simp at this
    exact real_inner_self_pos.2 this
  have hb : 0 < ⟪w, w⟫ := by
    have : w ≠ 0 := by
      intro h; rw [LinearIndependent.pair_iff] at hlin
      have := hlin 0 1 (by simp [h]); simp at this
    exact real_inner_self_pos.2 this
  simp only [inner_add_right, inner_smul_right, real_inner_comm u w] at h1 h2
  set a := ⟪u, u⟫
  set b := ⟪w, w⟫
  set c := ⟪u, w⟫
  have hpos : 0 < dc * eb := mul_pos_of_neg_of_neg hdc heb
  have hdbec : 0 < db * ec := lt_of_lt_of_le hpos hD
  have hdb' : 0 < db := lt_of_le_of_ne hdb (by rintro rfl; simp at hdbec)
  have hec : 0 < ec := by
    by_contra h; push Not at h; nlinarith
  have hc : 0 < c := by
    by_contra h; push Not at h; nlinarith [mul_pos hdb' ha]
  -- db*a ≤ -dc*c, ec*b ≤ -eb*c
  have e1 : db * a ≤ (-dc) * c := by linarith
  have e2 : ec * b ≤ (-eb) * c := by linarith
  have e3 : (db * a) * (ec * b) ≤ ((-dc) * c) * ((-eb) * c) :=
    mul_le_mul e1 e2 (by positivity) (by nlinarith)
  have e4 : (dc * eb) * c ^ 2 ≤ (db * ec) * c ^ 2 :=
    mul_le_mul_of_nonneg_right hD (by positivity)
  have : (db * ec) * (a * b - c ^ 2) ≤ 0 := by nlinarith
  have := mul_pos hdbec (sub_pos.2 (by nlinarith : c ^ 2 < a * b))
  linarith

/-- T24 wrapper: `n` is orthogonal to the edges `x2 - x0`, `x6 - x0`; the two views are
`g = n + db (x2-x0) + dc (x6-x0)`, `g' = n + eb (x2-x0) + ec (x6-x0)`. Then
`⟪x0,g⟫ < ⟪x2,g⟫` or `⟪x0,g'⟫ < ⟪x6,g'⟫`. -/
theorem lt_or_lt_of_views {x0 x2 x6 n : E}
    (hlin : LinearIndependent ℝ ![x2 - x0, x6 - x0])
    (hn2 : ⟪n, x2 - x0⟫ = 0) (hn6 : ⟪n, x6 - x0⟫ = 0)
    {db dc eb ec : ℝ} (hdb : 0 ≤ db) (hdc : dc < 0) (heb : eb < 0)
    (hD : dc * eb ≤ db * ec) :
    ⟪x0, n + db • (x2 - x0) + dc • (x6 - x0)⟫ < ⟪x2, n + db • (x2 - x0) + dc • (x6 - x0)⟫ ∨
    ⟪x0, n + eb • (x2 - x0) + ec • (x6 - x0)⟫ < ⟪x6, n + eb • (x2 - x0) + ec • (x6 - x0)⟫ := by
  rcases inner_pos_or_of_det hlin hdb hdc heb hD with h | h
  · left
    have : ⟪x2 - x0, n + db • (x2 - x0) + dc • (x6 - x0)⟫ > 0 := by
      rw [real_inner_comm] at hn2; simp only [inner_add_right, hn2, zero_add, inner_smul_right]; simpa [inner_add_right, inner_smul_right] using h
    rw [inner_sub_left] at this; linarith
  · right
    have : ⟪x6 - x0, n + eb • (x2 - x0) + ec • (x6 - x0)⟫ > 0 := by
      rw [real_inner_comm] at hn6; simp only [inner_add_right, hn6, zero_add, inner_smul_right]; simpa [inner_add_right, inner_smul_right] using h
    rw [inner_sub_left] at this; linarith

end LemmaCA
