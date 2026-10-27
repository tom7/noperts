module

public import Minimality.CaseC09Frame
public import Minimality.Crossing

@[expose] public section

/-!
# Type 09, acute case (c): the tests (`FEWER-FACES-PROOFS.md` §27, continued (4))
-/

namespace Minimality.CaseC09

open Finset
open scoped RealInnerProductSpace

namespace Frame09
variable {x : Fin 7 → ℝ³} (F : Frame09 x)

/-- The `u₁`-coordinates of the seven points (`x j = x 0 + cx j u₁ + cy j u₂ + cz j e`). -/
noncomputable def cx : Fin 7 → ℝ := ![0, F.S.tp, 0, 1, F.S.tm, 0, 0]
noncomputable def cy : Fin 7 → ℝ := ![0, 0, F.S.sp, 0, 0, 1, F.S.sm]
noncomputable def cz : Fin 7 → ℝ := ![0, F.S.hp, F.S.kp, 0, -F.S.hm, 0, -F.S.km]

lemma x_eq (j : Fin 7) :
    x j = x 0 + F.cx j • (x 3 - x 0) + F.cy j • (x 5 - x 0) + F.cz j • F.e := by
  fin_cases j
  · simp [cx, cy, cz]
  · show x 1 = x 0 + F.S.tp • (x 3 - x 0) + 0 • (x 5 - x 0) + F.S.hp • F.e
    rw [F.x1_eq]; simp
  · show x 2 = x 0 + 0 • (x 3 - x 0) + F.S.sp • (x 5 - x 0) + F.S.kp • F.e
    rw [F.x2_eq]; simp
  · show x 3 = x 0 + (1:ℝ) • (x 3 - x 0) + 0 • (x 5 - x 0) + 0 • F.e
    simp
  · show x 4 = x 0 + F.S.tm • (x 3 - x 0) + 0 • (x 5 - x 0) + (-F.S.hm) • F.e
    rw [F.x4_eq]; simp [sub_eq_add_neg]
  · show x 5 = x 0 + 0 • (x 3 - x 0) + (1:ℝ) • (x 5 - x 0) + 0 • F.e
    simp
  · show x 6 = x 0 + 0 • (x 3 - x 0) + F.S.sm • (x 5 - x 0) + (-F.S.km) • F.e
    rw [F.x6_eq]; simp [sub_eq_add_neg]

lemma coord_zero {a b c : ℝ} (h : a • (x 3 - x 0) + b • (x 5 - x 0) + c • F.e = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have := Fintype.linearIndependent_iff.mp F.indep ![a, b, c] (by
    simpa [Fin.sum_univ_three] using h)
  exact ⟨this 0, this 1, this 2⟩

lemma exists_normal (a1 a2 a3 : ℝ) :
    ∃ N : ℝ³, ∀ a b c : ℝ,
      ⟪N, a • (x 3 - x 0) + b • (x 5 - x 0) + c • F.e⟫ = a1 * a + a2 * b + a3 * c := by
  let ℓ : ℝ³ →ₗ[ℝ] ℝ := F.basis.constr ℝ ![a1, a2, a3]
  refine ⟨(InnerProductSpace.toDual ℝ ℝ³).symm (LinearMap.toContinuousLinearMap ℓ), fun a b c => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  have h0 : ℓ (x 3 - x 0) = a1 := by
    have := F.basis.constr_basis ℝ ![a1, a2, a3] 0
    rwa [F.basis_apply] at this
  have h1 : ℓ (x 5 - x 0) = a2 := by
    have := F.basis.constr_basis ℝ ![a1, a2, a3] 1
    rwa [F.basis_apply] at this
  have h2 : ℓ F.e = a3 := by
    have := F.basis.constr_basis ℝ ![a1, a2, a3] 2
    rwa [F.basis_apply] at this
  show ℓ _ = _
  rw [map_add, map_add, map_smul, map_smul, map_smul, h0, h1, h2]
  simp only [smul_eq_mul]; ring

end Frame09

lemma affineIndependent_of_pair {a b c : ℝ³}
    (h : ∀ s t : ℝ, s • (b - a) + t • (c - a) = 0 → s = 0 ∧ t = 0) :
    AffineIndependent ℝ ![a, b, c] := by
  rw [affineIndependent_iff_not_collinear_set]
  intro hcol
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (p₀ := a) (by simp)).mp hcol
  obtain ⟨rb, hrb⟩ := hv b (by simp)
  obtain ⟨rc, hrc⟩ := hv c (by simp)
  rw [vadd_eq_add] at hrb hrc
  have hb : b - a = rb • v := by rw [hrb]; abel
  have hc : c - a = rc • v := by rw [hrc]; abel
  have := h rc (-rb) (by rw [hb, hc, smul_smul, neg_smul, smul_smul, mul_comm]; simp)
  obtain ⟨h1, h2⟩ := this
  have h2' : rb = 0 := by linarith
  have h0 : b - a = 0 := by rw [hb, h2']; simp
  have h0' : c - a = 0 := by rw [hc, h1]; simp
  have := h 1 0 (by rw [h0]; simp)
  exact one_ne_zero this.1

namespace Frame09
variable {x : Fin 7 → ℝ³} (F : Frame09 x)

/-- **The coordinate form of Theorem 5.**  `W = {x j | j ∈ I}` lies in the plane
`a₁ cx + a₂ cy + a₃ cz = c₀` (frame coordinates), contains three points of independent
directions, and along the view `u₀ = p u₁ + q u₂ + r e` (with `a₁ p + a₂ q + a₃ r ≠ 0`)
every other point of the set reaches a point of `W` with positive weights. -/
theorem rupert_crossing (hx : Function.Injective x) (I : Finset (Fin 7)) (j0 j1 j2 : Fin 7)
    (h0 : j0 ∈ I) (h1 : j1 ∈ I) (h2 : j2 ∈ I)
    (hind : ∀ s t : ℝ,
      s * (F.cx j1 - F.cx j0) + t * (F.cx j2 - F.cx j0) = 0 →
      s * (F.cy j1 - F.cy j0) + t * (F.cy j2 - F.cy j0) = 0 →
      s * (F.cz j1 - F.cz j0) + t * (F.cz j2 - F.cz j0) = 0 → s = 0 ∧ t = 0)
    (a1 a2 a3 c0 : ℝ) (hplane : ∀ j ∈ I, a1 * F.cx j + a2 * F.cy j + a3 * F.cz j = c0)
    (p q r : ℝ) (hnp : a1 * p + a2 * q + a3 * r ≠ 0)
    (hcross : ∀ i : Fin 7, i ∉ I → ∃ (τ : ℝ) (m : Fin 7 → ℝ), (∀ j ∈ I, 0 < m j) ∧
      ∑ j ∈ I, m j = 1 ∧ ∑ j ∈ I, m j * F.cx j = F.cx i + τ * p ∧
      ∑ j ∈ I, m j * F.cy j = F.cy i + τ * q ∧ ∑ j ∈ I, m j * F.cz j = F.cz i + τ * r) :
    IsRupert (Finset.univ.image x) := by
  classical
  obtain ⟨N, hN⟩ := F.exists_normal a1 a2 a3
  have hNpt : ∀ a b c : ℝ, ⟪N, x 0 + a • (x 3 - x 0) + b • (x 5 - x 0) + c • F.e⟫ =
      ⟪N, x 0⟫ + (a1 * a + a2 * b + a3 * c) := by
    intro a b c
    rw [show x 0 + a • (x 3 - x 0) + b • (x 5 - x 0) + c • F.e =
      x 0 + (a • (x 3 - x 0) + b • (x 5 - x 0) + c • F.e) by abel, inner_add_right, hN]
  set W : Finset ℝ³ := I.image x with hW
  have hWV : W ⊆ Finset.univ.image x := Finset.image_subset_image (Finset.subset_univ _)
  have hWN : ∀ w ∈ W, ⟪N, w⟫ = ⟪N, x 0⟫ + c0 := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    rw [F.x_eq j, hNpt, hplane j hj]
  have hind3 : AffineIndependent ℝ ![x j0, x j1, x j2] := by
    refine affineIndependent_of_pair fun s t hst => hind s t ?_ ?_ ?_ |> fun h => h
    all_goals
      have e : s • (x j1 - x j0) + t • (x j2 - x j0) =
          (s * (F.cx j1 - F.cx j0) + t * (F.cx j2 - F.cx j0)) • (x 3 - x 0) +
          (s * (F.cy j1 - F.cy j0) + t * (F.cy j2 - F.cy j0)) • (x 5 - x 0) +
          (s * (F.cz j1 - F.cz j0) + t * (F.cz j2 - F.cz j0)) • F.e := by
        rw [F.x_eq j1, F.x_eq j0, F.x_eq j2]; module
      rw [e] at hst
      have := F.coord_zero hst
    · exact this.1
    · exact this.2.1
    · exact this.2.2
  have hu0 : ⟪N, p • (x 3 - x 0) + q • (x 5 - x 0) + r • F.e⟫ ≠ 0 := by
    rw [hN]; exact hnp
  refine isRupert_of_crossing (Finset.univ.image x) W hWV N (⟪N, x 0⟫ + c0) hWN
    (a := x j0) (b := x j1) (d := x j2) (Finset.mem_image_of_mem x h0)
    (Finset.mem_image_of_mem x h1) (Finset.mem_image_of_mem x h2) hind3
    (p • (x 3 - x 0) + q • (x 5 - x 0) + r • F.e) hu0 ?_
  intro v hv hvW
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
  have hi : i ∉ I := fun h => hvW (Finset.mem_image_of_mem x h)
  obtain ⟨τ, m, hm, hm1, hcx, hcy, hcz⟩ := hcross i hi
  have hinv : ∀ j, Function.invFun x (x j) = j := Function.leftInverse_invFun hx
  refine ⟨τ, fun w => m (Function.invFun x w), ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    simp only [hinv]
    exact hm j hj
  · rw [hW, Finset.sum_image hx.injOn]
    simp only [hinv]
    exact hm1
  · rw [hW, Finset.sum_image hx.injOn]
    simp only [hinv]
    have key : ∑ j ∈ I, m j • x j = (∑ j ∈ I, m j) • x 0 +
        (∑ j ∈ I, m j * F.cx j) • (x 3 - x 0) + (∑ j ∈ I, m j * F.cy j) • (x 5 - x 0) +
        (∑ j ∈ I, m j * F.cz j) • F.e := by
      simp only [Finset.sum_smul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [F.x_eq j]; module
    rw [key, hm1, hcx, hcy, hcz, F.x_eq i]
    module

end Frame09

/-! ### Positive weights in the two quads -/

/-- Weights in the upper-left quad `0, 1, 3, 4` of `F1` (coordinates `(X, Z)`, vertices
`(0,0)`, `(t+,h+)`, `(1,0)`, `(t-,-h-)`): the generic core. -/
lemma weights_core {tp tm hp hm X Z u0 l0 : ℝ} (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm)
    (htm1 : tm < 1) (hhp : 0 < hp) (hhm : 0 < hm) (hu0 : 0 ≤ u0) (hl0 : 0 ≤ l0)
    (hZ : hp * u0 - hm * l0 = Z) (h3 : tp * u0 + tm * l0 < X)
    (h0 : (1 - tp) * u0 + (1 - tm) * l0 < 1 - X) :
    ∃ m0 m1 m3 m4 : ℝ, 0 < m0 ∧ 0 < m1 ∧ 0 < m3 ∧ 0 < m4 ∧ m0 + m1 + m3 + m4 = 1 ∧
      m3 + tp * m1 + tm * m4 = X ∧ hp * m1 - hm * m4 = Z := by
  set A3 := X - (tp * u0 + tm * l0) with hA3
  set A0 := 1 - X - ((1 - tp) * u0 + (1 - tm) * l0) with hA0
  have hA3p : 0 < A3 := by rw [hA3]; linarith
  have hA0p : 0 < A0 := by rw [hA0]; linarith
  set c3 := tp * hm + tm * hp with hc3
  set c0 := (1 - tp) * hm + (1 - tm) * hp with hc0
  have hc3p : 0 < c3 := by rw [hc3]; positivity
  have hc0p : 0 < c0 := by
    rw [hc0]; have := sub_pos.2 htp1; have := sub_pos.2 htm1; positivity
  have hD : 0 < A3 * c0 + A0 * c3 := by positivity
  set s := A3 * A0 / (2 * (A3 * c0 + A0 * c3)) with hs
  have hsp : 0 < s := by rw [hs]; positivity
  have hs3 : s * c3 < A3 := by
    rw [hs, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos hA3p (mul_pos hA0p hc3p), mul_pos (mul_pos hA3p hA3p) hc0p]
  have hs0 : s * c0 < A0 := by
    rw [hs, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos hA3p (mul_pos hA0p hc0p), mul_pos (mul_pos hA0p hA0p) hc3p]
  refine ⟨A0 - s * c0, u0 + hm * s, A3 - s * c3, l0 + hp * s, by linarith, by positivity,
    by linarith, by positivity, ?_, ?_, ?_⟩
  · rw [hA3, hA0, hc3, hc0]; ring
  · rw [hA3, hc3]; ring
  · rw [← hZ]; ring

/-- The open upper-left quad: `(X, Z)` strictly inside `F1`'s image. -/
def InQuad1 (S : Shape09) (X Z : ℝ) : Prop :=
  Z < S.ap * X ∧ Z < S.bp * (1 - X) ∧ -Z < S.am * X ∧ -Z < S.bm * (1 - X)

lemma quad1_weights (S : Shape09) {X Z : ℝ} (h : InQuad1 S X Z) :
    ∃ m0 m1 m3 m4 : ℝ, 0 < m0 ∧ 0 < m1 ∧ 0 < m3 ∧ 0 < m4 ∧ m0 + m1 + m3 + m4 = 1 ∧
      m3 + S.tp * m1 + S.tm * m4 = X ∧ S.hp * m1 - S.hm * m4 = Z := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have htp := S.tp_pos; have htp1 := S.tp_lt; have htm := S.tm_pos; have htm1 := S.tm_lt
  have hhp := S.hp_pos; have hhm := S.hm_pos
  have e1 := S.ap_mul; have e2 := S.bp_mul; have e3 := S.am_mul; have e4 := S.bm_mul
  rcases le_or_gt 0 Z with hZ | hZ
  · refine weights_core htp htp1 htm htm1 hhp hhm (u0 := Z / S.hp) (l0 := 0)
      (div_nonneg hZ hhp.le) le_rfl (by field_simp; ring) ?_ ?_
    · rw [mul_zero, add_zero, ← sub_pos]
      have : S.hp * X - S.tp * Z > 0 := by
        have := mul_lt_mul_of_pos_left h1 htp
        have e : S.tp * (S.ap * X) = S.hp * X := by rw [← e1]; ring
        linarith
      have : X - S.tp * (Z / S.hp) = (S.hp * X - S.tp * Z) / S.hp := by field_simp
      rw [this]; positivity
    · rw [mul_zero, add_zero, ← sub_pos]
      have : S.hp * (1 - X) - (1 - S.tp) * Z > 0 := by
        have := mul_lt_mul_of_pos_left h2 (sub_pos.2 htp1)
        have e : (1 - S.tp) * (S.bp * (1 - X)) = S.hp * (1 - X) := by rw [← e2]; ring
        linarith
      have : 1 - X - (1 - S.tp) * (Z / S.hp) = (S.hp * (1 - X) - (1 - S.tp) * Z) / S.hp := by
        field_simp
      rw [this]; positivity
  · refine weights_core htp htp1 htm htm1 hhp hhm (u0 := 0) (l0 := -Z / S.hm)
      le_rfl (div_nonneg (by linarith) hhm.le) (by field_simp; ring) ?_ ?_
    · rw [mul_zero, zero_add, ← sub_pos]
      have : S.hm * X - S.tm * (-Z) > 0 := by
        have := mul_lt_mul_of_pos_left h3 htm
        have e : S.tm * (S.am * X) = S.hm * X := by rw [← e3]; ring
        linarith
      have : X - S.tm * (-Z / S.hm) = (S.hm * X - S.tm * (-Z)) / S.hm := by field_simp
      rw [this]; positivity
    · rw [mul_zero, zero_add, ← sub_pos]
      have : S.hm * (1 - X) - (1 - S.tm) * (-Z) > 0 := by
        have := mul_lt_mul_of_pos_left h4 (sub_pos.2 htm1)
        have e : (1 - S.tm) * (S.bm * (1 - X)) = S.hm * (1 - X) := by rw [← e4]; ring
        linarith
      have : 1 - X - (1 - S.tm) * (-Z / S.hm) = (S.hm * (1 - X) - (1 - S.tm) * (-Z)) / S.hm := by
        field_simp
      rw [this]; positivity

/-- The open lower quad `3456` in the `(x, y)`-projection. -/
def InQuadL (S : Shape09) (X Y : ℝ) : Prop :=
  0 < X ∧ 0 < Y ∧ X + Y < 1 ∧ 1 < X / S.tm + Y / S.sm

lemma quadL_weights (S : Shape09) {X Y : ℝ} (h : InQuadL S X Y) :
    ∃ m3 m4 m5 m6 : ℝ, 0 < m3 ∧ 0 < m4 ∧ 0 < m5 ∧ 0 < m6 ∧ m3 + m4 + m5 + m6 = 1 ∧
      m3 + S.tm * m4 = X ∧ m5 + S.sm * m6 = Y := by
  obtain ⟨hX, hY, hs, hq⟩ := h
  have htm := S.tm_pos; have hsm := S.sm_pos
  set PQ := X / S.tm + Y / S.sm - X - Y with hPQ
  have hPQp : 1 - X - Y < PQ := by rw [hPQ]; linarith
  have hPQ0 : 0 < PQ := by linarith
  set ρ := (1 - X - Y) / PQ with hρ
  have hρ0 : 0 < ρ := div_pos (by linarith) hPQ0
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one hPQ0]; exact hPQp
  have key : ρ * PQ = 1 - X - Y := by rw [hρ]; field_simp
  refine ⟨X * (1 - ρ), ρ * X / S.tm, Y * (1 - ρ), ρ * Y / S.sm, by nlinarith, by positivity,
    by nlinarith, by positivity, ?_, ?_, ?_⟩
  · have : ρ * X / S.tm + ρ * Y / S.sm = ρ * (X / S.tm + Y / S.sm) := by ring
    nlinarith [key, this]
  · field_simp; ring
  · field_simp; ring

/-- The weight function on the four vertices of `F1`. -/
def mF1 (m0 m1 m3 m4 : ℝ) : Fin 7 → ℝ := fun j =>
  if j = 0 then m0 else if j = 1 then m1 else if j = 3 then m3 else m4

lemma exists_between6 {L1 L2 L3 U1 U2 U3 : ℝ} (h11 : L1 < U1) (h12 : L1 < U2) (h13 : L1 < U3)
    (h21 : L2 < U1) (h22 : L2 < U2) (h23 : L2 < U3) (h31 : L3 < U1) (h32 : L3 < U2)
    (h33 : L3 < U3) :
    ∃ γ, L1 < γ ∧ L2 < γ ∧ L3 < γ ∧ γ < U1 ∧ γ < U2 ∧ γ < U3 := by
  have key : max (max L1 L2) L3 < min (min U1 U2) U3 := by
    simp only [max_lt_iff, lt_min_iff]; tauto
  have a1 : L1 ≤ max (max L1 L2) L3 := (le_max_left _ _).trans (le_max_left _ _)
  have a2 : L2 ≤ max (max L1 L2) L3 := (le_max_right _ _).trans (le_max_left _ _)
  have a3 : L3 ≤ max (max L1 L2) L3 := le_max_right _ _
  have b1 : min (min U1 U2) U3 ≤ U1 := (min_le_left _ _).trans (min_le_left _ _)
  have b2 : min (min U1 U2) U3 ≤ U2 := (min_le_left _ _).trans (min_le_right _ _)
  have b3 : min (min U1 U2) U3 ≤ U3 := min_le_right _ _
  exact ⟨(max (max L1 L2) L3 + min (min U1 U2) U3) / 2, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith⟩

namespace Shape09
variable (S : Shape09)

/-- 27.17's proof: from the four inequalities, the views `u₀ = -α u₁ + u₂ - γ e`. -/
theorem exists_view_of_T5F1 (hT : S.T5F1) :
    ∃ α γ : ℝ, InQuad1 S α γ ∧ InQuad1 S (S.sp * α) (S.kp + S.sp * γ) ∧
      InQuad1 S (S.sm * α) (-S.km + S.sm * γ) := by
  obtain ⟨α, hα1, hα2, hα3, hα4⟩ := hT
  have hA1 : 0 < S.A1 := add_pos S.ap_pos S.am_pos
  have hB1 : 0 < S.B1 := add_pos S.bp_pos S.bm_pos
  have hA2 : 0 < S.A2 := add_pos S.cp_pos S.cm_pos
  have eA1 : S.A1 = S.ap + S.am := rfl
  have eA2 : S.A2 = S.cp + S.cm := rfl
  have eB1 : S.B1 = S.bp + S.bm := rfl
  have em0 := S.em_eq
  have hep := S.ep_eq
  have hepp := S.ep_pos
  have hsp := S.sp_pos; have hsm := S.sm_pos; have hsp1 := S.sp_lt; have hsm1 := S.sm_lt
  have hap := S.ap_pos; have ham := S.am_pos; have hbp := S.bp_pos; have hbm := S.bm_pos
  have hcp := S.cp_pos; have hcm := S.cm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have hcm_eq : S.cm = S.bm / S.sm - S.bm := by
    field_simp; linarith [S.cm_mul']
  have hbsp : S.bp / S.sp * S.sp = S.bp := S.bsp_mul
  have hbsm : S.bm / S.sm * S.sm = S.bm := by field_simp
  have cpm := S.cp_mul; have cmm := S.cm_mul
  have hα0 : 0 < α := lt_trans (div_pos hA2 hA1) hα1
  have hα1' : S.A2 < α * S.A1 := (div_lt_iff₀ hA1).1 hα1
  rw [em0, add_zero] at hα2
  have hα2' : S.ep < (1 - α) * S.B1 := by
    have : S.ep / S.B1 < 1 - α := by linarith
    exact (div_lt_iff₀ hB1).1 this
  rw [em0, sub_zero] at hα4
  have hαlt : α < 1 := by
    have h := lt_trans hepp hα2'
    have := (pos_iff_pos_of_mul_pos h).2 hB1
    linarith
  rw [eB1] at hα2'
  have hprod : 0 < (1 - α) * (S.bp + S.bm) := mul_pos (sub_pos.2 hαlt) (add_pos hbp hbm)
  rw [eA1, eA2] at hα1'
  obtain ⟨γ, l1, l2, l3, u1, u2, u3⟩ := exists_between6
    (L1 := S.cm - S.am * α) (L2 := S.bm * α - S.bm) (L3 := S.bm * α - S.bm / S.sm + S.cm)
    (U1 := S.ap * α - S.cp) (U2 := S.bp * (1 - α)) (U3 := S.bp / S.sp - S.bp * α - S.cp)
    (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)
  refine ⟨α, γ, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · have := mul_lt_mul_of_pos_left u1 hsp; linarith
  · have := mul_lt_mul_of_pos_left u3 hsp; linarith
  · have := mul_lt_mul_of_pos_left l1 hsp; linarith [mul_pos hsp hcm]
  · have := mul_lt_mul_of_pos_left l2 hsp; linarith [mul_pos (sub_pos.2 hsp1) hbm]
  · have := mul_lt_mul_of_pos_left u1 hsm; linarith [mul_pos hsm hcp]
  · have := mul_lt_mul_of_pos_left u2 hsm; linarith [mul_pos (sub_pos.2 hsm1) hbp]
  · have := mul_lt_mul_of_pos_left l1 hsm; linarith
  · have := mul_lt_mul_of_pos_left l3 hsm; linarith

lemma f1_eq : S.f1 = S.hp + S.bm * (1 - S.tp) := by
  unfold f1; have := S.bp_mul; linarith

lemma f2_eq : S.f2 = S.kp + S.bm * (1 - S.sp) := by
  unfold f2; have := S.dp_mul; linarith

/-- 27.57's inequalities: the views `u₀ = w₁ u₁ + w₂ u₂ + (b-(w₁ + w₂) - 1) e`. -/
theorem exists_view_of_Q3456 (hQ : S.Q3456) :
    ∃ w1 w2 : ℝ, InQuadL S (S.bm * w1) (S.bm * w2) ∧
      InQuadL S (S.tp + S.f1 * w1) (S.f1 * w2) ∧ InQuadL S (S.f2 * w1) (S.sp + S.f2 * w2) := by
  obtain ⟨w1, w2, hw1, hw2, hM, hN⟩ := hQ
  have htm := S.tm_pos; have hsm := S.sm_pos; have htp := S.tp_pos; have hsp := S.sp_pos
  have hbm := S.bm_pos; have hf1 := S.f1_pos; have hf2 := S.f2_pos
  have M1 : w1 + w2 < 1 / S.bm := lt_of_lt_of_le hM (min_le_left _ _)
  have M2 : w1 + w2 < (1 - S.tp) / S.f1 :=
    lt_of_lt_of_le hM ((min_le_right _ _).trans (min_le_left _ _))
  have M3 : w1 + w2 < (1 - S.sp) / S.f2 :=
    lt_of_lt_of_le hM ((min_le_right _ _).trans (min_le_right _ _))
  have N1 : 1 / S.bm < w1 / S.tm + w2 / S.sm := lt_of_le_of_lt (le_max_left _ _) hN
  have N2 : (1 - S.tp / S.tm) / S.f1 < w1 / S.tm + w2 / S.sm :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hN
  have N3 : (1 - S.sp / S.sm) / S.f2 < w1 / S.tm + w2 / S.sm :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hN
  rw [lt_div_iff₀ hbm] at M1
  rw [lt_div_iff₀ hf1] at M2
  rw [lt_div_iff₀ hf2] at M3
  rw [div_lt_iff₀ hbm] at N1
  rw [div_lt_iff₀ hf1] at N2
  rw [div_lt_iff₀ hf2] at N3
  have htp1 := S.tp_lt; have hsp1 := S.sp_lt
  refine ⟨w1, w2, ⟨by positivity, by positivity, by linarith, ?_⟩,
    ⟨by positivity, by positivity, by linarith, ?_⟩, ⟨by positivity, by positivity, by linarith, ?_⟩⟩
  · have : S.bm * w1 / S.tm + S.bm * w2 / S.sm = (w1 / S.tm + w2 / S.sm) * S.bm := by ring
    rw [this]; linarith
  · have : (S.tp + S.f1 * w1) / S.tm + S.f1 * w2 / S.sm =
        S.tp / S.tm + (w1 / S.tm + w2 / S.sm) * S.f1 := by ring
    rw [this]; linarith
  · have : S.f2 * w1 / S.tm + (S.sp + S.f2 * w2) / S.sm =
        S.sp / S.sm + (w1 / S.tm + w2 / S.sm) * S.f2 := by ring
    rw [this]; linarith

end Shape09

namespace Frame09
variable {x : Fin 7 → ℝ³} (F : Frame09 x)

lemma cross_F1 (i : Fin 7) {τ p q r X Z : ℝ} (hq : F.cy i + τ * q = 0)
    (hX : F.cx i + τ * p = X) (hZ : F.cz i + τ * r = Z) (hin : InQuad1 F.S X Z) :
    ∃ (τ : ℝ) (m : Fin 7 → ℝ), (∀ j ∈ ({0, 1, 3, 4} : Finset (Fin 7)), 0 < m j) ∧
      ∑ j ∈ ({0, 1, 3, 4} : Finset (Fin 7)), m j = 1 ∧
      ∑ j ∈ ({0, 1, 3, 4} : Finset (Fin 7)), m j * F.cx j = F.cx i + τ * p ∧
      ∑ j ∈ ({0, 1, 3, 4} : Finset (Fin 7)), m j * F.cy j = F.cy i + τ * q ∧
      ∑ j ∈ ({0, 1, 3, 4} : Finset (Fin 7)), m j * F.cz j = F.cz i + τ * r := by
  obtain ⟨m0, m1, m3, m4, p0, p1, p3, p4, hs, hxx, hzz⟩ := quad1_weights F.S hin
  refine ⟨τ, mF1 m0 m1 m3 m4, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> simp [mF1, p0, p1, p3, p4]
  · simp [Finset.sum_insert, mF1]; linarith
  · rw [hX]; simp [Finset.sum_insert, mF1, cx]; linarith
  · rw [hq]; simp [Finset.sum_insert, mF1, cy]
  · rw [hZ]; simp [Finset.sum_insert, mF1, cz]; linarith

/-- **Theorem 5 with `W = F1`, from a view** `u₀ = -α u₁ + u₂ - γ e` (27.17's proof): the three
points `x 5, x 2, x 6` land in the open quad of `F1`. -/
theorem rupert_of_F1_view (hx : Function.Injective x) (α γ : ℝ)
    (h5 : InQuad1 F.S α γ) (h2 : InQuad1 F.S (F.S.sp * α) (F.S.kp + F.S.sp * γ))
    (h6 : InQuad1 F.S (F.S.sm * α) (-F.S.km + F.S.sm * γ)) :
    IsRupert (Finset.univ.image x) := by
  classical
  refine F.rupert_crossing hx {0, 1, 3, 4} 0 1 3 (by decide) (by decide) (by decide) ?_
    0 1 0 0 (by intro j hj; fin_cases j <;> simp_all [cy]) (-α) 1 (-γ) (by norm_num) ?_
  · intro s t h1 h2 h3
    simp only [cx, cy, cz] at h1 h2 h3
    have := F.S.hp_pos
    simp at h1 h2 h3
    rcases h3 with h3 | h3
    · subst h3; constructor <;> linarith
    · linarith
  · intro i hi
    fin_cases i
    · exact absurd (by decide) hi
    · exact absurd (by decide) hi
    · exact F.cross_F1 2 (τ := -F.S.sp) (by simp [cy]) (by simp [cx]) (by simp [cz]) h2
    · exact absurd (by decide) hi
    · exact absurd (by decide) hi
    · exact F.cross_F1 5 (τ := -1) (by simp [cy]) (by simp [cx]) (by simp [cz]) h5
    · exact F.cross_F1 6 (τ := -F.S.sm) (by simp [cy]) (by simp [cx]) (by simp [cz]) h6

/-- **Theorem 5 with `W` the lower quad `3456`** (27.57), the cross lemma. -/
lemma cross_L (i : Fin 7) {τ p q r X Y : ℝ} (hX : F.cx i + τ * p = X)
    (hY : F.cy i + τ * q = Y) (hZ : F.cz i + τ * r = -F.S.bm * (1 - X - Y))
    (hin : InQuadL F.S X Y) :
    ∃ (τ : ℝ) (m : Fin 7 → ℝ), (∀ j ∈ ({3, 4, 5, 6} : Finset (Fin 7)), 0 < m j) ∧
      ∑ j ∈ ({3, 4, 5, 6} : Finset (Fin 7)), m j = 1 ∧
      ∑ j ∈ ({3, 4, 5, 6} : Finset (Fin 7)), m j * F.cx j = F.cx i + τ * p ∧
      ∑ j ∈ ({3, 4, 5, 6} : Finset (Fin 7)), m j * F.cy j = F.cy i + τ * q ∧
      ∑ j ∈ ({3, 4, 5, 6} : Finset (Fin 7)), m j * F.cz j = F.cz i + τ * r := by
  obtain ⟨m3, m4, m5, m6, p3, p4, p5, p6, hs, hxx, hyy⟩ := quadL_weights F.S hin
  refine ⟨τ, fun j => if j = 3 then m3 else if j = 4 then m4 else if j = 5 then m5 else m6,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> simp [p3, p4, p5, p6]
  · simp [Finset.sum_insert]; linarith
  · rw [hX]; simp [Finset.sum_insert, cx]; linarith
  · rw [hY]; simp [Finset.sum_insert, cy]; linarith
  · rw [hZ]; simp [Finset.sum_insert, cz]
    have h1 := F.S.bm_mul; have h2 := F.S.km_eq
    rw [← h1, h2]
    linear_combination (-F.S.bm) * hs + F.S.bm * hxx + F.S.bm * hyy

theorem rupert_of_lower_view (hx : Function.Injective x) (w1 w2 : ℝ)
    (h0 : InQuadL F.S (F.S.bm * w1) (F.S.bm * w2))
    (h1 : InQuadL F.S (F.S.tp + F.S.f1 * w1) (F.S.f1 * w2))
    (h2 : InQuadL F.S (F.S.f2 * w1) (F.S.sp + F.S.f2 * w2)) :
    IsRupert (Finset.univ.image x) := by
  classical
  have hbm := F.S.bm_pos
  have hbmul := F.S.bm_mul
  have hkm := F.S.km_eq
  refine F.rupert_crossing hx {3, 4, 5, 6} 3 4 5 (by decide) (by decide) (by decide) ?_
    (-F.S.bm) (-F.S.bm) 1 (-F.S.bm) ?_ w1 w2 (F.S.bm * (w1 + w2) - 1) ?_ ?_
  · intro s t h1 h2 h3
    simp only [cx, cy, cz] at h1 h2 h3
    simp at h1 h2 h3
    have ht : t = 0 := by linarith
    subst ht
    have := F.S.tm_lt
    constructor
    · nlinarith
    · rfl
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> simp [cx, cy, cz] <;> linarith
  · intro h; have : (-F.S.bm * w1 + -F.S.bm * w2 + 1 * (F.S.bm * (w1 + w2) - 1)) = -1 := by ring
    rw [this] at h; norm_num at h
  · intro i hi
    fin_cases i
    · exact F.cross_L 0 (τ := F.S.bm) (by simp [cx]) (by simp [cy]) (by simp [cz]; ring) h0
    · refine F.cross_L 1 (τ := F.S.f1) (by simp [cx]) (by simp [cy]) ?_ h1
      simp only [cz]; simp
      rw [F.S.f1_eq]; ring
    · refine F.cross_L 2 (τ := F.S.f2) (by simp [cx]) (by simp [cy]) ?_ h2
      simp only [cz]; simp
      rw [F.S.f2_eq]; ring
    all_goals exact absurd (by decide) hi

/-- **Theorem 5 with `W = F1`** (27.17; the needed direction): `T5F1` gives a Rupert set. -/
theorem rupert_of_T5F1 (hx : Function.Injective x) (hT : F.S.T5F1) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨α, γ, h5, h2, h6⟩ := F.S.exists_view_of_T5F1 hT
  exact F.rupert_of_F1_view hx α γ h5 h2 h6

/-- **Theorem 5 with `W` the lower quad `3456`** (27.57): `Q3456` gives a Rupert set. -/
theorem rupert_of_Q3456 (hx : Function.Injective x) (hQ : F.S.Q3456) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨w1, w2, h0, h1, h2⟩ := F.S.exists_view_of_Q3456 hQ
  exact F.rupert_of_lower_view hx w1 w2 h0 h1 h2

/-- **The three crossing tests of item 3 (not proved here; hypotheses).**  The Rupert
implications of Corollary 27.29 (row `A^M`, a pair of edge crossings at `m2+`, Theorem 24.3),
Theorem 27.31 (the edge crossing at `xa xb` on the folded plane, type 09) and Proposition 27.32's
`M`-image (`c+ > b-`, one edge crossing), each with its special positions as explicit hypotheses.
They need `ManyTies.TiltTest`s (realizing tilts, `TiltSign` determinants for every other vertex)
and the metric-free unimodality of their rims at the frame's Gram metric. -/
structure Tests09 (F : Frame09 x) : Prop where
  /-- 27.29, row `A^M`. -/
  am : F.S.AM → IsRupert (Finset.univ.image x)
  /-- 27.31 for type 09 (the case `t- ≥ s-` or `a+ ≤ c+`), off the special positions
  `t- = s-`, `a+ = c+`. -/
  t31 : F.S.tm ≠ F.S.sm → F.S.ap ≠ F.S.cp → (¬ F.S.tm < F.S.sm ∨ ¬ F.S.cp < F.S.ap) →
    IsRupert (Finset.univ.image x)
  /-- 27.32's `M`-image (`c+ > d- = b-`), off the special position `c+ = b-`. -/
  t32 : F.S.cp ≠ F.S.bm → ¬ F.S.cp < F.S.bm → IsRupert (Finset.univ.image x)

/-- **In the frame, off the special positions, either `V` is Rupert or the five conditions of
Theorem 27.48 hold** (27.58, with the tests of item 3 as the hypotheses `T`). -/
theorem rupert_or_27_48 (hx : Function.Injective x) (T : Tests09 F)
    (sp0 : F.S.tm ≠ F.S.sm) (sp4 : F.S.ap ≠ F.S.cp) (sp5 : F.S.cp ≠ F.S.bm)
    (sp1 : F.S.am ≠ F.S.bp) (sp2 : F.S.am ≠ F.S.dp) (sp3 : F.S.bp ≠ F.S.sp * F.S.A2) :
    IsRupert (Finset.univ.image x) ∨
      (F.S.tm < F.S.sm ∧ F.S.bp < F.S.am ∧ F.S.am < F.S.dp ∧ F.S.cm < F.S.dp ∧
        F.S.bp < F.S.sp * F.S.A2) := by
  by_cases hts : F.S.tm < F.S.sm
  swap
  · exact Or.inl (T.t31 sp0 sp4 (Or.inl hts))
  by_cases hca : F.S.cp < F.S.ap
  swap
  · exact Or.inl (T.t31 sp0 sp4 (Or.inr hca))
  by_cases hcb : F.S.cp < F.S.bm
  swap
  · exact Or.inl (T.t32 sp5 hcb)
  by_cases hAM : F.S.AM
  · exact Or.inl (T.am hAM)
  by_cases hT5 : F.S.T5F1
  · exact Or.inl (F.rupert_of_T5F1 hx hT5)
  by_cases hQ : F.S.Q3456
  · exact Or.inl (F.rupert_of_Q3456 hx hQ)
  exact Or.inr (F.S.thm_27_58 hts hca hcb hAM hT5 hQ sp1 sp2 sp3)

end Frame09

end Minimality.CaseC09
