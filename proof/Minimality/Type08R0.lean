module

public import Minimality.Type08Rd

@[expose] public section

/-!
# Type 08: Lemma R0 of A.10 (`FEWER-FACES-PROOFS.md` §10 addendum)

Theorem R (`Type08Rd.lean`) takes the conditions (H1)–(H4) of A.10 as the hypothesis
`RdRim`.  Lemma R0 derives them on `R_d`: the named closing `K_v` (rim `v f g_f g_v` at the
view `u = v − w` along the axle `w → v`) has no weak saddle and the other closing `K_w`
(`w f g_f g_v`) has one, the far edge `g = [g_v, g_f]` is parallel to the realizing face
`F_j ∋ w, v, f`, not parallel to the chord `[v, f]`, and carries a horizontal double normal
perpendicular to `F_j` from the open chord `(v, f)` to the open edge `(g_v, g_f)`, and the
five-corner rim `v m f g_f g_v` (with the middle `m` of `F_j` over the chord `[v, f]`) has
distinct depths and is not strictly unimodal (`RdCond`).

* `IsFrame.decomp`, `IsFrame.inner_eq`, `IsFrame.det3_T`, `IsFrame.det3_eq`,
  `exists_rdFrame`: orthonormal frames, and the frame of A.10 (`T` along the axle, `N`
  normal to `F_j`, `s_f > 0`, `g` at `ν = −h < 0`).
* `two_peaks`, `rd_depths` (**(H1)**): `m` and `g_v` are the two peaks and
  `t_m, t₁ > 0 > t_f, t₂`, from the unimodal `K_v`, the weak saddle of `K_w` with the claim
  of Lemma 9.3 (one weighted inequality `A z_w + B z_{g_f} < C z_f + E z_{g_v}`,
  `A + B = C + E`), `m` over the chord, and the foot of the double normal.
* `rd_coords` (**(H2)**, and (H4) in the form `D(v) > 0 > D(f)`), in coordinates.
* `RdCond`, `rdRim_of_R0` (**Lemma R0**, abstract form): with also the face `Φ ∋ m, f, g_f`
  (an affine function vanishing there and negative at `v`, `g_v`: (H2)) and `g_v`, `w`
  weakly on one side of the plane `v f g_f` ((H4); strictly, since `g ∦ [v, f]`), `RdRim`
  holds.
* `quad_edge_claim`, `t4_claim`: the claims of Lemmas 9.3 and 5 as one weighted inequality.
* `isRupert_quad_edge_middle_rdCond` (N2–`K_c`) and `isRupert_t4b_rdCond` (T4–`K_b`):
  Lemma R0 with Theorem R for the two closings of A.10's table; `Φ` is `Q_ab`, resp.
  `a'b'c`.
* `type08_rd_sides` ((H4) from Lemma 9.7 / (T2), `κ_a > 0`): `b'`, `a'` on one side of the
  plane `c b c'` (N2) and `a'`, `c'` on opposite sides of the plane `b c b'` (T4; with the
  convex `Q_bc`, `d` and `c'` on one side).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Orthonormal frames -/

/-- The decomposition of a vector in an orthonormal frame. -/
theorem IsFrame.decomp {S T N : ℝ³} (h : IsFrame S T N) (x : ℝ³) :
    x = ⟪x, S⟫ • S + ⟪x, T⟫ • T + ⟪x, N⟫ • N := by
  have hA : orthoFrameMat S T N ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
    (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mpr h.mul_transpose
  have hAA := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hA
  have E := fun j k => congrFun (congrFun hAA j) k
  have e00 : S 0 * S 0 + T 0 * T 0 + N 0 * N 0 = 1 := by
    have := E 0 0; simp [orthoFrameMat, Matrix.mul_apply, Fin.sum_univ_three] at this; linarith
  have e01 : S 0 * S 1 + T 0 * T 1 + N 0 * N 1 = 0 := by
    have := E 0 1; simp [orthoFrameMat, Matrix.mul_apply, Fin.sum_univ_three] at this; linarith
  have e02 : S 0 * S 2 + T 0 * T 2 + N 0 * N 2 = 0 := by
    have := E 0 2; simp [orthoFrameMat, Matrix.mul_apply, Fin.sum_univ_three] at this; linarith
  have e11 : S 1 * S 1 + T 1 * T 1 + N 1 * N 1 = 1 := by
    have := E 1 1; simp [orthoFrameMat, Matrix.mul_apply, Fin.sum_univ_three] at this; linarith
  have e12 : S 1 * S 2 + T 1 * T 2 + N 1 * N 2 = 0 := by
    have := E 1 2; simp [orthoFrameMat, Matrix.mul_apply, Fin.sum_univ_three] at this; linarith
  have e22 : S 2 * S 2 + T 2 * T 2 + N 2 * N 2 = 1 := by
    have := E 2 2; simp [orthoFrameMat, Matrix.mul_apply, Fin.sum_univ_three] at this; linarith
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply, Fin.sum_univ_three,
    RCLike.inner_apply, conj_trivial]
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
  · linear_combination (-(x 0)) * e00 - x 1 * e01 - x 2 * e02
  · linear_combination (-(x 0)) * e01 - x 1 * e11 - x 2 * e12
  · linear_combination (-(x 0)) * e02 - x 1 * e12 - x 2 * e22

/-- Parseval in an orthonormal frame. -/
theorem IsFrame.inner_eq {S T N : ℝ³} (h : IsFrame S T N) (a b : ℝ³) :
    ⟪a, b⟫ = ⟪a, S⟫ * ⟪b, S⟫ + ⟪a, T⟫ * ⟪b, T⟫ + ⟪a, N⟫ * ⟪b, N⟫ := by
  conv_lhs => rw [h.decomp b]
  simp only [inner_add_right, real_inner_smul_right]
  ring

theorem inner_smul_self_inv_norm {x : ℝ³} (hx : x ≠ 0) : ⟪‖x‖⁻¹ • x, ‖x‖⁻¹ • x⟫ = 1 := by
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp

/-- **A frame for `R_d`**: `T = u / ‖u‖`, `N` normal to `u` and `w` (a multiple of
`u × w`, oriented so that `P` is on its negative side), and `S` the unit vector in the plane
of `u`, `w` orthogonal to `u` with `⟪w, S⟫ > 0`. -/
theorem exists_rdFrame {u w P : ℝ³} (hP : det3 u w P ≠ 0) :
    ∃ S N : ℝ³, IsFrame S (‖u‖⁻¹ • u) N ∧ 0 < ⟪w, S⟫ ∧ ⟪u, S⟫ = 0 ∧
      ∃ r : ℝ, r ≠ 0 ∧ (∀ X, ⟪X, N⟫ = r * det3 u w X) ∧ ⟪P, N⟫ < 0 := by
  have hdet : ∀ a b c : ℝ³, det3 a b c = ⟪cross a b, c⟫ := fun _ _ _ => rfl
  have hu : u ≠ 0 := by
    rintro rfl; apply hP; simp [det3_expand]
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu
  set n := cross u w with hn
  have hnX : ∀ X, ⟪X, n⟫ = det3 u w X := fun X => by rw [real_inner_comm]; rfl
  have hn0 : n ≠ 0 := by
    intro h0; apply hP; rw [← hnX, h0, inner_zero_right]
  have hnu : ⟪u, n⟫ = 0 := by rw [hnX]; simp only [det3_expand]; ring
  have hnw : ⟪w, n⟫ = 0 := by rw [hnX]; simp only [det3_expand]; ring
  set k := ⟪w, u⟫ / ⟪u, u⟫ with hk
  set q := w - k • u with hq
  have hqu : ⟪q, u⟫ = 0 := by
    rw [hq, inner_sub_left, real_inner_smul_left, hk]; field_simp; ring
  have hq0 : q ≠ 0 := by
    intro h0
    have : w = k • u := by rw [← sub_eq_zero]; exact h0
    apply hP; rw [this]; simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring
  have hqn : ⟪q, n⟫ = 0 := by rw [hq, inner_sub_left, real_inner_smul_left, hnw, hnu]; ring
  -- the orientation of `N`
  obtain ⟨σ, hσ, hσP⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ σ * det3 u w P < 0 := by
    rcases lt_or_gt_of_ne hP with h | h
    · exact ⟨1, Or.inl rfl, by linarith⟩
    · exact ⟨-1, Or.inr rfl, by linarith⟩
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hnn : ‖n‖ ≠ 0 := norm_ne_zero_iff.mpr hn0
  have hqq : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq0
  have hun : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  refine ⟨‖q‖⁻¹ • q, (σ * ‖n‖⁻¹) • n, ⟨inner_smul_self_inv_norm hq0, inner_smul_self_inv_norm hu,
    ?_, ?_, ?_, ?_⟩, ?_, ?_, σ * ‖n‖⁻¹, mul_ne_zero (by rcases hσ with rfl | rfl <;> norm_num)
      (inv_ne_zero hnn), fun X => ?_, ?_⟩
  · rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp; linear_combination hσσ
  · rw [real_inner_smul_left, real_inner_smul_right, hqu]; ring
  · rw [real_inner_smul_left, real_inner_smul_right, hqn]; ring
  · rw [real_inner_smul_left, real_inner_smul_right, hnu]; ring
  · have : ⟪w, q⟫ = ⟪q, q⟫ := by
      have hw : w = q + k • u := by rw [hq]; abel
      conv_lhs => rw [hw]
      rw [inner_add_left, real_inner_smul_left, real_inner_comm q u, hqu]; ring
    rw [real_inner_smul_right, this]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hq0)) (real_inner_self_pos.mpr hq0)
  · rw [real_inner_smul_right, real_inner_comm, hqu, mul_zero]
  · rw [real_inner_smul_right, hnX]
  · rw [real_inner_smul_right, hnX, mul_comm σ, mul_assoc]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr (norm_pos_iff.mpr hn0)) hσP

/-! ### (H1): the depths -/

/-- A cyclic sequence of five distinct depths that is not strictly unimodal has two
strict local maxima. -/
theorem two_peaks {z : ZMod 5 → ℝ} (hinj : Function.Injective z) (h : ¬ StrictUnimodal z) :
    ∃ i j : ZMod 5, i ≠ j ∧ (z (i - 1) < z i ∧ z (i + 1) < z i) ∧
      (z (j - 1) < z j ∧ z (j + 1) < z j) := by
  classical
  have hne : ∀ i : ZMod 5, z i ≠ z (i + 1) := by
    intro i hi
    have key : ∀ i : ZMod 5, i ≠ i + 1 := by decide
    exact key i (hinj hi)
  have hcard : (univ.filter fun i => z (i - 1) < z i ∧ z (i + 1) < z i).card ≠ 1 :=
    fun hc => h ⟨hne, hc⟩
  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image (univ : Finset (ZMod 5)) z univ_nonempty
  have hi₀ : i₀ ∈ univ.filter fun i => z (i - 1) < z i ∧ z (i + 1) < z i := by
    simp only [mem_filter, mem_univ, true_and]
    have h1 : i₀ - 1 ≠ i₀ := (by decide : ∀ i : ZMod 5, i - 1 ≠ i) i₀
    have h2 : i₀ + 1 ≠ i₀ := (by decide : ∀ i : ZMod 5, i + 1 ≠ i) i₀
    exact ⟨lt_of_le_of_ne (hmax _ (mem_univ _)) (fun e => h1 (hinj e)),
      lt_of_le_of_ne (hmax _ (mem_univ _)) (fun e => h2 (hinj e))⟩
  have h2 : 1 < (univ.filter fun i => z (i - 1) < z i ∧ z (i + 1) < z i).card := by
    have := Finset.card_pos.mpr ⟨i₀, hi₀⟩
    omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp h2
  simp only [mem_filter, mem_univ, true_and] at hi hj
  exact ⟨i, j, hij, hi, hj⟩

theorem quint_inner_eq (v m f gf gv u : ℝ³) :
    (fun i => ⟪quint v m f gf gv i, u⟫) = quint ⟪v, u⟫ ⟪m, u⟫ ⟪f, u⟫ ⟪gf, u⟫ ⟪gv, u⟫ := by
  funext i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **(H1) of Lemma R0, the depths.**  Depths `z` of `v, m, f, g_f, g_v` and of the other axle
end `w`: `m` lies over the chord `[v, f]` (`z_m = z_v + s (z_f − z_v) + D`, `0 < s < 1`,
`D > 0`), `K_v` (`v f g_f g_v`) has no weak saddle and `K_w` (`w f g_f g_v`) has one, the claim
of Lemma 9.3 holds (`A z_w + B z_{g_f} < C z_f + E z_{g_v}` with positive weights,
`A + B = C + E`), the five-corner rim `v m f g_f g_v` has distinct depths and is not
strictly unimodal, and the foot of the double normal is at one depth on the open chord
`(v, f)` and the open edge `(g_v, g_f)`.  Then `m` and `g_v` are the peaks of the rim
and `z_f, z_{g_f} < z_v`: `t_m, t₁ > 0 > t_f, t₂`. -/
theorem rd_depths {zv zm zf zgf zgv zw s D A B C E lam mu : ℝ}
    (hm : zm = zv + s * (zf - zv) + D) (hs0 : 0 < s) (hs1 : s < 1) (hD : 0 < D)
    (hNv : NWS4 (quad zv zf zgf zgv)) (hNw : ¬ NWS4 (quad zw zf zgf zgv))
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hE : 0 < E) (hsum : A + B = C + E)
    (hlow : A * zw + B * zgf < C * zf + E * zgv)
    (hinj : Function.Injective (quint zv zm zf zgf zgv))
    (h5 : ¬ StrictUnimodal (quint zv zm zf zgf zgv))
    (hl0 : 0 < lam) (hl1 : lam < 1) (hmu0 : 0 < mu) (hmu1 : mu < 1)
    (hcr : lam * (zf - zv) = (1 - mu) * (zgv - zv) + mu * (zgf - zv)) :
    zv < zm ∧ zf < zm ∧ zv < zgv ∧ zgf < zgv ∧ zf < zv ∧ zgf < zv := by
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3] at hNv hNw
  -- `m` is not a valley
  have hval : ¬ (zm < zv ∧ zm < zf) := by
    rintro ⟨h1, h2⟩
    nlinarith [mul_pos hs0 (sub_pos.mpr h2), mul_pos (sub_pos.mpr hs1) (sub_pos.mpr h1)]
  have hfv : zm < zf → zv < zf := by
    intro h; by_contra hc; push Not at hc
    nlinarith [mul_nonneg (sub_pos.mpr hs1).le (sub_nonneg.mpr hc)]
  have hvf : zm < zv → zf < zv := by
    intro h; by_contra hc; push Not at hc
    nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hc)]
  -- `g_f` is not a peak (`K_w` has a weak saddle, and the claim)
  have hgf : ¬ (zf < zgf ∧ zgv < zgf) := by
    rintro ⟨h1, h2⟩
    have hw : zf ≤ zw ∧ zgv ≤ zw := by
      by_contra hc
      simp only [not_and_or, not_le] at hc
      exact hNw ⟨by rcases hc with h | h <;> simp [h], Or.inr (Or.inr (Or.inl h1))⟩
    rcases le_total zf zgv with h | h
    · have := congrArg (fun t => t * zgv) hsum
      linarith [mul_le_mul_of_nonneg_left hw.2 hA.le, mul_lt_mul_of_pos_left h2 hB,
        mul_le_mul_of_nonneg_left h hC.le]
    · have := congrArg (fun t => t * zf) hsum
      linarith [mul_le_mul_of_nonneg_left hw.1 hA.le, mul_lt_mul_of_pos_left h1 hB,
        mul_le_mul_of_nonneg_left h hE.le]
  -- the two peaks are `m` and `g_v`
  obtain ⟨i, j, hij, hi, hj⟩ := two_peaks hinj h5
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  obtain ⟨c0, c1, c2, c3, c4⟩ := zmod5_sub_one
  have hpk : zv < zm ∧ zf < zm ∧ zv < zgv ∧ zgf < zgv := by
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [b0, b1, b2, b3, b4, c0, c1, c2, c3, c4, quint_0, quint_1, quint_2, quint_3,
      quint_4] at hi hj <;>
    first
    | exact absurd rfl hij
    | (refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
    | (exfalso; apply hval; constructor <;> linarith)
    | (exfalso; apply hgf; constructor <;> linarith)
    | (exfalso; have := hfv (by linarith)
       rcases hNv.2 with h | h | h | h <;> linarith)
  obtain ⟨p1, p2, p3, p4⟩ := hpk
  -- the foot of the double normal: `z_f < z_v`, then `z_{g_f} < z_v`
  have hfv' : zf < zv := by
    rcases lt_or_gt_of_ne (show zf ≠ zv from fun e => absurd (@hinj 2 0 e) (by decide)) with h | h
    · exact h
    exfalso
    have hgf' : zf < zgf := by
      have hne : zf ≠ zgf := fun e => absurd (@hinj 2 3 e) (by decide)
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact h'
      · rcases hNv.2 with hh | hh | hh | hh <;> linarith
    nlinarith [mul_pos (sub_pos.mpr hl1) (sub_pos.mpr h), mul_nonneg hmu0.le (sub_pos.mpr hgf').le,
      mul_nonneg (sub_pos.mpr hmu1).le (sub_pos.mpr p4).le]
  refine ⟨p1, p2, p3, p4, hfv', ?_⟩
  nlinarith [mul_pos hl0 (sub_pos.mpr hfv'), mul_pos (sub_pos.mpr hmu1) (sub_pos.mpr p3)]

/-! ### (H2)–(H4) in coordinates -/

theorem det3_pt_e1 (a b c a' b' c' : ℝ) :
    det3 (pt a b c) (pt a' b' c') (pt 0 1 0) = c * a' - a * c' := by
  simp only [det3_expand, pt_zero, pt_one, pt_two]; ring

/-- Determinants against `T` in an orthonormal frame `S, T, N`. -/
theorem IsFrame.det3_T {S T N : ℝ³} (hF : IsFrame S T N) (X Y : ℝ³) :
    det3 X Y T = det3 S T N * (⟪X, N⟫ * ⟪Y, S⟫ - ⟪X, S⟫ * ⟪Y, N⟫) := by
  have h1 := det3_frameCoords S T N X Y T
  have hsq := hF.det3_sq
  obtain ⟨-, hTT, -, hST, -, hTN⟩ := hF
  rw [real_inner_comm S T, hST, hTT, hTN, det3_pt_e1] at h1
  linear_combination (-(det3 S T N)) * h1 - det3 X Y T * hsq

theorem det3_pt_rd₁ (a b c d k e f : ℝ) :
    det3 (pt a b 0) (pt c d k) (pt e f k) = k * (b * (e - c) + a * (d - f)) := by
  simp only [det3_expand, pt_zero, pt_one, pt_two]; ring

theorem det3_pt_rd₂ (a b c d k L : ℝ) :
    det3 (pt a b 0) (pt c d k) (pt 0 (-L) 0) = a * k * L := by
  simp only [det3_expand, pt_zero, pt_one, pt_two]; ring

theorem inner_foot {D a b c : ℝ³} {lam mu : ℝ} (h : D = lam • a - b - mu • (c - b)) (X : ℝ³) :
    ⟪D, X⟫ = lam * ⟪a, X⟫ - ⟪b, X⟫ - mu * (⟪c, X⟫ - ⟪b, X⟫) := by
  subst h; simp only [inner_sub_left, real_inner_smul_left]

/-- Determinants in an orthonormal frame. -/
theorem IsFrame.det3_eq {S T N : ℝ³} (hF : IsFrame S T N) (X Y Z : ℝ³) :
    det3 X Y Z = det3 S T N * det3 (pt ⟪X, S⟫ ⟪X, T⟫ ⟪X, N⟫) (pt ⟪Y, S⟫ ⟪Y, T⟫ ⟪Y, N⟫)
      (pt ⟪Z, S⟫ ⟪Z, T⟫ ⟪Z, N⟫) := by
  rw [det3_frameCoords, ← mul_assoc, hF.det3_sq, one_mul]

/-- **(H2) and (H4) of Lemma R0, in coordinates** (`v` the origin, depth `t`, the face
`F_j` at `ν = 0`, `g` at `ν = −h`).  The face `Φ` through `m`, `f`, `g_f` (the affine
function `c₀ + α s + β t + γ ν`, negative at `v` and `g_v`) gives `σ_mf < σ_g`; with
`σ_vf < σ_g` and the foot `y = λ f = g_v + μ (g_f − g_v)` of the double normal, `D(v) > 0`
and `D(f) < 0`. -/
theorem rd_coords {sm tm sf tf s1 t1 s2 t2 h lam mu c0 α β γ : ℝ}
    (hsm : 0 < sm) (hmf : sm < sf)
    (htm : 0 < tm) (htf : tf < 0)
    (hc0 : c0 < 0) (hΦm : c0 + α * sm + β * tm = 0) (hΦf : c0 + α * sf + β * tf = 0)
    (hΦ2 : c0 + α * s2 + β * t2 - γ * h = 0) (hΦ1 : c0 + α * s1 + β * t1 - γ * h < 0)
    (hH4 : tf * (s2 - s1) < sf * (t2 - t1))
    (hl0 : 0 < lam) (hl1 : lam < 1) (hcs : lam * sf = s1 + mu * (s2 - s1))
    (hct : lam * tf = t1 + mu * (t2 - t1)) :
    (tf - tm) * (s2 - s1) < (t2 - t1) * (sf - sm) ∧ 0 < s1 * t2 - s2 * t1 ∧
      (s2 - s1) * (tf - t1) < (t2 - t1) * (sf - s1) := by
  have e1 : α * (sf - sm) + β * (tf - tm) = 0 := by linear_combination hΦf - hΦm
  have hsf : 0 < sf := by linarith
  have hP : 0 < tm * sf - tf * sm := by
    have := mul_pos htm hsf
    have := mul_pos (neg_pos.mpr htf) hsm
    nlinarith
  have key1 : β * (tm * sf - tf * sm) = (sf - sm) * (-c0) := by
    linear_combination (sf - sm) * hΦm - sm * e1
  have hβ : 0 < β := by
    have : 0 < β * (tm * sf - tf * sm) := by rw [key1]; exact mul_pos (by linarith) (by linarith)
    exact pos_of_mul_pos_left this hP.le
  have key2 : (sf - sm) * (α * (s1 - s2) + β * (t1 - t2)) =
      β * ((tf - tm) * (s2 - s1) - (sf - sm) * (t2 - t1)) := by
    linear_combination (s1 - s2) * e1
  have hneg : (sf - sm) * (α * (s1 - s2) + β * (t1 - t2)) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · rw [key2] at hneg
    have := neg_of_mul_neg_right hneg hβ.le
    linarith
  · have : s1 * t2 - s2 * t1 = lam * (sf * (t2 - t1) - tf * (s2 - s1)) := by
      linear_combination (s2 - s1) * hct - (t2 - t1) * hcs
    rw [this]; exact mul_pos hl0 (by linarith)
  · have : (t2 - t1) * (sf - s1) - (s2 - s1) * (tf - t1) =
        (1 - lam) * (sf * (t2 - t1) - tf * (s2 - s1)) := by
      linear_combination (t2 - t1) * hcs - (s2 - s1) * hct
    nlinarith [mul_pos (sub_pos.mpr hl1) (show 0 < sf * (t2 - t1) - tf * (s2 - s1) by linarith)]

/-! ### Lemma R0 -/

/-- **The class `R_d`** of A.10 (off `Σ`) for the five-corner rim `v m f g_f g_v` at the view
along the axle `w → v`: the far edge `g = [g_v, g_f]` is parallel to the face `F_j` through
`w, v, f`; `g_v` is off the plane of `v, f, g_f` (the double normal below crosses
transversally); a horizontal double normal perpendicular to `F_j` joins an interior point of
the chord `[v, f]` to an interior point of `g`; and the five depths are distinct and not
strictly unimodal (a two-peaked rim). -/
def RdCond (v m f gf gv w : ℝ³) : Prop :=
  det3 (v - w) (f - v) (gf - gv) = 0 ∧ det3 (f - v) (gf - v) (gv - v) ≠ 0 ∧
  (∃ lam mu : ℝ, 0 < lam ∧ lam < 1 ∧ 0 < mu ∧ mu < 1 ∧
    ⟪v + lam • (f - v) - (gv + mu • (gf - gv)), v - w⟫ = 0 ∧
    ⟪v + lam • (f - v) - (gv + mu • (gf - gv)), f - v⟫ = 0) ∧
  Function.Injective (fun i => ⟪quint v m f gf gv i, v - w⟫) ∧
  ¬ StrictUnimodal (fun i => ⟪quint v m f gf gv i, v - w⟫)

set_option maxHeartbeats 1000000 in
/-- **Lemma R0 of A.10, abstract form.**  Let `m = v + s (f − v) + δ (v − w)` (`0 < s < 1`,
`δ > 0`: the middle of `F_j` over the chord `[v, f]`), let `g_v` be off `F_j`'s plane, and let
the rim of `K_v` run `v f g_f g_v` at the view `u = v − w` (one orientation of the triangle
tests at `v → f` and `g_f → g_v`).  Let `Φ` be a face through `m, f, g_f` with `v, g_v`
strictly beneath it, and let `g_v` and `w` lie weakly on one side of the plane `v f g_f`.  If
`K_v = v f g_f g_v` has no weak saddle, `K_w = w f g_f g_v` has one, the claim of Lemma 9.3
holds, and the point is in `R_d` (`RdCond`), then (H1)–(H4) hold: `RdRim`. -/
theorem rdRim_of_R0 {v m f gf gv w : ℝ³} {s δ : ℝ}
    (hm : m = v + s • (f - v) + δ • (v - w)) (hs0 : 0 < s) (hs1 : s < 1) (hδ : 0 < δ)
    (hoff : det3 (v - w) (f - v) (gv - v) ≠ 0)
    (horient : 0 < det3 (f - v) (gf - v) (v - w) * det3 (gv - gf) (v - gf) (v - w))
    (hΦ : ∃ (φ : ℝ³ → ℝ) (Nφ : ℝ³), (∀ y z, φ y - φ z = ⟪Nφ, y - z⟫) ∧ φ m = 0 ∧ φ f = 0 ∧
      φ gf = 0 ∧ φ v < 0 ∧ φ gv < 0)
    (hside : 0 ≤ det3 (f - v) (gf - v) (gv - v) * det3 (f - v) (gf - v) (w - v))
    (hNv : NWS4 (quad ⟪v, v - w⟫ ⟪f, v - w⟫ ⟪gf, v - w⟫ ⟪gv, v - w⟫))
    (hNw : ¬ NWS4 (quad ⟪w, v - w⟫ ⟪f, v - w⟫ ⟪gf, v - w⟫ ⟪gv, v - w⟫))
    (hlow : ∃ A B C E : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < E ∧ A + B = C + E ∧
      A * ⟪w, v - w⟫ + B * ⟪gf, v - w⟫ < C * ⟪f, v - w⟫ + E * ⟪gv, v - w⟫)
    (hR : RdCond v m f gf gv w) :
    RdRim v m f gf gv (v - w) := by
  obtain ⟨hpar, hcop, ⟨lam, mu, hl0, hl1, hmu0, hmu1, hD1, hD2⟩, hinj, h5⟩ := hR
  obtain ⟨φ, Nφ, hφ, φm, φf, φgf, φv, φgv⟩ := hΦ
  obtain ⟨A, B, C, E, hA, hB, hC, hE, hsum, hlo⟩ := hlow
  obtain ⟨u, rfl⟩ : ∃ u, w = v - u := ⟨v - w, by abel⟩
  simp only [sub_sub_cancel] at *
  have hu : u ≠ 0 := by rintro rfl; apply hoff; simp [det3_expand]
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu
  obtain ⟨S, N, hF, hfS, huS, r, hr, hNX, hgvN⟩ := exists_rdFrame hoff
  have hL : 0 < ‖u‖ := norm_pos_iff.mpr hu
  set L := ‖u‖ with hL_def
  set T := L⁻¹ • u with hT_def
  have hTX : ∀ X, ⟪X, T⟫ = L⁻¹ * ⟪X, u⟫ := fun X => real_inner_smul_right _ _ _
  have huL : ⟪u, u⟫ = L * L := by rw [real_inner_self_eq_norm_sq]; ring
  have hLT : L • T = u := by rw [hT_def, smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  have hdetu : ∀ X Y, det3 X Y u = L * det3 X Y T := by
    intro X Y; conv_lhs => rw [← hLT]
    simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring
  set ε := det3 S T N with hε
  have hεε : ε * ε = 1 := hF.det3_sq
  -- the coordinates of the points (relative to `v`)
  have hmv : m - v = s • (f - v) + δ • u := by rw [hm]; abel
  have νf : ⟪f - v, N⟫ = 0 := by rw [hNX]; simp only [det3_expand]; ring
  have νu : ⟪u, N⟫ = 0 := by rw [hNX]; simp only [det3_expand]; ring
  have νm : ⟪m - v, N⟫ = 0 := by
    rw [hmv, inner_add_left, real_inner_smul_left, real_inner_smul_left, νf, νu]; ring
  have νg : ⟪gf - v, N⟫ = ⟪gv - v, N⟫ := by
    have : det3 u (f - v) (gf - v) - det3 u (f - v) (gv - v) = det3 u (f - v) (gf - gv) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [hNX, hNX, ← sub_eq_zero, ← mul_sub, this, hpar, mul_zero]
  have hTS : ⟪T, S⟫ = 0 := by rw [real_inner_comm]; exact hF.2.2.2.1
  have hTT : ⟪T, T⟫ = 1 := hF.2.1
  have hTN : ⟪T, N⟫ = 0 := hF.2.2.2.2.2
  have uS : ⟪u, S⟫ = 0 := huS
  have uT : ⟪u, T⟫ = L := by rw [hTX, huL]; field_simp
  have smv : ⟪m - v, S⟫ = s * ⟪f - v, S⟫ := by
    rw [hmv, inner_add_left, real_inner_smul_left, real_inner_smul_left, uS]; ring
  have tmv : ⟪m - v, T⟫ = s * ⟪f - v, T⟫ + δ * L := by
    rw [hmv, inner_add_left, real_inner_smul_left, real_inner_smul_left, uT]
  -- (H1): the depths
  have hTv : ∀ P, ⟪P - v, T⟫ = L⁻¹ * (⟪P, u⟫ - ⟪v, u⟫) := by
    intro P; rw [hTX, inner_sub_left]
  have hcr : lam * (⟪f, u⟫ - ⟪v, u⟫) = (1 - mu) * (⟪gv, u⟫ - ⟪v, u⟫) + mu * (⟪gf, u⟫ - ⟪v, u⟫) := by
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left] at hD1
    linear_combination hD1
  have hmz : ⟪m, u⟫ = ⟪v, u⟫ + s * (⟪f, u⟫ - ⟪v, u⟫) + δ * ⟪u, u⟫ := by
    rw [hm]; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  rw [quint_inner_eq] at hinj h5
  obtain ⟨d1, -, d3, -, d5, d6⟩ := rd_depths hmz hs0 hs1 (mul_pos hδ huu) hNv hNw hA hB hC hE
    hsum hlo hinj h5 hl0 hl1 hmu0 hmu1 hcr
  have hLi : 0 < L⁻¹ := inv_pos.mpr hL
  have htm : 0 < ⟪m - v, T⟫ := by rw [hTv]; exact mul_pos hLi (by linarith)
  have ht1 : 0 < ⟪gv - v, T⟫ := by rw [hTv]; exact mul_pos hLi (by linarith)
  have htf : ⟪f - v, T⟫ < 0 := by rw [hTv]; exact mul_neg_of_pos_of_neg hLi (by linarith)
  have ht2 : ⟪gf - v, T⟫ < 0 := by rw [hTv]; exact mul_neg_of_pos_of_neg hLi (by linarith)
  -- the orientation of the rim: `s₁ < s₂`
  have h12 : ⟪gv - v, S⟫ < ⟪gf - v, S⟫ := by
    rw [det3_cyc v gf gv u, hdetu, hdetu, hF.det3_T, hF.det3_T, νf, νg] at horient
    have e : L * (ε * (0 * ⟪gf - v, S⟫ - ⟪f - v, S⟫ * ⟪gv - v, N⟫)) *
        (L * (ε * (⟪gv - v, N⟫ * ⟪gv - v, S⟫ - ⟪gf - v, S⟫ * ⟪gv - v, N⟫))) =
        (L * L) * (ε * ε) * (⟪f - v, S⟫ * (⟪gv - v, N⟫ * ⟪gv - v, N⟫)) *
          (⟪gf - v, S⟫ - ⟪gv - v, S⟫) := by ring
    rw [e, hεε, mul_one] at horient
    have hpos : 0 < L * L * (⟪f - v, S⟫ * (⟪gv - v, N⟫ * ⟪gv - v, N⟫)) :=
      mul_pos (mul_pos hL hL) (mul_pos hfS (mul_pos_of_neg_of_neg hgvN hgvN))
    have := pos_of_mul_pos_right horient hpos.le
    linarith
  -- (H4): `σ_vf < σ_g`
  have hH4 : ⟪f - v, T⟫ * (⟪gf - v, S⟫ - ⟪gv - v, S⟫) <
      ⟪f - v, S⟫ * (⟪gf - v, T⟫ - ⟪gv - v, T⟫) := by
    rw [hF.det3_eq (f - v) (gf - v) (gv - v), hF.det3_eq (f - v) (gf - v),
      show v - u - v = -u by abel, inner_neg_left, inner_neg_left, inner_neg_left, uS, uT, νu,
      neg_zero, νf, νg, det3_pt_rd₁, det3_pt_rd₂] at hside
    rw [hF.det3_eq, νf, νg, det3_pt_rd₁] at hcop
    set X := ⟪f - v, T⟫ * (⟪gv - v, S⟫ - ⟪gf - v, S⟫) +
      ⟪f - v, S⟫ * (⟪gf - v, T⟫ - ⟪gv - v, T⟫) with hX
    have e : ε * (⟪gv - v, N⟫ * X) * (ε * (⟪f - v, S⟫ * ⟪gv - v, N⟫ * L)) =
        (ε * ε) * (⟪gv - v, N⟫ * ⟪gv - v, N⟫ * ⟪f - v, S⟫ * L) * X := by ring
    rw [e, hεε, one_mul] at hside
    have hpos : 0 < ⟪gv - v, N⟫ * ⟪gv - v, N⟫ * ⟪f - v, S⟫ * L :=
      mul_pos (mul_pos (mul_pos_of_neg_of_neg hgvN hgvN) hfS) hL
    have hX0 : 0 ≤ X := nonneg_of_mul_nonneg_right (by linarith) hpos
    have hX1 : X ≠ 0 := by rintro h0; apply hcop; rw [h0]; ring
    have := lt_of_le_of_ne hX0 (Ne.symm hX1)
    linarith
  -- the foot of the double normal
  have hDv : v + lam • (f - v) - (gv + mu • (gf - gv)) =
      lam • (f - v) - (gv - v) - mu • ((gf - v) - (gv - v)) := by module
  have hct : lam * ⟪f - v, T⟫ = ⟪gv - v, T⟫ + mu * (⟪gf - v, T⟫ - ⟪gv - v, T⟫) := by
    have := inner_foot hDv T
    rw [hTX, hD1, mul_zero] at this
    linarith
  have hcs : lam * ⟪f - v, S⟫ = ⟪gv - v, S⟫ + mu * (⟪gf - v, S⟫ - ⟪gv - v, S⟫) := by
    have hpar2 := hF.inner_eq (v + lam • (f - v) - (gv + mu • (gf - gv))) (f - v)
    rw [hD2, νf, mul_zero, add_zero, hTX, hD1, mul_zero, zero_mul, add_zero] at hpar2
    have h0 : ⟪v + lam • (f - v) - (gv + mu • (gf - gv)), S⟫ = 0 :=
      (mul_eq_zero.mp hpar2.symm).resolve_right hfS.ne'
    rw [inner_foot hDv S] at h0
    linarith
  -- the face `Φ`
  have hΦ : ∀ P, φ P = φ v + ⟪Nφ, S⟫ * ⟪P - v, S⟫ + ⟪Nφ, T⟫ * ⟪P - v, T⟫ +
      ⟪Nφ, N⟫ * ⟪P - v, N⟫ := by
    intro P; have := hφ P v; rw [hF.inner_eq] at this; linarith
  have Φm := hΦ m; have Φf := hΦ f; have Φgf := hΦ gf; have Φgv := hΦ gv
  rw [φm, νm] at Φm
  rw [φf, νf] at Φf
  rw [φgf, νg] at Φgf
  have hsmf : ⟪m - v, S⟫ < ⟪f - v, S⟫ := by
    rw [smv]; have := mul_lt_mul_of_pos_right hs1 hfS; linarith
  have hsm0 : 0 < ⟪m - v, S⟫ := by rw [smv]; exact mul_pos hs0 hfS
  obtain ⟨H2, Dv, Df⟩ := rd_coords (sm := ⟪m - v, S⟫) (tm := ⟪m - v, T⟫) (sf := ⟪f - v, S⟫)
    (tf := ⟪f - v, T⟫) (s1 := ⟪gv - v, S⟫) (t1 := ⟪gv - v, T⟫) (s2 := ⟪gf - v, S⟫)
    (t2 := ⟪gf - v, T⟫) (h := -⟪gv - v, N⟫) (c0 := φ v) (α := ⟪Nφ, S⟫) (β := ⟪Nφ, T⟫)
    (γ := ⟪Nφ, N⟫) hsm0 hsmf htm htf φv
    (by linarith) (by linarith) (by linarith) (by linarith) hH4 hl0 hl1 hcs hct
  unfold RdRim
  exact ⟨S, N, ⟪m - v, S⟫, ⟪m - v, T⟫, ⟪f - v, S⟫, ⟪f - v, T⟫, ⟪gv - v, S⟫, ⟪gv - v, T⟫,
    ⟪gf - v, S⟫, ⟪gf - v, T⟫, -⟪gv - v, N⟫, hF, ⟨rfl, rfl, νm⟩, ⟨rfl, rfl, νf⟩,
    ⟨rfl, rfl, by rw [νg, neg_neg]⟩, ⟨rfl, rfl, by rw [neg_neg]⟩, neg_pos.mpr hgvN,
    hsm0, hsmf, h12, htm, ht1, htf, ht2, H2, Dv, Df⟩

/-! ### The two type-08 closings -/

/-- **The claim of Lemma 9.3** at a quad edge `x → y` of an octahedron, in either
orientation, as one weighted inequality: `A z_x + B z_{y'} < C z_p + E z_{p'}` with
positive weights, `A + B = C + E` (`z = ⟪·, y − x⟫`). -/
theorem quad_edge_claim {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y) :
    ∃ A B C E : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < E ∧ A + B = C + E ∧
      A * ⟪x, y - x⟫ + B * ⟪y', y - x⟫ < C * ⟪p, y - x⟫ + E * ⟪p', y - x⟫ := by
  have key : ∀ {p p' : ℝ³} (F : OctFacets x x' y y' p p'), F.a'b'c.f x < F.a'b'c.f y →
      F.a'b'c'.f x < F.a'b'c'.f y → 0 < det3 (p - y) (p' - y) (y - x) →
      ∃ A B C E : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < E ∧ A + B = C + E ∧
        A * ⟪x, y - x⟫ + B * ⟪y', y - x⟫ < C * ⟪p, y - x⟫ + E * ⟪p', y - x⟫ := by
    intro p p' F hq₁ hq₂ hor
    have hnd := F.nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true] at hnd
    obtain ⟨⟨-, -, hxy', hxp, hxp'⟩, -, ⟨hyy', hyp, -⟩, ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
    obtain ⟨E1, E2, E3, -⟩ := quad_edge_tests F hq₁ hq₂ hor
    have hS₁ := E2 p' (by simp) (Ne.symm hpp') (Ne.symm hy'p')
    have hS₂ : 0 < det3 (y' - x) (p' - x) (y - x) := by
      rw [← det3_cyc x y' p']; exact E3 x (by simp) hxy' hxp'
    have hS₃ : 0 < det3 (p - x) (p' - x) (y - x) := by rw [det3_shift_xy]; exact hor
    have hS₄ : 0 < det3 (p - x) (y' - x) (y - x) := by
      rw [det3_shift_xy]; exact E1 y' (by simp) (Ne.symm hyy') hy'p (Ne.symm hxy')
    have hsum := four_point_sum x p y' p' (y - x)
    exact ⟨_, _, _, _, hS₁, hS₃, hS₂, hS₄, by linarith, quad_edge_lower F hS₁ hS₂ hS₃ hS₄⟩
  rcases lt_or_gt_of_ne (quad_orient_ne F) with hn | hp
  · obtain ⟨A, B, C, E, hA, hB, hC, hE, hs, hl⟩ :=
      key F.swap₃ hq₂ hq₁ (by rw [det3_swap12]; linarith)
    exact ⟨A, B, E, C, hA, hB, hE, hC, by linarith, by linarith⟩
  · exact key F hq₁ hq₂ hp

theorem det3_cyc' (a b c : ℝ³) : det3 a b c = det3 b c a := by
  simp only [det3_expand]; ring

/-- **Lemma R0 and Theorem R for `K_y` (N2–`K_c`).**  At a quad edge `x → y` of an
octahedron (`x'` hidden), with one more point `m` over the chord from `y` to `p`: if the
face `Φ` through `m, p, y'` has `y`, `p'` strictly beneath it, `p'` and `x` lie weakly on
one side of the plane `y p y'`, `K_y`'s rim `y p y' p'` has no weak saddle and `K_x`'s
rim `x p y' p'` has one, and the five-corner rim `y m p y' p'` is in `R_d` (`RdCond`),
the seven points are Rupert. -/
theorem isRupert_quad_edge_middle_rdCond {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hmid : ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ 0 < δ ∧ m = y + s • (p - y) + δ • (y - x))
    (hΦ : ∃ (φ : ℝ³ → ℝ) (Nφ : ℝ³), (∀ a b, φ a - φ b = ⟪Nφ, a - b⟫) ∧ φ m = 0 ∧ φ p = 0 ∧
      φ y' = 0 ∧ φ y < 0 ∧ φ p' < 0)
    (hside : 0 ≤ det3 (p - y) (y' - y) (p' - y) * det3 (p - y) (y' - y) (x - y))
    (hNy : NWS4 (quad ⟪y, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫))
    (hNx : ¬ NWS4 (quad ⟪x, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫))
    (hR : RdCond y m p y' p' x) :
    IsRupert (insert m {x, x', y, y', p, p'}) := by
  obtain ⟨s, δ, hs0, hs1, hδ, hm⟩ := hmid
  obtain ⟨E1, -, E3, -⟩ := quad_edge_tests_or F hq₁ hq₂
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨-, -, hxy', -, -⟩, -, ⟨hyy', hyp, hyp'⟩, ⟨hy'p, hy'p'⟩, -, -⟩ := hnd
  have e1 := E1 y' (by simp) (Ne.symm hyy') hy'p (Ne.symm hxy')
  have e3 := E3 y (by simp) hyy' hyp'
  have hρ := quad_orient_ne F
  have horient : 0 < det3 (p - y) (y' - y) (y - x) * det3 (p' - y') (y - y') (y - x) := by
    have := mul_pos e1 e3
    have hρρ := mul_self_pos.mpr hρ
    have e : det3 (p - y) (p' - y) (y - x) * det3 (p - y) (y' - y) (y - x) *
        (det3 (p - y) (p' - y) (y - x) * det3 (p' - y') (y - y') (y - x)) =
        (det3 (p - y) (p' - y) (y - x) * det3 (p - y) (p' - y) (y - x)) *
          (det3 (p - y) (y' - y) (y - x) * det3 (p' - y') (y - y') (y - x)) := by ring
    rw [e] at this
    exact pos_of_mul_pos_right this hρρ.le
  have hoff : det3 (y - x) (p - y) (p' - y) ≠ 0 := by rw [det3_cyc']; exact hρ
  exact isRupert_quad_edge_middle_rd F hq₁ hq₂ ⟨s, δ, hs0, hs1, hm⟩
    (rdRim_of_R0 hm hs0 hs1 hδ hoff horient hΦ hside hNy hNx (quad_edge_claim F hq₁ hq₂) hR)

/-- The determinants of Lemma R0 for `K_b` (T4), in the frame `d; a, c, b`. -/
theorem t4rd_dets {a b b' c c' d : ℝ³} {α β α₁ β₁ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d)) :
    det3 (b - d) (c - b) (c' - b) = -(α₁ * det3 (a - d) (c - d) (b - d)) ∧
    det3 (c - b) (b' - b) (b - d) = -(α * det3 (a - d) (c - d) (b - d)) ∧
    det3 (c' - b') (b - b') (b - d) = -(β * α₁ * det3 (a - d) (c - d) (b - d)) := by
  subst hb' hc'
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- **The claim of Lemma 5** (for `K − a` at the edge `d → b`, T4), as one weighted
inequality `A z_d + B z_{b'} < C z_c + E z_{c'}`, `A + B = C + E` (`z = ⟪·, b − d⟫`). -/
theorem t4_claim {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d)) (hdb : d ≠ b)
    (hE : det3 (a - d) (c - d) (b - d) ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hα₁ : 1 < α₁) (hβ₁ : 0 < β₁) (hκ : 0 < α + α₁ * (β - 1)) :
    ∃ A B C E : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < E ∧ A + B = C + E ∧
      A * ⟪d, b - d⟫ + B * ⟪b', b - d⟫ < C * ⟪c, b - d⟫ + E * ⟪c', b - d⟫ := by
  obtain ⟨K0, K1, K2, K3, K4, K5, K6, K7, K8, K9, K10, K11, K12, K13, K14, K15, K16, K17, K18,
    K19, K20, K21, K22, K23, K24, K25, K26, D3, D21, D2, D1⟩ := t4_slide_dets hb' hc' ha'
  have hα₁p : 0 < α₁ := by linarith
  have hκ' : 0 < α + β * α₁ - α₁ := by
    rw [show α + β * α₁ - α₁ = α + α₁ * (β - 1) by ring]; exact hκ
  have pβα₁ : 0 < β * α₁ := mul_pos hβ hα₁p
  have hlowG : ∀ s t : ℝ³,
      (fun X => -(det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (X - d))) s -
      (fun X => -(det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (X - d))) t =
      ⟪-(det3 (a - d) (c - d) (b - d)) • cross (a - d) (c - d), s - t⟫ := by
    intro s t
    simp only [det3, real_inner_smul_left]
    have e : ⟪cross (a - d) (c - d), s - t⟫ =
        ⟪cross (a - d) (c - d), s - d⟫ - ⟪cross (a - d) (c - d), t - d⟫ := by
      rw [← inner_sub_right]; congr 1; abel
    rw [e]; ring
  have hEE := mul_self_pos.mpr hE
  have Gd : (fun X => -(det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (X - d))) d = 0 := by
    simp only [sub_self]; simp [det3_expand]
  have Gb' : (fun X => -(det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (X - d))) b' = 0 := by
    simp only [K25, mul_zero, neg_zero]
  have Gb : (fun X => -(det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (X - d))) b < 0 := by
    simp only; linarith
  have Gc : (fun X => -(det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (X - d))) c = 0 := by
    simp only; rw [show det3 (a - d) (c - d) (c - d) = 0 by simp [det3_expand]; ring]; ring
  have Gc' : (fun X => -(det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (X - d))) c' < 0 := by
    simp only; rw [K26]
    have := mul_pos hβ₁ hEE
    linarith [show det3 (a - d) (c - d) (b - d) * (β₁ * det3 (a - d) (c - d) (b - d)) =
      β₁ * (det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (b - d)) by ring]
  rcases lt_or_gt_of_ne hE with hEn | hEp
  · have S₁ : 0 < det3 (b' - c) (c' - c) (b - d) := by
      rw [D3]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hκ' hEn)
    have S₂ : 0 < det3 (b' - d) (c' - d) (b - d) := by
      rw [D21]; exact neg_pos.mpr (mul_neg_of_pos_of_neg pβα₁ hEn)
    have S₃ : 0 < det3 (c - d) (c' - d) (b - d) := by
      rw [D2]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hα₁p hEn)
    have S₄ : 0 < det3 (c - d) (b' - d) (b - d) := by
      rw [D1]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hα hEn)
    have hlow := quad_lower_of_face hlowG hdb Gd Gb' Gb S₂ S₄ (Or.inl ⟨Gc, Gc'⟩)
    have hsum := four_point_sum d c b' c' (b - d)
    exact ⟨_, _, _, _, S₁, S₃, S₂, S₄, by linarith, hlow⟩
  · have S₁ : 0 < det3 (b' - c') (c - c') (b - d) := by rw [K2]; exact mul_pos hκ' hEp
    have S₂ : 0 < det3 (b' - d) (c - d) (b - d) := by rw [K24]; exact mul_pos hα hEp
    have S₃ : 0 < det3 (c' - d) (c - d) (b - d) := by rw [K14]; exact mul_pos hα₁p hEp
    have S₄ : 0 < det3 (c' - d) (b' - d) (b - d) := by rw [K13]; exact mul_pos pβα₁ hEp
    have hlow := quad_lower_of_face hlowG hdb Gd Gb' Gb S₂ S₄ (Or.inr ⟨Gc, Gc'⟩)
    have hsum := four_point_sum d c' b' c (b - d)
    exact ⟨_, _, _, _, S₁, S₃, S₄, S₂, by linarith, by linarith⟩

/-- **Lemma R0 and Theorem R for `K_b` (T4).**  In the frame `d; a, c, b` of the T4 case
(far ends `c'`, `c` at the view along `d b`, `b'` a corner): if the face `Φ = a'b'c` has `b`
and `c'` strictly beneath it, `a'` and `c'` lie weakly on opposite sides of the plane
`b c b'`, `K_b`'s rim `b c' b' c` has no weak saddle and `K_d`'s rim `d c' b' c` has one, and
the five-corner rim `b a' c b' c'` is in `R_d` (`RdCond`), `K` is Rupert. -/
theorem isRupert_t4b_rdCond {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d)) (hdb : d ≠ b)
    (hE : det3 (a - d) (c - d) (b - d) ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hα₁ : 1 < α₁) (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) (hαβ₂ : 1 < α₂ + β₂) (hκ : 0 < α + α₁ * (β - 1))
    (hΦ : ∃ (φ : ℝ³ → ℝ) (Nφ : ℝ³), (∀ x y, φ x - φ y = ⟪Nφ, x - y⟫) ∧ φ a' = 0 ∧ φ c = 0 ∧
      φ b' = 0 ∧ φ b < 0 ∧ φ c' < 0)
    (hside : det3 (c - b) (b' - b) (a' - b) * det3 (c - b) (b' - b) (c' - b) ≤ 0)
    (hNb : NWS4 (quad ⟪b, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫))
    (hNd : ¬ NWS4 (quad ⟪d, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫))
    (hR : RdCond b a' c b' c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨T1, T2, T3⟩ := t4rd_dets (b := b) hb' hc'
  have hα₁p : 0 < α₁ := by linarith
  have hm : a' = b + β₂ • (c - b) + (α₂ + β₂ - 1) • (b - d) := by rw [ha']; module
  have hoff : det3 (b - d) (c - b) (c' - b) ≠ 0 := by
    rw [T1]; exact neg_ne_zero.mpr (mul_ne_zero hα₁p.ne' hE)
  have horient : 0 < det3 (c - b) (b' - b) (b - d) * det3 (c' - b') (b - b') (b - d) := by
    rw [T2, T3]
    have := mul_self_pos.mpr hE
    have e : -(α * det3 (a - d) (c - d) (b - d)) * -(β * α₁ * det3 (a - d) (c - d) (b - d)) =
        α * β * α₁ * (det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (b - d)) := by ring
    rw [e]; exact mul_pos (mul_pos (mul_pos hα hβ) hα₁p) this
  have hside' : 0 ≤ det3 (c - b) (b' - b) (c' - b) * det3 (c - b) (b' - b) (d - b) := by
    have e : det3 (c - b) (b' - b) (a' - b) = -(α₂ + β₂ - 1) * det3 (c - b) (b' - b) (d - b) := by
      rw [hm]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [e] at hside
    have hk : 0 < α₂ + β₂ - 1 := by linarith
    nlinarith [mul_pos hk hk]
  have hNv : NWS4 (quad ⟪b, b - d⟫ ⟪c, b - d⟫ ⟪b', b - d⟫ ⟪c', b - d⟫) := NWS4_quad_swap hNb
  have hNw : ¬ NWS4 (quad ⟪d, b - d⟫ ⟪c, b - d⟫ ⟪b', b - d⟫ ⟪c', b - d⟫) :=
    fun h => hNd (NWS4_quad_swap h)
  exact isRupert_t4b_rd hc' hα₁ hβ₁ (Ne.symm hdb)
    (rdRim_of_R0 hm hβ₂ hβ₂1 (by linarith) hoff horient hΦ hside' hNv hNw
      (t4_claim hb' hc' ha' hdb hE hα hβ hα₁ hβ₁ hκ) hR)

/-! ### (H4) from the Gale diagram -/

/-- **(H4) for both closings, from Lemma 9.7 / (T2).**  In the labelling of Lemma 6 (only
`κ_a > 0` and the signs `[a' b], [a' b'] < 0 < [a c], [a c']` are used): projecting along
`c' − c`, `c` lies inside the triangle of `b, b', a` (so `b'` and `a'` lie on one side of
the plane `c b c'`: N2–`K_c`), and projecting along `b' − b`, `b` lies inside the triangle of
`a', c, c'` (so `a'` and `c'` lie on opposite sides of the plane `b c b'`: T4–`K_b`). -/
theorem type08_rd_sides {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : 0 < galeD G.l G.m a a')
    (ha'b : galeD G.l G.m a' b < 0) (ha'b' : galeD G.l G.m a' b' < 0)
    (hac : 0 < galeD G.l G.m a c) (hac' : 0 < galeD G.l G.m a c') :
    0 < det3 (b - c) (c' - c) (b' - c) * det3 (b - c) (c' - c) (a' - c) ∧
      det3 (c - b) (b' - b) (a' - b) * det3 (c - b) (b' - b) (c' - b) < 0 := by
  have sw : ∀ X Y Z : ℝ³, det3 X Y Z = -det3 X Z Y := fun X Y Z => by
    simp only [det3_expand]; ring
  have ng : ∀ X Y P Q : ℝ³, det3 X Y (Q - P) = -det3 X Y (P - Q) := fun X Y P Q => by
    simp only [det3_expand, PiLp.sub_apply]; ring
  constructor
  · obtain ⟨e, he, sab, sba', -, -⟩ := axis_quad_signs h
    obtain ⟨hBCD, -⟩ := inTri_of_dep (G.hl.galeD G.hm a') (galeD_self _ _ a')
      (by rw [galeD_anti]; linarith) ha'b ha'b' he sab
    rw [sw (b - c) (c' - c) (b' - c), sw (b - c) (c' - c) (a' - c)]
    rcases he with rfl | rfl
    · nlinarith [mul_pos hBCD sba']
    · rw [ng (b - c) (b' - c) c c', ng (b - c) (a' - c) c c']
      nlinarith [mul_pos hBCD sba']
  · obtain ⟨e, he, sab, -, -, -⟩ := axis_quad_signs h.swap₁.perm₂₃
    obtain ⟨h1, -⟩ := inTri_of_dep (G.hl.galeD' G.hm a).swap₁.perm₂₃ (galeD_self _ _ a)
      (by rw [galeD_anti]; linarith) (by rw [galeD_anti]; linarith)
      (by rw [galeD_anti]; linarith) he sab
    have k1 : det3 (c - b) (b' - b) (a' - b) = det3 (a' - b) (c - b) (b' - b) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [k1, sw (c - b) (b' - b) (c' - b)]
    rcases he with rfl | rfl
    · nlinarith [mul_pos sab h1]
    · rw [ng (a' - b) (c - b) b b', ng (c - b) (c' - b) b b']
      nlinarith [mul_pos sab h1]

end Minimality

end
