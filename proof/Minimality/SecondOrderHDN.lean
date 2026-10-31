module

public import Minimality.SecondOrderT2b

@[expose] public section

/-!
# A level double normal is a passage at second order (Theorem H2, plan specpos §2)

At the view `e_z`, let `vp vm ∈ V` be two shadow points at equal depth (a level, i.e. horizontal, double normal) with
chord `D = P vp - P vm`, each strictly inside every edge half-plane tight at the other.  Tilt about an in-screen
axis `w` not parallel to `D`, pivoting at `vp`: every point drifts along `(w 1, -w 0)` in proportion to its height
above the chord's level, so `vp` and `vm` stand still.  If every other boundary point drifts inward
(`hdrift`), the motion is weakly inward, every balanced load lives on `{vp, vm}`, and its second-order term is
`Q · |D|² = -⟪F₊, D⟫ · cross2 D w ^ 2 < 0`.  So `isRupert_of_secondOrder_noBalanced` applies.

`isRupert_of_levelHDN` removes such an HDN outright rather than escaping it through a further coincidence.  It fails
for a corner–edge HDN (only `w ∥ D` is then weakly inward) and for a doubled chord end.
-/
namespace Minimality
open scoped RealInnerProductSpace

theorem levelHDN_key (w : ℝ²) (vp x : ℝ³) (m : ℝ²) :
    ⟪m, screenVel !₂[w 0, w 1, 0] (-((crossMatrix !₂[w 0, w 1, 0]).toEuclideanLin vp)) x⟫
      = (x 2 - vp 2) * cross2 m w := by
  simp [screenVel, proj_xy, crossMatrix, cross2, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Fin.sum_univ_two, PiLp.inner_apply]
  ring

theorem levelHDN_Q (w : ℝ²) (x : ℝ³) (m : ℝ²) :
    ⟪m, proj_xy ((crossMatrix !₂[w 0, w 1, 0]).toEuclideanLin ((crossMatrix !₂[w 0, w 1, 0]).toEuclideanLin x))⟫
      = ⟪m, w⟫ * ⟪w, proj_xy x⟫ - (w 0 ^ 2 + w 1 ^ 2) * ⟪m, proj_xy x⟫ := by
  simp [proj_xy, crossMatrix, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Fin.sum_univ_two, PiLp.inner_apply]
  ring

theorem levelHDN_sum_inner {ι : Type*} [Fintype ι] (n : ι → ℝ²) (a : ι → ℝ) (X : ℝ²) :
    ∑ e, a e * ⟪n e, X⟫ = ⟪∑ e, a e • n e, X⟫ := by
  simp [sum_inner, inner_smul_left]

theorem levelHDN_lagrange (F D w : ℝ²) :
    (D 0 ^ 2 + D 1 ^ 2) * ⟪F, w⟫ = ⟪F, D⟫ * ⟪D, w⟫ + cross2 D F * cross2 D w := by
  simp [cross2, PiLp.inner_apply, Fin.sum_univ_two]; ring
theorem levelHDN_torque {ι : Type*} [Fintype ι] (n : ι → ℝ²) (a : ι → ℝ) (p : ℝ²) :
    ∑ e, a e * (p 0 * n e 1 - p 1 * n e 0) = p 0 * (∑ e, a e • n e) 1 - p 1 * (∑ e, a e • n e) 0 := by
  simp [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => by ring

theorem levelHDN_Qsum {ι : Type*} [Fintype ι] (n : ι → ℝ²) (a : ι → ℝ) (w x : ℝ²) (c : ℝ) :
    ∑ e, a e * (⟪n e, w⟫ * ⟪w, x⟫ - c * ⟪n e, x⟫) =
      ⟪∑ e, a e • n e, w⟫ * ⟪w, x⟫ - c * ⟪∑ e, a e • n e, x⟫ := by
  rw [← levelHDN_sum_inner, ← levelHDN_sum_inner, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => by ring

theorem isRupert_of_levelHDN (V : Finset ℝ³) {ι : Type*} [Fintype ι] (n : ι → ℝ²) (h : ι → ℝ)
    (hpoly : {y : ℝ² | ∀ e, ⟪n e, y⟫ < h e} ⊆ proj_xy '' convexHull ℝ (V : Set ℝ³))
    (hin : ∀ v ∈ V, ∀ e, ⟪n e, proj_xy v⟫ ≤ h e)
    (vp vm : ℝ³) (hvp : vp ∈ V) (hvm : vm ∈ V) (hlev : vp 2 = vm 2)
    (w : ℝ²) (hax : cross2 (proj_xy vp - proj_xy vm) w ≠ 0)
    (hsepP : ∀ e, ⟪n e, proj_xy vp⟫ = h e → ⟪n e, proj_xy vm⟫ < h e)
    (hsepM : ∀ e, ⟪n e, proj_xy vm⟫ = h e → ⟪n e, proj_xy vp⟫ < h e)
    (hdrift : ∀ v ∈ V, v ≠ vp → v ≠ vm → ∀ e, ⟪n e, proj_xy v⟫ = h e →
      (v 2 - vp 2) * cross2 (n e) w < 0) :
    IsRupert V := by
  classical
  have hne : vp ≠ vm := by
    rintro rfl; apply hax; simp [cross2]
  set ω : ℝ³ := !₂[w 0, w 1, 0] with hω
  set τ : ℝ³ := -((crossMatrix ω).toEuclideanLin vp) with hτ
  have key : ∀ x e, ⟪n e, screenVel ω τ x⟫ = (x 2 - vp 2) * cross2 (n e) w :=
    fun x e => levelHDN_key w vp x (n e)
  have hweak : ∀ v ∈ V, ∀ e, ⟪n e, proj_xy v⟫ < h e ∨
      (⟪n e, proj_xy v⟫ = h e ∧ ⟪n e, screenVel ω τ v⟫ ≤ 0) := by
    intro v hv e
    rcases lt_or_eq_of_le (hin v hv e) with h1 | h1
    · exact Or.inl h1
    · right
      refine ⟨h1, ?_⟩
      rw [key]
      by_cases a : v = vp
      · subst a; simp
      by_cases b : v = vm
      · subst b; rw [← hlev]; simp
      · exact (hdrift v hv a b e h1).le
  refine isRupert_of_secondOrder_noBalanced V n h hpoly ω τ hweak ?_
  intro lam hlam hsupp hex hF hT hD
  have hz : ∀ v : V, (v : ℝ³) ≠ vp → (v : ℝ³) ≠ vm → ∀ e, lam v e = 0 := by
    intro v a b e
    by_contra hne'
    obtain ⟨t1, t2⟩ := hsupp v e hne'
    rw [key] at t2
    have := hdrift v v.2 a b e t1
    linarith
  let P : V := ⟨vp, hvp⟩
  let M : V := ⟨vm, hvm⟩
  have hPM : P ≠ M := fun e => hne (congrArg Subtype.val e)
  have two : ∀ f : V → ℝ, (∀ v : V, (v : ℝ³) ≠ vp → (v : ℝ³) ≠ vm → f v = 0) → ∑ v, f v = f P + f M := by
    intro f hf
    exact Fintype.sum_eq_add P M hPM (fun x hx =>
      hf x (fun e => hx.1 (Subtype.ext e)) (fun e => hx.2 (Subtype.ext e)))
  have twoV : ∀ f : V → ℝ², (∀ v : V, (v : ℝ³) ≠ vp → (v : ℝ³) ≠ vm → f v = 0) → ∑ v, f v = f P + f M := by
    intro f hf
    exact Fintype.sum_eq_add P M hPM (fun x hx =>
      hf x (fun e => hx.1 (Subtype.ext e)) (fun e => hx.2 (Subtype.ext e)))
  set Fp : ℝ² := ∑ e, lam P e • n e with hFp
  set Fm : ℝ² := ∑ e, lam M e • n e with hFm
  have hFsum : Fp + Fm = 0 := by
    rw [← hF, twoV (fun v => ∑ e, lam v e • n e)]
    intro v a b; simp [hz v a b]
  have hFm' : Fm = -Fp := eq_neg_of_add_eq_zero_right hFsum
  have hTor : (proj_xy vp) 0 * Fp 1 - (proj_xy vp) 1 * Fp 0
      + ((proj_xy vm) 0 * Fm 1 - (proj_xy vm) 1 * Fm 0) = 0 := by
    rw [← levelHDN_torque, ← levelHDN_torque, ← two (fun v => ∑ e, lam v e *
      ((proj_xy (v : ℝ³)) 0 * n e 1 - (proj_xy (v : ℝ³)) 1 * n e 0))]
    · exact hT
    · intro v a b; simp [hz v a b]
  set D : ℝ² := proj_xy vp - proj_xy vm with hDdef
  have hcr : cross2 D Fp = 0 := by
    have : Fm 0 = - Fp 0 := by rw [hFm']; simp
    have h1 : Fm 1 = - Fp 1 := by rw [hFm']; simp
    simp only [cross2, hDdef, PiLp.sub_apply]
    rw [this, h1] at hTor
    linarith
  -- positivity of <Fp, D>
  have hnD_p : ∀ e, lam P e ≠ 0 → 0 < ⟪n e, D⟫ := by
    intro e he
    obtain ⟨t1, _⟩ := hsupp P e he
    have := hsepP e t1
    rw [hDdef, inner_sub_right, t1]; linarith
  have hnD_m : ∀ e, lam M e ≠ 0 → ⟪n e, D⟫ < 0 := by
    intro e he
    obtain ⟨t1, _⟩ := hsupp M e he
    have := hsepM e t1
    rw [hDdef, inner_sub_right, t1]; linarith
  have hFpD : ⟪Fp, D⟫ = ∑ e, lam P e * ⟪n e, D⟫ := (levelHDN_sum_inner n _ D).symm
  have hFmD : ⟪Fm, D⟫ = ∑ e, lam M e * ⟪n e, D⟫ := (levelHDN_sum_inner n _ D).symm
  have hpos : 0 < ⟪Fp, D⟫ := by
    by_cases hP : ∃ e, lam P e ≠ 0
    · obtain ⟨e0, he0⟩ := hP
      rw [hFpD]
      refine Finset.sum_pos' (fun e _ => ?_) ⟨e0, Finset.mem_univ _, ?_⟩
      · by_cases he : lam P e = 0
        · simp [he]
        · exact (mul_pos (lt_of_le_of_ne (hlam P e) (Ne.symm he)) (hnD_p e he)).le
      · exact mul_pos (lt_of_le_of_ne (hlam P e0) (Ne.symm he0)) (hnD_p e0 he0)
    · push Not at hP
      have hM : ∃ e, lam M e ≠ 0 := by
        obtain ⟨v, e, hve⟩ := hex
        by_cases a : (v : ℝ³) = vp
        · exact (hve (by rw [show v = P from Subtype.ext a]; exact hP e)).elim
        by_cases b : (v : ℝ³) = vm
        · exact ⟨e, by rwa [show v = M from Subtype.ext b] at hve⟩
        · exact absurd (hz v a b e) hve
      obtain ⟨e0, he0⟩ := hM
      have : ⟪Fm, D⟫ < 0 := by
        rw [hFmD]
        refine Finset.sum_neg' (fun e _ => ?_) ⟨e0, Finset.mem_univ _, ?_⟩
        · by_cases he : lam M e = 0
          · simp [he]
          · exact (mul_neg_of_pos_of_neg (lt_of_le_of_ne (hlam M e) (Ne.symm he)) (hnD_m e he)).le
        · exact mul_neg_of_pos_of_neg (lt_of_le_of_ne (hlam M e0) (Ne.symm he0)) (hnD_m e0 he0)
      rw [hFm', inner_neg_left] at this
      linarith
  -- the second-order sum
  have hQ : ∑ v : V, ∑ e, lam v e * ⟪n e, proj_xy ((crossMatrix ω).toEuclideanLin
      ((crossMatrix ω).toEuclideanLin (v : ℝ³)))⟫ =
      (⟪Fp, w⟫ * ⟪w, proj_xy vp⟫ - (w 0 ^ 2 + w 1 ^ 2) * ⟪Fp, proj_xy vp⟫) +
      (⟪Fm, w⟫ * ⟪w, proj_xy vm⟫ - (w 0 ^ 2 + w 1 ^ 2) * ⟪Fm, proj_xy vm⟫) := by
    rw [two (fun v => ∑ e, lam v e * ⟪n e, proj_xy ((crossMatrix ω).toEuclideanLin
      ((crossMatrix ω).toEuclideanLin (v : ℝ³)))⟫)]
    · simp only [hω, levelHDN_Q]
      rw [levelHDN_Qsum, levelHDN_Qsum]
    · intro v a b; simp [hz v a b]
  rw [hQ, hFm']
  have hDn : 0 < D 0 ^ 2 + D 1 ^ 2 := by
    have : D ≠ 0 := by
      intro h0; apply hax; rw [h0]; simp [cross2]
    by_contra hle
    apply this
    have h0 : D 0 = 0 := by nlinarith [sq_nonneg (D 0), sq_nonneg (D 1)]
    have h1 : D 1 = 0 := by nlinarith [sq_nonneg (D 0), sq_nonneg (D 1)]
    ext i; fin_cases i <;> simp [h0, h1]
  have hcr2 : 0 < cross2 D w ^ 2 := by
    have := hax; positivity
  have L := levelHDN_lagrange Fp D w
  have I2 : ⟪D, w⟫ ^ 2 + cross2 D w ^ 2 = (D 0 ^ 2 + D 1 ^ 2) * (w 0 ^ 2 + w 1 ^ 2) := by
    simp [cross2, PiLp.inner_apply, Fin.sum_univ_two]; ring
  have hD' : proj_xy vm = proj_xy vp - D := by rw [hDdef]; abel
  have hw : ⟪w, proj_xy vm⟫ = ⟪w, proj_xy vp⟫ - ⟪w, D⟫ := by rw [hD', inner_sub_right]
  have hxx : ⟪-Fp, proj_xy vm⟫ = -⟪Fp, proj_xy vp⟫ + ⟪Fp, D⟫ := by
    rw [hD', inner_neg_left, inner_sub_right]; ring
  rw [inner_neg_left, hw, hxx]
  rw [hcr] at L
  rw [← real_inner_comm D w] at L I2
  -- Q * |D|^2 = -<Fp,D> cross^2
  have hmain : ((⟪Fp, w⟫ * ⟪w, proj_xy vp⟫ - (w 0 ^ 2 + w 1 ^ 2) * ⟪Fp, proj_xy vp⟫) +
      (-⟪Fp, w⟫ * (⟪w, proj_xy vp⟫ - ⟪w, D⟫) - (w 0 ^ 2 + w 1 ^ 2) *
        (-⟪Fp, proj_xy vp⟫ + ⟪Fp, D⟫))) * (D 0 ^ 2 + D 1 ^ 2) = -(⟪Fp, D⟫ * cross2 D w ^ 2) := by
    linear_combination (⟪w, D⟫) * L + ⟪Fp, D⟫ * I2
  have : 0 < ⟪Fp, D⟫ * cross2 D w ^ 2 := mul_pos hpos hcr2
  by_contra hge
  push Not at hge
  have := mul_nonneg hge hDn.le
  linarith
end Minimality
