module

public import Minimality.Type24Side
public import Minimality.RimHDN
public import Minimality.HDNApex

@[expose] public section

/-!
# Rim-only horizontal double normals: the antipodal reduction (Lemma HA)

* `hdr_noHDN` (Lemma HA, plane): on a strictly convex ccw polygon `p` with injective depths `z`, if every
  edge `i` has a strictly farthest vertex `c i` and its foot on the edge line is either outside the open
  edge or at a different depth than `c i`, then `p` has no horizontal double normal.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality.HDNRim
open Minimality

theorem inner2 (a b : ℝ²) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

theorem core_lag (E0 E1 N0 N1 V0 V1 : ℝ) (hd : N0 * E0 + N1 * E1 = 0) :
    (E0 ^ 2 + E1 ^ 2) * (N0 * V0 + N1 * V1) = (E0 * N1 - E1 * N0) * (E0 * V1 - E1 * V0) := by
  linear_combination (E0 * V0 + E1 * V1) * hd

theorem exists_other {k : ℕ} [NeZero k] (hk : 3 ≤ k) (i : ZMod k) :
    ∃ j : ZMod k, j ≠ i ∧ j ≠ i + 1 := by
  refine ⟨i + ((2 : ℕ) : ZMod k), ?_, ?_⟩
  · intro h
    have := zmod_add_ne (k := k) (a := 2) (b := 0) (by omega) (by omega) (by omega) i
    simp at this; exact this (by simpa using h)
  · intro h
    have := zmod_add_ne (k := k) (a := 2) (b := 1) (by omega) (by omega) (by omega) i
    simp at this; exact this (by simpa using h)

set_option maxHeartbeats 800000 in
/-- One double-normal pair with `Y` in the open edge `i`. -/
theorem hdr_core {k : ℕ} [NeZero k] (p : ZMod k → ℝ²) (z : ZMod k → ℝ) (hp : IsCcwPolygon p)
    (c : ZMod k → ZMod k)
    (hanti : ∀ i l, l ≠ c i →
      cross2 (p (i + 1) - p i) (p l - p i) < cross2 (p (i + 1) - p i) (p (c i) - p i))
    (hfoot : ∀ i, 0 < ⟪p (c i) - p i, p (i + 1) - p i⟫ →
      ⟪p (c i) - p i, p (i + 1) - p i⟫ < ⟪p (i + 1) - p i, p (i + 1) - p i⟫ →
      ⟪p (i + 1) - p i, p (i + 1) - p i⟫ * z (c i) ≠
        (⟪p (i + 1) - p i, p (i + 1) - p i⟫ - ⟪p (c i) - p i, p (i + 1) - p i⟫) * z i +
          ⟪p (c i) - p i, p (i + 1) - p i⟫ * z (i + 1))
    {i j : ZMod k} {s s' : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hs'0 : 0 ≤ s') (hs'1 : s' ≤ 1)
    {Y Y' : ℝ²} (hY : Y = p i + s • (p (i + 1) - p i))
    (hY' : Y' = p j + s' • (p (j + 1) - p j)) (hne : Y ≠ Y')
    (h1 : ∀ l, ⟪Y - Y', p l - Y⟫ ≤ 0) (h2 : ∀ l, ⟪Y' - Y, p l - Y'⟫ ≤ 0) :
    (1 - s') * z j + s' * z (j + 1) ≠ (1 - s) * z i + s * z (i + 1) := by
  intro hdep
  obtain ⟨l0, hl0i, hl0i1⟩ := exists_other hp.1 i
  have hcr0 := hp.2 i l0 hl0i hl0i1
  obtain ⟨E0, hE0⟩ : ∃ E0 : ℝ, E0 = p (i + 1) 0 - p i 0 := ⟨_, rfl⟩
  obtain ⟨E1, hE1⟩ : ∃ E1 : ℝ, E1 = p (i + 1) 1 - p i 1 := ⟨_, rfl⟩
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℝ, N0 = Y' 0 - Y 0 := ⟨_, rfl⟩
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℝ, N1 = Y' 1 - Y 1 := ⟨_, rfl⟩
  have hY0 : Y 0 = p i 0 + s * E0 := by rw [hY, hE0]; simp
  have hY1 : Y 1 = p i 1 + s * E1 := by rw [hY, hE1]; simp
  have hZ0 : Y' 0 = p j 0 + s' * (p (j + 1) 0 - p j 0) := by rw [hY']; simp
  have hZ1 : Y' 1 = p j 1 + s' * (p (j + 1) 1 - p j 1) := by rw [hY']; simp
  have hZ0' : Y' 0 = p i 0 + s * E0 + N0 := by linarith only [hN0, hY0]
  have hZ1' : Y' 1 = p i 1 + s * E1 + N1 := by linarith only [hN1, hY1]
  have g1 : ∀ l, 0 ≤ N0 * (p l 0 - p i 0) + N1 * (p l 1 - p i 1) - s * (N0 * E0 + N1 * E1) := by
    intro l
    have := h1 l
    rw [inner2] at this
    simp only [PiLp.sub_apply] at this
    rw [hZ0', hZ1', hY0, hY1] at this
    linarith only [this]
  have g2 : ∀ l, N0 * (p l 0 - p i 0) + N1 * (p l 1 - p i 1) ≤
      N0 * (Y' 0 - p i 0) + N1 * (Y' 1 - p i 1) := by
    intro l
    have := h2 l
    rw [inner2] at this
    simp only [PiLp.sub_apply] at this
    rw [hZ0', hZ1', hY0, hY1] at this
    rw [hZ0', hZ1']
    linarith only [this]
  have hdot : N0 * E0 + N1 * E1 = 0 := by
    have a1 := g1 i
    have a2 := g1 (i + 1)
    have e0 : p (i + 1) 0 - p i 0 = E0 := hE0.symm
    have e1 : p (i + 1) 1 - p i 1 = E1 := hE1.symm
    rw [e0, e1] at a2
    simp only [sub_self, mul_zero, add_zero, zero_sub] at a1
    apply le_antisymm
    · by_contra hh; push Not at hh
      nlinarith only [mul_pos hs0 hh, a1]
    · by_contra hh; push Not at hh
      nlinarith only [mul_neg_of_pos_of_neg (sub_pos.mpr hs1) hh, a2, hs1]
  have hcr0' : 0 < E0 * (p l0 1 - p i 1) - E1 * (p l0 0 - p i 0) := by
    simp only [cross2, PiLp.sub_apply] at hcr0
    rw [hE0, hE1]; exact hcr0
  have hEE : 0 < E0 ^ 2 + E1 ^ 2 := by
    by_contra hh; push Not at hh
    have e0 : E0 = 0 := by
      have : E0 ^ 2 = 0 := le_antisymm (by nlinarith only [hh, sq_nonneg E1]) (sq_nonneg _)
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    have e1 : E1 = 0 := by
      have : E1 ^ 2 = 0 := le_antisymm (by nlinarith only [hh, sq_nonneg E0]) (sq_nonneg _)
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    rw [e0, e1] at hcr0'; simp at hcr0'
  have hκ0 : 0 ≤ E0 * N1 - E1 * N0 := by
    have a' : 0 ≤ N0 * (p l0 0 - p i 0) + N1 * (p l0 1 - p i 1) := by
      have := g1 l0; rw [hdot] at this; linarith only [this]
    have key := core_lag E0 E1 N0 N1 (p l0 0 - p i 0) (p l0 1 - p i 1) hdot
    by_contra hh; push Not at hh
    nlinarith only [mul_nonneg hEE.le a', mul_neg_of_neg_of_pos hh hcr0', key]
  have hκ : 0 < E0 * N1 - E1 * N0 := by
    refine lt_of_le_of_ne hκ0 ?_
    intro hz
    have h0 : N0 ^ 2 + N1 ^ 2 = 0 := by
      have : (E0 ^ 2 + E1 ^ 2) * (N0 ^ 2 + N1 ^ 2) = 0 := by
        have := core_lag E0 E1 N0 N1 N0 N1 hdot
        rw [← hz] at this
        linarith only [this, hz]
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hEE.ne'
      · exact h
    have n0 : N0 = 0 := by
      have : N0 ^ 2 = 0 := le_antisymm (by nlinarith only [h0, sq_nonneg N1]) (sq_nonneg _)
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    have n1 : N1 = 0 := by
      have : N1 ^ 2 = 0 := le_antisymm (by nlinarith only [h0, sq_nonneg N0]) (sq_nonneg _)
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    apply hne
    ext m; fin_cases m
    · simp; linarith only [hN0, n0]
    · simp; linarith only [hN1, n1]
  obtain ⟨a, ha⟩ : ∃ a : ZMod k → ℝ,
      a = fun l => E0 * (p l 1 - p i 1) - E1 * (p l 0 - p i 0) := ⟨_, rfl⟩
  have hlev : ∀ l, a l ≤ E0 * (Y' 1 - p i 1) - E1 * (Y' 0 - p i 0) := by
    intro l
    have b' := g2 l
    have k1 := core_lag E0 E1 N0 N1 (p l 0 - p i 0) (p l 1 - p i 1) hdot
    have k2 := core_lag E0 E1 N0 N1 (Y' 0 - p i 0) (Y' 1 - p i 1) hdot
    have : (E0 ^ 2 + E1 ^ 2) * (N0 * (p l 0 - p i 0) + N1 * (p l 1 - p i 1)) ≤
        (E0 ^ 2 + E1 ^ 2) * (N0 * (Y' 0 - p i 0) + N1 * (Y' 1 - p i 1)) :=
      mul_le_mul_of_nonneg_left b' hEE.le
    rw [k1, k2] at this
    have := le_of_mul_le_mul_left this hκ
    simpa [ha] using this
  have hW : E0 * (Y' 1 - p i 1) - E1 * (Y' 0 - p i 0) = (1 - s') * a j + s' * a (j + 1) := by
    rw [hZ0, hZ1, ha]; ring
  have hant : ∀ l, l ≠ c i → a l < a (c i) := fun l hl => by
    have := hanti i l hl
    simp only [cross2, PiLp.sub_apply] at this
    rw [ha]; simp only; rw [hE0, hE1]; exact this
  have hcl := hlev (c i)
  rw [hW] at hcl
  have hjc : (s' = 0 ∧ j = c i) ∨ (s' = 1 ∧ j + 1 = c i) := by
    have hj1 : j + 1 ≠ j := (zmod_ne_add_one (by have := hp.1; omega) j).symm
    by_cases hj : j = c i
    · left
      refine ⟨?_, hj⟩
      have hj' : j + 1 ≠ c i := by rw [← hj]; exact hj1
      have h3 := hant _ hj'
      rw [← hj] at hcl h3
      by_contra hs0'
      have h4 : 0 < s' := lt_of_le_of_ne hs'0 (Ne.symm hs0')
      nlinarith only [mul_pos h4 (sub_pos.mpr h3), hcl]
    · right
      by_cases hj' : j + 1 = c i
      · refine ⟨?_, hj'⟩
        have h3 := hant _ hj
        rw [← hj'] at hcl h3
        by_contra hs1'
        have h4 : s' < 1 := lt_of_le_of_ne hs'1 hs1'
        nlinarith only [mul_pos (sub_pos.mpr h4) (sub_pos.mpr h3), hcl]
      · exfalso
        have a1 := hant _ hj
        have a2 := hant _ hj'
        nlinarith only [mul_nonneg (sub_nonneg.mpr hs'1) (sub_nonneg.mpr a1.le),
          mul_nonneg hs'0 (sub_nonneg.mpr a2.le), hcl, a1, a2, hs'0, hs'1]
  obtain ⟨hYc0, hYc1, hdc⟩ : Y' 0 = p (c i) 0 ∧ Y' 1 = p (c i) 1 ∧
      (1 - s') * z j + s' * z (j + 1) = z (c i) := by
    rcases hjc with ⟨rfl, rfl⟩ | ⟨rfl, h⟩
    · refine ⟨?_, ?_, by simp⟩
      · rw [hZ0]; simp
      · rw [hZ1]; simp
    · rw [← h]
      refine ⟨?_, ?_, by simp⟩
      · rw [hZ0]; simp
      · rw [hZ1]; simp
  have hEE' : ⟪p (i + 1) - p i, p (i + 1) - p i⟫ = E0 ^ 2 + E1 ^ 2 := by
    rw [inner2]; simp only [PiLp.sub_apply]; rw [← hE0, ← hE1]; ring
  have ht : ⟪p (c i) - p i, p (i + 1) - p i⟫ = s * (E0 ^ 2 + E1 ^ 2) := by
    rw [inner2]; simp only [PiLp.sub_apply]; rw [← hE0, ← hE1]
    have n0 : N0 = p (c i) 0 - p i 0 - s * E0 := by linarith only [hN0, hYc0, hY0]
    have n1 : N1 = p (c i) 1 - p i 1 - s * E1 := by linarith only [hN1, hYc1, hY1]
    rw [n0, n1] at hdot
    linarith only [hdot]
  have hf := hfoot i (by rw [ht]; exact mul_pos hs0 hEE)
    (by rw [ht, hEE']; nlinarith only [hs1, hEE])
  apply hf
  rw [ht, hEE']
  rw [hdc] at hdep
  rw [hdep]; ring

theorem seg_param (q1 q2 : ℝ²) (t1 t2 : ℝ) {y : ℝ³}
    (hy : y ∈ segment ℝ (liftPt q1 t1) (liftPt q2 t2)) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ proj_xy y = q1 + s • (q2 - q1) ∧ y 2 = (1 - s) * t1 + s * t2 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  have ha' : a = 1 - b := by linarith
  subst ha'
  refine ⟨b, hb, by linarith, ?_, ?_⟩
  · rw [← projL_apply, map_add, map_smul, map_smul, projL_apply, projL_apply, proj_xy_liftPt,
      proj_xy_liftPt]
    module
  · simp [liftPt_two]

/-- **Lemma HA (plane).** -/
theorem hdr_noHDN {k : ℕ} [NeZero k] (p : ZMod k → ℝ²) (z : ZMod k → ℝ) (hp : IsCcwPolygon p)
    (hz : Function.Injective z) (c : ZMod k → ZMod k)
    (hanti : ∀ i l, l ≠ c i →
      cross2 (p (i + 1) - p i) (p l - p i) < cross2 (p (i + 1) - p i) (p (c i) - p i))
    (hfoot : ∀ i, 0 < ⟪p (c i) - p i, p (i + 1) - p i⟫ →
      ⟪p (c i) - p i, p (i + 1) - p i⟫ < ⟪p (i + 1) - p i, p (i + 1) - p i⟫ →
      ⟪p (i + 1) - p i, p (i + 1) - p i⟫ * z (c i) ≠
        (⟪p (i + 1) - p i, p (i + 1) - p i⟫ - ⟪p (c i) - p i, p (i + 1) - p i⟫) * z i +
          ⟪p (c i) - p i, p (i + 1) - p i⟫ * z (i + 1)) :
    ¬ HasHorizontalDoubleNormal p z := by
  rintro ⟨y, y', ⟨i, hyi⟩, ⟨j, hyj⟩, hdep, hne, hn1, hn2⟩
  obtain ⟨s, hs0, hs1, hY, hYd⟩ := seg_param _ _ _ _ hyi
  obtain ⟨s', hs'0, hs'1, hY', hYd'⟩ := seg_param _ _ _ _ hyj
  have h1 : ∀ l, ⟪proj_xy y - proj_xy y', p l - proj_xy y⟫ ≤ 0 := fun l =>
    hn2 (p l) (subset_convexHull ℝ _ ⟨l, rfl⟩)
  have h2 : ∀ l, ⟪proj_xy y' - proj_xy y, p l - proj_xy y'⟫ ≤ 0 := fun l =>
    hn1 (p l) (subset_convexHull ℝ _ ⟨l, rfl⟩)
  by_cases hi : 0 < s ∧ s < 1
  · exact hdr_core p z hp c hanti hfoot hi.1 hi.2 hs'0 hs'1 hY hY' hne h1 h2
      (by rw [← hYd, ← hYd', hdep])
  by_cases hj : 0 < s' ∧ s' < 1
  · exact hdr_core p z hp c hanti hfoot hj.1 hj.2 hs0 hs1 hY' hY hne.symm h2 h1
      (by rw [← hYd, ← hYd', hdep])
  · have corner : ∀ (i : ZMod k) (s : ℝ), 0 ≤ s → s ≤ 1 → ¬ (0 < s ∧ s < 1) →
        ∃ m, (p i + s • (p (i + 1) - p i) = p m) ∧ (1 - s) * z i + s * z (i + 1) = z m := by
      intro i s h0 h1 h
      have : s = 0 ∨ s = 1 := by
        by_contra hh; push Not at hh
        exact h ⟨lt_of_le_of_ne h0 (Ne.symm hh.1), lt_of_le_of_ne h1 hh.2⟩
      rcases this with rfl | rfl
      · exact ⟨i, by simp, by simp⟩
      · exact ⟨i + 1, by simp, by simp⟩
    obtain ⟨m, hm, hmd⟩ := corner i s hs0 hs1 hi
    obtain ⟨m', hm', hmd'⟩ := corner j s' hs'0 hs'1 hj
    have : m = m' := hz (by rw [← hmd, ← hmd', ← hYd, ← hYd', hdep])
    subst this
    exact hne (by rw [hY, hY', hm, hm'])

section bridge
open Minimality.HDNApex

theorem depth_rot {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) {u : ℝ³} {r : ℝ}
    (hRu : R.toEuclideanLin u = r • ez) (a : ℝ³) : r * (R.toEuclideanLin a) 2 = ⟪a, u⟫ := by
  have := inner_toEuclideanLin_SO3 hR a u
  rw [hRu, real_inner_smul_right] at this
  rw [← this]
  simp [ez, PiLp.inner_apply]

theorem inner_proj_rot {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) {u : ℝ³} {r : ℝ} (hr : r ≠ 0)
    (hRu : R.toEuclideanLin u = r • ez) (a b : ℝ³) :
    ⟪proj_xy (R.toEuclideanLin a), proj_xy (R.toEuclideanLin b)⟫ = scr u a b := by
  have h1 := inner_toEuclideanLin_SO3 hR a b
  have h2 := inner_toEuclideanLin_SO3 hR u u
  rw [hRu] at h2
  have e2 : ⟪u, u⟫ = r ^ 2 := by
    rw [← h2, real_inner_smul_left, real_inner_smul_right]; simp [ez]; ring
  have da := depth_rot hR hRu a
  have db := depth_rot hR hRu b
  have e1 : ⟪a, b⟫ = ⟪proj_xy (R.toEuclideanLin a), proj_xy (R.toEuclideanLin b)⟫ +
      (R.toEuclideanLin a) 2 * (R.toEuclideanLin b) 2 := by
    rw [← h1]
    simp [proj_xy, PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two]; ring
  unfold scr
  rw [e2, ← da, ← db, e1]
  field_simp
  ring

/-- **Rim-only no HDN from the antipodal conditions, in space** (Lemma HA at the view `u`). -/
theorem noHDNRim_of_anti {k : ℕ} [NeZero k] {p : ZMod k → ℝ³} {u : ℝ³}
    (hk : 3 ≤ k) (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (p (i + 1) - p i) (p j - p i) u)
    (hinj : Function.Injective fun i => ⟪p i, u⟫) (c : ZMod k → ZMod k)
    (hanti : ∀ i l, l ≠ c i →
      det3 (p (i + 1) - p i) (p l - p i) u < det3 (p (i + 1) - p i) (p (c i) - p i) u)
    (hfoot : ∀ i, 0 < scr u (p (c i) - p i) (p (i + 1) - p i) →
      scr u (p (c i) - p i) (p (i + 1) - p i) < scr u (p (i + 1) - p i) (p (i + 1) - p i) →
      scr u (p (i + 1) - p i) (p (i + 1) - p i) * ⟪p (c i), u⟫ ≠
        (scr u (p (i + 1) - p i) (p (i + 1) - p i) - scr u (p (c i) - p i) (p (i + 1) - p i)) *
          ⟪p i, u⟫ + scr u (p (c i) - p i) (p (i + 1) - p i) * ⟪p (i + 1), u⟫) :
    NoHDNRim p u := by
  intro R hR r hr hRu hccw
  have hcrx : ∀ i l, r * cross2 (proj_xy (R.toEuclideanLin (p (i + 1) - p i)))
      (proj_xy (R.toEuclideanLin (p l - p i))) = det3 (p (i + 1) - p i) (p l - p i) u :=
    fun i l => cross2_proj_rot hR hRu _ _
  have hrpos : 0 < r := by
    obtain ⟨l0, h0, h1⟩ := exists_other hk 0
    have a := hcyc 0 l0 h0 h1
    have b := hccw.2 0 l0 h0 h1
    simp only [proj_rot_sub] at b
    rw [← hcrx] at a
    by_contra hh; push Not at hh
    nlinarith only [mul_nonneg_of_nonpos_of_nonpos hh hh, a, b, hh]
  refine hdr_noHDN (fun i => proj_xy (R.toEuclideanLin (p i))) (fun i => (R.toEuclideanLin (p i)) 2)
    hccw ?_ c ?_ ?_
  · intro i j h
    refine hinj ?_
    show ⟪p i, u⟫ = ⟪p j, u⟫
    rw [← depth_rot hR hRu, ← depth_rot hR hRu]
    simp only at h; rw [h]
  · intro i l hl
    simp only [proj_rot_sub]
    have := hanti i l hl
    rw [← hcrx, ← hcrx] at this
    exact lt_of_mul_lt_mul_left this hrpos.le
  · intro i h0 h1
    simp only [proj_rot_sub, inner_proj_rot hR hr hRu] at h0 h1 ⊢
    intro heq
    apply hfoot i h0 h1
    have xc := depth_rot hR hRu (p (c i))
    have xi := depth_rot hR hRu (p i)
    have xi1 := depth_rot hR hRu (p (i + 1))
    linear_combination r * heq - (scr u (p (i + 1) - p i) (p (i + 1) - p i)) * xc +
      (scr u (p (i + 1) - p i) (p (i + 1) - p i) - scr u (p (c i) - p i) (p (i + 1) - p i)) * xi +
      scr u (p (c i) - p i) (p (i + 1) - p i) * xi1

end bridge

/-! ### `EdgeRim'`: the edge rim with a rim-only no-HDN hypothesis -/

/-- `EdgeRim` with `NoHDNRim` of the rim cycle `x ∘ r` in place of `NoHDNAt` of its point set. -/
def EdgeRim' (x : Fin 7 → ℝ³) (u : ℝ³) (d : Fin 7) (h : ℝ) (k : ℕ) [NeZero k]
    (r : ZMod k → Fin 7) : Prop :=
  3 ≤ k ∧ h ≠ 0 ∧ x d = x (r 0) - h • u ∧
    (∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (r (i + 1)) - x (r i)) (x (r j) - x (r i)) u) ∧
    (∀ v, v ≠ d → (∀ j, v ≠ r j) → ∀ i,
      0 < det3 (x (r (i + 1)) - x (r i)) (x v - x (r i)) u) ∧
    Function.Injective (fun i => ⟪x (r i), u⟫) ∧
    NoHDNRim (fun i => x (r i)) u

theorem EdgeRim.toRim' {x : Fin 7 → ℝ³} {u : ℝ³} {d : Fin 7} {h : ℝ} {k : ℕ} [NeZero k]
    {r : ZMod k → Fin 7} (hR : EdgeRim x u d h k r) : EdgeRim' x u d h k r := by
  obtain ⟨a, b, c, d', e, f, g⟩ := hR
  exact ⟨a, b, c, d', e, f, g.rim _ (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩

/-- Theorem 8.10 with 8.9 at an `EdgeRim'` view (rim-only no HDN). -/
theorem isRupert_edgeRim_dsp_rim {x : Fin 7 → ℝ³} {u : ℝ³} (hu : u ≠ 0) {d : Fin 7} {h : ℝ}
    {k : ℕ} [NeZero k] {r : ZMod k → Fin 7} (hR : EdgeRim' x u d h k r) {a c : ZMod k}
    (hpp : ParPairAt (fun i => x (r i)) u a c) (hds : DepthSepZ (fun i => ⟪x (r i), u⟫) a c) :
    IsRupert (Finset.univ.image x) := by
  classical
  obtain ⟨hk, hh, hd, hcyc, hrest, -, hnd⟩ := hR
  refine isRupert_of_edgeView_depthSeparated_rim (Finset.univ.image x) ∅ u hu hk
    (fun i => x (r i)) 0 (x d) h (Finset.mem_image_of_mem x (Finset.mem_univ _)) hd hh
    (fun i => Finset.mem_image_of_mem x (Finset.mem_univ _))
    (fun _ => Finset.notMem_empty _) hcyc ?_ (depthSepAt_of hpp hds) hnd
    (fun m hm => absurd hm (Finset.notMem_empty _))
  intro v hv _ hvw hvp i
  obtain ⟨v', -, rfl⟩ := Finset.mem_image.mp hv
  exact hrest v' (fun e => hvw (by rw [e])) (fun j e => hvp j (by rw [e])) i

/-- **An `EdgeRim'` from the determinant tests, injective depths and the antipodal conditions.** -/
theorem edgeRim'_of_anti {x : Fin 7 → ℝ³} {u : ℝ³} {d : Fin 7} {h : ℝ} {k : ℕ} [NeZero k]
    {r : ZMod k → Fin 7} (hk : 3 ≤ k) (hh : h ≠ 0) (hd : x d = x (r 0) - h • u)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (r (i + 1)) - x (r i)) (x (r j) - x (r i)) u)
    (hrest : ∀ v, v ≠ d → (∀ j, v ≠ r j) → ∀ i,
      0 < det3 (x (r (i + 1)) - x (r i)) (x v - x (r i)) u)
    (hinj : Function.Injective (fun i => ⟪x (r i), u⟫)) (c : ZMod k → ZMod k)
    (hanti : ∀ i l, l ≠ c i →
      det3 (x (r (i + 1)) - x (r i)) (x (r l) - x (r i)) u <
        det3 (x (r (i + 1)) - x (r i)) (x (r (c i)) - x (r i)) u)
    (hfoot : ∀ i, 0 < HDNApex.scr u (x (r (c i)) - x (r i)) (x (r (i + 1)) - x (r i)) →
      HDNApex.scr u (x (r (c i)) - x (r i)) (x (r (i + 1)) - x (r i)) <
        HDNApex.scr u (x (r (i + 1)) - x (r i)) (x (r (i + 1)) - x (r i)) →
      HDNApex.scr u (x (r (i + 1)) - x (r i)) (x (r (i + 1)) - x (r i)) * ⟪x (r (c i)), u⟫ ≠
        (HDNApex.scr u (x (r (i + 1)) - x (r i)) (x (r (i + 1)) - x (r i)) -
          HDNApex.scr u (x (r (c i)) - x (r i)) (x (r (i + 1)) - x (r i))) * ⟪x (r i), u⟫ +
          HDNApex.scr u (x (r (c i)) - x (r i)) (x (r (i + 1)) - x (r i)) *
            ⟪x (r (i + 1)), u⟫) :
    EdgeRim' x u d h k r :=
  ⟨hk, hh, hd, hcyc, hrest, hinj,
    noHDNRim_of_anti (p := fun i => x (r i)) hk hcyc hinj c hanti hfoot⟩

end Minimality.HDNRim
