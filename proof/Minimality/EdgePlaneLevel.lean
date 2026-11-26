module

public import Minimality.SplitEdgePlane

/-!
# The level-extremum arch is an Edge-Plane view (up to perturbation)

Job LLEV (Carbon A72 Theorem 1.3(c), the Level-Edge EP Criterion; used as Lemma 2.2 of A75 and A77).
A strict rim `lab : ZMod k → Fin n` of a view `w₀` with `HiddenInTriangles` and a level rim edge
`⟪E_a, w₀⟫ = 0` (`E_i = X_{i+1} - X_i`, `X_i = x (lab i)`), whose other `k - 2` vertices lie strictly on one side
of the level (`0 < ε ⟪X_j - X_a, w₀⟫`, `ε = ±1`; the level pair is the strict shallowest / deepest pair), and whose
interior angles at `X_a`, `X_{a+1}` sum to less than `π` (`det3 E_{a-1} E_{a+1} w₀ < 0`), gives `Gen.EdgePlaneAny x`.

Conventions: `StrictRimN` says every other point is strictly left of every rim edge (ccw rim) in the sense
`0 < det3 E_i (X_m - X_i) w₀`, with `det3 p q w = ⟪p × q, w⟫`; this is Carbon's orientation, so
`det3 E_{a-1} E_{a+1} w₀ < 0` is exactly `sin(φ_a + φ_{a+1}) < 0` for the exterior angles, i.e. the two interior
angles at `X_a`, `X_{a+1}` sum to `< π`.  No sign of the statement had to be changed.

Proof.  Tilt `w_t = w₀ + t v`, `v = -τ E_a`, and take `α = t |E_a|²/2`, `μ = τ`, `s = -s̃ D(t)` with `D(t) = ⟪E_a, w_t⟫`.
The `1/D` of `edgePlaneSpin` cancels, every row becomes a polynomial `rowT` in `t`, and at `t = 0` it equals
`Z_j(w₀) ⟪U, E_i⟫` with `U = ν (E_a × w₀) - m E_a`; rows `(a-1, a)` and `(a+1, a+1)` are exactly `α A_{a-1}` and
`(α + μ D) A_{a+1}`.  The arch condition makes the interval for `(ν, m)` nonempty (`harch_id`), and then
`⟪U, E_i⟫ > 0` for all `i ≠ a` by convexity (`mono_pos`: Cramer identity at `w₀`).
-/

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.Split.Level

variable {n : ℕ}

theorem det3_cross_id (E d w : ℝ³) :
    det3 E (cross d w) w = ⟪d, w⟫ * ⟪E, w⟫ - ⟪w, w⟫ * ⟪E, d⟫ := by
  simp only [inner3, det3, cross_0, cross_1, cross_2]; ring

/-- The harch identity: for `q ⊥ w`, `⟪p,q⟫ [r,q] - ⟪r,q⟫ [p,q] = -|q|² [p,r]` (2-D, `[,] = det3 · · w`). -/
theorem harch_id (p q r w : ℝ³) (h : ⟪q, w⟫ = 0) :
    ⟪p, q⟫ * det3 r q w - ⟪r, q⟫ * det3 p q w = -(⟪q, q⟫ * det3 p r w) := by
  have hh : det3 p r q * ⟪q, w⟫ = 0 := by rw [h, mul_zero]
  simp only [inner3, det3] at hh ⊢
  linear_combination hh

/-- Cramer: a functional `⟪U, ·⟫` killing `w`. -/
theorem cramer_inner (U e1 e2 P w : ℝ³) (h : ⟪U, w⟫ = 0) :
    det3 e1 e2 w * ⟪U, P⟫ = det3 P e2 w * ⟪U, e1⟫ + det3 e1 P w * ⟪U, e2⟫ := by
  have hh : det3 e1 e2 P * ⟪U, w⟫ = 0 := by rw [h, mul_zero]
  simp only [inner3, det3] at hh ⊢
  linear_combination hh

theorem inner_cross_det (a w E : ℝ³) : ⟪cross a w, E⟫ = det3 E a w := by
  simp only [inner3, det3, cross_0, cross_1, cross_2]; ring

theorem zk {k : ℕ} [NeZero k] (hk : 3 ≤ k) : (1 : ZMod k) ≠ 0 ∧ (2 : ZMod k) ≠ 0 := by
  constructor
  · intro h
    have h1 : ((1 : ℕ) : ZMod k) = 0 := by simpa using h
    have := Nat.le_of_dvd one_pos ((ZMod.natCast_eq_zero_iff 1 k).1 h1)
    omega
  · intro h
    have h1 : ((2 : ℕ) : ZMod k) = 0 := by simpa using h
    have := Nat.le_of_dvd two_pos ((ZMod.natCast_eq_zero_iff 2 k).1 h1)
    omega

theorem zk_ne {k : ℕ} [NeZero k] (hk : 3 ≤ k) (i : ZMod k) :
    i + 1 ≠ i ∧ i + 1 + 1 ≠ i ∧ i - 1 ≠ i ∧ i + 1 + 1 ≠ i + 1 ∧ i - 1 ≠ i + 1 := by
  obtain ⟨h1, h2⟩ := zk hk
  refine ⟨fun h => h1 ?_, fun h => h2 ?_, fun h => h1 ?_, fun h => h1 ?_, zmod_pred_ne_succ hk i⟩
  · calc (1 : ZMod k) = (i + 1) - i := by ring
      _ = 0 := by rw [h]; ring
  · calc (2 : ZMod k) = (i + 1 + 1) - i := by ring
      _ = 0 := by rw [h]; ring
  · calc (1 : ZMod k) = i - (i - 1) := by ring
      _ = 0 := by rw [h]; ring
  · calc (1 : ZMod k) = (i + 1 + 1) - (i + 1) := by ring
      _ = 0 := by rw [h]; ring

/-- The signs of the two angle determinants at the level edge. -/
theorem signsA {k : ℕ} [NeZero k] (hk : 3 ≤ k) (X : ZMod k → ℝ³) (w : ℝ³) (a : ZMod k)
    (hcyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < det3 (X (i + 1) - X i) (X j - X i) w) :
    0 < det3 (X a - X (a - 1)) (X (a + 1) - X a) w ∧
      det3 (X (a + 1 + 1) - X (a + 1)) (X (a + 1) - X a) w < 0 := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := zk_ne hk a
  constructor
  · have t1 := hcyc (a - 1) (a + 1) (Ne.symm n5) (by rw [sub_add_cancel]; exact n1)
    rw [sub_add_cancel] at t1
    have e : det3 (X a - X (a - 1)) (X (a + 1) - X (a - 1)) w =
        det3 (X a - X (a - 1)) (X (a + 1) - X a) w := by
      simp only [det3, PiLp.sub_apply]; ring
    linarith
  · have t1 := hcyc a (a + 1 + 1) n2 n4
    have e : det3 (X (a + 1) - X a) (X (a + 1 + 1) - X a) w =
        -det3 (X (a + 1 + 1) - X (a + 1)) (X (a + 1) - X a) w := by
      simp only [det3, PiLp.sub_apply]; ring
    linarith

/-- Convexity step: a functional increasing along the two edges next to the level edge and decreasing along it
is increasing along every other edge. -/
theorem mono_pos {k : ℕ} [NeZero k] (hk : 3 ≤ k) (X : ZMod k → ℝ³) (w U : ℝ³) (a : ZMod k)
    (hcyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < det3 (X (i + 1) - X i) (X j - X i) w)
    (hUw : ⟪U, w⟫ = 0) (h0 : ⟪U, X (a + 1) - X a⟫ < 0) (h1 : 0 < ⟪U, X a - X (a - 1)⟫)
    (h2 : 0 < ⟪U, X (a + 1 + 1) - X (a + 1)⟫) :
    ∀ i, i ≠ a → 0 < ⟪U, X (i + 1) - X i⟫ := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := zk_ne hk a
  have hsA : det3 (X (a + 1) - X a) (X a - X (a - 1)) w < 0 := by
    have := (signsA hk X w a hcyc).1
    have e : det3 (X (a + 1) - X a) (X a - X (a - 1)) w =
        -det3 (X a - X (a - 1)) (X (a + 1) - X a) w := by
      simp only [det3, PiLp.sub_apply]; ring
    linarith
  have hsA' : det3 (X a - X (a + 1)) (X (a + 1 + 1) - X (a + 1)) w < 0 := by
    have := hcyc a (a + 1 + 1) n2 n4
    have e : det3 (X a - X (a + 1)) (X (a + 1 + 1) - X (a + 1)) w =
        -det3 (X (a + 1) - X a) (X (a + 1 + 1) - X a) w := by
      simp only [det3, PiLp.sub_apply]; ring
    linarith
  have hlow : ∀ j, j ≠ a → j ≠ a + 1 → ⟪U, X j - X a⟫ < 0 := by
    intro j hja hja1
    by_cases hj : j = a - 1
    · subst hj
      rw [inner_sub_right] at h1 ⊢
      linarith
    · have sB : det3 (X j - X a) (X a - X (a - 1)) w < 0 := by
        have t := hcyc (a - 1) j hj (by rw [sub_add_cancel]; exact hja)
        rw [sub_add_cancel] at t
        have e : det3 (X j - X a) (X a - X (a - 1)) w =
            -det3 (X a - X (a - 1)) (X j - X (a - 1)) w := by
          simp only [det3, PiLp.sub_apply]; ring
        linarith
      have sC : 0 < det3 (X (a + 1) - X a) (X j - X a) w := hcyc a j hja hja1
      have cr := cramer_inner U (X (a + 1) - X a) (X a - X (a - 1)) (X j - X a) w hUw
      simp only [inner_sub_right] at cr h0 h1 ⊢
      by_contra hge
      push Not at hge
      nlinarith [mul_pos_of_neg_of_neg sB (show _ < (0 : ℝ) from by linarith : ⟪U, X (a + 1)⟫ - ⟪U, X a⟫ < 0),
        mul_pos sC (show (0 : ℝ) < ⟪U, X a⟫ - ⟪U, X (a - 1)⟫ from h1),
        mul_nonneg (neg_nonneg.2 hsA.le) (show (0 : ℝ) ≤ ⟪U, X j⟫ - ⟪U, X a⟫ by linarith)]
  have hup : ∀ j, j ≠ a → j ≠ a + 1 → 0 < ⟪U, X j - X (a + 1)⟫ := by
    intro j hja hja1
    by_cases hj : j = a + 1 + 1
    · subst hj; exact h2
    · have sB : det3 (X j - X (a + 1)) (X (a + 1 + 1) - X (a + 1)) w < 0 := by
        have t := hcyc (a + 1) j hja1 hj
        have e : det3 (X j - X (a + 1)) (X (a + 1 + 1) - X (a + 1)) w =
            -det3 (X (a + 1 + 1) - X (a + 1)) (X j - X (a + 1)) w := by
          simp only [det3, PiLp.sub_apply]; ring
        linarith
      have sC : det3 (X a - X (a + 1)) (X j - X (a + 1)) w < 0 := by
        have t := hcyc a j hja hja1
        have e : det3 (X a - X (a + 1)) (X j - X (a + 1)) w =
            -det3 (X (a + 1) - X a) (X j - X a) w := by
          simp only [det3, PiLp.sub_apply]; ring
        linarith
      have cr := cramer_inner U (X a - X (a + 1)) (X (a + 1 + 1) - X (a + 1)) (X j - X (a + 1)) w hUw
      simp only [inner_sub_right] at cr h0 h2 ⊢
      by_contra hge
      push Not at hge
      nlinarith [mul_neg_of_neg_of_pos sB (show (0 : ℝ) < ⟪U, X a⟫ - ⟪U, X (a + 1)⟫ by linarith),
        mul_neg_of_neg_of_pos sC (show (0 : ℝ) < ⟪U, X (a + 1 + 1)⟫ - ⟪U, X (a + 1)⟫ from h2),
        mul_nonneg_of_nonpos_of_nonpos hsA'.le (show ⟪U, X j⟫ - ⟪U, X (a + 1)⟫ ≤ (0 : ℝ) by linarith)]
  intro i hia
  by_cases hi1 : i = a - 1
  · subst hi1; rw [sub_add_cancel]; exact h1
  by_cases hi2 : i = a + 1
  · subst hi2; exact h2
  have hl := hlow i hia hi2
  have hu := hup i hia hi2
  have sD : 0 < det3 (X (i + 1) - X i) (X (a + 1) - X i) w :=
    hcyc i (a + 1) (Ne.symm hi2) (fun h => hia (add_right_cancel h).symm)
  have sE : det3 (X a - X i) (X (i + 1) - X i) w < 0 := by
    have t := hcyc i a (Ne.symm hia) (fun h => hi1 (eq_sub_of_add_eq h.symm))
    have e : det3 (X a - X i) (X (i + 1) - X i) w = -det3 (X (i + 1) - X i) (X a - X i) w := by
      simp only [det3, PiLp.sub_apply]; ring
    linarith
  have sF : 0 < det3 (X a - X i) (X (a + 1) - X i) w := by
    have t := hcyc a i hia hi2
    have e : det3 (X a - X i) (X (a + 1) - X i) w = det3 (X (a + 1) - X a) (X i - X a) w := by
      simp only [det3, PiLp.sub_apply]; ring
    linarith
  have cr := cramer_inner U (X a - X i) (X (a + 1) - X i) (X (i + 1) - X i) w hUw
  simp only [inner_sub_right] at cr hl hu ⊢
  by_contra hge
  push Not at hge
  nlinarith [mul_pos sD (show (0 : ℝ) < ⟪U, X a⟫ - ⟪U, X i⟫ by linarith),
    mul_pos_of_neg_of_neg sE (show ⟪U, X (a + 1)⟫ - ⟪U, X i⟫ < (0 : ℝ) by linarith),
    mul_nonneg sF.le (show (0 : ℝ) ≤ -(⟪U, X (i + 1)⟫ - ⟪U, X i⟫) by linarith)]


/-- Reals: an interval for `(ν, m)`. -/
theorem exists_nu_m (A1 A2 g1 g2 : ℝ) (h1 : 0 < A1) (h2 : A2 < 0) (h3 : 0 < g1 * A2 - g2 * A1) :
    ∃ ν m : ℝ, (ν = 1 ∨ ν = -1) ∧ 0 < m ∧ 0 < ν * A1 - m * g1 ∧ 0 < ν * A2 - m * g2 := by
  have hA1 : A1 ≠ 0 := h1.ne'
  have hA2 : A2 ≠ 0 := h2.ne
  have hlo : g1 / A1 < g2 / A2 := by
    have e : g2 / A2 - g1 / A1 = (g1 * A2 - g2 * A1) / (-(A2 * A1)) := by
      field_simp; ring
    have : 0 < g2 / A2 - g1 / A1 := by
      rw [e]; exact div_pos h3 (by nlinarith [mul_neg_of_neg_of_pos h2 h1])
    linarith
  obtain ⟨t, htlo, hthi, ht0⟩ : ∃ t : ℝ, g1 / A1 < t ∧ t < g2 / A2 ∧ t ≠ 0 := by
    by_cases hmid : (g1 / A1 + g2 / A2) / 2 = 0
    · exact ⟨(g2 / A2) / 2, by linarith, by linarith, fun h => by linarith⟩
    · exact ⟨_, by linarith, by linarith, hmid⟩
  have c1 : g1 < t * A1 := (div_lt_iff₀ h1).1 htlo
  have c2 : g2 < t * A2 := (lt_div_iff_of_neg h2).1 hthi
  rcases lt_or_gt_of_ne ht0 with tn | tp
  · refine ⟨-1, -1 / t, Or.inr rfl, div_pos_of_neg_of_neg (by norm_num) tn, ?_, ?_⟩
    · have e : -1 * A1 - (-1 / t) * g1 = (g1 - t * A1) / t := by field_simp; ring
      rw [e]; exact div_pos_of_neg_of_neg (by linarith) tn
    · have e : -1 * A2 - (-1 / t) * g2 = (g2 - t * A2) / t := by field_simp; ring
      rw [e]; exact div_pos_of_neg_of_neg (by linarith) tn
  · refine ⟨1, 1 / t, Or.inl rfl, by positivity, ?_, ?_⟩
    · have e : 1 * A1 - (1 / t) * g1 = (t * A1 - g1) / t := by field_simp
      rw [e]; exact div_pos (by linarith) tp
    · have e : 1 * A2 - (1 / t) * g2 = (t * A2 - g2) / t := by field_simp
      rw [e]; exact div_pos (by linarith) tp

theorem hidden_ev {k : ℕ} [NeZero k] {x : Fin n → ℝ³} {w : ℝ³} {lab : ZMod k → Fin n}
    (h : HiddenInTriangles x w lab) (v : ℝ³) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), HiddenInTriangles x (w + s • v) lab := by
  refine eventually_all.2 fun m => ev_imp fun hm => ?_
  obtain ⟨p, hp, q, hq, r, hr, h1, h2, h3, h4⟩ := h m hm
  filter_upwards [Minimality.eventually_pos_affine (Or.inl h1) (B := det3 (q - p) (r - p) v),
    Minimality.eventually_pos_affine (Or.inl h2) (B := det3 (q - p) (x m - p) v),
    Minimality.eventually_pos_affine (Or.inl h3) (B := det3 (r - q) (x m - q) v),
    Minimality.eventually_pos_affine (Or.inl h4) (B := det3 (p - r) (x m - r) v)] with s s1 s2 s3 s4
  refine ⟨p, hp, q, hq, r, hr, ?_, ?_, ?_, ?_⟩
  · rw [det3_add_smul]; exact s1
  · rw [det3_add_smul]; exact s2
  · rw [det3_add_smul]; exact s3
  · rw [det3_add_smul]; exact s4

/-- The tilted row, with the `1/D` of `edgePlaneSpin` cancelled. -/
noncomputable def rowT {k : ℕ} (X : ZMod k → ℝ³) (w0 v : ℝ³) (a i j : ZMod k) (τ st t : ℝ) : ℝ :=
  (t * (⟪X (a + 1) - X a, X (a + 1) - X a⟫ / 2) + τ * ⟪X j - X a, w0 + t • v⟫) *
      det3 (X (i + 1) - X i) (X (a + 1) - X a) (w0 + t • v)
    - st * t * ⟪X (a + 1) - X a, v⟫ *
      det3 (X (i + 1) - X i) (cross (w0 + t • v) (X j - X a)) (w0 + t • v)
    - st * ⟪X j - X a, w0 + t • v⟫ *
      det3 (X (i + 1) - X i) (cross (X (a + 1) - X a) (w0 + t • v)) (w0 + t • v)

theorem rowT_cont {k : ℕ} (X : ZMod k → ℝ³) (w0 v : ℝ³) (a i j : ZMod k) (τ st : ℝ) :
    Continuous (rowT X w0 v a i j τ st) := by
  unfold rowT
  simp only [det3, inner3, cross_0, cross_1, cross_2, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  fun_prop

theorem rowT_zero {k : ℕ} (X : ZMod k → ℝ³) (w0 v : ℝ³) (a i j : ZMod k) (τ st : ℝ)
    (hlev : ⟪X (a + 1) - X a, w0⟫ = 0) :
    rowT X w0 v a i j τ st 0 = ⟪X j - X a, w0⟫ *
      (τ * det3 (X (i + 1) - X i) (X (a + 1) - X a) w0 +
        st * ⟪w0, w0⟫ * ⟪X (i + 1) - X i, X (a + 1) - X a⟫) := by
  unfold rowT
  simp only [zero_smul, add_zero, zero_mul, mul_zero, zero_add, sub_zero]
  rw [det3_cross_id, hlev]
  ring

/-- The actual Edge-Plane row at the tilted view equals `rowT`. -/
theorem rowT_eq {k : ℕ} (X : ZMod k → ℝ³) (w0 v : ℝ³) (a i j : ZMod k) (τ st t : ℝ)
    (hlev : ⟪X (a + 1) - X a, w0⟫ = 0) (hc : ⟪X (a + 1) - X a, v⟫ ≠ 0) (ht : t ≠ 0) :
    (t * (⟪X (a + 1) - X a, X (a + 1) - X a⟫ / 2) + τ * ⟪X j - X a, w0 + t • v⟫) *
        det3 (X (i + 1) - X i) (X (a + 1) - X a) (w0 + t • v) +
      (-st * t * ⟪X (a + 1) - X a, v⟫) * edgePlaneSpin X (w0 + t • v) a i j =
    rowT X w0 v a i j τ st t := by
  have hD : ⟪X (a + 1) - X a, w0 + t • v⟫ = t * ⟪X (a + 1) - X a, v⟫ := by
    rw [inner_add_right, hlev, real_inner_smul_right, zero_add]
  unfold edgePlaneSpin rowT
  rw [hD]
  field_simp
  ring

theorem rowT_a {k : ℕ} (X : ZMod k → ℝ³) (w0 v : ℝ³) (a i : ZMod k) (τ st t : ℝ) :
    rowT X w0 v a i a τ st t = t * (⟪X (a + 1) - X a, X (a + 1) - X a⟫ / 2) *
      det3 (X (i + 1) - X i) (X (a + 1) - X a) (w0 + t • v) := by
  unfold rowT
  have h0 : det3 (X (i + 1) - X i) (cross (w0 + t • v) 0) (w0 + t • v) = 0 := by
    simp [det3, cross_0, cross_1, cross_2]
  simp only [sub_self, inner_zero_left, mul_zero, add_zero, zero_mul, sub_zero]
  rw [h0]; ring

theorem rowT_a1 {k : ℕ} (X : ZMod k → ℝ³) (w0 v : ℝ³) (a i : ZMod k) (τ st t : ℝ)
    (hlev : ⟪X (a + 1) - X a, w0⟫ = 0) :
    rowT X w0 v a i (a + 1) τ st t =
      (t * (⟪X (a + 1) - X a, X (a + 1) - X a⟫ / 2) + τ * (t * ⟪X (a + 1) - X a, v⟫)) *
        det3 (X (i + 1) - X i) (X (a + 1) - X a) (w0 + t • v) := by
  have hD : ⟪X (a + 1) - X a, w0 + t • v⟫ = t * ⟪X (a + 1) - X a, v⟫ := by
    rw [inner_add_right, hlev, real_inner_smul_right, zero_add]
  have hc : det3 (X (i + 1) - X i) (cross (w0 + t • v) (X (a + 1) - X a)) (w0 + t • v) =
      -det3 (X (i + 1) - X i) (cross (X (a + 1) - X a) (w0 + t • v)) (w0 + t • v) := by
    simp only [det3, cross_0, cross_1, cross_2]; ring
  unfold rowT
  rw [hD, hc]
  ring


/-- **LLEV (Carbon A72 Theorem 1.3(c) / A75 Lemma 2.2, the level-extremum arch).**  A strict rim `lab` of `w₀` with
`HiddenInTriangles`, a level rim edge `a → a+1`, all other rim vertices strictly on one side of that level
(`0 < ε ⟪X_j - X_a, w₀⟫`), and interior angles at `X_a`, `X_{a+1}` summing to `< π`
(`det3 E_{a-1} E_{a+1} w₀ < 0`) give `Gen.EdgePlaneAny x`.  No facets, no injectivity of `x`, no genericity. -/
theorem edgePlaneAny_of_level_extremum {k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (w₀ : ℝ³)
    (hR : StrictRimN x w₀ lab) (hH : HiddenInTriangles x w₀ lab) (a : ZMod k)
    (hlev : ⟪x (lab (a + 1)) - x (lab a), w₀⟫ = 0) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hside : ∀ j, j ≠ a → j ≠ a + 1 → 0 < ε * ⟪x (lab j) - x (lab a), w₀⟫)
    (harch : det3 (x (lab a) - x (lab (a - 1))) (x (lab (a + 2)) - x (lab (a + 1))) w₀ < 0) :
    Gen.EdgePlaneAny x := by
  classical
  let X : ZMod k → ℝ³ := fun i => x (lab i)
  have hcyc : ∀ w : ℝ³, StrictRimN x w lab → ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      0 < det3 (X (i + 1) - X i) (X j - X i) w :=
    fun w hw i j h1 h2 => hw (lab j) i (fun h => h1 (hinj h)) (fun h => h2 (hinj h))
  obtain ⟨n1, n2, n3, n4, n5⟩ := zk_ne hk a
  have hlev' : ⟪X (a + 1) - X a, w₀⟫ = 0 := hlev
  have hside' : ∀ j, j ≠ a → j ≠ a + 1 → 0 < ε * ⟪X j - X a, w₀⟫ := hside
  have harch' : det3 (X a - X (a - 1)) (X (a + 1 + 1) - X (a + 1)) w₀ < 0 := by
    have e : a + 2 = a + 1 + 1 := by ring
    rw [e] at harch; exact harch
  have he2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hd0 : X (a + 1) - X a ≠ 0 := by
    intro h0
    have := hcyc w₀ hR a (a + 1 + 1) n2 n4
    rw [h0] at this
    simp [det3] at this
  have hdpos : 0 < ⟪X (a + 1) - X a, X (a + 1) - X a⟫ := real_inner_self_pos.2 hd0
  have hw0pos : 0 < ⟪w₀, w₀⟫ := by
    apply real_inner_self_pos.2
    intro h0
    have := hcyc w₀ hR a (a + 1 + 1) n2 n4
    rw [h0] at this
    simp [det3] at this
  obtain ⟨hAm, hAp⟩ := signsA hk X w₀ a (hcyc w₀ hR)
  have hid := harch_id (X a - X (a - 1)) (X (a + 1) - X a) (X (a + 1 + 1) - X (a + 1)) w₀ hlev'
  have h3 : 0 < ⟪X a - X (a - 1), X (a + 1) - X a⟫ * det3 (X (a + 1 + 1) - X (a + 1)) (X (a + 1) - X a) w₀ -
      ⟪X (a + 1 + 1) - X (a + 1), X (a + 1) - X a⟫ * det3 (X a - X (a - 1)) (X (a + 1) - X a) w₀ := by
    rw [hid]
    have := mul_pos hdpos (neg_pos.2 harch')
    linarith
  obtain ⟨ν, m, hν, hm, c1, c2⟩ := exists_nu_m _ _ _ _ hAm hAp h3
  have hν2 : ν * ν = 1 := by rcases hν with rfl | rfl <;> norm_num
  obtain ⟨U, hU⟩ : ∃ U : ℝ³, U = ν • cross (X (a + 1) - X a) w₀ - m • (X (a + 1) - X a) := ⟨_, rfl⟩
  have hUw : ⟪U, w₀⟫ = 0 := by
    rw [hU, inner_sub_left, real_inner_smul_left, real_inner_smul_left, inner_cross_right, hlev']; ring
  have Uval : ∀ E : ℝ³, ⟪U, E⟫ = ν * det3 E (X (a + 1) - X a) w₀ - m * ⟪X (a + 1) - X a, E⟫ := by
    intro E
    rw [hU, inner_sub_left, real_inner_smul_left, real_inner_smul_left, inner_cross_det]
  have hpos : ∀ i, i ≠ a → 0 < ⟪U, X (i + 1) - X i⟫ := by
    refine mono_pos hk X w₀ U a (hcyc w₀ hR) hUw ?_ ?_ ?_
    · rw [Uval, det3_self]; nlinarith [mul_pos hm hdpos]
    · have hcm := real_inner_comm (X a - X (a - 1)) (X (a + 1) - X a)
      rw [Uval, hcm]; exact c1
    · have hcm := real_inner_comm (X (a + 1 + 1) - X (a + 1)) (X (a + 1) - X a)
      rw [Uval, hcm]; exact c2
  obtain ⟨st, hst⟩ : ∃ st : ℝ, st * ⟪w₀, w₀⟫ = -(ε * m) :=
    ⟨-(ε * m) / ⟪w₀, w₀⟫, div_mul_cancel₀ _ hw0pos.ne'⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ³, v = (-(ε * ν)) • (X (a + 1) - X a) := ⟨_, rfl⟩
  have hc : ⟪X (a + 1) - X a, v⟫ = -(ε * ν) * ⟪X (a + 1) - X a, X (a + 1) - X a⟫ := by
    rw [hv, real_inner_smul_right]
  have hεν : (ε * ν) * (ε * ν) = 1 := by nlinarith
  have hcne : ⟪X (a + 1) - X a, v⟫ ≠ 0 := by
    rw [hc]
    intro h
    have : (ε * ν) * ⟪X (a + 1) - X a, X (a + 1) - X a⟫ = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · rw [h'] at hεν; norm_num at hεν
    · exact hdpos.ne' h'
  have E3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) → j ≠ a → j ≠ a + 1 →
      0 < rowT X w₀ v a i j (ε * ν) st t := by
    refine eventually_all.2 fun i => eventually_all.2 fun j => ev_imp fun hia => ev_imp fun _ =>
      ev_imp fun hja => ev_imp fun hja1 => ?_
    have h0 : 0 < rowT X w₀ v a i j (ε * ν) st 0 := by
      rw [rowT_zero X w₀ v a i j (ε * ν) st hlev']
      have hz := hside' j hja hja1
      have hp := hpos i hia
      rw [Uval] at hp
      have hcomm := real_inner_comm (X (i + 1) - X i) (X (a + 1) - X a)
      rw [hcomm] at hp
      have hp' := mul_pos hz hp
      have e : st * ⟪w₀, w₀⟫ * ⟪X (i + 1) - X i, X (a + 1) - X a⟫ =
          -(ε * m) * ⟪X (i + 1) - X i, X (a + 1) - X a⟫ := by rw [hst]
      rw [e]
      nlinarith [hp']
    exact ((rowT_cont X w₀ v a i j (ε * ν) st).continuousAt.eventually (lt_mem_nhds h0)).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨t, ⟨⟨ht1, ht2⟩, ht3⟩, ht0⟩ :=
    ((((strictRim_ev hR v).and (hidden_ev hH v)).and E3).and self_mem_nhdsWithin).exists
  have htpos : 0 < t := ht0
  have hDne : ⟪X (a + 1) - X a, w₀ + t • v⟫ ≠ 0 := by
    rw [inner_add_right, hlev', real_inner_smul_right, zero_add]
    exact mul_ne_zero htpos.ne' hcne
  refine ⟨k, inferInstance, lab, w₀ + t • v, a, -st * t * ⟪X (a + 1) - X a, v⟫,
    t * (⟪X (a + 1) - X a, X (a + 1) - X a⟫ / 2), ε * ν, hk, hinj, ht1, ht2, hDne, ?_⟩
  intro i j hia hj
  have key : 0 < rowT X w₀ v a i j (ε * ν) st t := by
    by_cases hja : j = a
    · have hi : i = a - 1 := by
        rcases hj with h | h
        · exact absurd (h.symm.trans hja) hia
        · exact eq_sub_of_add_eq (h.symm.trans hja)
      subst hi
      rw [hja, rowT_a]
      have := (signsA hk X (w₀ + t • v) a (hcyc _ ht1)).1
      rw [sub_add_cancel]
      exact mul_pos (mul_pos htpos (by linarith)) this
    · by_cases hja1 : j = a + 1
      · have hi : i = a + 1 := by
          rcases hj with h | h
          · exact h.symm.trans hja1
          · exact absurd (add_right_cancel (h.symm.trans hja1)) hia
        subst hi
        rw [hja1, rowT_a1 X w₀ v a (a + 1) _ _ t hlev']
        have := (signsA hk X (w₀ + t • v) a (hcyc _ ht1)).2
        rw [hc]
        have e : t * (⟪X (a + 1) - X a, X (a + 1) - X a⟫ / 2) +
            ε * ν * (t * (-(ε * ν) * ⟪X (a + 1) - X a, X (a + 1) - X a⟫)) =
            -(t * (⟪X (a + 1) - X a, X (a + 1) - X a⟫ / 2)) := by
          have : ε * ν * (t * (-(ε * ν) * ⟪X (a + 1) - X a, X (a + 1) - X a⟫)) =
              -((ε * ν) * (ε * ν)) * (t * ⟪X (a + 1) - X a, X (a + 1) - X a⟫) := by ring
          rw [this, hεν]; ring
        rw [e]
        have hp : 0 < t * (⟪X (a + 1) - X a, X (a + 1) - X a⟫ / 2) := mul_pos htpos (by linarith)
        nlinarith
      · exact ht3 i j hia hj hja hja1
  have := rowT_eq X w₀ v a i j (ε * ν) st t hlev' hcne htpos.ne'
  exact lt_of_lt_of_eq key this.symm

end Minimality.Split.Level
