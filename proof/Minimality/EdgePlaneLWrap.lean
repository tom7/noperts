module

public import Minimality.EdgePlaneLevel

/-!
# L-Wrap: Edge-Plane at the adjacent edge `a + 1`, zero tilt

Job LWRAP (Carbon A78 Theorem 2.1, `edgePlaneAny_of_lwrap_adj_twoRed`).  A strict rim with `HiddenInTriangles`, a
level edge `a → a+1` that is the strict shallowest (`ε = 1`) or deepest (`ε = -1`) pair, and an `L-Wrap`
(`det3 E_{a-1} E_{a+1} w₀ > 0`, the level edge itself is blocked) in which the edges `i ∉ {a-1, a, a+1}` all have
`B_i = det3 E_i E_{a+1} w₀ < 0`: the Edge-Plane rows at the ADJACENT edge `a+1` and the view `w₀` itself (no tilt)
reduce to one 1D slope inequality (H3).

Notation.  `Z_j = ⟪X_j - X_{a+1}, w₀⟫`, `B_i = det3 E_i E_{a+1} w₀`, `Y_{i,j} = -edgePlaneSpin X w₀ (a+1) i j / B_i`
(`lwY`), `α₀ = max 0 (max (σ Y_{a,a}) (σ Y_{a-1,a}))`.  The row `(α + μ Z_j) B_i + σ S_{i,j}` equals
`(α + μ Z_j - σ Y_{i,j}) B_i`.  Rows `(a, a+1), (a,a), (a-1,a)` have `Z = 0` and `B > 0`; row `(a-1,a-1)` has `B > 0`;
all others have `B < 0` and `ε Z_j > 0`.  The parameters are Carbon's: `s = σ`, `μ = ε (m_lo + m_hi)/2`,
`α = α₀ + ((m_hi - m_lo)/4) z_min`, with `m_lo` the left side of (H3), `m_hi` any number below all right sides
(and above `m_lo`), `z_min > 0` below all `ε Z_j`, `j ∉ {a, a+1}`.

The hypotheses `ε = ±1`, `σ = ±1` are not needed (any real `ε`, `σ`: only `ε Z_j > 0` and the scale of H3 matter).
All of Carbon's claims hold in these conventions; the only change is notational (`a + 2` is written `a + 1 + 1`).
-/

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.Split.LWrap

/-- The scaled height `Y_{i,j}^{(b)} = -S_{i,j}^{(b)} / B_i^{(b)}` of A78 Section 0. -/
noncomputable def lwY {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (b i j : ZMod k) : ℝ :=
  -edgePlaneSpin X w b i j / det3 (X (i + 1) - X i) (X (b + 1) - X b) w

/-- A finite family has a common lower bound strictly above any lower bound that is strict on each member. -/
theorem exists_lower {ι : Type*} [Fintype ι] (P : ι → Prop) (f : ι → ℝ) (c : ℝ)
    (h : ∀ p, P p → c < f p) : ∃ m, c < m ∧ ∀ p, P p → m ≤ f p := by
  classical
  by_cases hne : ∃ p, P p
  · obtain ⟨p0, hp0, hmin⟩ := Finset.exists_min_image (Finset.univ.filter P) f
      (by obtain ⟨p, hp⟩ := hne; exact ⟨p, by simpa using hp⟩)
    exact ⟨f p0, h p0 (by simpa using hp0), fun p hp => hmin p (by simpa using hp)⟩
  · exact ⟨c + 1, by linarith, fun p hp => absurd ⟨p, hp⟩ hne⟩

theorem three_ne {k : ℕ} [NeZero k] (hk : 4 ≤ k) : (3 : ZMod k) ≠ 0 := by
  intro h
  have h1 : ((3 : ℕ) : ZMod k) = 0 := by simpa using h
  have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 3 k).1 h1)
  omega

/-- **LWRAP (Carbon A78 Theorem 2.1, two Red edges).** -/
theorem edgePlaneAny_of_lwrap_adj_twoRed {n k : ℕ} [NeZero k] (hk : 4 ≤ k) (x : Fin n → ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (w₀ : ℝ³)
    (hrim : StrictRimN x w₀ lab) (hhid : HiddenInTriangles x w₀ lab) (a : ZMod k)
    (ε : ℝ)
    (H1a : ⟪x (lab (a + 1)) - x (lab a), w₀⟫ = 0)
    (H1b : ∀ j, j ≠ a → j ≠ a + 1 → 0 < ε * ⟪x (lab j) - x (lab (a + 1)), w₀⟫)
    (H2a : 0 < det3 (x (lab a) - x (lab (a - 1))) (x (lab (a + 1 + 1)) - x (lab (a + 1))) w₀)
    (H2b : ∀ i, i ≠ a - 1 → i ≠ a → i ≠ a + 1 →
      det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1 + 1)) - x (lab (a + 1))) w₀ < 0)
    (σ : ℝ)
    (H3 : ∀ i j : ZMod k, i ≠ a - 1 → i ≠ a → i ≠ a + 1 → (j = i ∨ j = i + 1) →
      (σ * lwY (fun i => x (lab i)) w₀ (a + 1) (a - 1) (a - 1) -
          max 0 (max (σ * lwY (fun i => x (lab i)) w₀ (a + 1) a a)
            (σ * lwY (fun i => x (lab i)) w₀ (a + 1) (a - 1) a))) /
        (ε * ⟪x (lab (a - 1)) - x (lab (a + 1)), w₀⟫) <
      (σ * lwY (fun i => x (lab i)) w₀ (a + 1) i j -
          max 0 (max (σ * lwY (fun i => x (lab i)) w₀ (a + 1) a a)
            (σ * lwY (fun i => x (lab i)) w₀ (a + 1) (a - 1) a))) /
        (ε * ⟪x (lab j) - x (lab (a + 1)), w₀⟫)) :
    Gen.EdgePlaneAny x := by
  classical
  let X : ZMod k → ℝ³ := fun i => x (lab i)
  have hk3 : 3 ≤ k := by omega
  have hcyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < det3 (X (i + 1) - X i) (X j - X i) w₀ :=
    fun i j h1 h2 => hrim (lab j) i (fun h => h1 (hinj h)) (fun h => h2 (hinj h))
  obtain ⟨n1, n2, n3, n4, n5⟩ := Level.zk_ne hk3 a
  have n6 : a + 1 + 1 ≠ a - 1 := by
    intro h
    apply three_ne hk
    have e : (3 : ZMod k) = (a + 1 + 1) - (a - 1) := by ring
    rw [e, h, sub_self]
  have n7 : a - 1 ≠ a := n3
  have H1a' : ⟪X (a + 1) - X a, w₀⟫ = 0 := H1a
  have H1b' : ∀ j, j ≠ a → j ≠ a + 1 → 0 < ε * ⟪X j - X (a + 1), w₀⟫ := H1b
  have hD : ⟪X (a + 1 + 1) - X (a + 1), w₀⟫ ≠ 0 := by
    have := H1b' (a + 1 + 1) n2 n4
    intro h; rw [h, mul_zero] at this; exact lt_irrefl _ this
  have hZa : ⟪X a - X (a + 1), w₀⟫ = 0 := by
    have e : X a - X (a + 1) = -(X (a + 1) - X a) := by abel
    rw [e, inner_neg_left, H1a', neg_zero]
  have hBa : 0 < det3 (X (a + 1) - X a) (X (a + 1 + 1) - X (a + 1)) w₀ := by
    have h := (Level.signsA hk3 X w₀ a hcyc).2
    have e : det3 (X (a + 1) - X a) (X (a + 1 + 1) - X (a + 1)) w₀ =
        -det3 (X (a + 1 + 1) - X (a + 1)) (X (a + 1) - X a) w₀ := by
      simp only [det3, PiLp.sub_apply]; ring
    linarith
  have hBa1 : 0 < det3 (X (a - 1 + 1) - X (a - 1)) (X (a + 1 + 1) - X (a + 1)) w₀ := by
    rw [sub_add_cancel]; exact H2a
  have H2b' : ∀ i, i ≠ a - 1 → i ≠ a → i ≠ a + 1 →
      det3 (X (i + 1) - X i) (X (a + 1 + 1) - X (a + 1)) w₀ < 0 := H2b
  have key : ∀ (α μ : ℝ) (i j : ZMod k),
      det3 (X (i + 1) - X i) (X (a + 1 + 1) - X (a + 1)) w₀ ≠ 0 →
      (α + μ * ⟪X j - X (a + 1), w₀⟫) * det3 (X (i + 1) - X i) (X (a + 1 + 1) - X (a + 1)) w₀ +
          σ * edgePlaneSpin X w₀ (a + 1) i j =
        (α + μ * ⟪X j - X (a + 1), w₀⟫ - σ * lwY X w₀ (a + 1) i j) *
          det3 (X (i + 1) - X i) (X (a + 1 + 1) - X (a + 1)) w₀ := by
    intro α μ i j hB
    have h : lwY X w₀ (a + 1) i j * det3 (X (i + 1) - X i) (X (a + 1 + 1) - X (a + 1)) w₀ =
        -edgePlaneSpin X w₀ (a + 1) i j := by
      unfold lwY; exact div_mul_cancel₀ _ hB
    linear_combination σ * h
  obtain ⟨α0, hα0⟩ : ∃ α0 : ℝ, α0 = max 0 (max (σ * lwY X w₀ (a + 1) a a)
      (σ * lwY X w₀ (a + 1) (a - 1) a)) := ⟨_, rfl⟩
  have hα0a : 0 ≤ α0 := by rw [hα0]; exact le_max_left _ _
  have hα0b : σ * lwY X w₀ (a + 1) a a ≤ α0 := by
    rw [hα0]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hα0c : σ * lwY X w₀ (a + 1) (a - 1) a ≤ α0 := by
    rw [hα0]; exact (le_max_right _ _).trans (le_max_right _ _)
  have H3' : ∀ i j : ZMod k, i ≠ a - 1 → i ≠ a → i ≠ a + 1 → (j = i ∨ j = i + 1) →
      (σ * lwY X w₀ (a + 1) (a - 1) (a - 1) - α0) / (ε * ⟪X (a - 1) - X (a + 1), w₀⟫) <
      (σ * lwY X w₀ (a + 1) i j - α0) / (ε * ⟪X j - X (a + 1), w₀⟫) := by
    rw [hα0]; exact H3
  have ht1 : 0 < ε * ⟪X (a - 1) - X (a + 1), w₀⟫ := H1b' (a - 1) n7 n5
  set m_lo : ℝ := (σ * lwY X w₀ (a + 1) (a - 1) (a - 1) - α0) / (ε * ⟪X (a - 1) - X (a + 1), w₀⟫)
    with hmlo
  have hmlo' : m_lo * (ε * ⟪X (a - 1) - X (a + 1), w₀⟫) =
      σ * lwY X w₀ (a + 1) (a - 1) (a - 1) - α0 := div_mul_cancel₀ _ ht1.ne'
  obtain ⟨m_hi, hlohi, hmhi⟩ := exists_lower (ι := ZMod k × ZMod k)
    (fun p => p.1 ≠ a - 1 ∧ p.1 ≠ a ∧ p.1 ≠ a + 1 ∧ (p.2 = p.1 ∨ p.2 = p.1 + 1))
    (fun p => (σ * lwY X w₀ (a + 1) p.1 p.2 - α0) / (ε * ⟪X p.2 - X (a + 1), w₀⟫)) m_lo
    (fun p hp => H3' p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2)
  obtain ⟨zmin, hzmin0, hzmin⟩ := exists_lower (ι := ZMod k)
    (fun j => j ≠ a ∧ j ≠ a + 1) (fun j => ε * ⟪X j - X (a + 1), w₀⟫) 0
    (fun j hj => H1b' j hj.1 hj.2)
  have hδ : 0 < (m_hi - m_lo) / 4 := by linarith
  have hdz : 0 < (m_hi - m_lo) / 4 * zmin := mul_pos hδ hzmin0
  have hαgt : α0 < α0 + (m_hi - m_lo) / 4 * zmin := by linarith
  have hαpos : 0 < α0 + (m_hi - m_lo) / 4 * zmin := by linarith
  have rows : ∀ i j : ZMod k, i ≠ a + 1 → (j = i ∨ j = i + 1) →
      0 < ((α0 + (m_hi - m_lo) / 4 * zmin) + (ε * ((m_lo + m_hi) / 2)) * ⟪X j - X (a + 1), w₀⟫) *
          det3 (X (i + 1) - X i) (X (a + 1 + 1) - X (a + 1)) w₀ +
        σ * edgePlaneSpin X w₀ (a + 1) i j := by
    intro i j hia hj
    by_cases hi1 : i = a - 1
    · subst hi1
      have hBne := hBa1.ne'
      rw [key _ _ _ _ hBne]
      refine mul_pos ?_ hBa1
      rcases hj with hj | hj
      · subst hj
        have e : (ε * ((m_lo + m_hi) / 2)) * ⟪X (a - 1) - X (a + 1), w₀⟫ =
            (m_lo + m_hi) / 2 * (ε * ⟪X (a - 1) - X (a + 1), w₀⟫) := by ring
        rw [e]
        nlinarith [mul_pos hδ ht1]
      · rw [sub_add_cancel] at hj
        rw [hj]
        have : (ε * ((m_lo + m_hi) / 2)) * ⟪X a - X (a + 1), w₀⟫ = 0 := by rw [hZa]; ring
        rw [this]
        nlinarith
    by_cases hi2 : i = a
    · rw [hi2] at hj ⊢
      rcases hj with hj | hj
      · rw [hj]
        rw [key _ _ _ _ hBa.ne']
        refine mul_pos ?_ hBa
        have : (ε * ((m_lo + m_hi) / 2)) * ⟪X a - X (a + 1), w₀⟫ = 0 := by rw [hZa]; ring
        rw [this]
        nlinarith
      · rw [hj]
        have hS : edgePlaneSpin X w₀ (a + 1) a (a + 1) = 0 := by
          unfold edgePlaneSpin
          simp [det3, cross_0, cross_1, cross_2]
        rw [hS]
        simp only [sub_self, inner_zero_left, mul_zero, add_zero]
        exact mul_pos hαpos hBa
    · have hB := H2b' i hi1 hi2 hia
      rw [key _ _ _ _ hB.ne]
      have hja : j ≠ a ∧ j ≠ a + 1 := by
        rcases hj with hj | hj
        · subst hj; exact ⟨hi2, hia⟩
        · subst hj
          exact ⟨fun h => hi1 (eq_sub_of_add_eq h), fun h => hi2 (add_right_cancel h)⟩
      have ht := H1b' j hja.1 hja.2
      have hq := hmhi (i, j) ⟨hi1, hi2, hia, hj⟩
      have hq' : m_hi * (ε * ⟪X j - X (a + 1), w₀⟫) ≤ σ * lwY X w₀ (a + 1) i j - α0 :=
        (le_div_iff₀ ht).1 hq
      have hz := hzmin j hja
      have e : (ε * ((m_lo + m_hi) / 2)) * ⟪X j - X (a + 1), w₀⟫ =
          (m_lo + m_hi) / 2 * (ε * ⟪X j - X (a + 1), w₀⟫) := by ring
      refine mul_pos_of_neg_of_neg ?_ hB
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left hz hδ.le]
  refine ⟨k, inferInstance, lab, w₀, a + 1, σ, α0 + (m_hi - m_lo) / 4 * zmin,
    ε * ((m_lo + m_hi) / 2), hk3, hinj, hrim, hhid, hD, ?_⟩
  intro i j hia hj
  exact rows i j hia hj

end Minimality.Split.LWrap
