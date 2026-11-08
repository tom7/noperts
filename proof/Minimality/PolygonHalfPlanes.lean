module

public import Minimality.SecondOrder
public import Minimality.CycSeq

@[expose] public section

/-!
# Half-plane form of a strictly convex polygon (plan specpos A3a)

`halfPlanes_of_ccwPolygon`: a strictly convex counterclockwise polygon `c : ZMod k → ℝ²` is the intersection of
its edge half-planes (outward normals `-rot90 (c (i+1) - c i)`): the open intersection lies in the convex hull,
and the hull lies in the closed intersection.  Supplies `hpoly`/`hS` of the second-order theorems from a rim.
Proof: a fan from `c 0` (the sign change is found by `Nat.find`), and convexity of half-spaces.
-/

namespace Minimality
open scoped RealInnerProductSpace

lemma poly_inner (e y p : ℝ²) :
    ⟪-rot90 e, y⟫ - ⟪-rot90 e, p⟫ = -cross2 e (y - p) := by
  simp [rot90, cross2, PiLp.inner_apply, Fin.sum_univ_two]
  ring

lemma poly_natCast_ne {k : ℕ} (n : ℕ) (h0 : 0 < n) (hk : n < k) : (n : ZMod k) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.le_of_dvd h0 h) (by omega)

lemma poly_fan (a b q y : ℝ²) (hD : 0 < cross2 (b - a) (q - a))
    (h1 : 0 ≤ cross2 (b - a) (y - a)) (h2 : cross2 (q - a) (y - a) ≤ 0)
    (h3 : 0 < cross2 (q - b) (y - b)) : y ∈ convexHull ℝ {a, b, q} := by
  have hDne : cross2 (b - a) (q - a) ≠ 0 := hD.ne'
  obtain ⟨t, htD⟩ : ∃ t, t * cross2 (b - a) (q - a) = cross2 (b - a) (y - a) :=
    ⟨_, div_mul_cancel₀ _ hDne⟩
  obtain ⟨s, hsD⟩ : ∃ s, s * cross2 (b - a) (q - a) = -cross2 (q - a) (y - a) :=
    ⟨_, div_mul_cancel₀ _ hDne⟩
  have ht0 : 0 ≤ t := by
    by_contra h; push Not at h; nlinarith [mul_neg_of_neg_of_pos h hD]
  have hs0 : 0 ≤ s := by
    by_contra h; push Not at h; nlinarith [mul_neg_of_neg_of_pos h hD]
  have hst : s + t ≤ 1 := by
    by_contra h; push Not at h
    have h4 : cross2 (b - a) (q - a) < (s + t) * cross2 (b - a) (q - a) := by nlinarith
    simp only [cross2, PiLp.sub_apply] at h3 h4 htD hsD
    nlinarith
  have hy_eq : y = (1 - s - t) • a + s • b + t • q := by
    ext j
    fin_cases j
    · simp only [Fin.zero_eta, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      apply mul_left_cancel₀ hDne
      simp only [cross2, PiLp.sub_apply] at htD hsD ⊢
      linear_combination (-(b 0 - a 0)) * hsD + (-(q 0 - a 0)) * htD
    · simp only [Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      apply mul_left_cancel₀ hDne
      simp only [cross2, PiLp.sub_apply] at htD hsD ⊢
      linear_combination (-(b 1 - a 1)) * hsD + (-(q 1 - a 1)) * htD
  rw [hy_eq]
  have hconv := convex_convexHull ℝ ({a, b, q} : Set ℝ²)
  have hm : ∀ z ∈ ({a, b, q} : Set ℝ²), z ∈ convexHull ℝ ({a, b, q} : Set ℝ²) :=
    fun z hz => subset_convexHull ℝ _ hz
  have := hconv.sum_mem (t := Finset.univ) (w := ![1 - s - t, s, t]) (z := ![a, b, q])
    (by intro j _; fin_cases j <;> simp <;> linarith)
    (by simp [Fin.sum_univ_three]; ring)
    (by intro j _; fin_cases j <;> simp <;> apply hm <;> simp)
  simpa [Fin.sum_univ_three, add_assoc] using this

theorem halfPlanes_of_ccwPolygon {k : ℕ} [NeZero k] (c : ZMod k → ℝ²) (hk : 3 ≤ k)
    (hccw : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < cross2 (c (i + 1) - c i) (c j - c i)) :
    {y : ℝ² | ∀ i, ⟪-rot90 (c (i + 1) - c i), y⟫ < ⟪-rot90 (c (i + 1) - c i), c i⟫} ⊆
        convexHull ℝ (Set.range c) ∧
      ∀ y ∈ convexHull ℝ (Set.range c), ∀ i,
        ⟪-rot90 (c (i + 1) - c i), y⟫ ≤ ⟪-rot90 (c (i + 1) - c i), c i⟫ := by
  constructor
  · intro y hy
    have hy' : ∀ i, 0 < cross2 (c (i + 1) - c i) (y - c i) := by
      intro i; have := hy i; have := poly_inner (c (i + 1) - c i) y (c i); linarith
    set g : ℕ → ℝ² := fun n => c (n : ZMod k) with hg
    have gsucc : ∀ n : ℕ, g (n + 1) = c ((n : ZMod k) + 1) := by intro n; simp [hg]
    set f : ℕ → ℝ := fun n => cross2 (g n - g 0) (y - g 0) with hf
    have hk1 : ((k - 1 : ℕ) : ZMod k) + 1 = 0 := by
      have : k - 1 + 1 = k := by omega
      rw [← Nat.cast_succ, Nat.succ_eq_add_one, this]; simp
    have hf1 : 0 < f 1 := by
      have := hy' 0
      simp only [hf, hg]; simpa using this
    have hfk : f (k - 1) < 0 := by
      have := hy' ((k - 1 : ℕ) : ZMod k)
      rw [hk1] at this
      simp only [hf, hg, Nat.cast_zero]
      simp only [cross2, PiLp.sub_apply] at this ⊢
      nlinarith
    have hex : ∃ n, 1 ≤ n ∧ f n ≤ 0 := ⟨k - 1, by omega, hfk.le⟩
    classical
    obtain ⟨m, hm⟩ : ∃ m, m = Nat.find hex := ⟨_, rfl⟩
    have hmspec : 1 ≤ m ∧ f m ≤ 0 := by rw [hm]; exact Nat.find_spec hex
    have hmle : m ≤ k - 1 := by rw [hm]; exact Nat.find_min' hex ⟨by omega, hfk.le⟩
    have hm2 : 2 ≤ m := by
      by_contra hlt
      have : m = 1 := by have := hmspec.1; omega
      rw [this] at hmspec; linarith [hmspec.2]
    have hfi : 0 < f (m - 1) := by
      by_contra hneg
      push Not at hneg
      exact Nat.find_min hex (m := m - 1) (by omega) ⟨by omega, hneg⟩
    obtain ⟨i, hi⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
    have him : i = m - 1 := by omega
    rw [← him] at hfi
    have hfi1 : f (i + 1) ≤ 0 := by rw [← hi]; exact hmspec.2
    have hne0 : (i : ZMod k) ≠ 0 := poly_natCast_ne i (by omega) (by omega)
    have hne1 : ((i + 1 : ℕ) : ZMod k) ≠ 0 := poly_natCast_ne (i + 1) (by omega) (by omega)
    have hD : 0 < cross2 (g i - g 0) (g (i + 1) - g 0) := by
      have := hccw (i : ZMod k) 0 hne0.symm (by
        intro h; apply hne1; push_cast; exact h.symm)
      rw [← gsucc] at this
      simp only [cross2, hg, PiLp.sub_apply] at this ⊢
      simp only [Nat.cast_zero] at this ⊢
      nlinarith
    have hai := hy' (i : ZMod k)
    rw [← gsucc] at hai
    have hai' : 0 < cross2 (g (i + 1) - g i) (y - g i) := hai
    have := poly_fan (g 0) (g i) (g (i + 1)) y hD hfi.le hfi1 hai'
    refine convexHull_mono ?_ this
    intro z hz
    rcases hz with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · intro y hy i
    have hconv : Convex ℝ {z : ℝ² | ⟪-rot90 (c (i + 1) - c i), z⟫ ≤ ⟪-rot90 (c (i + 1) - c i), c i⟫} :=
      convex_halfSpace_le (by
        constructor <;> intros <;> simp [inner_add_right, inner_smul_right]) _
    have hsub : Set.range c ⊆ {z : ℝ² | ⟪-rot90 (c (i + 1) - c i), z⟫ ≤ ⟪-rot90 (c (i + 1) - c i), c i⟫} := by
      rintro _ ⟨j, rfl⟩
      rw [Set.mem_setOf_eq]
      by_cases h1 : j = i
      · rw [h1]
      by_cases h2 : j = i + 1
      · have := poly_inner (c (i + 1) - c i) (c j) (c i)
        rw [h2] at this ⊢
        have h3 : cross2 (c (i + 1) - c i) (c (i + 1) - c i) = 0 := by simp [cross2]; ring
        rw [h3] at this; linarith
      · have := poly_inner (c (i + 1) - c i) (c j) (c i)
        have := hccw i j h1 h2
        linarith
    exact (convexHull_min hsub hconv) hy
end Minimality
