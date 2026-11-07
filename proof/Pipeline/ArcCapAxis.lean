module

public import Pipeline.ArcCapClaim

@[expose] public section

/-!
# The U cap on the full square: the axis cap

The U cap of `Pipeline.ArcCap` on all four sides of the square |a|, |b| ≤ μ₀ (sides 0..3, see
`ChartId.u`), for a frame E₁, E₂, X that is orthogonal but not of equal lengths, with the Cayley
weights `k₁ n₁ = k₂ n₂ = k₃ n₃ = 1` (`FrameOkG`, n_i the squared lengths): then the apex
coordinates of a rotation are just w·E₁, w·E₂, w·X.

* `square_good`: from a checked certificate on `axisCharts` (no wedge), every pose with view
  X − a E₁ − b E₂, |a|, |b| ≤ μ₀, and apex coordinates |x|, |y| ≤ μ₀, |z| ≤ S μ₀², is good.
* `square_not_rupert`: the same for views and rotations given by dot products.
-/

namespace Noperts.Pipeline

namespace ArcCap

open Noperts.Pipeline.KCap
open Noperts.Pipeline.KCap.PVec

theorem exists_tau {m b : ℝ} (hm : 0 ≤ m) (hb : |b| ≤ m) : ∃ τ : ℝ, |τ| ≤ 1 ∧ b = m * τ := by
  rcases hm.lt_or_eq with hpos | hz
  · refine ⟨b / m, ?_, by field_simp⟩
    rw [abs_div, abs_of_pos hpos, div_le_one hpos]; exact hb
  · subst hz
    have : b = 0 := by simpa using hb
    exact ⟨0, by norm_num, by simp [this]⟩

section real

variable {K : Type} [ExactScalarOps K] [ExactScalarVal K]
variable {V : Array (KCap.KVec K)} {fr : Frame K}

/-- **The square**: with a checked certificate on the four sides, every pose of the square and the
weighted box is good. -/
theorem square_good {pr : Params} {c : Cert} (hp : pr.Ok) (hc : certCheckOn axisCharts V fr pr c = true)
    (hRc : 0 < (pr.Rc : ℝ)) (hSc : 0 < (pr.Sc : ℝ)) (hwd : pr.wedge = false) (hR : 2 ≤ (pr.R : ℝ))
    (hS : 0 < (pr.S : ℝ)) {a b x y z : ℝ} (ha : |a| ≤ pr.mu0) (hb : |b| ≤ pr.mu0) (hx : |x| ≤ pr.mu0)
    (hy : |y| ≤ pr.mu0) (hz : |z| ≤ pr.S * (pr.mu0 : ℝ) ^ 2) : Good V fr a b x y z := by
  have hm0 : 0 ≤ max |a| |b| := le_max_of_le_left (abs_nonneg _)
  have hR0q : (0 : ℚ) < pr.R := by exact_mod_cast (by linarith : (0 : ℝ) < pr.R)
  have hSq : (0 : ℚ) < pr.S := by exact_mod_cast hS
  have hmu : (0 : ℝ) ≤ pr.mu0 := le_trans (abs_nonneg _) ha
  have cube : ∀ side : ℕ, side < 4 → ∀ k ∈ uKinds, ∀ y, KPoly.InBox (rootBox pr (.u side k)) y →
      PointGood V fr pr (.u side k) y := by
    intro side hs
    refine cert_goodU hp hc hRc hSc (fun h => absurd h (by simp [hwd])) side ?_
    intro k hk
    exact mem_uCharts (by simp [axisCharts]; omega) hk
  obtain ⟨μ, e, s, h0, h1, he0, he1, hme, hs, hcase⟩ :=
    Cap.weighted_cube ![1, 1, 2] (by intro i; fin_cases i <;> simp) ![(pr.R : ℝ), pr.R, pr.S]
      (by intro i; fin_cases i <;> simp [hR0q, hSq]) pr.mu0 (max |a| |b|) hm0 (max_le ha hb)
      ![2 * y, -2 * x, z]
      (by
        intro i
        fin_cases i
        · simp only [Fin.zero_eta, Matrix.cons_val_zero, pow_one, abs_mul, abs_two]
          nlinarith
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, pow_one, abs_mul, abs_neg, abs_two]
          nlinarith
        · simp only [Fin.reduceFinMk, Matrix.cons_val]; exact hz)
  have s0 := hs 0; have s1 := hs 1; have s2 := hs 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, pow_one] at s0 s1 s2
  have hr : ∀ i : Fin 3, |s i| ≤ rng pr i := by
    intro i
    fin_cases i
    · simpa [rng] using s0.2
    · simpa [rng] using s1.2
    · simpa [rng] using s2.2
  have hf : e = 1 ∨ ∃ k : Fin 3, |s k| = rng pr k := by
    rcases hcase with h | ⟨k, hk⟩
    · exact Or.inl h
    · right
      refine ⟨k, ?_⟩
      fin_cases k
      · simpa [rng] using hk
      · simpa [rng] using hk
      · simpa [rng] using hk
  have ex : -1 / 2 * (μ * s 1) = x := by have := s1.1; linarith
  have ey : 1 / 2 * (μ * s 0) = y := by have := s0.1; linarith
  have ez : μ * μ * s 2 = z := by have := s2.1; rw [this]; ring
  have G : ∀ side : ℕ, side < 4 → ∀ τ : ℝ, |τ| ≤ 1 → GoodU V fr side μ τ e (s 0) (s 1) (s 2) := fun side hside τ hτ =>
    goodU_of_cube V fr pr side (cube side hside) h0 h1 hτ he0 he1 hr hf
  rw [← ex, ← ey, ← ez]
  rcases le_total |b| |a| with hba | hab
  · -- m = |a|
    have hm : μ * e = |a| := by rw [← hme]; exact max_eq_left hba
    obtain ⟨τ, hτ, hbτ⟩ := exists_tau (abs_nonneg a) hba
    rcases le_total 0 a with ha0 | ha0
    · have hm' : μ * e = a := by rw [hm, abs_of_nonneg ha0]
      have hG := G 0 (by norm_num) τ hτ
      simp only [GoodU, if_true] at hG
      rw [hm'] at hG
      rw [abs_of_nonneg ha0] at hbτ
      rw [hbτ]; simpa using hG
    · have hm' : μ * e = -a := by rw [hm, abs_of_nonpos ha0]
      have hG := G 1 (by norm_num) τ hτ
      simp only [GoodU, one_ne_zero, if_false, if_true] at hG
      rw [hm'] at hG
      rw [abs_of_nonpos ha0] at hbτ
      rw [hbτ]; simpa using hG
  · have hm : μ * e = |b| := by rw [← hme]; exact max_eq_right hab
    obtain ⟨τ, hτ, haτ⟩ := exists_tau (abs_nonneg b) hab
    rcases le_total 0 b with hb0 | hb0
    · have hm' : μ * e = b := by rw [hm, abs_of_nonneg hb0]
      have hG := G 2 (by norm_num) τ hτ
      simp only [GoodU] at hG
      rw [hm'] at hG
      rw [abs_of_nonneg hb0] at haτ
      rw [haτ]; simpa using hG
    · have hm' : μ * e = -b := by rw [hm, abs_of_nonpos hb0]
      have hG := G 3 (by norm_num) τ hτ
      simp only [GoodU] at hG
      rw [hm'] at hG
      rw [abs_of_nonpos hb0] at haτ
      rw [haτ]; simpa using hG

/-- A frame E₁, E₂, X orthogonal, of squared lengths n₁, n₂, n₃, with the Cayley weights
k_i = 1 / n_i. -/
structure FrameOkG (fr : Frame K) (n1 n2 nx : ℝ) : Prop where
  h12 : rdot (kval fr.E1) (kval fr.E2) = 0
  h1x : rdot (kval fr.E1) (kval fr.X) = 0
  h2x : rdot (kval fr.E2) (kval fr.X) = 0
  e1 : rdot (kval fr.E1) (kval fr.E1) = n1
  e2 : rdot (kval fr.E2) (kval fr.E2) = n2
  ex : rdot (kval fr.X) (kval fr.X) = nx
  p1 : 0 < n1
  p2 : 0 < n2
  px : 0 < nx
  k1 : (fr.k1 : ℝ) * n1 = 1
  k2 : (fr.k2 : ℝ) * n2 = 1
  k3 : (fr.k3 : ℝ) * nx = 1

/-- The views of the square |a|, |b| ≤ μ₀ of the frame: v ∝ X − a E₁ − b E₂. -/
def InSquare (fr : Frame K) (n1 n2 nx m : ℝ) (v : Fin 3 → ℝ) : Prop :=
  0 < rdot v (kval fr.X) ∧ |rdot v (kval fr.E1)| * nx ≤ m * n1 * rdot v (kval fr.X) ∧
    |rdot v (kval fr.E2)| * nx ≤ m * n2 * rdot v (kval fr.X)

theorem rdot_sq_le' (a b : Fin 3 → ℝ) : rdot a b ^ 2 ≤ rdot a a * rdot b b := rdot_sq_le a b

/-- **The axis cap**: no pose with view in the square and a rotation of Cayley norm at most r is
Rupert, whatever the offset, if n₁ r², n₂ r² ≤ μ₀² and n₃ r² ≤ (S μ₀²)². -/
theorem square_not_rupert {pr : Params} {c : Cert} {n1 n2 nx r : ℝ} (hp : pr.Ok)
    (hc : certCheckOn axisCharts V fr pr c = true) (hRc : 0 < (pr.Rc : ℝ)) (hSc : 0 < (pr.Sc : ℝ))
    (hwd : pr.wedge = false) (hR : 2 ≤ (pr.R : ℝ)) (hS : 0 < (pr.S : ℝ)) (hf : FrameOkG fr n1 n2 nx)
    (hr1 : n1 * r ^ 2 ≤ (pr.mu0 : ℝ) ^ 2) (hr2 : n2 * r ^ 2 ≤ (pr.mu0 : ℝ) ^ 2)
    (hr3 : nx * r ^ 2 ≤ ((pr.S : ℝ) * (pr.mu0 : ℝ) ^ 2) ^ 2)
    (p : MatrixPose) (hv : InSquare fr n1 n2 nx pr.mu0 p.view) (w : Fin 3 → ℝ)
    (hR' : p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2)) (hw : rdot w w ≤ r ^ 2) :
    ¬ RupertPose p (hull V) := by
  have n1ne : n1 ≠ 0 := hf.p1.ne'
  have n2ne : n2 ≠ 0 := hf.p2.ne'
  have nxne : nx ≠ 0 := hf.px.ne'
  have dec : ∀ v : Fin 3 → ℝ, v = (rdot v (kval fr.E1) / n1) • kval fr.E1 + (rdot v (kval fr.E2) / n2) • kval fr.E2 +
      (rdot v (kval fr.X) / nx) • kval fr.X := by
    intro v
    have := decomp3 _ _ _ v hf.h12 hf.h1x hf.h2x (by rw [hf.e1]; exact n1ne) (by rw [hf.e2]; exact n2ne)
      (by rw [hf.ex]; exact nxne)
    rwa [hf.e1, hf.e2, hf.ex] at this
  obtain ⟨hx0, h1, h2⟩ := hv
  set e1 := rdot p.view (kval fr.E1) with he1
  set e2 := rdot p.view (kval fr.E2) with he2
  set xx := rdot p.view (kval fr.X) with hxx
  have hmu : (0 : ℝ) ≤ pr.mu0 := by
    by_contra hneg
    push_neg at hneg
    have h3 : 0 ≤ (pr.mu0 : ℝ) * (n1 * xx) := by
      rw [← mul_assoc]; exact le_trans (mul_nonneg (abs_nonneg _) hf.px.le) h1
    exact absurd h3 (not_le.mpr (mul_neg_of_neg_of_pos hneg (mul_pos hf.p1 hx0)))
  have rb : ∀ (e : Fin 3 → ℝ) (n : ℝ), 0 < n → rdot e e = n → n * r ^ 2 ≤ ((pr.mu0 : ℝ)) ^ 2 →
      |rdot w e| ≤ pr.mu0 := by
    intro e n hn0 he hn
    have h := rdot_sq_le w e
    rw [he] at h
    apply abs_le_of_sq_le_sq _ hmu
    have : rdot w w * n ≤ r ^ 2 * n := mul_le_mul_of_nonneg_right hw hn0.le
    nlinarith
  have rbz : |rdot w (kval fr.X)| ≤ pr.S * (pr.mu0 : ℝ) ^ 2 := by
    have h := rdot_sq_le w (kval fr.X)
    rw [hf.ex] at h
    apply abs_le_of_sq_le_sq _ (by positivity)
    have : rdot w w * nx ≤ r ^ 2 * nx := mul_le_mul_of_nonneg_right hw hf.px.le
    nlinarith
  have hG := square_good (V := V) (fr := fr) hp hc hRc hSc hwd hR hS (a := -(e1 * nx) / (n1 * xx))
    (b := -(e2 * nx) / (n2 * xx)) (x := rdot w (kval fr.E1)) (y := rdot w (kval fr.E2)) (z := rdot w (kval fr.X))
    (by
      rw [abs_div, abs_neg, abs_mul, abs_of_pos hf.px, abs_of_pos (mul_pos hf.p1 hx0), div_le_iff₀ (mul_pos hf.p1 hx0)]
      linarith)
    (by
      rw [abs_div, abs_neg, abs_mul, abs_of_pos hf.px, abs_of_pos (mul_pos hf.p2 hx0), div_le_iff₀ (mul_pos hf.p2 hx0)]
      linarith)
    (rb _ _ hf.p1 hf.e1 hr1) (rb _ _ hf.p2 hf.e2 hr2) rbz
  refine hG p (xx / nx) ?_ ?_
  · conv_lhs => rw [dec p.view]
    funext i
    simp only [uR, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · have hw' : wR fr (rdot w (kval fr.E1)) (rdot w (kval fr.E2)) (rdot w (kval fr.X)) = w := by
      conv_rhs => rw [dec w]
      funext i
      simp only [wR, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have k1 : (fr.k1 : ℝ) = 1 / n1 := by field_simp; linarith [hf.k1]
      have k2 : (fr.k2 : ℝ) = 1 / n2 := by field_simp; linarith [hf.k2]
      have k3 : (fr.k3 : ℝ) = 1 / nx := by field_simp; linarith [hf.k3]
      rw [k1, k2, k3]
      ring
    rw [hw']; exact hR'

end real

end ArcCap

end Noperts.Pipeline

end
