module

public import Pipeline.ArcCapCover

@[expose] public section

/-!
# The arc cap's claim

`neoParams` are the parameters of `capcert-neo` for the solid M18 (radii 1/8,
regime change t* = 17/86, flexes (17 − 22 t)/64 and (17 − 64 t)/22, views up to
t = 13/32). With a checked certificate:

* `Fits β f t b x y z ν`: the pose of apex coordinates (t, b, x, y, z) has weighted
  norm at most ν for the b scale β and the flex f. `fit_cube` is the weighted cube.
* `w0_good`, `w1_good`, `w2_good`: the pieces at a radius ν.
* `arc_good`: near t*, between the two flexes. The mid chart's coordinate r is
  bounded by a lemma on the norms: if the mid chart's norm μ has
  (5/3) μ < δ = |t − t*| / (2 t*), then the pose fits W0 or W1 at the radius δ,
  otherwise |r| ≤ 10/3 + 5/4 t* < 6.
* `wedge_good`, `u_good`, `cover_good`: every pose with (a, b) in the half square
  or the wedge and |x|, |y|, |z| ≤ 1/46 is good.
-/

namespace Noperts.Pipeline

namespace ArcCap

open Noperts.Pipeline.KCap
open Noperts.Pipeline.KCap.PVec

/-- The parameters of the certificate of M18. -/
def neoParams : Params where
  mu0 := 1 / 8
  R := 2
  S := 8
  Rc := 1 / 2
  Sc := 8
  nu0 := 1 / 8
  R1 := 3
  R2 := 32
  R3 := 128
  Z := 16
  tstar := 17 / 86
  zh := 2
  zmid := 6
  bmid := 5 / 4 * (17 / 86)
  tsplit := 11 / 32
  tend := 13 / 32
  f0c := 17 / 64
  f0d := -22 / 64
  f1c := 17 / 22
  f1d := -64 / 22

theorem neoParams_ok : neoParams.Ok := by norm_num [Params.Ok, neoParams]

/-- The first flex and the second. -/
noncomputable def f0 (t : ℝ) : ℝ := 17 / 64 + -22 / 64 * t
noncomputable def f1 (t : ℝ) : ℝ := 17 / 22 + -64 / 22 * t

/-- The pose (t, b, x, y, z) has weighted norm at most ν, for the b scale β and the flex f. -/
structure Fits (β f t b x y z ν : ℝ) : Prop where
  hb : |b| ≤ β * ν
  h1 : |2 * x| ≤ 3 * ν * t
  h2 : |2 * y - f * (2 * x)| ≤ 32 * ν ^ 2 * t
  h3 : |z - t * x| ≤ 128 * ν ^ 2 * t ^ 2

/-- The weighted cube of a fitting pose: a point of the boundary of the cube at a radius μ ≤ ν. -/
theorem fit_cube {β f t b x y z ν : ℝ} (hβ : 0 < β) (ht : 0 < t) (hν : 0 ≤ ν) (hF : Fits β f t b x y z ν) :
    ∃ μ al s1 s2 s3 : ℝ, 0 ≤ μ ∧ μ ≤ ν ∧ |al| ≤ 1 ∧ |s1| ≤ 3 ∧ |s2| ≤ 32 ∧ |s3| ≤ 128 ∧
      (|al| = 1 ∨ |s1| = 3 ∨ |s2| = 32 ∨ |s3| = 128) ∧
      b = β * (μ * al) ∧ 2 * x = μ * t * s1 ∧ 2 * y - f * (2 * x) = μ ^ 2 * t * s2 ∧
      z - t * x = μ ^ 2 * t ^ 2 * s3 := by
  have ht2 : 0 < t ^ 2 := pow_pos ht 2
  obtain ⟨μ, e, s, h0, h1, he0, he1, hme, hs, hc⟩ :=
    Cap.weighted_cube ![1, 2, 2] (by intro i; fin_cases i <;> simp) ![3, 32, 128]
      (by intro i; fin_cases i <;> simp) ν (|b| / β) (div_nonneg (abs_nonneg _) hβ.le)
      (by rw [div_le_iff₀ hβ]; linarith [hF.hb])
      ![2 * x / t, (2 * y - f * (2 * x)) / t, (z - t * x) / t ^ 2]
      (by
        intro i
        fin_cases i
        · simp only [Fin.zero_eta, Matrix.cons_val_zero, pow_one, abs_div, abs_of_pos ht]
          rw [div_le_iff₀ ht]; linarith [hF.h1]
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, abs_div, abs_of_pos ht]
          rw [div_le_iff₀ ht]; linarith [hF.h2]
        · simp only [Fin.reduceFinMk, Matrix.cons_val, abs_div, abs_of_pos ht2]
          rw [div_le_iff₀ ht2]; linarith [hF.h3])
  have s0 := hs 0; have s1 := hs 1; have s2 := hs 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, pow_one] at s0 s1 s2
  have hbe : |b| = β * (μ * e) := by rw [← hme]; field_simp
  refine ⟨μ, if 0 ≤ b then e else -e, s 0, s 1, s 2, h0, h1, ?_, s0.2, s1.2, s2.2, ?_, ?_, ?_, ?_, ?_⟩
  · split_ifs <;> simp [abs_of_nonneg he0, he1]
  · rcases hc with rfl | ⟨k, hk⟩
    · left; split_ifs <;> simp
    · right
      fin_cases k
      · left; simpa using hk
      · right; left; simpa using hk
      · right; right; simpa using hk
  · split_ifs with hb0
    · rw [← abs_of_nonneg hb0, hbe]
    · have := abs_of_neg (not_le.mp hb0)
      rw [mul_neg, mul_neg, ← hbe, this, neg_neg]
  · have := s0.1; field_simp at this; linarith
  · have := s1.1; field_simp at this; linarith
  · have := s2.1; field_simp at this; linarith

section real

variable {K : Type} [ExactScalarOps K] [ExactScalarVal K]
variable {V : Array (KCap.KVec K)} {fr : Frame K}

theorem good_of_goodW {π : Piece} {μ p al s1 s2 s3 t b x y z : ℝ}
    (ht : tR neoParams π μ p al = t) (hb : bR neoParams π μ t al = b) (e1 : 2 * x = μ * t * s1)
    (e2 : 2 * y - fR neoParams π t * (2 * x) = μ ^ 2 * t * s2) (e3 : z - t * x = μ ^ 2 * t ^ 2 * s3)
    (h : GoodW V fr neoParams π μ p al s1 s2 s3) : Good V fr t b x y z := by
  simp only [GoodW, ht, hb] at h
  have a1 : 1 / 2 * (μ * t * s1) = x := by rw [← e1]; ring
  have a2 : 1 / 2 * (μ * t * s1 * fR neoParams π t + μ * μ * (t * s2)) = y := by
    rw [← e1]
    have : μ * μ * (t * s2) = 2 * y - fR neoParams π t * (2 * x) := by rw [e2]; ring
    rw [this]; ring
  have a3 : 1 / 2 * (μ * t * s1 * t) + μ * μ * (t * t) * s3 = z := by
    rw [← e1]
    have : μ * μ * (t * t) * s3 = z - t * x := by rw [e3]; ring
    rw [this]; ring
  rw [a1, a2, a3] at h
  exact h

/-- The chart cube of a piece, from a checked certificate. -/
theorem cube_good {c : Cert} (hc : certCheck V fr neoParams c = true) (π : Piece) {μ p al s1 s2 s3 : ℝ}
    (h0 : 0 ≤ μ) (h1 : μ ≤ 1 / 8) (hp : Mem (p1Box neoParams π) p) (hal : |al| ≤ 1) (hs1 : |s1| ≤ 3)
    (hs2 : |s2| ≤ 32) (hs3 : |s3| ≤ 128) (hf : |al| = 1 ∨ |s1| = 3 ∨ |s2| = 32 ∨ |s3| = 128) :
    GoodW V fr neoParams π μ p al s1 s2 s3 := by
  have cZ : (neoParams.Z : ℝ) = 16 := by norm_num [neoParams]
  have c0 : (neoParams.nu0 : ℝ) = 1 / 8 := by norm_num [neoParams]
  have c1 : (neoParams.R1 : ℝ) = 3 := by norm_num [neoParams]
  have c2 : (neoParams.R2 : ℝ) = 32 := by norm_num [neoParams]
  have c3 : (neoParams.R3 : ℝ) = 128 := by norm_num [neoParams]
  exact goodW_of_cube V fr neoParams π (cert_goodW neoParams_ok hc π) (by norm_num [cZ]) (by norm_num [c2])
    (by norm_num [c3]) h0 (by rw [c0]; exact h1) hp hal (by rw [c1]; exact hs1) (by rw [c2]; exact hs2)
    (by rw [c3]; exact hs3) (by rw [c1, c2, c3]; exact hf)

theorem w0_good {c : Cert} (hc : certCheck V fr neoParams c = true) {t b x y z ν : ℝ} (ht : 0 < t) (hν : 0 ≤ ν)
    (hν1 : ν ≤ 1 / 8) (hF : Fits t (f0 t) t b x y z ν) (hle : t ≤ 17 / 86 * (1 - 2 * ν)) :
    Good V fr t b x y z := by
  obtain ⟨μ, al, s1, s2, s3, h0, h1, hal, hs1, hs2, hs3, hf, hb, e1, e2, e3⟩ := fit_cube ht ht hν hF
  have hd : 0 < 17 / 86 * (1 - 2 * μ) := by nlinarith
  have hp0 : 0 ≤ t / (17 / 86 * (1 - 2 * μ)) := div_nonneg ht.le hd.le
  have hp1 : t / (17 / 86 * (1 - 2 * μ)) ≤ 1 := by rw [div_le_one hd]; nlinarith
  refine good_of_goodW (π := .w0) (p := t / (17 / 86 * (1 - 2 * μ))) (al := al) (s1 := s1) (s2 := s2) (s3 := s3)
    ?_ ?_ e1 ?_ e3 (cube_good hc .w0 h0 (by linarith) ?_ hal hs1 hs2 hs3 hf)
  · simp only [tR, neoParams]; push_cast; exact mul_div_cancel₀ _ hd.ne'
  · simp only [bR]; exact hb.symm
  · simp only [fR, neoParams]; push_cast; rw [← e2]; simp only [f0]
  · simpa [p1Box] using mem_zero hp0 (by simpa using hp1)

theorem w1_good {c : Cert} (hc : certCheck V fr neoParams c = true) {t b x y z ν : ℝ} (ht : 0 < t) (hν : 0 ≤ ν)
    (hν1 : ν ≤ 1 / 8) (hF : Fits t (f1 t) t b x y z ν) (hlo : 17 / 86 * (1 + 2 * ν) ≤ t) (hhi : t ≤ 11 / 32) :
    Good V fr t b x y z := by
  obtain ⟨μ, al, s1, s2, s3, h0, h1, hal, hs1, hs2, hs3, hf, hb, e1, e2, e3⟩ := fit_cube ht ht hν hF
  have hd : 0 < 11 / 32 - 17 / 86 * (1 + 2 * μ) := by nlinarith
  have hp0 : 0 ≤ (t - 17 / 86 * (1 + 2 * μ)) / (11 / 32 - 17 / 86 * (1 + 2 * μ)) :=
    div_nonneg (by nlinarith) hd.le
  have hp1 : (t - 17 / 86 * (1 + 2 * μ)) / (11 / 32 - 17 / 86 * (1 + 2 * μ)) ≤ 1 := by
    rw [div_le_one hd]; linarith
  refine good_of_goodW (π := .w1) (p := (t - 17 / 86 * (1 + 2 * μ)) / (11 / 32 - 17 / 86 * (1 + 2 * μ))) (al := al)
    (s1 := s1) (s2 := s2) (s3 := s3) ?_ ?_ e1 ?_ e3 (cube_good hc .w1 h0 (by linarith) ?_ hal hs1 hs2 hs3 hf)
  · simp only [tR, neoParams]; push_cast
    rw [mul_div_cancel₀ _ hd.ne']; ring
  · simp only [bR]; exact hb.symm
  · simp only [fR, neoParams]; push_cast; rw [← e2]; simp only [f1]
  · simpa [p1Box] using mem_zero hp0 (by simpa using hp1)

theorem w2_good {c : Cert} (hc : certCheck V fr neoParams c = true) {t b x y z ν : ℝ} (ht : 0 < t) (hν : 0 ≤ ν)
    (hν1 : ν ≤ 1 / 8) (hF : Fits t (f1 t) t b x y z ν) (hlo : 11 / 32 ≤ t) (hhi : t ≤ 13 / 32) :
    Good V fr t b x y z := by
  obtain ⟨μ, al, s1, s2, s3, h0, h1, hal, hs1, hs2, hs3, hf, hb, e1, e2, e3⟩ := fit_cube ht ht hν hF
  refine good_of_goodW (π := .w2) (p := (t - 11 / 32) * 16) (al := al) (s1 := s1) (s2 := s2) (s3 := s3)
    ?_ ?_ e1 ?_ e3 (cube_good hc .w2 h0 (by linarith) ?_ hal hs1 hs2 hs3 hf)
  · simp only [tR, neoParams]; push_cast; ring
  · simp only [bR]; exact hb.symm
  · simp only [fR, neoParams]; push_cast; rw [← e2]; simp only [f1]
  · simpa [p1Box] using mem_zero (w := 1) (by linarith) (by push_cast; linarith)

/-- The mid chart's fit gives a point of Wm if |t − t*| / (2 t*) ≤ (5/3) μ. -/
theorem wm_good {c : Cert} (hc : certCheck V fr neoParams c = true) {t b x y z μ al s1 s2 s3 : ℝ}
    (h0 : 0 ≤ μ) (h1 : μ ≤ 1 / 8) (hal : |al| ≤ 1) (hs1 : |s1| ≤ 3) (hs2 : |s2| ≤ 32) (hs3 : |s3| ≤ 128)
    (hf : |al| = 1 ∨ |s1| = 3 ∨ |s2| = 32 ∨ |s3| = 128)
    (hb : b = 5 / 4 * (17 / 86) * (μ * al)) (e1 : 2 * x = μ * t * s1)
    (e2 : 2 * y - f0 t * (2 * x) = μ ^ 2 * t * s2) (e3 : z - t * x = μ ^ 2 * t ^ 2 * s3)
    (hδ : |t - 17 / 86| ≤ 2 * (17 / 86) * (5 / 3 * μ)) : Good V fr t b x y z := by
  have hbb : |b| ≤ 5 / 4 * (17 / 86) * μ := by
    rw [hb, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4 * (17 / 86)), abs_mul, abs_of_nonneg h0]
    have := mul_le_mul_of_nonneg_left hal h0
    nlinarith
  -- r μ = t / t* − 1 + b.
  have hr : ∃ r : ℝ, |r| ≤ 6 ∧ μ * r = t / (17 / 86) - 1 + b := by
    rcases h0.lt_or_eq with hpos | hz
    · refine ⟨(t / (17 / 86) - 1 + b) / μ, ?_, by field_simp⟩
      rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      have ha := abs_le.mp hδ
      have hbb' := abs_le.mp hbb
      refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [ha.1, ha.2, hbb'.1, hbb'.2]
    · subst hz
      have hδ0 : t = 17 / 86 := by
        have : |t - 17 / 86| ≤ 0 := by simpa using hδ
        have := abs_nonpos_iff.mp this
        linarith
      have hb0 : b = 0 := by simpa using hb
      exact ⟨0, by norm_num, by rw [hδ0, hb0]; norm_num⟩
  obtain ⟨r, hr6, hrμ⟩ := hr
  refine good_of_goodW (π := .wm) (p := r) (al := al) (s1 := s1) (s2 := s2) (s3 := s3)
    ?_ ?_ e1 ?_ e3 (cube_good hc .wm h0 h1 ?_ hal hs1 hs2 hs3 hf)
  · simp only [tR, neoParams]; push_cast
    rw [hrμ, ← hb]; ring
  · simp only [bR, neoParams]; push_cast; exact hb.symm
  · simp only [fR, neoParams]; push_cast; rw [← e2]; simp only [f0]
  · have : p1Box neoParams .wm = sym 6 := by simp [p1Box, neoParams]
    rw [this]
    exact mem_sym (by simpa using hr6)

/-- **The regime change**: the pose near t* is in W0, Wm or W1, by the lemma on the norms. -/
theorem arc_good {c : Cert} (hc : certCheck V fr neoParams c = true) {t b x y z : ℝ}
    (hlo : 3 / 4 * (17 / 86) ≤ t) (hhi : t ≤ 5 / 4 * (17 / 86)) (hF : Fits t (f0 t) t b x y z (1 / 8)) :
    Good V fr t b x y z := by
  have ht : 0 < t := by linarith
  have hFm : Fits (5 / 4 * (17 / 86)) (f0 t) t b x y z (1 / 8) :=
    ⟨le_trans hF.hb (by nlinarith), hF.h1, hF.h2, hF.h3⟩
  obtain ⟨μ, al, s1, s2, s3, h0, h1, hal, hs1, hs2, hs3, hf, hb, e1, e2, e3⟩ :=
    fit_cube (by norm_num) ht (by norm_num) hFm
  have hbb : |b| ≤ 5 / 4 * (17 / 86) * μ := by
    rw [hb, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4 * (17 / 86)), abs_mul, abs_of_nonneg h0]
    have := mul_le_mul_of_nonneg_left hal h0
    nlinarith
  have hm1 : |2 * x| ≤ 3 * μ * t := by
    rw [e1, abs_mul, abs_mul, abs_of_nonneg h0, abs_of_pos ht]
    nlinarith [mul_nonneg h0 ht.le]
  have hm2 : |2 * y - f0 t * (2 * x)| ≤ 32 * μ ^ 2 * t := by
    rw [e2, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg h0 2), abs_of_pos ht]
    nlinarith [mul_nonneg (pow_nonneg h0 2) ht.le]
  have hm3 : |z - t * x| ≤ 128 * μ ^ 2 * t ^ 2 := by
    rw [e3, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg h0 2), abs_of_pos (pow_pos ht 2)]
    nlinarith [mul_nonneg (pow_nonneg h0 2) (pow_pos ht 2).le]
  have hwm : |t - 17 / 86| ≤ 2 * (17 / 86) * (5 / 3 * μ) → Good V fr t b x y z :=
    wm_good hc h0 h1 hal hs1 hs2 hs3 hf hb e1 e2 e3
  have step : ∀ δ : ℝ, 0 ≤ δ → 5 / 3 * μ < δ → |b| ≤ t * δ ∧ |2 * x| ≤ 3 * δ * t ∧
      32 * μ ^ 2 * t ≤ 32 * δ ^ 2 * t ∧ |z - t * x| ≤ 128 * δ ^ 2 * t ^ 2 := by
    intro δ hδ0 hlt
    have hμδ : μ ≤ δ := by linarith
    have hsq : μ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ h0 hμδ 2
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := mul_le_mul_of_nonneg_right hlo hδ0
      linarith
    · exact le_trans hm1 (mul_le_mul_of_nonneg_right (by linarith) ht.le)
    · exact mul_le_mul_of_nonneg_right (by linarith) ht.le
    · exact le_trans hm3 (mul_le_mul_of_nonneg_right (by linarith) (pow_pos ht 2).le)
  rcases le_total t (17 / 86) with hle | hge
  · -- Below t*: the first flex at the radius δ.
    set δ := (17 / 86 - t) / (2 * (17 / 86)) with hδ
    have hδt : t = 17 / 86 * (1 - 2 * δ) := by rw [hδ]; ring
    have hδ0 : 0 ≤ δ := by rw [hδ]; apply div_nonneg <;> linarith
    have hδ1 : δ ≤ 1 / 8 := by rw [hδ]; rw [div_le_iff₀ (by norm_num)]; linarith
    by_cases hc' : 5 / 3 * μ < δ
    · obtain ⟨c1, c2, c3, c4⟩ := step δ hδ0 hc'
      exact w0_good hc ht hδ0 hδ1 ⟨c1, c2, le_trans hm2 c3, c4⟩ hδt.le
    · apply hwm
      rw [abs_of_nonpos (by linarith)]
      have : δ ≤ 5 / 3 * μ := not_lt.mp hc'
      rw [hδ, div_le_iff₀ (by norm_num)] at this
      linarith
  · -- Above t*: the second flex at the radius δ.
    set δ := (t - 17 / 86) / (2 * (17 / 86)) with hδ
    have hδt : t = 17 / 86 * (1 + 2 * δ) := by rw [hδ]; ring
    have hδ0 : 0 ≤ δ := by rw [hδ]; apply div_nonneg <;> linarith
    have hδ1 : δ ≤ 1 / 8 := by rw [hδ]; rw [div_le_iff₀ (by norm_num)]; linarith
    by_cases hc' : 5 / 3 * μ < δ
    · have hμ35 : μ ≤ 3 / 5 * δ := by linarith
      obtain ⟨c1, c2, c3, c4⟩ := step δ hδ0 hc'
      refine w1_good hc ht hδ0 hδ1 ⟨c1, c2, ?_, c4⟩ hδt.ge (by linarith)
      · -- The flexes differ by (903/352) (t − t*).
        have hdiff : 2 * y - f1 t * (2 * x) = (2 * y - f0 t * (2 * x)) + 903 / 352 * (t - 17 / 86) * (2 * x) := by
          simp only [f0, f1]; ring
        have h2 : |903 / 352 * (t - 17 / 86) * (2 * x)| ≤ 903 / 352 * (2 * (17 / 86) * δ) * (3 * μ * t) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 903 / 352),
            abs_of_nonneg (by linarith : 0 ≤ t - 17 / 86)]
          have e : t - 17 / 86 = 2 * (17 / 86) * δ := by rw [hδ]; ring
          rw [e]
          exact mul_le_mul_of_nonneg_left hm1 (by positivity)
        rw [hdiff]
        refine le_trans (abs_add_le _ _) ?_
        have hμ2 : μ ^ 2 ≤ 9 / 25 * δ ^ 2 := by
          have := pow_le_pow_left₀ h0 hμ35 2
          rw [mul_pow] at this; norm_num at this ⊢; linarith
        have hμd : μ * δ ≤ 3 / 5 * δ ^ 2 := by
          have := mul_le_mul_of_nonneg_right hμ35 hδ0
          rw [pow_two]; linarith
        have a1 : 32 * μ ^ 2 * t ≤ 32 * (9 / 25 * δ ^ 2) * t := by
          apply mul_le_mul_of_nonneg_right _ ht.le; linarith
        have a2 : 903 / 352 * (2 * (17 / 86) * δ) * (3 * μ * t) ≤ 903 / 352 * (2 * (17 / 86)) * 3 * (3 / 5 * δ ^ 2) * t := by
          have : 903 / 352 * (2 * (17 / 86) * δ) * (3 * μ * t) = 903 / 352 * (2 * (17 / 86)) * 3 * (μ * δ) * t := by ring
          rw [this]
          apply mul_le_mul_of_nonneg_right _ ht.le
          apply mul_le_mul_of_nonneg_left hμd (by norm_num)
        have a3 : 0 ≤ δ ^ 2 * t := by positivity
        have a4 := hm2
        nlinarith
    · apply hwm
      rw [abs_of_nonneg (by linarith)]
      have : δ ≤ 5 / 3 * μ := not_lt.mp hc'
      rw [hδ, div_le_iff₀ (by norm_num)] at this
      linarith

/-- A rotation within 1/46 fits at the radius 1/8 from t = 1/8 on: the first flex, -/
theorem fit0 {t b x y z : ℝ} (hlo : 1 / 8 ≤ t) (hhi : t ≤ 13 / 32) (hb : |b| ≤ t / 8)
    (hx : |x| ≤ 1 / 46) (hy : |y| ≤ 1 / 46) (hz : |z| ≤ 1 / 46) : Fits t (f0 t) t b x y z (1 / 8) := by
  have ax := abs_le.mp hx
  have ay := abs_le.mp hy
  have az := abs_le.mp hz
  have hf : |f0 t| ≤ 1 / 4 := by
    simp only [f0]; rw [abs_le]; constructor <;> linarith
  have hfx : |f0 t * (2 * x)| ≤ 1 / 4 * (1 / 23) := by
    rw [abs_mul]
    apply mul_le_mul hf _ (abs_nonneg _) (by norm_num)
    rw [abs_mul]; norm_num; linarith
  have hfx' := abs_le.mp hfx
  have htx : |t * x| ≤ t * (1 / 46) := by
    rw [abs_mul, abs_of_pos (by linarith)]
    exact mul_le_mul_of_nonneg_left hx (by linarith)
  have htx' := abs_le.mp htx
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> nlinarith

/-- and the second, from t = 1/5 on. -/
theorem fit1 {t b x y z : ℝ} (hlo : 1 / 5 ≤ t) (hhi : t ≤ 13 / 32) (hb : |b| ≤ t / 8)
    (hx : |x| ≤ 1 / 46) (hy : |y| ≤ 1 / 46) (hz : |z| ≤ 1 / 46) : Fits t (f1 t) t b x y z (1 / 8) := by
  have ax := abs_le.mp hx
  have ay := abs_le.mp hy
  have az := abs_le.mp hz
  have hf : |f1 t| ≤ 1 / 2 := by
    simp only [f1]; rw [abs_le]; constructor <;> linarith
  have hfx : |f1 t * (2 * x)| ≤ 1 / 2 * (1 / 23) := by
    rw [abs_mul]
    apply mul_le_mul hf _ (abs_nonneg _) (by norm_num)
    rw [abs_mul]; norm_num; linarith
  have hfx' := abs_le.mp hfx
  have htx : |t * x| ≤ t * (1 / 46) := by
    rw [abs_mul, abs_of_pos (by linarith)]
    exact mul_le_mul_of_nonneg_left hx (by linarith)
  have htx' := abs_le.mp htx
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> nlinarith

/-- **The wedge**: every view t ∈ [1/8, 13/32], |b| ≤ t/8, every rotation within 1/46. -/
theorem wedge_good {c : Cert} (hc : certCheck V fr neoParams c = true) {t b x y z : ℝ}
    (hlo : 1 / 8 ≤ t) (hhi : t ≤ 13 / 32) (hb : |b| ≤ t / 8)
    (hx : |x| ≤ 1 / 46) (hy : |y| ≤ 1 / 46) (hz : |z| ≤ 1 / 46) : Good V fr t b x y z := by
  have ht : 0 < t := by linarith
  rcases le_total t (3 / 4 * (17 / 86)) with h1 | h1
  · exact w0_good hc ht (by norm_num) le_rfl (fit0 hlo hhi hb hx hy hz) (by linarith)
  rcases le_total t (5 / 4 * (17 / 86)) with h2 | h2
  · exact arc_good hc h1 h2 (fit0 hlo hhi hb hx hy hz)
  rcases le_total t (11 / 32) with h3 | h3
  · exact w1_good hc ht (by norm_num) le_rfl (fit1 (by linarith) hhi hb hx hy hz) (by linarith) h3
  · exact w2_good hc ht (by norm_num) le_rfl (fit1 (by linarith) hhi hb hx hy hz) h3 hhi

end real

end ArcCap

end Noperts.Pipeline

end
