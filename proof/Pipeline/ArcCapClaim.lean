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
  wedge := true

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
theorem fit_cube {β f t b x y z ν : ℝ} (hβ : 0 < β) (ht : 0 < t) (_hν : 0 ≤ ν) (hF : Fits β f t b x y z ν) :
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

omit [ExactScalarVal K] in
theorem prune_fit {μ τ q σ1 σ3 : ℝ} (hpos : 0 < μ) (hq0 : 0 ≤ q) (hτ : |τ| ≤ 1 / 8) (hq34 : q ≤ 3 / 4)
    (k3 : q * |σ1 - f0 μ| ≤ 1) (k4 : q * |8 * σ3 - 1 / 4| ≤ 2) :
    Fits μ (f0 μ) μ (μ * τ) (-1 / 2 * (μ * -(1 / 2 * q))) (1 / 2 * (μ * (1 / 2 * (q * σ1))))
      (μ * μ * (8 * (q * σ3))) (1 / 8) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [abs_mul, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_left hτ hpos.le
  · have : 2 * (-1 / 2 * (μ * -(1 / 2 * q))) = 1 / 2 * (μ * q) := by ring
    rw [this, abs_of_nonneg (by positivity)]
    have := mul_le_mul_of_nonneg_left hq34 hpos.le
    linarith
  · have : 2 * (1 / 2 * (μ * (1 / 2 * (q * σ1)))) - f0 μ * (2 * (-1 / 2 * (μ * -(1 / 2 * q)))) =
        1 / 2 * μ * (q * (σ1 - f0 μ)) := by ring
    rw [this, abs_mul, abs_of_pos (by positivity), abs_mul, abs_of_nonneg hq0]
    have := mul_le_mul_of_nonneg_left k3 (by positivity : 0 ≤ 1 / 2 * μ)
    linarith
  · have : μ * μ * (8 * (q * σ3)) - μ * (-1 / 2 * (μ * -(1 / 2 * q))) = μ ^ 2 * (q * (8 * σ3 - 1 / 4)) := by ring
    rw [this, abs_mul, abs_of_pos (by positivity), abs_mul, abs_of_nonneg hq0]
    have := mul_le_mul_of_nonneg_left k4 (by positivity : 0 ≤ μ ^ 2)
    linarith

/-- Points of the wedge boxes of the cone (1, −) of side true are wedge poses. -/
theorem prune_point {c : Cert} (hc : certCheck V fr neoParams c = true) (box : Box)
    (h : wedgeBoxOk neoParams box = true) (y : Fin 5 → ℝ) (hy : KPoly.InBox box y)
    (hr : KPoly.InBox (rootBox neoParams (.u 0 (.cone 1 false))) y) :
    PointGood V fr neoParams (.u 0 (.cone 1 false)) y := by
  rw [pointGood_u]
  have e0 : KPoly.eval 5 (uS (K := K) neoParams (.cone 1 false) 0) y = 1 / 2 * (y 2 * y 3) := by
    simp [uS, KPoly.eval_mul, eval_pconst, eval_pvar, eval_faceCoord, rc, neoParams, freeVar]
  have e1 : KPoly.eval 5 (uS (K := K) neoParams (.cone 1 false) 1) y = -(1 / 2 * y 2) := by
    simp [uS, KPoly.eval_mul, eval_pconst, eval_pvar, eval_faceCoord, rc, neoParams, signQ]
  have e2 : KPoly.eval 5 (uS (K := K) neoParams (.cone 1 false) 2) y = 8 * (y 2 * y 4) := by
    simp [uS, KPoly.eval_mul, eval_pconst, eval_pvar, eval_faceCoord, rc, neoParams, freeVar]
  rw [e0, e1, e2]
  simp only [uE, eval_kOne, GoodU, mul_one, ↓reduceIte, Nat.zero_ne_one, or_false]
  set μ := y 0 with hμ
  set τ := y 1
  set q := y 2
  set σ1 := y 3
  set σ3 := y 4
  have hμ0 : 0 ≤ μ := by simpa [rootBox] using (hr 0).1
  have hμ1 : μ ≤ 1 / 8 := by simpa [rootBox, neoParams] using (hr 0).2
  have hq0 : 0 ≤ q := by simpa [rootBox] using (hr 2).1
  have x0 := hy 0; have x1 := hy 1; have x2 := hy 2; have x3 := hy 3; have x4 := hy 4
  rcases hμ0.lt_or_eq with hpos | hz
  swap
  · -- μ = 0: the view X at the identity, a point of W0.
    have hG := cube_good (V := V) (fr := fr) hc .w0 (μ := 0) (p := 0) (al := 1) (s1 := 0) (s2 := 0) (s3 := 0)
      le_rfl (by norm_num) (by simpa [p1Box] using mem_zero (w := 1) le_rfl (by norm_num)) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa [GoodW, tR, bR, ← hz] using hG
  simp only [wedgeBoxOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := h
  simp only [neoParams] at a1 a2 a3 a4
  set L0 := (box 0).1
  set H0 := (box 0).1 + (box 0).2
  set L1 := (box 1).1
  set H1 := (box 1).1 + (box 1).2
  set H2 := (box 2).1 + (box 2).2
  set L3 := (box 3).1
  set H3 := (box 3).1 + (box 3).2
  set L4 := (box 4).1
  set H4 := (box 4).1 + (box 4).2
  set dsig := max |L3 - (17 / 64 + -22 / 64 * L0)| |H3 - (17 / 64 + -22 / 64 * H0)| with hdsig
  set dspin := max |8 * L4 - 1 / 2 / 2| |8 * H4 - 1 / 2 / 2| with hdspin
  have r1 : (max |(L1 : ℝ)| |(H1 : ℝ)|) ≤ 1 / 8 := by
    have := (Rat.cast_le (K := ℝ)).mpr a1; push_cast at this; exact this
  have r2 : (1 / 2 : ℝ) * H2 ≤ 3 * (1 / 8) := by
    have := (Rat.cast_le (K := ℝ)).mpr a2; push_cast at this; exact this
  have r3 : (1 / 2 : ℝ) * H2 * dsig ≤ 32 * (1 / 8) ^ 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr a3
    rw [Rat.cast_mul, Rat.cast_mul] at this
    push_cast at this ⊢; exact this
  have r4 : (H2 : ℝ) * dspin ≤ 128 * (1 / 8) ^ 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr a4
    rw [Rat.cast_mul] at this
    push_cast at this ⊢; exact this
  have y1L : (L1 : ℝ) ≤ τ := x1.1
  have y1H : τ ≤ (H1 : ℝ) := by simpa [H1] using x1.2
  have y2H : q ≤ (H2 : ℝ) := by simpa [H2] using x2.2
  have y0L : (L0 : ℝ) ≤ μ := x0.1
  have y0H : μ ≤ (H0 : ℝ) := by simpa [H0] using x0.2
  have y3L : (L3 : ℝ) ≤ σ1 := x3.1
  have y3H : σ1 ≤ (H3 : ℝ) := by simpa [H3] using x3.2
  have y4L : (L4 : ℝ) ≤ σ3 := x4.1
  have y4H : σ3 ≤ (H4 : ℝ) := by simpa [H4] using x4.2
  have absMax : ∀ {lo hi v : ℝ}, lo ≤ v → v ≤ hi → |v| ≤ max |lo| |hi| := by
    intro lo hi v h1 h2
    rcases le_total 0 v with h | h
    · rw [abs_of_nonneg h]; exact le_trans (le_trans h2 (le_abs_self hi)) (le_max_right _ _)
    · rw [abs_of_nonpos h]; exact le_trans (le_trans (by linarith) (neg_le_abs lo)) (le_max_left _ _)
  have hτ : |τ| ≤ 1 / 8 := le_trans (absMax y1L y1H) r1
  have hdsig' : |σ1 - f0 μ| ≤ (dsig : ℝ) := by
    have := absMax (lo := (L3 : ℝ) - (17 / 64 + -22 / 64 * L0)) (hi := (H3 : ℝ) - (17 / 64 + -22 / 64 * H0))
      (v := σ1 - f0 μ) (by simp only [f0]; linarith) (by simp only [f0]; linarith)
    rw [hdsig]; push_cast; exact this
  have hdspin' : |8 * σ3 - 1 / 4| ≤ (dspin : ℝ) := by
    have := absMax (lo := 8 * (L4 : ℝ) - 1 / 2 / 2) (hi := 8 * (H4 : ℝ) - 1 / 2 / 2) (v := 8 * σ3 - 1 / 4)
      (by linarith) (by linarith)
    rw [hdspin]; push_cast; exact this
  have hd0 : (0 : ℝ) ≤ dsig := le_trans (abs_nonneg _) hdsig'
  have hd1 : (0 : ℝ) ≤ dspin := le_trans (abs_nonneg _) hdspin'
  have hq34 : q ≤ 3 / 4 := by linarith
  have k3 : q * |σ1 - f0 μ| ≤ 1 := by
    have := mul_le_mul y2H hdsig' (abs_nonneg _) (le_trans hq0 y2H)
    nlinarith
  have k4 : q * |8 * σ3 - 1 / 4| ≤ 2 := by
    have := mul_le_mul y2H hdspin' (abs_nonneg _) (le_trans hq0 y2H)
    nlinarith
  have hF := prune_fit hpos hq0 hτ hq34 k3 k4
  exact w0_good hc hpos (by norm_num) le_rfl hF (by linarith)

/-- **The U cap**: every view of the half square, every rotation of the weighted box. -/
theorem u_good {c : Cert} (hc : certCheck V fr neoParams c = true) {a b x y z : ℝ}
    (ha : |a| ≤ 1 / 8) (hb : |b| ≤ 1 / 8) (hab : b ≤ a) (hx : |x| ≤ 1 / 8) (hy : |y| ≤ 1 / 8)
    (hz : |z| ≤ 1 / 8) : Good V fr a b x y z := by
  have cube := fun side (hs : side = 0 ∨ side = 3) => cert_goodU (V := V) (fr := fr) neoParams_ok hc
    (by norm_num [neoParams]) (by norm_num [neoParams]) (fun _ => prune_point hc) side
    (fun k hk => mem_required_u hs hk)
  have hm0 : 0 ≤ max |a| |b| := le_max_of_le_left (abs_nonneg _)
  obtain ⟨μ, e, s, h0, h1, he0, he1, hme, hs, hcase⟩ :=
    Cap.weighted_cube ![1, 1, 2] (by intro i; fin_cases i <;> simp) ![2, 2, 8]
      (by intro i; fin_cases i <;> simp) (1 / 8) (max |a| |b|) hm0 (max_le ha hb) ![2 * y, -2 * x, z]
      (by
        intro i
        fin_cases i
        · simp only [Fin.zero_eta, Matrix.cons_val_zero, pow_one, abs_mul, abs_two]; linarith
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, pow_one, abs_mul, abs_neg, abs_two]
          linarith
        · simp only [Fin.reduceFinMk, Matrix.cons_val]; norm_num; linarith)
  have s0 := hs 0; have s1 := hs 1; have s2 := hs 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, pow_one] at s0 s1 s2
  have hr : ∀ i : Fin 3, |s i| ≤ rng neoParams i := by
    intro i
    fin_cases i
    · simpa [rng, neoParams] using s0.2
    · simpa [rng, neoParams] using s1.2
    · simpa [rng, neoParams] using s2.2
  have hf : e = 1 ∨ ∃ k : Fin 3, |s k| = rng neoParams k := by
    rcases hcase with h | ⟨k, hk⟩
    · exact Or.inl h
    · right
      refine ⟨k, ?_⟩
      fin_cases k
      · simpa [rng, neoParams] using hk
      · simpa [rng, neoParams] using hk
      · simpa [rng, neoParams] using hk
  have hμ1 : μ ≤ neoParams.mu0 := by simpa [neoParams] using h1
  have ex : -1 / 2 * (μ * s 1) = x := by have := s1.1; linarith
  have ey : 1 / 2 * (μ * s 0) = y := by have := s0.1; linarith
  have ez : μ * μ * s 2 = z := by have := s2.1; rw [this]; ring
  by_cases hba : |b| ≤ a
  · have ha0 : 0 ≤ a := le_trans (abs_nonneg _) hba
    have hm : μ * e = a := by
      rw [← hme, abs_of_nonneg ha0]; exact max_eq_left hba
    rcases ha0.lt_or_eq with hpos | hz0
    · have hτ : |b / a| ≤ 1 := by
        rw [abs_div, abs_of_pos hpos, div_le_one hpos]; exact hba
      have hG := goodU_of_cube V fr neoParams 0 (cube 0 (Or.inl rfl)) h0 hμ1 hτ he0 he1 hr hf
      simp only [GoodU, hm, ex, ey, ez] at hG
      rwa [mul_div_cancel₀ _ hpos.ne'] at hG
    · have hb0 : b = 0 := by
        have : |b| ≤ 0 := by rw [hz0]; exact hba
        exact abs_nonpos_iff.mp this
      have hG := goodU_of_cube V fr neoParams 0 (cube 0 (Or.inl rfl)) h0 hμ1 (τ := 0) (by norm_num) he0 he1 hr hf
      simp only [GoodU, hm, ex, ey, ez, mul_zero] at hG
      rwa [hb0]
  · have hlt := not_le.mp hba
    have hb0 : b < 0 := by
      by_contra hcon
      rw [abs_of_nonneg (not_lt.mp hcon)] at hlt
      linarith
    rw [abs_of_neg hb0] at hlt
    have hnb : 0 < -b := by linarith
    have hab' : |a| ≤ -b := abs_le.mpr ⟨by linarith, by linarith⟩
    have hm : μ * e = -b := by
      rw [← hme, abs_of_neg hb0]; exact max_eq_right hab'
    have hτ : |a / -b| ≤ 1 := by
      rw [abs_div, abs_of_pos hnb, div_le_one hnb]; exact hab'
    have hG := goodU_of_cube V fr neoParams 3 (cube 3 (Or.inr rfl)) h0 hμ1 hτ he0 he1 hr hf
    simp only [GoodU, hm, ex, ey, ez] at hG
    rw [mul_div_cancel₀ _ hnb.ne'] at hG
    simpa using hG

/-- **The cover**: a view of the half square or the wedge, a rotation within 1/46 in each apex
coordinate. -/
theorem cover_good {c : Cert} (hc : certCheck V fr neoParams c = true) {a b x y z : ℝ}
    (hv : (|a| ≤ 1 / 8 ∧ |b| ≤ 1 / 8 ∧ b ≤ a) ∨ (|b| ≤ a / 8 ∧ a ≤ 13 / 32))
    (hx : |x| ≤ 1 / 46) (hy : |y| ≤ 1 / 46) (hz : |z| ≤ 1 / 46) : Good V fr a b x y z := by
  have hx' : |x| ≤ 1 / 8 := by linarith
  have hy' : |y| ≤ 1 / 8 := by linarith
  have hz' : |z| ≤ 1 / 8 := by linarith
  rcases hv with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · exact u_good hc h1 h2 h3 hx' hy' hz'
  · have ha0 : 0 ≤ a := by linarith [abs_nonneg b]
    rcases lt_or_ge a (1 / 8) with hlt | hge
    · exact u_good hc (by rw [abs_of_nonneg ha0]; linarith) (by linarith) (by linarith [le_abs_self b]) hx' hy' hz'
    · exact wedge_good hc hge h2 h1 hx hy hz

/-- The apex frame is orthogonal, of squared length 9. -/
structure FrameOk (fr : Frame K) : Prop where
  h12 : rdot (kval fr.E1) (kval fr.E2) = 0
  h1x : rdot (kval fr.E1) (kval fr.X) = 0
  h2x : rdot (kval fr.E2) (kval fr.X) = 0
  n1 : rdot (kval fr.E1) (kval fr.E1) = 9
  n2 : rdot (kval fr.E2) (kval fr.E2) = 9
  nx : rdot (kval fr.X) (kval fr.X) = 9
  k1 : (fr.k1 : ℝ) = 1 / 3
  k2 : (fr.k2 : ℝ) = 1 / 3
  k3 : (fr.k3 : ℝ) = 1 / 3
  w1 : fr.W1 = fr.E1
  w2 : fr.W2 = fr.E2
  w3 : fr.W3 = fr.X

/-- The view polygon P, by linear inequalities in the view v: the half square
|v·E₁|, |v·E₂| ≤ v·X / 8, v·E₁ ≤ v·E₂, and the wedge |v·E₂| ≤ −(v·E₁) / 8, −v·E₁ ≤ (13/32) v·X. -/
def InPolygon (fr : Frame K) (v : Fin 3 → ℝ) : Prop :=
  0 < rdot v (kval fr.X) ∧
    ((|rdot v (kval fr.E1)| ≤ rdot v (kval fr.X) / 8 ∧ |rdot v (kval fr.E2)| ≤ rdot v (kval fr.X) / 8 ∧
        rdot v (kval fr.E1) ≤ rdot v (kval fr.E2)) ∨
      (|rdot v (kval fr.E2)| ≤ -rdot v (kval fr.E1) / 8 ∧ -rdot v (kval fr.E1) ≤ 13 / 32 * rdot v (kval fr.X)))

/-- **The arc cap**: with a checked certificate, no pose whose view lies in the polygon P and whose
relative rotation is the Cayley rotation of w, |w·E₁|, |w·E₂|, |w·X| ≤ 3/46 (each apex coordinate at
most 1/46), is Rupert, whatever the offset. -/
theorem arc_not_rupert {c : Cert} (hc : certCheck V fr neoParams c = true) (hf : FrameOk fr)
    (p : MatrixPose) (hv : InPolygon fr p.view) (w : Fin 3 → ℝ)
    (hR : p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2))
    (h1 : |rdot w (kval fr.E1)| ≤ 3 / 46) (h2 : |rdot w (kval fr.E2)| ≤ 3 / 46)
    (h3 : |rdot w (kval fr.X)| ≤ 3 / 46) : ¬ RupertPose p (hull V) := by
  have hn : ∀ {a : ℝ}, a = 9 → a ≠ 0 := fun h => by rw [h]; norm_num
  have dec : ∀ v : Fin 3 → ℝ, v = (rdot v (kval fr.E1) / 9) • kval fr.E1 + (rdot v (kval fr.E2) / 9) • kval fr.E2 +
      (rdot v (kval fr.X) / 9) • kval fr.X := by
    intro v
    have := decomp3 _ _ _ v hf.h12 hf.h1x hf.h2x (hn hf.n1) (hn hf.n2) (hn hf.nx)
    rwa [hf.n1, hf.n2, hf.nx] at this
  obtain ⟨hx0, hreg⟩ := hv
  set e1 := rdot p.view (kval fr.E1) with he1
  set e2 := rdot p.view (kval fr.E2) with he2
  set xx := rdot p.view (kval fr.X) with hxx
  have hreg' : (|-e1 / xx| ≤ 1 / 8 ∧ |-e2 / xx| ≤ 1 / 8 ∧ -e2 / xx ≤ -e1 / xx) ∨
      (|-e2 / xx| ≤ -e1 / xx / 8 ∧ -e1 / xx ≤ 13 / 32) := by
    have absd : ∀ {q r : ℝ}, |q| ≤ r * xx → |-q / xx| ≤ r := by
      intro q r h
      rw [abs_div, abs_neg, abs_of_pos hx0, div_le_iff₀ hx0]; exact h
    rcases hreg with ⟨a1, a2, a3⟩ | ⟨a1, a2⟩
    · left
      refine ⟨absd (by linarith), absd (by linarith), ?_⟩
      rw [div_le_div_iff_of_pos_right hx0]; linarith
    · right
      constructor
      · have e : -e1 / xx / 8 = (-e1 / 8) / xx := by ring
        rw [e, abs_div, abs_neg, abs_of_pos hx0]
        exact (div_le_div_iff_of_pos_right hx0).mpr (by linarith)
      · rw [div_le_iff₀ hx0]; exact a2
  have hG := cover_good (V := V) (fr := fr) hc (a := -e1 / xx) (b := -e2 / xx) (x := rdot w (kval fr.E1) / 3)
    (y := rdot w (kval fr.E2) / 3) (z := rdot w (kval fr.X) / 3) hreg'
    (by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]; linarith)
    (by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]; linarith)
    (by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]; linarith)
  refine hG p (xx / 9) ?_ ?_
  · conv_lhs => rw [dec p.view]
    funext i
    simp only [uR, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · have hw : wR fr (rdot w (kval fr.E1) / 3) (rdot w (kval fr.E2) / 3) (rdot w (kval fr.X) / 3) = w := by
      conv_rhs => rw [dec w]
      funext i
      simp only [wR, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hf.k1, hf.k2, hf.k3, hf.w1, hf.w2, hf.w3]
      ring
    rw [hw]; exact hR

theorem rdot_sq_le (a b : Fin 3 → ℝ) : rdot a b ^ 2 ≤ rdot a a * rdot b b := by
  simp only [rdot]
  nlinarith [sq_nonneg (a 0 * b 1 - a 1 * b 0), sq_nonneg (a 0 * b 2 - a 2 * b 0),
    sq_nonneg (a 1 * b 2 - a 2 * b 1)]

/-- The arc cap for a Cayley vector of Euclidean length at most 1/46 (what `CayleyNear` gives for a
rotation within 1/46 of the identity). -/
theorem arc_not_rupert_of_norm {c : Cert} (hc : certCheck V fr neoParams c = true) (hf : FrameOk fr)
    (p : MatrixPose) (hv : InPolygon fr p.view) (w : Fin 3 → ℝ)
    (hR : p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2))
    (hw : rdot w w ≤ (1 / 46) ^ 2) : ¬ RupertPose p (hull V) := by
  have hb : ∀ e : Fin 3 → ℝ, rdot e e = 9 → |rdot w e| ≤ 3 / 46 := by
    intro e he
    have h := rdot_sq_le w e
    rw [he] at h
    apply abs_le_of_sq_le_sq _ (by norm_num)
    nlinarith
  exact arc_not_rupert hc hf p hv w hR (hb _ hf.n1) (hb _ hf.n2) (hb _ hf.nx)

end real

end ArcCap

end Noperts.Pipeline

end
