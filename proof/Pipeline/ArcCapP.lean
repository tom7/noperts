module

public import Pipeline.ArcCapAxis

@[expose] public section

/-!
# The wedge along a circle of views and the U cap around it (the P cap)

For a special view P with an edge-on face whose circle of views carries a two-dimensional first-order
flex (M12: P = (2, 1, 0) and face 024), the views near the circle are blown up as

  u = X − t E₁ − b E₂,   w = x W₁ + y W₂ + z W₃   (rotation basis `Frame.W1..W3`, weights k = 1),

* the wedge `ChartId.p` (`PKind`): (t, b, x, y, z) = (t, t ν α, ν t s₁, ν t s₂, ν² t² s₃) with
  t = thi · p₁, ν ≤ ν₀ and (α; s₁, s₂, s₃) on the boundary of the cube [−1, 1] × ∏ [−R_i, R_i]:
  at α = ±1 the cone `fp` over the cube, else the faces `face0`, `face1`, `face2` (the last with the
  ratio split of (s₁, s₂) at Z ν);
* the U cap `ChartId.pu` (the charts of `ChartId.u` on the four sides of the square), whose boxes on side 0
  inside the wedge are left to it (`wpTest`).

* `wp_good`: every pose of the wedge cube (t ≤ thi, |b| ≤ ν₀ t, |x| ≤ ν₀ R₁ t, |y| ≤ ν₀ R₂ t,
  |z| ≤ ν₀² R₃ t²) is good, from the checked charts `p`.
* `cert_goodPU`: the charts `pu` of a side are closed, given `wp_good`.
-/

namespace Noperts.Pipeline

namespace ArcCap

open Noperts.Pipeline.KCap
open Noperts.Pipeline.KCap.PVec

section real

variable {K : Type} [ExactScalarOps K] [ExactScalarVal K]

/-- A pose of the wedge `p` is good. -/
def GoodP (V : Array (KCap.KVec K)) (fr : Frame K) (t ν α s1 s2 s3 : ℝ) : Prop :=
  Good V fr t (t * ν * α) (ν * t * s1) (ν * t * s2) (ν * ν * (t * t) * s3)

theorem pointGood_p (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (k : PKind) (y : Fin 5 → ℝ) :
    PointGood V fr pr (.p k) y ↔ GoodP V fr (pr.thi * y 1) (y 0) (KPoly.eval 5 (pAl (K := K) k) y)
      (KPoly.eval 5 (pS (K := K) pr k 0) y) (KPoly.eval 5 (pS (K := K) pr k 1) y)
      (KPoly.eval 5 (pS (K := K) pr k 2) y) := by
  simp only [PointGood, coords, pCoords, GoodP, KPoly.eval_mul, eval_pconst, eval_pvar]

theorem mem_pKinds_fp (al : Bool) (k : Fin 3) (sg : Bool) : PKind.fp al k sg ∈ pKinds := by
  fin_cases k <;> cases al <;> cases sg <;> simp [pKinds]

theorem mem_pKinds_face0 (sg : Bool) : PKind.face0 sg ∈ pKinds := by cases sg <;> simp [pKinds]

theorem mem_pKinds_face1 (sg : Bool) : PKind.face1 sg ∈ pKinds := by cases sg <;> simp [pKinds]

theorem mem_pKinds_face2 (m : ℕ) (hm : m < 5) (sg : Bool) : PKind.face2 m sg ∈ pKinds := by
  cases sg <;> simp [pKinds] <;> omega

/-- At ν = 0 the wedge's pose depends on t only. -/
theorem goodP_zero (V : Array (KCap.KVec K)) (fr : Frame K) (t α s1 s2 s3 : ℝ)
    (h : GoodP V fr t 0 1 0 0 0) : GoodP V fr t 0 α s1 s2 s3 := by
  simpa [GoodP] using h

/-- **The wedge's cube**: with every chart of the wedge closed, a pose given by a point of the boundary of
the cube, at a radius ν ≤ ν₀, is good. -/
theorem goodP_of_cube (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params)
    (hg : ∀ k ∈ pKinds, ∀ y, KPoly.InBox (rootBox pr (.p k)) y → PointGood V fr pr (.p k) y)
    (hthi : 0 < (pr.thi : ℝ)) (hZ : 0 < (pr.Z : ℝ)) (hR1 : 0 < (pr.R1 : ℝ)) (hR2 : 0 < (pr.R2 : ℝ))
    (hR3 : 0 < (pr.R3 : ℝ))
    {ν p α s1 s2 s3 : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ pr.nu0) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hal : |α| ≤ 1) (h1 : |s1| ≤ pr.R1) (h2 : |s2| ≤ pr.R2) (h3 : |s3| ≤ pr.R3)
    (hf : |α| = 1 ∨ |s1| = pr.R1 ∨ |s2| = pr.R2 ∨ |s3| = pr.R3) :
    GoodP V fr (pr.thi * p) ν α s1 s2 s3 := by
  have hν : Mem (0, pr.nu0) ν := mem_zero hν0 hν1
  have hp : Mem (0, 1) p := mem_zero hp0 (by simpa using hp1)
  -- The cone point: α = ±1 and s in the cube.
  have hcone : ∀ (A : Bool) (s1 s2 s3 : ℝ), |s1| ≤ pr.R1 → |s2| ≤ pr.R2 → |s3| ≤ pr.R3 →
      GoodP V fr (pr.thi * p) ν ((signQ A : ℚ) : ℝ) s1 s2 s3 := by
    intro A s1 s2 s3 h1 h2 h3
    obtain ⟨tt, htt0, hle, ⟨i0, hi0⟩, a, sgn, σ, hσa, hσ1, hv⟩ :=
      maxface (n := 3) (by norm_num) ![s1 / pr.R1, s2 / pr.R2, s3 / pr.R3]
    have htt1 : tt ≤ 1 := by
      rw [← hi0]
      fin_cases i0 <;> simp [abs_div, abs_of_pos hR1, abs_of_pos hR2, abs_of_pos hR3, div_le_one, hR1, hR2, hR3,
        h1, h2, h3]
    have hb := other3_bound a σ hσ1
    set y : Fin 5 → ℝ := ![ν, p, tt, (other3 a σ).1, (other3 a σ).2] with hy
    have hin : KPoly.InBox (rootBox pr (.p (.fp A a sgn))) y :=
      inBox_vec hν hp (mem_zero htt0 (by simpa using htt1)) (mem_one hb.1) (mem_one hb.2)
    have hG := (pointGood_p V fr pr (.fp A a sgn) y).mp (hg _ (mem_pKinds_fp A a sgn) y hin)
    have hσ' : σ a = ((signQ sgn * 1 : ℚ) : ℝ) := by simpa using hσa
    have e : ∀ i : Fin 3, KPoly.eval 5 (pS (K := K) pr (.fp A a sgn) i) y = (pR pr i : ℝ) * (tt * σ i) := by
      intro i
      simp only [pS, pCone, KPoly.eval_mul, eval_pconst, eval_pvar]
      rw [hy, eval_faceCoord_of a sgn 1 σ hσ' i]
      simp
    have v0 := hv 0; have v1 := hv 1; have v2 := hv 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at v0 v1 v2
    have e0 : (pR pr ((0 : Fin 3) : ℕ) : ℝ) * (tt * σ 0) = s1 := by
      show (pr.R1 : ℝ) * (tt * σ 0) = s1
      rw [← v0]; field_simp
    have e1 : (pR pr ((1 : Fin 3) : ℕ) : ℝ) * (tt * σ 1) = s2 := by
      show (pr.R2 : ℝ) * (tt * σ 1) = s2
      rw [← v1]; field_simp
    have e2 : (pR pr ((2 : Fin 3) : ℕ) : ℝ) * (tt * σ 2) = s3 := by
      show (pr.R3 : ℝ) * (tt * σ 2) = s3
      rw [← v2]; field_simp
    have y0 : y 0 = ν := rfl
    have y1 : y 1 = p := rfl
    have E0 := e 0; have E1 := e 1; have E2 := e 2
    rw [e0] at E0; rw [e1] at E1; rw [e2] at E2
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at E0 E1 E2
    simp only [pAl, y0, y1, eval_pconst] at hG
    rw [E0, E1, E2] at hG
    exact hG
  rcases hν0.lt_or_eq with hpos | hzero
  swap
  · -- ν = 0.
    subst hzero
    apply goodP_zero
    have := hcone true 0 0 0 (by simpa using hR1.le) (by simpa using hR2.le) (by simpa using hR3.le)
    simpa [signQ] using this
  have hal' := mem_one hal
  have hq1 := mem_sym h1
  have hq2 := mem_sym h2
  have hq3 := mem_sym h3
  have hZν := mul_pos hZ hpos
  rcases hf with hf | hf | hf | hf
  · obtain ⟨A, hA⟩ := exists_sign hf
    rw [mul_one] at hA
    rw [hA]
    exact hcone A s1 s2 s3 h1 h2 h3
  · obtain ⟨sg, hs⟩ := exists_sign hf
    set y : Fin 5 → ℝ := ![ν, p, α, s2, s3] with hy
    have hin : KPoly.InBox (rootBox pr (.p (.face0 sg))) y := inBox_vec hν hp hal' hq2 hq3
    have hG := (pointGood_p V fr pr (.face0 sg) y).mp (hg _ (mem_pKinds_face0 sg) y hin)
    simpa [y, pAl, pS, eval_pconst, eval_pvar, ← hs] using hG
  · obtain ⟨sg, hs⟩ := exists_sign hf
    set y : Fin 5 → ℝ := ![ν, p, α, s1, s3] with hy
    have hin : KPoly.InBox (rootBox pr (.p (.face1 sg))) y := inBox_vec hν hp hal' hq1 hq3
    have hG := (pointGood_p V fr pr (.face1 sg) y).mp (hg _ (mem_pKinds_face1 sg) y hin)
    simpa [y, pAl, pS, eval_pconst, eval_pvar, ← hs] using hG
  · obtain ⟨sg, rfl⟩ := exists_sign hf
    -- the four (s₁, s₂) regimes
    by_cases c1 : pr.Z * ν < s1
    · set y : Fin 5 → ℝ := ![ν, p, α, s1 - pr.Z * ν, s2] with hy
      have hin : KPoly.InBox (rootBox pr (.p (.face2 1 sg))) y := by
        show KPoly.InBox ![(0, pr.nu0), (0, 1), (-1, 2), (0, pr.R1), sym pr.R2] y
        exact inBox_vec hν hp hal' (mem_zero (by simp [y]; linarith) (by simp [y]; linarith [(abs_le.mp h1).2])) hq2
      have hG := (pointGood_p V fr pr (.face2 1 sg) y).mp (hg _ (mem_pKinds_face2 1 (by norm_num) sg) y hin)
      simp [y, pAl, pS, eval_pconst, eval_pvar, KPoly.eval_add, KPoly.eval_mul] at hG
      convert hG using 2 <;> ring
    by_cases c2 : s1 < -(pr.Z * ν)
    · set y : Fin 5 → ℝ := ![ν, p, α, -s1 - pr.Z * ν, s2] with hy
      have hin : KPoly.InBox (rootBox pr (.p (.face2 2 sg))) y := by
        show KPoly.InBox ![(0, pr.nu0), (0, 1), (-1, 2), (0, pr.R1), sym pr.R2] y
        exact inBox_vec hν hp hal' (mem_zero (by simp [y]; linarith) (by simp [y]; linarith [(abs_le.mp h1).1])) hq2
      have hG := (pointGood_p V fr pr (.face2 2 sg) y).mp (hg _ (mem_pKinds_face2 2 (by norm_num) sg) y hin)
      simp [y, pAl, pS, eval_pconst, eval_pvar, KPoly.eval_add, KPoly.eval_mul] at hG
      convert hG using 2 <;> ring
    have b1 : |s1| ≤ pr.Z * ν := abs_le.mpr ⟨by linarith, by linarith⟩
    have r1 : |s1 / ν| ≤ pr.Z := by
      rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]; exact b1
    have d1 : ν * (s1 / ν) = s1 := by field_simp
    by_cases c3 : pr.Z * ν < s2
    · set y : Fin 5 → ℝ := ![ν, p, α, s1 / ν, s2 - pr.Z * ν] with hy
      have hin : KPoly.InBox (rootBox pr (.p (.face2 3 sg))) y := by
        show KPoly.InBox ![(0, pr.nu0), (0, 1), (-1, 2), sym pr.Z, (0, pr.R2)] y
        exact inBox_vec hν hp hal' (mem_sym r1) (mem_zero (by simp [y]; linarith) (by simp [y]; linarith [(abs_le.mp h2).2]))
      have hG := (pointGood_p V fr pr (.face2 3 sg) y).mp (hg _ (mem_pKinds_face2 3 (by norm_num) sg) y hin)
      simp [y, pAl, pS, eval_pconst, eval_pvar, KPoly.eval_add, KPoly.eval_mul, d1] at hG
      convert hG using 2 <;> ring
    by_cases c4 : s2 < -(pr.Z * ν)
    · set y : Fin 5 → ℝ := ![ν, p, α, s1 / ν, -s2 - pr.Z * ν] with hy
      have hin : KPoly.InBox (rootBox pr (.p (.face2 4 sg))) y := by
        show KPoly.InBox ![(0, pr.nu0), (0, 1), (-1, 2), sym pr.Z, (0, pr.R2)] y
        exact inBox_vec hν hp hal' (mem_sym r1) (mem_zero (by simp [y]; linarith) (by simp [y]; linarith [(abs_le.mp h2).1]))
      have hG := (pointGood_p V fr pr (.face2 4 sg) y).mp (hg _ (mem_pKinds_face2 4 (by norm_num) sg) y hin)
      simp [y, pAl, pS, eval_pconst, eval_pvar, KPoly.eval_add, KPoly.eval_mul, d1] at hG
      convert hG using 2 <;> ring
    have b2 : |s2| ≤ pr.Z * ν := abs_le.mpr ⟨by linarith, by linarith⟩
    have r2 : |s2 / ν| ≤ pr.Z := by
      rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]; exact b2
    have d2 : ν * (s2 / ν) = s2 := by field_simp
    set y : Fin 5 → ℝ := ![ν, p, α, s1 / ν, s2 / ν] with hy
    have hin : KPoly.InBox (rootBox pr (.p (.face2 0 sg))) y := by
      show KPoly.InBox ![(0, pr.nu0), (0, 1), (-1, 2), sym pr.Z, sym pr.Z] y
      exact inBox_vec hν hp hal' (mem_sym r1) (mem_sym r2)
    have hG := (pointGood_p V fr pr (.face2 0 sg) y).mp (hg _ (mem_pKinds_face2 0 (by norm_num) sg) y hin)
    simp [y, pAl, pS, eval_pconst, eval_pvar, KPoly.eval_add, KPoly.eval_mul, d1, d2] at hG
    exact hG

/-- **The wedge cube is good**: every pose with view (t, b), t ≤ thi, and rotation (x, y, z) of weighted norm
at most ν₀ (|b| ≤ ν₀ t, |x| ≤ ν₀ R₁ t, |y| ≤ ν₀ R₂ t, |z| ≤ ν₀² R₃ t²). -/
theorem wp_good (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params)
    (hg : ∀ k ∈ pKinds, ∀ y, KPoly.InBox (rootBox pr (.p k)) y → PointGood V fr pr (.p k) y)
    (hthi : 0 < (pr.thi : ℝ)) (hZ : 0 < (pr.Z : ℝ)) (hR1 : 0 < (pr.R1 : ℝ)) (hR2 : 0 < (pr.R2 : ℝ))
    (hR3 : 0 < (pr.R3 : ℝ)) (hn0 : 0 ≤ (pr.nu0 : ℝ)) {t b x y z : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ pr.thi)
    (hb : |b| ≤ pr.nu0 * t) (hx : |x| ≤ pr.nu0 * pr.R1 * t) (hy : |y| ≤ pr.nu0 * pr.R2 * t)
    (hz : |z| ≤ pr.nu0 ^ 2 * pr.R3 * t ^ 2) : Good V fr t b x y z := by
  rcases ht0.lt_or_eq with htp | htz
  swap
  · subst htz
    have hb0 : b = 0 := by simpa using hb
    have hx0 : x = 0 := by simpa using hx
    have hy0 : y = 0 := by simpa using hy
    have hz0 : z = 0 := by simpa using hz
    subst hb0 hx0 hy0 hz0
    have := goodP_of_cube V fr pr hg hthi hZ hR1 hR2 hR3 (ν := 0) (p := 0) (α := 1) (s1 := 0) (s2 := 0) (s3 := 0)
      le_rfl hn0 le_rfl zero_le_one (by simp) (by simpa using hR1.le) (by simpa using hR2.le)
      (by simpa using hR3.le) (Or.inl (by simp))
    simpa [GoodP] using this
  have ht2 : 0 < t ^ 2 := pow_pos htp 2
  obtain ⟨μ, e, s, h0, h1, he0, he1, hme, hs, hcase⟩ :=
    Cap.weighted_cube ![1, 1, 2] (by intro i; fin_cases i <;> simp) ![(pr.R1 : ℝ), pr.R2, pr.R3]
      (by intro i; fin_cases i <;> simp [hR1, hR2, hR3]) pr.nu0 (|b| / t) (div_nonneg (abs_nonneg _) ht0)
      (by rw [div_le_iff₀ htp]; exact hb) ![x / t, y / t, z / t ^ 2]
      (by
        intro i
        fin_cases i
        · simp only [Fin.zero_eta, Matrix.cons_val_zero, pow_one, abs_div, abs_of_pos htp]
          rw [div_le_iff₀ htp]; linarith
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, pow_one, abs_div, abs_of_pos htp]
          rw [div_le_iff₀ htp]; linarith
        · simp only [Fin.reduceFinMk, Matrix.cons_val, abs_div, abs_of_pos ht2]
          rw [div_le_iff₀ ht2]; linarith)
  have s0 := hs 0; have s1 := hs 1; have s2 := hs 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, pow_one] at s0 s1 s2
  have hbe : |b| = t * (μ * e) := by rw [← hme]; field_simp
  have hpt : (pr.thi : ℝ) * (t / pr.thi) = t := by field_simp
  have key := goodP_of_cube V fr pr hg hthi hZ hR1 hR2 hR3 (ν := μ) (p := t / pr.thi) (α := if 0 ≤ b then e else -e)
    (s1 := s 0) (s2 := s 1) (s3 := s 2) h0 h1 (div_nonneg ht0 hthi.le) (by rw [div_le_one hthi]; exact ht1)
    (by split_ifs <;> simp [abs_of_nonneg he0, he1]) s0.2 s1.2 s2.2
    (by
      rcases hcase with rfl | ⟨k, hk⟩
      · left; split_ifs <;> simp
      · right
        fin_cases k
        · left; simpa using hk
        · right; left; simpa using hk
        · right; right; simpa using hk)
  rw [hpt] at key
  have eb : b = t * μ * (if 0 ≤ b then e else -e) := by
    split_ifs with hb0
    · rw [← abs_of_nonneg hb0, hbe]; ring
    · have h' : b = -(t * (μ * e)) := by rw [← hbe]; linarith [abs_of_neg (not_le.mp hb0)]
      rw [h']; ring
  have ex : x = μ * t * s 0 := by have := s0.1; field_simp at this; linarith
  have ey : y = μ * t * s 1 := by have := s1.1; field_simp at this; linarith
  have ez : z = μ * μ * (t * t) * s 2 := by have := s2.1; field_simp at this; linarith
  rw [ex, ey, ez, eb]
  exact key

/-! ### The U cap's boxes inside the wedge -/

/-- The wedge cube is good (the conclusion of `wp_good`). -/
def WpGood (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) : Prop :=
  ∀ {t b x y z : ℝ}, 0 ≤ t → t ≤ pr.thi → |b| ≤ pr.nu0 * t → |x| ≤ pr.nu0 * pr.R1 * t →
    |y| ≤ pr.nu0 * pr.R2 * t → |z| ≤ pr.nu0 ^ 2 * pr.R3 * t ^ 2 → Good V fr t b x y z

theorem pointGood_pu (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (side : ℕ) (k : UKind)
    (y : Fin 5 → ℝ) : PointGood V fr pr (.pu side k) y ↔ PointGood V fr pr (.u side k) y := Iff.rfl

/-- A pose of the U cap's side 0 with e > 0 inside the wedge is good. -/
theorem goodU_of_wp {V : Array (KCap.KVec K)} {fr : Frame K} {pr : Params} (hwp : WpGood V fr pr)
    {μ τ e s0 s1 s2 : ℝ} (hμ : 0 ≤ μ) (he : 0 ≤ e) (hte : μ * e ≤ pr.thi) (hτ : |τ| ≤ pr.nu0)
    (h1 : |s1| ≤ 2 * pr.nu0 * pr.R1 * e) (h0 : |s0| ≤ 2 * pr.nu0 * pr.R2 * e)
    (h2 : |s2| ≤ pr.nu0 ^ 2 * pr.R3 * e ^ 2) : GoodU V fr 0 μ τ e s0 s1 s2 := by
  show Good V fr (μ * e) (μ * e * τ) (-1 / 2 * (μ * s1)) (1 / 2 * (μ * s0)) (μ * μ * s2)
  have hμe : 0 ≤ μ * e := mul_nonneg hμ he
  refine hwp hμe hte ?_ ?_ ?_ ?_
  · rw [abs_mul, abs_of_nonneg hμe]; nlinarith [abs_nonneg τ]
  · rw [abs_mul, abs_mul, abs_of_nonneg hμ]
    have : |(-1 / 2 : ℝ)| = 1 / 2 := by rw [abs_div]; norm_num
    rw [this]; nlinarith [abs_nonneg s1]
  · rw [abs_mul, abs_mul, abs_of_nonneg hμ]
    have : |(1 / 2 : ℝ)| = 1 / 2 := by rw [abs_div]; norm_num
    rw [this]; nlinarith [abs_nonneg s0]
  · rw [abs_mul, abs_mul, abs_of_nonneg hμ]
    nlinarith [abs_nonneg s2, sq_nonneg μ]

theorem mxB_sound {box : Box} {y : Fin 5 → ℝ} (hy : KPoly.InBox box y) (i : Fin 5) :
    |y i| ≤ (mxB box i : ℝ) := by
  have h := hy i
  have h1 := h.1
  have h2 : y i ≤ (((box i).1 + (box i).2 : ℚ) : ℝ) := by push_cast; exact h.2
  have m1 : ((|(box i).1| : ℚ) : ℝ) ≤ (mxB box i : ℝ) := by exact_mod_cast le_max_left _ _
  have m2 : ((|(box i).1 + (box i).2| : ℚ) : ℝ) ≤ (mxB box i : ℝ) := by exact_mod_cast le_max_right _ _
  push_cast at m1 m2
  have a1 := le_abs_self (((box i).1 : ℚ) : ℝ)
  have a2 := neg_abs_le (((box i).1 : ℚ) : ℝ)
  have a3 := le_abs_self ((((box i).1 + (box i).2 : ℚ)) : ℝ)
  push_cast at a3 h2
  rw [abs_le]
  constructor <;> linarith

theorem uS_bound {pr : Params} (hrc : ∀ i, 0 ≤ (rc pr i : ℝ)) {box : Box} {y : Fin 5 → ℝ}
    (hy : KPoly.InBox box y) (k : UKind) (i : Fin 3) :
    |KPoly.eval 5 (uS (K := K) pr k i) y| ≤ (uSmax pr box k i : ℝ) := by
  cases k with
  | fe => fin_cases i <;> simp [uS, uSmax, eval_pvar] <;> exact mxB_sound hy _
  | face ax sg =>
    simp only [uS, uSmax, eval_faceCoord]
    split_ifs with hi
    · have : rng pr ax = rng pr i := by rw [← hi]
      rw [this]; push_cast; rw [abs_mul]
      have : |((signQ sg : ℚ) : ℝ)| = 1 := by cases sg <;> simp [signQ]
      rw [this, one_mul]
    · exact mxB_sound hy _
  | cone ax sg =>
    simp only [uS, uSmax, KPoly.eval_mul, eval_pconst, eval_pvar, eval_faceCoord]
    push_cast
    rw [abs_mul, abs_mul, abs_of_nonneg (hrc i)]
    refine mul_le_mul_of_nonneg_left (mul_le_mul (mxB_sound hy 2) ?_ (abs_nonneg _)
      (le_trans (abs_nonneg _) (mxB_sound hy 2))) (hrc i)
    split_ifs
    · rw [abs_mul]
      have : |((signQ sg : ℚ) : ℝ)| = 1 := by cases sg <;> simp [signQ]
      simp [this]
    · exact mxB_sound hy _

/-- **The prune**: a box of side 0 passing `wpTest` consists of good poses. -/
theorem pu_prune {V : Array (KCap.KVec K)} {fr : Frame K} {pr : Params} (hp : pr.Ok) (hwp : WpGood V fr pr)
    (hrc : ∀ i, 0 ≤ (rc pr i : ℝ)) {k : UKind} {box : Box} (h : wpTest pr box k = true) {y : Fin 5 → ℝ}
    (hy : KPoly.InBox box y) (hr : KPoly.InBox (rootBox pr (.pu 0 k)) y) : PointGood V fr pr (.pu 0 k) y := by
  obtain ⟨-, -, -, h4, h5, h6, h7, -, -⟩ := hp
  simp only [wpTest, decide_eq_true_eq] at h
  obtain ⟨hlo, hn, hs1, hs0, hs2, hmu⟩ := h
  have hlo' : (0 : ℝ) < uElo box k := by exact_mod_cast hlo
  have hn' : (mxB box 1 : ℝ) ≤ pr.nu0 := by exact_mod_cast hn
  have hs1' : (uSmax pr box k 1 : ℝ) ≤ 2 * pr.nu0 * pr.R1 * uElo box k := by exact_mod_cast hs1
  have hs0' : (uSmax pr box k 0 : ℝ) ≤ 2 * pr.nu0 * pr.R2 * uElo box k := by exact_mod_cast hs0
  have hs2' : (uSmax pr box k 2 : ℝ) ≤ pr.nu0 ^ 2 * pr.R3 * uElo box k ^ 2 := by exact_mod_cast hs2
  have hmu' : (((box 0).1 + (box 0).2 : ℚ) : ℝ) * (uEhi box k : ℝ) ≤ pr.thi := by exact_mod_cast hmu
  -- the values of e and μ
  have he : (uElo box k : ℝ) ≤ KPoly.eval 5 (uE (K := K) k) y ∧ KPoly.eval 5 (uE (K := K) k) y ≤ uEhi box k := by
    cases k with
    | face ax sg =>
      have := hy 2
      simp only [uE, uElo, uEhi, eval_pvar]
      push_cast at this ⊢
      exact this
    | fe => simp [uE, uElo, uEhi, eval_kOne]
    | cone ax sg => simp [uE, uElo, uEhi, eval_kOne]
  have hμ0 : 0 ≤ y 0 := by
    have := (hr 0).1
    cases k <;> simpa [rootBox] using this
  have hμ1 : y 0 ≤ (((box 0).1 + (box 0).2 : ℚ) : ℝ) := by push_cast; exact (hy 0).2
  have hel : (0 : ℝ) ≤ uElo box k := hlo'.le
  have hnu0 : (0 : ℝ) ≤ pr.nu0 := by exact_mod_cast h4
  have hR1 : (0 : ℝ) ≤ pr.R1 := by exact_mod_cast h5
  have hR2 : (0 : ℝ) ≤ pr.R2 := by exact_mod_cast h6
  have hR3 : (0 : ℝ) ≤ pr.R3 := by exact_mod_cast h7
  rw [pointGood_pu, pointGood_u]
  have e0 := uS_bound (K := K) (pr := pr) hrc hy k 0
  have e1 := uS_bound (K := K) (pr := pr) hrc hy k 1
  have e2 := uS_bound (K := K) (pr := pr) hrc hy k 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue] at e0 e1 e2
  refine goodU_of_wp hwp hμ0 (le_trans hel he.1) ?_ ?_ ?_ ?_ ?_
  · exact le_trans (mul_le_mul hμ1 he.2 (le_trans hel he.1) (le_trans hμ0 hμ1)) hmu'
  · exact le_trans (mxB_sound hy 1) hn'
  · refine le_trans e1 (le_trans hs1' ?_)
    exact mul_le_mul_of_nonneg_left he.1 (by positivity)
  · refine le_trans e0 (le_trans hs0' ?_)
    exact mul_le_mul_of_nonneg_left he.1 (by positivity)
  · refine le_trans e2 (le_trans hs2' ?_)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hel he.1 2) (by positivity)

theorem rc_nonneg {pr : Params} (hRc : 0 < (pr.Rc : ℝ)) (hSc : 0 < (pr.Sc : ℝ)) (i : ℕ) : 0 ≤ (rc pr i : ℝ) := by
  rcases i with _ | _ | i <;> simp [rc, hRc.le, hSc.le]

/-- The P cap's U charts of a side are closed. -/
theorem cert_goodPU {V : Array (KCap.KVec K)} {fr : Frame K} {pr : Params} {c : Cert} {req : List ChartId}
    (hp : pr.Ok) (hc : certCheckOn req V fr pr c = true) (hRc : 0 < (pr.Rc : ℝ)) (hSc : 0 < (pr.Sc : ℝ))
    (hwp : WpGood V fr pr) (side : ℕ) (hside : ∀ k ∈ uKinds, ChartId.pu side k ∈ req) :
    ∀ k ∈ uKinds, ∀ y, KPoly.InBox (rootBox pr (.pu side k)) y → PointGood V fr pr (.pu side k) y := by
  have hpr : ∀ (k : UKind) (box : Box), (pr.pwp && decide (side = 0) && wpTest pr box k) = true →
      ∀ y, KPoly.InBox box y → KPoly.InBox (rootBox pr (.pu side k)) y → PointGood V fr pr (.pu side k) y := by
    intro k box h y hy hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨-, rfl⟩, h⟩ := h
    exact pu_prune hp hwp (rc_nonneg hRc hSc) h hy hr
  have hcone : ∀ (a : ℕ) sg, a < 3 → ∀ y, KPoly.InBox (rootBox pr (.pu side (.cone a sg))) y →
      PointGood V fr pr (.pu side (.cone a sg)) y := by
    intro a sg ha
    obtain ⟨t, ht⟩ := cert_tree hc (hside _ (mem_uKinds_cone ⟨a, ha⟩ sg))
    refine chart_good V fr pr hp _ t ht ?_
    intro box h y hy hr
    simp only [coneOk, Bool.false_or] at h
    exact hpr _ box h y hy hr
  intro k hk
  cases k with
  | cone a sg =>
    have ha : a < 3 := by
      simp [uKinds] at hk
      omega
    exact hcone a sg ha
  | face a sg =>
    obtain ⟨t, ht⟩ := cert_tree hc (hside _ hk)
    refine chart_good V fr pr hp _ t ht ?_
    intro box h y hy hr
    simp only [coneOk, Bool.false_or] at h
    exact hpr _ box h y hy hr
  | fe =>
    obtain ⟨t, ht⟩ := cert_tree hc (hside _ hk)
    refine chart_good V fr pr hp _ t ht ?_
    intro box h y hy hr
    simp only [coneOk, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨⟨h2, h3⟩, h4⟩ | h
    · have b2 := withinB_sound h2 hy
      have b3 := withinB_sound h3 hy
      have b4 := withinB_sound h4 hy
      simp only [Rat.cast_zero, sub_zero] at b2 b3 b4
      exact fe_good_of_cone V fr pr side hRc hSc (fun a sg => hcone a sg a.isLt) y hr b2 b3 b4
    · exact hpr _ box (by simpa [Bool.and_eq_true] using h) y hy hr

theorem rootBox_pu (pr : Params) (side : ℕ) (k : UKind) : rootBox pr (.pu side k) = rootBox pr (.u side k) := by
  cases k <;> rfl

theorem mem_pCharts_p {k : PKind} (hk : k ∈ pKinds) : ChartId.p k ∈ pCharts := by
  simp only [pCharts, List.mem_append, List.mem_map]
  exact Or.inr ⟨k, hk, rfl⟩

theorem mem_pCharts_pu {side : ℕ} (hs : side < 4) {k : UKind} (hk : k ∈ uKinds) : ChartId.pu side k ∈ pCharts := by
  simp only [pCharts, List.mem_append, List.mem_flatMap, List.mem_map]
  refine Or.inl ⟨side, ?_, k, hk, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- The wedge's charts are closed. -/
theorem cert_goodP {V : Array (KCap.KVec K)} {fr : Frame K} {pr : Params} {c : Cert} (hp : pr.Ok)
    (hc : certCheckOn pCharts V fr pr c = true) :
    ∀ k ∈ pKinds, ∀ y, KPoly.InBox (rootBox pr (.p k)) y → PointGood V fr pr (.p k) y := by
  intro k hk
  obtain ⟨t, ht⟩ := cert_tree hc (mem_pCharts_p hk)
  exact chart_good V fr pr hp _ t ht (fun box h => by simp [coneOk] at h)

/-- **The P cap**: from a checked certificate, every pose with view X − a E₁ − b E₂, |a|, |b| ≤ μ₀, and
rotation (x, y, z) in the rotation basis, |x|, |y| ≤ R μ₀ / 2, |z| ≤ S μ₀², is good. -/
theorem pcap_good {V : Array (KCap.KVec K)} {fr : Frame K} {pr : Params} {c : Cert} (hp : pr.Ok)
    (hc : certCheckOn pCharts V fr pr c = true) (hRc : 0 < (pr.Rc : ℝ)) (hSc : 0 < (pr.Sc : ℝ))
    (hthi : 0 < (pr.thi : ℝ)) (hZ : 0 < (pr.Z : ℝ)) (hR1 : 0 < (pr.R1 : ℝ)) (hR2 : 0 < (pr.R2 : ℝ))
    (hR3 : 0 < (pr.R3 : ℝ)) (hR : 0 < (pr.R : ℝ)) (hS : 0 < (pr.S : ℝ))
    {a b x y z : ℝ} (ha : |a| ≤ pr.mu0) (hb : |b| ≤ pr.mu0)
    (hx : |x| ≤ pr.R * pr.mu0 / 2) (hy : |y| ≤ pr.R * pr.mu0 / 2) (hz : |z| ≤ pr.S * (pr.mu0 : ℝ) ^ 2) :
    Good V fr a b x y z := by
  have hn0 : (0 : ℝ) ≤ pr.nu0 := by exact_mod_cast hp.2.2.2.1
  have hwp : WpGood V fr pr := fun {t b x y z} h0 h1 h2 h3 h4 h5 =>
    wp_good V fr pr (cert_goodP hp hc) hthi hZ hR1 hR2 hR3 hn0 h0 h1 h2 h3 h4 h5
  refine square_good_of_cube ?_ hR hS ha hb hx hy hz
  intro side hs k hk y hy'
  rw [← rootBox_pu] at hy'
  exact cert_goodPU hp hc hRc hSc hwp side (fun k hk => mem_pCharts_pu hs hk) k hk y hy'

/-- A frame with an orthogonal view frame (squared lengths n₁, n₂, n_x) and an orthogonal rotation basis
(squared lengths m₁, m₂, m₃), with the weights k = 1. -/
structure FrameOkP (fr : Frame K) (n1 n2 nx m1 m2 m3 : ℝ) : Prop where
  h12 : rdot (kval fr.E1) (kval fr.E2) = 0
  h1x : rdot (kval fr.E1) (kval fr.X) = 0
  h2x : rdot (kval fr.E2) (kval fr.X) = 0
  e1 : rdot (kval fr.E1) (kval fr.E1) = n1
  e2 : rdot (kval fr.E2) (kval fr.E2) = n2
  ex : rdot (kval fr.X) (kval fr.X) = nx
  p1 : 0 < n1
  p2 : 0 < n2
  px : 0 < nx
  w12 : rdot (kval fr.W1) (kval fr.W2) = 0
  w1x : rdot (kval fr.W1) (kval fr.W3) = 0
  w2x : rdot (kval fr.W2) (kval fr.W3) = 0
  f1 : rdot (kval fr.W1) (kval fr.W1) = m1
  f2 : rdot (kval fr.W2) (kval fr.W2) = m2
  f3 : rdot (kval fr.W3) (kval fr.W3) = m3
  q1 : 0 < m1
  q2 : 0 < m2
  q3 : 0 < m3
  k1 : (fr.k1 : ℝ) = 1
  k2 : (fr.k2 : ℝ) = 1
  k3 : (fr.k3 : ℝ) = 1

/-- **The P cap, for dot products**: no pose with view in the square (|v·E₁| n_x ≤ μ₀ n₁ v·X, …) and a
rotation of Cayley norm at most r is Rupert, whatever the offset, if r² ≤ m₁ (R μ₀ / 2)², m₂ (R μ₀ / 2)²
and m₃ (S μ₀²)². -/
theorem pcapGen_not_rupert {V : Array (KCap.KVec K)} {fr : Frame K} {pr : Params} {c : Cert} {n1 n2 nx m1 m2 m3 r : ℝ}
    (hp : pr.Ok) (hc : certCheckOn pCharts V fr pr c = true) (hRc : 0 < (pr.Rc : ℝ)) (hSc : 0 < (pr.Sc : ℝ))
    (hthi : 0 < (pr.thi : ℝ)) (hZ : 0 < (pr.Z : ℝ)) (hR1 : 0 < (pr.R1 : ℝ)) (hR2 : 0 < (pr.R2 : ℝ))
    (hR3 : 0 < (pr.R3 : ℝ)) (hR : 0 < (pr.R : ℝ)) (hS : 0 < (pr.S : ℝ)) (hf : FrameOkP fr n1 n2 nx m1 m2 m3)
    (hr1 : r ^ 2 ≤ m1 * ((pr.R : ℝ) * pr.mu0 / 2) ^ 2) (hr2 : r ^ 2 ≤ m2 * ((pr.R : ℝ) * pr.mu0 / 2) ^ 2)
    (hr3 : r ^ 2 ≤ m3 * ((pr.S : ℝ) * (pr.mu0 : ℝ) ^ 2) ^ 2)
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
  have decw : ∀ v : Fin 3 → ℝ, v = (rdot v (kval fr.W1) / m1) • kval fr.W1 + (rdot v (kval fr.W2) / m2) • kval fr.W2 +
      (rdot v (kval fr.W3) / m3) • kval fr.W3 := by
    intro v
    have := decomp3 _ _ _ v hf.w12 hf.w1x hf.w2x (by rw [hf.f1]; exact hf.q1.ne') (by rw [hf.f2]; exact hf.q2.ne')
      (by rw [hf.f3]; exact hf.q3.ne')
    rwa [hf.f1, hf.f2, hf.f3] at this
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
  have hRm : 0 ≤ (pr.R : ℝ) * pr.mu0 / 2 := by have := mul_nonneg hR.le hmu; linarith
  have rb : ∀ (e : Fin 3 → ℝ) (m : ℝ), 0 < m → rdot e e = m → r ^ 2 ≤ m * ((pr.R : ℝ) * pr.mu0 / 2) ^ 2 →
      |rdot w e / m| ≤ pr.R * pr.mu0 / 2 := by
    intro e m hm0 he hrm
    rw [abs_div, abs_of_pos hm0, div_le_iff₀ hm0]
    have h := rdot_sq_le w e
    rw [he] at h
    apply abs_le_of_sq_le_sq _ (mul_nonneg hRm hm0.le)
    have h3 : rdot w w * m ≤ r ^ 2 * m := mul_le_mul_of_nonneg_right hw hm0.le
    have h4 := mul_le_mul_of_nonneg_right hrm hm0.le
    calc rdot w e ^ 2 ≤ r ^ 2 * m := by linarith
      _ ≤ (m * ((pr.R : ℝ) * pr.mu0 / 2) ^ 2) * m := h4
      _ = ((pr.R : ℝ) * pr.mu0 / 2 * m) ^ 2 := by ring
  have rbz : |rdot w (kval fr.W3) / m3| ≤ pr.S * (pr.mu0 : ℝ) ^ 2 := by
    rw [abs_div, abs_of_pos hf.q3, div_le_iff₀ hf.q3]
    have h := rdot_sq_le w (kval fr.W3)
    rw [hf.f3] at h
    apply abs_le_of_sq_le_sq _ (mul_nonneg (mul_nonneg hS.le (sq_nonneg _)) hf.q3.le)
    have h3 : rdot w w * m3 ≤ r ^ 2 * m3 := mul_le_mul_of_nonneg_right hw hf.q3.le
    have h4 := mul_le_mul_of_nonneg_right hr3 hf.q3.le
    calc rdot w (kval fr.W3) ^ 2 ≤ r ^ 2 * m3 := by linarith
      _ ≤ (m3 * ((pr.S : ℝ) * (pr.mu0 : ℝ) ^ 2) ^ 2) * m3 := h4
      _ = ((pr.S : ℝ) * (pr.mu0 : ℝ) ^ 2 * m3) ^ 2 := by ring
  have hG := pcap_good (V := V) (fr := fr) hp hc hRc hSc hthi hZ hR1 hR2 hR3 hR hS
    (a := -(e1 * nx) / (n1 * xx)) (b := -(e2 * nx) / (n2 * xx)) (x := rdot w (kval fr.W1) / m1)
    (y := rdot w (kval fr.W2) / m2) (z := rdot w (kval fr.W3) / m3)
    (by
      rw [abs_div, abs_neg, abs_mul, abs_of_pos hf.px, abs_of_pos (mul_pos hf.p1 hx0), div_le_iff₀ (mul_pos hf.p1 hx0)]
      linarith)
    (by
      rw [abs_div, abs_neg, abs_mul, abs_of_pos hf.px, abs_of_pos (mul_pos hf.p2 hx0), div_le_iff₀ (mul_pos hf.p2 hx0)]
      linarith)
    (rb _ _ hf.q1 hf.f1 hr1) (rb _ _ hf.q2 hf.f2 hr2) rbz
  refine hG p (xx / nx) ?_ ?_
  · conv_lhs => rw [dec p.view]
    funext i
    simp only [uR, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · have hw' : wR fr (rdot w (kval fr.W1) / m1) (rdot w (kval fr.W2) / m2) (rdot w (kval fr.W3) / m3) = w := by
      conv_rhs => rw [decw w]
      funext i
      simp only [wR, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hf.k1, hf.k2, hf.k3, one_mul]
      ring
    rw [hw']; exact hR'

end real

end ArcCap

end Noperts.Pipeline

end
