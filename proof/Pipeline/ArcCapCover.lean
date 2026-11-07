module

public import Pipeline.ArcCap

@[expose] public section

/-!
# The chart boxes of an arc cap cover its poses

A checked certificate closes every chart (`ArcCap.chart_good`). Here the charts
are put together.

* `goodW_of_cube`, `goodU_of_cube`: a pose of the wedge or the U cap given by a
  point of the boundary of the chart cube, at a radius ν ≤ ν₀, is a chart point.
* `w_good`, `uCone_good`, `uFe_good`, `uFace_good`, `cert_goodW`, `cert_goodU`:
  from `certCheck`, with the wedge piece of the identity cone (1, −) of side true
  left to `hprune`.
-/

namespace Noperts.Pipeline

namespace ArcCap

open Noperts.Pipeline.KCap
open Noperts.Pipeline.KCap.PVec

variable {K : Type} [ExactScalarOps K]

/-! ### Boxes -/

/-- x lies in the interval r = (lower end, width). -/
def Mem (r : ℚ × ℚ) (x : ℝ) : Prop := (r.1 : ℝ) ≤ x ∧ x ≤ (r.1 : ℝ) + (r.2 : ℝ)

theorem inBox_vec {b0 b1 b2 b3 b4 : ℚ × ℚ} {x0 x1 x2 x3 x4 : ℝ} (h0 : Mem b0 x0) (h1 : Mem b1 x1)
    (h2 : Mem b2 x2) (h3 : Mem b3 x3) (h4 : Mem b4 x4) :
    KPoly.InBox ![b0, b1, b2, b3, b4] ![x0, x1, x2, x3, x4] := by
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem mem_sym {r : ℚ} {x : ℝ} (h : |x| ≤ r) : Mem (sym r) x := by
  have := abs_le.mp h
  simp only [Mem, sym]; push_cast
  constructor <;> linarith [this.1, this.2]

theorem mem_zero {w : ℚ} {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ w) : Mem (0, w) x := by
  simpa [Mem] using And.intro h0 h1

theorem mem_one {x : ℝ} (h : |x| ≤ 1) : Mem (-1, 2) x := by
  have := abs_le.mp h
  simp only [Mem]; push_cast
  constructor <;> linarith [this.1, this.2]

/-! ### Real charts -/

section real

variable [ExactScalarVal K]

/-- The value of `pT`. -/
noncomputable def tR (pr : Params) (π : Piece) (ν p al : ℝ) : ℝ :=
  match π with
  | .w0 => ((pr.tstar : ℝ) * (1 - pr.zh * ν)) * p
  | .wm => (pr.tstar : ℝ) * (1 - pr.bmid * (ν * al) + ν * p)
  | .w1 => (pr.tstar : ℝ) * (1 + pr.zh * ν) + ((pr.tsplit : ℝ) - (pr.tstar : ℝ) * (1 + pr.zh * ν)) * p
  | .w2 => (pr.tsplit : ℝ) + ((pr.tend - pr.tsplit : ℚ) : ℝ) * p

noncomputable def bR (pr : Params) (π : Piece) (ν t al : ℝ) : ℝ :=
  match π with
  | .wm => (pr.bmid : ℝ) * (ν * al)
  | _ => t * (ν * al)

noncomputable def fR (pr : Params) (π : Piece) (t : ℝ) : ℝ :=
  match π with
  | .w0 | .wm => (pr.f0c : ℝ) + pr.f0d * t
  | .w1 | .w2 => (pr.f1c : ℝ) + pr.f1d * t

theorem eval_pT (pr : Params) (π : Piece) (al : KPoly K 5) (y : Fin 5 → ℝ) :
    KPoly.eval 5 (pT pr π al) y = tR pr π (y 0) (y 1) (KPoly.eval 5 al y) := by
  cases π <;> simp [pT, tR, KPoly.eval_mul, KPoly.eval_add, KPoly.eval_sub, eval_pconst, eval_pvar, eval_kOne]

theorem eval_pB (pr : Params) (π : Piece) (t al : KPoly K 5) (y : Fin 5 → ℝ) :
    KPoly.eval 5 (pB pr π t al) y = bR pr π (y 0) (KPoly.eval 5 t y) (KPoly.eval 5 al y) := by
  cases π <;> simp [pB, bR, KPoly.eval_mul, eval_pconst, eval_pvar]

theorem eval_pF (pr : Params) (π : Piece) (t : KPoly K 5) (y : Fin 5 → ℝ) :
    KPoly.eval 5 (pF pr π t) y = fR pr π (KPoly.eval 5 t y) := by
  cases π <;> simp [pF, fR, KPoly.eval_mul, KPoly.eval_add, eval_pconst]

/-- A wedge pose is good. -/
def GoodW (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (π : Piece) (ν p al s1 s2 s3 : ℝ) : Prop :=
  let t := tR pr π ν p al
  Good V fr t (bR pr π ν t al) (1 / 2 * (ν * t * s1)) (1 / 2 * (ν * t * s1 * fR pr π t + ν * ν * (t * s2)))
    (1 / 2 * (ν * t * s1 * t) + ν * ν * (t * t) * s3)

/-- A pose of the U cap is good. -/
def GoodU (V : Array (KCap.KVec K)) (fr : Frame K) (side : ℕ) (μ τ e s0 s1 s2 : ℝ) : Prop :=
  Good V fr (if side = 0 then μ * e else if side = 1 then -1 * (μ * e) else μ * e * τ)
    (if side = 0 ∨ side = 1 then μ * e * τ else if side = 2 then μ * e else -1 * (μ * e))
    (-1 / 2 * (μ * s1)) (1 / 2 * (μ * s0)) (μ * μ * s2)

theorem pointGood_w (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (π : Piece) (k : WKind) (y : Fin 5 → ℝ) :
    PointGood V fr pr (.w π k) y ↔ GoodW V fr pr π (y 0) (y 1) (KPoly.eval 5 (wAl (K := K) k) y)
      (KPoly.eval 5 (wS1 (K := K) pr k) y) (KPoly.eval 5 (wS2 (K := K) pr k) y)
      (KPoly.eval 5 (wS3 (K := K) pr k) y) := by
  simp only [PointGood, coords, wCoords, GoodW, KPoly.eval_mul, KPoly.eval_add, eval_pconst, eval_pvar,
    eval_pT, eval_pB, eval_pF]
  norm_num

theorem pointGood_u (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (side : ℕ) (k : UKind) (y : Fin 5 → ℝ) :
    PointGood V fr pr (.u side k) y ↔ GoodU V fr side (y 0) (y 1) (KPoly.eval 5 (uE (K := K) k) y)
      (KPoly.eval 5 (uS (K := K) pr k 0) y) (KPoly.eval 5 (uS (K := K) pr k 1) y)
      (KPoly.eval 5 (uS (K := K) pr k 2) y) := by
  by_cases h0 : side = 0
  · subst h0
    simp [PointGood, coords, uCoords, GoodU, KPoly.eval_mul, eval_pconst, eval_pvar]
  by_cases h1 : side = 1
  · subst h1
    simp [PointGood, coords, uCoords, GoodU, KPoly.eval_mul, eval_pconst, eval_pvar]
  by_cases h2 : side = 2
  · subst h2
    simp [PointGood, coords, uCoords, GoodU, KPoly.eval_mul, eval_pconst, eval_pvar]
  simp [PointGood, coords, uCoords, GoodU, KPoly.eval_mul, eval_pconst, eval_pvar, h0, h1, h2]

/-- A face coordinate evaluates back to the vector it came from. -/
theorem eval_faceCoord_of (a : Fin 3) (sg : Bool) (c : ℚ) (v : Fin 3 → ℝ)
    (hv : v a = ((signQ sg * c : ℚ) : ℝ)) (i : Fin 3) (y0 y1 y2 : ℝ) :
    KPoly.eval 5 (faceCoord (K := K) 3 a sg c i)
      ![y0, y1, y2, (other3 a v).1, (other3 a v).2] = v i := by
  rw [eval_faceCoord]
  fin_cases a <;> fin_cases i <;> simp [freeVar, other3] at hv ⊢ <;> first | exact hv.symm | skip

theorem mem_wKinds_fe (al pos : Bool) : WKind.fe al pos ∈ wKinds := by
  cases al <;> cases pos <;> simp [wKinds]

theorem mem_wKinds_cone (al : Bool) (a : Fin 3) (sg : Bool) : WKind.cone al a sg ∈ wKinds := by
  fin_cases a <;> cases al <;> cases sg <;> simp [wKinds]

theorem mem_wKinds_face0 (sg : Bool) : WKind.face0 sg ∈ wKinds := by
  cases sg <;> simp [wKinds]

theorem mem_wKinds_face1 (x : S1) (sg : Bool) : WKind.face1 x sg ∈ wKinds := by
  cases x <;> cases sg <;> simp [wKinds]

theorem mem_wKinds_face2 (x : S1) (sg : Bool) : WKind.face2 x sg ∈ wKinds := by
  cases x <;> cases sg <;> simp [wKinds]

theorem mem_uKinds_fe : UKind.fe ∈ uKinds := by simp [uKinds]

theorem mem_uKinds_face (a : Fin 3) (sg : Bool) : UKind.face a sg ∈ uKinds := by
  fin_cases a <;> cases sg <;> simp [uKinds]

theorem mem_uKinds_cone (a : Fin 3) (sg : Bool) : UKind.cone a sg ∈ uKinds := by
  fin_cases a <;> cases sg <;> simp [uKinds]

/-- A sign of a real of absolute value c. -/
theorem exists_sign {x c : ℝ} (h : |x| = c) : ∃ sg : Bool, x = ((signQ sg : ℚ) : ℝ) * c := by
  rcases abs_cases x with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact ⟨true, by simp [signQ]; linarith⟩
  · exact ⟨false, by simp [signQ]; linarith⟩

/-- The wedge's s₁ by mode: a value of s₁ with |s₁| ≤ R₁ is one of the three modes. -/
theorem exists_s1 (pr : Params) (hZ : 0 ≤ (pr.Z : ℝ)) {ν s1 : ℝ} (hν : 0 < ν) (h1 : |s1| ≤ pr.R1) :
    ∃ (x : S1) (q : ℝ), Mem (s1Box pr x) q ∧
      KPoly.eval 5 (s1Of (K := K) pr x 3) ![ν, 0, 0, q, 0] = s1 := by
  have hb := abs_le.mp h1
  by_cases hp : pr.Z * ν < s1
  · refine ⟨.p, s1 - pr.Z * ν, mem_zero (by linarith) ?_, ?_⟩
    · nlinarith [mul_nonneg hZ hν.le]
    · simp [s1Of, KPoly.eval_mul, KPoly.eval_add, eval_pconst, eval_pvar]
  by_cases hm : s1 < -(pr.Z * ν)
  · refine ⟨.m, -s1 - pr.Z * ν, mem_zero (by linarith) ?_, ?_⟩
    · nlinarith [mul_nonneg hZ hν.le]
    · simp [s1Of, KPoly.eval_mul, KPoly.eval_add, eval_pconst, eval_pvar]
  · refine ⟨.i, s1 / ν, mem_sym ?_, ?_⟩
    · rw [abs_div, abs_of_pos hν, div_le_iff₀ hν]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · simp [s1Of, KPoly.eval_mul, eval_pvar]; field_simp

/-- `s1Of` depends on the variables 0 and 3 only. -/
theorem eval_s1Of_congr (pr : Params) (x : S1) (y y' : Fin 5 → ℝ) (h0 : y 0 = y' 0) (h3 : y 3 = y' 3) :
    KPoly.eval 5 (s1Of (K := K) pr x 3) y = KPoly.eval 5 (s1Of (K := K) pr x 3) y' := by
  cases x <;> simp [s1Of, KPoly.eval_mul, KPoly.eval_add, eval_pconst, eval_pvar, h0, h3]

/-- At ν = 0 the wedge's pose depends on p only. -/
theorem goodW_zero (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (π : Piece) (p al s1 s2 s3 : ℝ)
    (h : GoodW V fr pr π 0 p 1 0 0 0) : GoodW V fr pr π 0 p al s1 s2 s3 := by
  have ht : tR pr π 0 p al = tR pr π 0 p 1 := by cases π <;> simp [tR]
  have hb : ∀ t, bR pr π 0 t al = bR pr π 0 t 1 := by intro t; cases π <;> simp [bR]
  simp only [GoodW, ht, hb] at h ⊢
  simpa using h

/-- **The wedge's cube**: with every chart of the piece closed, a pose given by a point of the
boundary of the cube, at a radius ν ≤ ν₀, is good. -/
theorem goodW_of_cube (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (π : Piece)
    (hg : ∀ k ∈ wKinds, ∀ y, KPoly.InBox (rootBox pr (.w π k)) y → PointGood V fr pr (.w π k) y)
    (hZ : 0 < (pr.Z : ℝ)) (hR2 : 0 < (pr.R2 : ℝ)) (hR3 : 0 < (pr.R3 : ℝ))
    {ν p al s1 s2 s3 : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ pr.nu0) (hp : Mem (p1Box pr π) p)
    (hal : |al| ≤ 1) (h1 : |s1| ≤ pr.R1) (h2 : |s2| ≤ pr.R2) (h3 : |s3| ≤ pr.R3)
    (hf : |al| = 1 ∨ |s1| = pr.R1 ∨ |s2| = pr.R2 ∨ |s3| = pr.R3) :
    GoodW V fr pr π ν p al s1 s2 s3 := by
  have hν : Mem (0, pr.nu0) ν := mem_zero hν0 hν1
  -- The cone point with (r, s₂, s₃) in the cube.
  have hcone : ∀ (A : Bool) (r s2 s3 : ℝ), |r| ≤ pr.Z → |s2| ≤ pr.R2 → |s3| ≤ pr.R3 →
      GoodW V fr pr π ν p ((signQ A : ℚ) : ℝ) (ν * r) s2 s3 := by
    intro A r s2 s3 hr h2 h3
    obtain ⟨tt, htt0, hle, ⟨i0, hi0⟩, a, sgn, σ, hσa, hσ1, hv⟩ :=
      maxface (n := 3) (by norm_num) ![r / pr.Z, s2 / pr.R2, s3 / pr.R3]
    have htt1 : tt ≤ 1 := by
      rw [← hi0]
      fin_cases i0 <;> simp [abs_div, abs_of_pos hZ, abs_of_pos hR2, abs_of_pos hR3, div_le_one, hZ, hR2, hR3, hr, h2, h3]
    have hb := other3_bound a σ hσ1
    set y : Fin 5 → ℝ := ![ν, p, tt, (other3 a σ).1, (other3 a σ).2] with hy
    have hin : KPoly.InBox (rootBox pr (.w π (.cone A a sgn))) y :=
      inBox_vec hν hp (mem_zero htt0 (by simpa using htt1)) (mem_one hb.1) (mem_one hb.2)
    have hG := (pointGood_w V fr pr π (.cone A a sgn) y).mp (hg _ (mem_wKinds_cone A a sgn) y hin)
    have hσ' : σ a = ((signQ sgn * 1 : ℚ) : ℝ) := by simpa using hσa
    have e : ∀ i : Fin 3, KPoly.eval 5 (wCone (K := K) pr a sgn i) y = (wrc pr i : ℝ) * (tt * σ i) := by
      intro i
      simp only [wCone, KPoly.eval_mul, eval_pconst, eval_pvar]
      rw [hy, eval_faceCoord_of a sgn 1 σ hσ' i]
      simp
    have v0 := hv 0; have v1 := hv 1; have v2 := hv 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at v0 v1 v2
    have e0 : (wrc pr ((0 : Fin 3) : ℕ) : ℝ) * (tt * σ 0) = r := by
      show (pr.Z : ℝ) * (tt * σ 0) = r
      rw [← v0]; field_simp
    have e1 : (wrc pr ((1 : Fin 3) : ℕ) : ℝ) * (tt * σ 1) = s2 := by
      show (pr.R2 : ℝ) * (tt * σ 1) = s2
      rw [← v1]; field_simp
    have e2 : (wrc pr ((2 : Fin 3) : ℕ) : ℝ) * (tt * σ 2) = s3 := by
      show (pr.R3 : ℝ) * (tt * σ 2) = s3
      rw [← v2]; field_simp
    have y0 : y 0 = ν := rfl
    have y1 : y 1 = p := rfl
    simp only [wAl, wS1, wS2, wS3, KPoly.eval_mul, eval_pvar, eval_pconst, y0, y1] at hG
    have E0 := e 0; have E1 := e 1; have E2 := e 2
    rw [e0] at E0; rw [e1] at E1; rw [e2] at E2
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at E0 E1 E2
    rw [E0, E1, E2] at hG
    exact hG
  rcases hν0.lt_or_eq with hpos | hzero
  swap
  · -- ν = 0.
    subst hzero
    apply goodW_zero
    have := hcone true 0 0 0 (by simpa using hZ.le) (by simpa using hR2.le) (by simpa using hR3.le)
    simpa [signQ] using this
  have hal' := mem_one hal
  have hq2 := mem_sym h2
  have hq3 := mem_sym h3
  rcases hf with hf | hf | hf | hf
  · obtain ⟨A, hA⟩ := exists_sign hf
    rw [mul_one] at hA
    by_cases hp1 : pr.Z * ν < s1
    · set y : Fin 5 → ℝ := ![ν, p, s1 - pr.Z * ν, s2, s3] with hy
      have hin : KPoly.InBox (rootBox pr (.w π (.fe A true))) y :=
        inBox_vec hν hp (mem_zero (by linarith) (by nlinarith [(abs_le.mp h1).2, mul_pos hZ hpos])) hq2 hq3
      have hG := (pointGood_w V fr pr π (.fe A true) y).mp (hg _ (mem_wKinds_fe A true) y hin)
      simpa [y, wAl, wS1, wS2, wS3, s1Of, KPoly.eval_mul, KPoly.eval_add, eval_pconst, eval_pvar, ← hA] using hG
    by_cases hm : s1 < -(pr.Z * ν)
    · set y : Fin 5 → ℝ := ![ν, p, -s1 - pr.Z * ν, s2, s3] with hy
      have hin : KPoly.InBox (rootBox pr (.w π (.fe A false))) y :=
        inBox_vec hν hp (mem_zero (by linarith) (by nlinarith [(abs_le.mp h1).1, mul_pos hZ hpos])) hq2 hq3
      have hG := (pointGood_w V fr pr π (.fe A false) y).mp (hg _ (mem_wKinds_fe A false) y hin)
      simpa [y, wAl, wS1, wS2, wS3, s1Of, KPoly.eval_mul, KPoly.eval_add, eval_pconst, eval_pvar, ← hA] using hG
    · have hr : |s1 / ν| ≤ pr.Z := by
        rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      have := hcone A (s1 / ν) s2 s3 hr h2 h3
      rw [mul_div_cancel₀ _ hpos.ne', ← hA] at this
      exact this
  · obtain ⟨sg, hs⟩ := exists_sign hf
    set y : Fin 5 → ℝ := ![ν, p, al, s2, s3] with hy
    have hin : KPoly.InBox (rootBox pr (.w π (.face0 sg))) y := inBox_vec hν hp hal' hq2 hq3
    have hG := (pointGood_w V fr pr π (.face0 sg) y).mp (hg _ (mem_wKinds_face0 sg) y hin)
    simpa [y, wAl, wS1, wS2, wS3, eval_pconst, eval_pvar, ← hs] using hG
  · obtain ⟨sg, hs⟩ := exists_sign hf
    obtain ⟨x, q, hq, he⟩ := exists_s1 (K := K) pr hZ.le hpos h1
    set y : Fin 5 → ℝ := ![ν, p, al, q, s3] with hy
    have hin : KPoly.InBox (rootBox pr (.w π (.face1 x sg))) y := inBox_vec hν hp hal' hq hq3
    have hG := (pointGood_w V fr pr π (.face1 x sg) y).mp (hg _ (mem_wKinds_face1 x sg) y hin)
    have e1 : KPoly.eval 5 (s1Of (K := K) pr x 3) y = s1 := by
      rw [← he]; exact eval_s1Of_congr pr x _ _ rfl rfl
    simp only [wAl, wS1, wS2, wS3, e1] at hG
    simpa [y, eval_pconst, eval_pvar, ← hs] using hG
  · obtain ⟨sg, hs⟩ := exists_sign hf
    obtain ⟨x, q, hq, he⟩ := exists_s1 (K := K) pr hZ.le hpos h1
    set y : Fin 5 → ℝ := ![ν, p, al, q, s2] with hy
    have hin : KPoly.InBox (rootBox pr (.w π (.face2 x sg))) y := inBox_vec hν hp hal' hq hq2
    have hG := (pointGood_w V fr pr π (.face2 x sg) y).mp (hg _ (mem_wKinds_face2 x sg) y hin)
    have e1 : KPoly.eval 5 (s1Of (K := K) pr x 3) y = s1 := by
      rw [← he]; exact eval_s1Of_congr pr x _ _ rfl rfl
    simp only [wAl, wS1, wS2, wS3, e1] at hG
    simpa [y, eval_pconst, eval_pvar, ← hs] using hG

/-- **The U cube**: with every chart of the side closed, a pose of the cube is good. -/
theorem goodU_of_cube (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (side : ℕ)
    (hg : ∀ k ∈ uKinds, ∀ y, KPoly.InBox (rootBox pr (.u side k)) y → PointGood V fr pr (.u side k) y)
    {μ τ e : ℝ} {s : Fin 3 → ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ pr.mu0) (hτ : |τ| ≤ 1)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hs : ∀ i : Fin 3, |s i| ≤ rng pr i)
    (hf : e = 1 ∨ ∃ k : Fin 3, |s k| = rng pr k) :
    GoodU V fr side μ τ e (s 0) (s 1) (s 2) := by
  have hμ : Mem (0, pr.mu0) μ := mem_zero hμ0 hμ1
  rcases hf with rfl | ⟨a, ha⟩
  · set y : Fin 5 → ℝ := ![μ, τ, s 0, s 1, s 2] with hy
    have hin : KPoly.InBox (rootBox pr (.u side .fe)) y :=
      inBox_vec hμ (mem_one hτ) (mem_sym (hs 0)) (mem_sym (hs 1)) (mem_sym (hs 2))
    have hG := (pointGood_u V fr pr side .fe y).mp (hg _ mem_uKinds_fe y hin)
    simpa [y, uE, uS, eval_kOne, eval_pvar] using hG
  · obtain ⟨sg, hsg⟩ := exists_sign ha
    have hsg' : s a = ((signQ sg * rng pr a : ℚ) : ℝ) := by push_cast; exact hsg
    set y : Fin 5 → ℝ := ![μ, τ, e, (other3 a s).1, (other3 a s).2] with hy
    have m : ∀ i : Fin 3, Mem (sym (rng pr i)) (s i) := fun i => mem_sym (hs i)
    have hfree : Mem (sym (faceFree pr a).1) (other3 a s).1 ∧ Mem (sym (faceFree pr a).2) (other3 a s).2 := by
      fin_cases a
      · exact ⟨m 1, m 2⟩
      · exact ⟨m 0, m 2⟩
      · exact ⟨m 0, m 1⟩
    have hin : KPoly.InBox (rootBox pr (.u side (.face a sg))) y :=
      inBox_vec hμ (mem_one hτ) (mem_zero he0 (by simpa using he1)) hfree.1 hfree.2
    have hG := (pointGood_u V fr pr side (.face a sg) y).mp (hg _ (mem_uKinds_face a sg) y hin)
    have e' : ∀ i : Fin 3, KPoly.eval 5 (uS (K := K) pr (.face a sg) i) y = s i := fun i =>
      eval_faceCoord_of a sg _ s hsg' i _ _ _
    have e0 := e' 0; have e1 := e' 1; have e2 := e' 2
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at e0 e1 e2
    rw [e0, e1, e2] at hG
    simpa [y, uE, eval_pvar] using hG

/-! ### From the certificate -/

theorem cert_tree {V : Array (KCap.KVec K)} {fr : Frame K} {pr : Params} {c : Cert} {req : List ChartId}
    (hc : certCheckOn req V fr pr c = true) {id : ChartId} (hid : id ∈ req) :
    ∃ t, chartCheck V fr pr id t = true := by
  have := List.all_eq_true.mp hc id hid
  obtain ⟨e, -, he⟩ := List.any_eq_true.mp this
  simp only [Bool.and_eq_true, decide_eq_true_eq] at he
  obtain ⟨rfl, h⟩ := he
  exact ⟨e.2, h⟩

theorem mem_required_w (π : Piece) {k : WKind} (hk : k ∈ wKinds) : ChartId.w π k ∈ requiredCharts := by
  simp only [requiredCharts, List.mem_append]
  right
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨π, by cases π <;> simp, k, hk, rfl⟩

theorem mem_uCharts {sides : List ℕ} {side : ℕ} (hs : side ∈ sides) {k : UKind} (hk : k ∈ uKinds) :
    ChartId.u side k ∈ uCharts sides := by
  simp only [uCharts, List.mem_flatMap, List.mem_map]
  exact ⟨side, hs, k, hk, rfl⟩

theorem mem_required_u {side : ℕ} (hs : side = 0 ∨ side = 3) {k : UKind} (hk : k ∈ uKinds) :
    ChartId.u side k ∈ requiredCharts := by
  simp only [requiredCharts, List.mem_append]
  left
  exact mem_uCharts (by rcases hs with rfl | rfl <;> simp) hk

/-- The wedge's charts are closed. -/
theorem cert_goodW {V : Array (KCap.KVec K)} {fr : Frame K} {pr : Params} {c : Cert} (hp : pr.Ok)
    (hc : certCheck V fr pr c = true) (π : Piece) :
    ∀ k ∈ wKinds, ∀ y, KPoly.InBox (rootBox pr (.w π k)) y → PointGood V fr pr (.w π k) y := by
  intro k hk
  obtain ⟨t, ht⟩ := cert_tree hc (mem_required_w π hk)
  exact chart_good V fr pr hp _ t ht (fun box h => by simp [coneOk] at h)

/-- An F_e point inside the identity cone is a point of a cone chart. -/
theorem fe_good_of_cone (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (side : ℕ)
    (hRc : 0 < (pr.Rc : ℝ)) (hSc : 0 < (pr.Sc : ℝ))
    (hcone : ∀ (a : Fin 3) sg y, KPoly.InBox (rootBox pr (.u side (.cone a sg))) y →
      PointGood V fr pr (.u side (.cone a sg)) y)
    (y : Fin 5 → ℝ) (hyr : KPoly.InBox (rootBox pr (.u side .fe)) y)
    (h2 : |y 2| ≤ pr.Rc) (h3 : |y 3| ≤ pr.Rc) (h4 : |y 4| ≤ pr.Sc) :
    PointGood V fr pr (.u side .fe) y := by
  obtain ⟨tt, htt0, hle, ⟨i0, hi0⟩, a, sgn, σ, hσa, hσ1, hv⟩ :=
    maxface (n := 3) (by norm_num) ![y 2 / pr.Rc, y 3 / pr.Rc, y 4 / pr.Sc]
  have htt1 : tt ≤ 1 := by
    rw [← hi0]
    fin_cases i0 <;> simp [abs_div, abs_of_pos hRc, abs_of_pos hSc, div_le_one, hRc, hSc, h2, h3, h4]
  have hb := other3_bound a σ hσ1
  set y' : Fin 5 → ℝ := ![y 0, y 1, tt, (other3 a σ).1, (other3 a σ).2] with hy'
  have hin : KPoly.InBox (rootBox pr (.u side (.cone a sgn))) y' :=
    inBox_vec (hyr 0) (hyr 1) (mem_zero htt0 (by simpa using htt1)) (mem_one hb.1) (mem_one hb.2)
  have hG := (pointGood_u V fr pr side (.cone a sgn) y').mp (hcone a sgn y' hin)
  have hσ' : σ a = ((signQ sgn * 1 : ℚ) : ℝ) := by simpa using hσa
  have e : ∀ i : Fin 3, KPoly.eval 5 (uS (K := K) pr (.cone a sgn) i) y' = (rc pr i : ℝ) * (tt * σ i) := by
    intro i
    simp only [uS, KPoly.eval_mul, eval_pconst, eval_pvar]
    rw [hy', eval_faceCoord_of a sgn 1 σ hσ' i]
    simp
  have v0 := hv 0; have v1 := hv 1; have v2 := hv 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at v0 v1 v2
  have E0 := e 0; have E1 := e 1; have E2 := e 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at E0 E1 E2
  have r0 : (rc pr 0 : ℝ) * (tt * σ 0) = y 2 := by
    show (pr.Rc : ℝ) * (tt * σ 0) = y 2
    rw [← v0]; field_simp
  have r1 : (rc pr 1 : ℝ) * (tt * σ 1) = y 3 := by
    show (pr.Rc : ℝ) * (tt * σ 1) = y 3
    rw [← v1]; field_simp
  have r2 : (rc pr 2 : ℝ) * (tt * σ 2) = y 4 := by
    show (pr.Sc : ℝ) * (tt * σ 2) = y 4
    rw [← v2]; field_simp
  rw [E0, E1, E2, r0, r1, r2] at hG
  rw [pointGood_u]
  simpa [y', uE, uS, eval_kOne, eval_pvar] using hG

/-- The U charts are closed, the part of the cone (1, −) of side true in the wedge left to `hprune`. -/
theorem cert_goodU {V : Array (KCap.KVec K)} {fr : Frame K} {pr : Params} {c : Cert} {req : List ChartId}
    (hp : pr.Ok) (hc : certCheckOn req V fr pr c = true) (hRc : 0 < (pr.Rc : ℝ)) (hSc : 0 < (pr.Sc : ℝ))
    (hprune : pr.wedge = true → ∀ box, wedgeBoxOk pr box = true → ∀ y, KPoly.InBox box y →
      KPoly.InBox (rootBox pr (.u 0 (.cone 1 false))) y →
      PointGood V fr pr (.u 0 (.cone 1 false)) y)
    (side : ℕ) (hside : ∀ k ∈ uKinds, ChartId.u side k ∈ req) :
    ∀ k ∈ uKinds, ∀ y, KPoly.InBox (rootBox pr (.u side k)) y → PointGood V fr pr (.u side k) y := by
  have hcone : ∀ (a : ℕ) sg, a < 3 → ∀ y, KPoly.InBox (rootBox pr (.u side (.cone a sg))) y →
      PointGood V fr pr (.u side (.cone a sg)) y := by
    intro a sg ha
    obtain ⟨t, ht⟩ := cert_tree hc (hside _ (mem_uKinds_cone ⟨a, ha⟩ sg))
    refine chart_good V fr pr hp _ t ht ?_
    intro box h y hy hr
    by_cases hs : side = 0 ∧ a = 1 ∧ sg = false
    · obtain ⟨rfl, rfl, rfl⟩ := hs
      simp only [coneOk, Bool.and_eq_true] at h
      exact hprune h.1 box h.2 y hy hr
    · exfalso
      revert h
      rcases side with _ | side
      · rcases sg <;> obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by omega
        all_goals first | exact absurd ⟨rfl, rfl, rfl⟩ hs | simp [coneOk]
      · rcases sg <;> obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by omega
        all_goals simp [coneOk]
  intro k hk
  cases k with
  | cone a sg =>
    have ha : a < 3 := by
      simp [uKinds] at hk
      omega
    exact hcone a sg ha
  | face a sg =>
    obtain ⟨t, ht⟩ := cert_tree hc (hside _ hk)
    exact chart_good V fr pr hp _ t ht (fun box h => by simp [coneOk] at h)
  | fe =>
    obtain ⟨t, ht⟩ := cert_tree hc (hside _ hk)
    refine chart_good V fr pr hp _ t ht ?_
    intro box h y hy hr
    simp only [coneOk, Bool.and_eq_true] at h
    obtain ⟨⟨h2, h3⟩, h4⟩ := h
    have b2 := withinB_sound h2 hy
    have b3 := withinB_sound h3 hy
    have b4 := withinB_sound h4 hy
    simp only [Rat.cast_zero, sub_zero] at b2 b3 b4
    exact fe_good_of_cone V fr pr side hRc hSc (fun a sg => hcone a sg a.isLt) y hr b2 b3 b4

end real

end ArcCap

end Noperts.Pipeline

end
