module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Type 09, acute case (c): the pure-algebra layer of `FEWER-FACES-PROOFS.md` §27, continued (4)

No geometry: real-number implications only.  The normal form of §27, continued (2) §0 is
`v = 0`, `xa = e₁`, `xb = e₂`, `m1± = (t±, 0, ±h±)`, `m2± = (0, s±, ±k±)`, with the slopes
`a± = h±/t±`, `b± = h±/(1 - t±)`, `c± = k±/s±`, `d± = k±/(1 - s±)`,
`A1 = a+ + a-`, `A2 = c+ + c-`, `B1 = b+ + b-`.  Type 09 has the roof `b+ < d+` and
`k- = (1 - s-) h- / (1 - t-)` (that is `b- = d-`).

* `Shape09`: the parameters with their standing hypotheses (positivity, `t±, s± < 1`, roof).
* `Shape09.T5F1` (27.17), `Shape09.AM` (27.29 row `A^M`), `Shape09.Q3456` (27.57): the closed forms
  of the three failing hypotheses of "27.34 fails".
* `Shape09.q3456_of_lt` (27.57), `Shape09.thm_27_58` (27.58): the five conditions of 27.48.
* Part 2 (27.48): the rim steps and the two failure inequalities `t48_T1_fail`, `t48_T2_fail`
  and their contradiction `t48_contra`.
-/

namespace Minimality.CaseC09

/-! ### Real-variable lemmas for the comparisons of 27.57 -/

lemma x_lt_y {X Y P Q : ℝ} (hY : 0 < Y) (hP : 0 < P) (hXY : X < Y) (hPQ : P < Q) :
    X * P < Y * Q := by
  rcases le_or_gt X 0 with h | h
  · nlinarith [mul_pos hY (hP.trans hPQ)]
  · nlinarith [mul_pos h (sub_pos.2 hPQ), mul_pos (sub_pos.2 hXY) hP]

lemma tmsm_lt {tm sm sp : ℝ} (htm : 0 < tm) (hsp1 : sp < 1) (hsm1 : sm < 1) (hts : tm < sm) :
    tm * (sm - sp) < sm * (1 - sp) := by
  have hsm : 0 < sm := htm.trans hts
  rcases le_or_gt sm sp with h | h
  · nlinarith [mul_pos hsm (sub_pos.2 hsp1), mul_nonneg htm.le (sub_nonneg.2 h)]
  · nlinarith [mul_pos (sub_pos.2 h) (sub_pos.2 hts), mul_pos (sub_pos.2 h) (sub_pos.2 hsm1)]

lemma cmp_12 {tp tm bp bm am : ℝ} (htp1 : tp < 1) (htm : 0 < tm) (hbpa : bp < am)
    (R : bm * (1 - tm) = am * tm) : tm * ((1 - tp) * (bp + bm)) < (1 - tp) * bm := by
  have h1 : tm * (bp + bm) < bm := by nlinarith [mul_lt_mul_of_pos_left hbpa htm]
  nlinarith [mul_lt_mul_of_pos_left h1 (sub_pos.2 htp1)]

lemma cmp_21 {tp tm bp bm : ℝ} (htp1 : tp < 1) (htm1 : tm < 1) (hbp : 0 < bp) (hbm : 0 < bm) :
    (tm - tp) * bm < (1 - tp) * (bp + bm) := by
  nlinarith [mul_pos (sub_pos.2 htp1) hbp, mul_pos (sub_pos.2 htm1) hbm]

lemma cmp_23 {tp tm sp bp bm dp am : ℝ} (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm)
    (htm1 : tm < 1) (hbp : 0 < bp) (hbm : 0 < bm) (hdp : 0 < dp) (had : dp < am)
    (R : bm * (1 - tm) = am * tm) (hp1 : sp < 1) :
    (tm - tp) * ((1 - sp) * (dp + bm)) < (1 - sp) * ((1 - tp) * (bp + bm)) := by
  have key : (tm - tp) * (dp + bm) < (1 - tp) * (bp + bm) := by
    have hh : (tm - tp) * dp < bp * (1 - tp) + bm * (1 - tm) := by
      rcases le_or_gt tm tp with h | h
      · nlinarith [mul_pos hbp (sub_pos.2 htp1), mul_pos hbm (sub_pos.2 htm1),
          mul_nonneg (sub_nonneg.2 h) hdp.le]
      · nlinarith [mul_pos hbp (sub_pos.2 htp1), mul_pos htm (sub_pos.2 had),
          mul_pos (sub_pos.2 h) hdp, mul_pos htp hdp]
    nlinarith
  nlinarith [mul_lt_mul_of_pos_left key (sub_pos.2 hp1)]

lemma alpha_exists {lo hi p R : ℝ} (hlo : lo < hi) (hmid : p * lo < R) :
    ∃ α : ℝ, lo < α ∧ α < hi ∧ p * α < R := by
  rcases le_or_gt p 0 with hp | hp
  · refine ⟨(lo + hi) / 2, by linarith, by linarith, ?_⟩
    nlinarith
  · set ε := min ((hi - lo) / 2) ((R - p * lo) / (2 * p)) with hε
    have h0 : 0 < ε := lt_min (by linarith) (by apply div_pos <;> linarith)
    have h1 : ε ≤ (hi - lo) / 2 := min_le_left _ _
    have h2 : ε ≤ (R - p * lo) / (2 * p) := min_le_right _ _
    have h3 : p * ε ≤ (R - p * lo) / 2 := by
      have := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * p)).1 h2
      linarith
    exact ⟨lo + ε, by linarith, by linarith, by nlinarith⟩

lemma lo_lt_of {A1 A2 B1 e q : ℝ} (hA1 : 0 < A1) (hB1 : 0 < B1) (he : e ≤ q)
    (hP : q * A1 < B1 * (A1 - A2)) : A2 / A1 < 1 - e / B1 := by
  have h1 : e / B1 ≤ q / B1 := div_le_div_of_nonneg_right he hB1.le
  have h2 : q / B1 < 1 - A2 / A1 := by
    have : 1 - A2 / A1 = (A1 - A2) / A1 := by field_simp
    rw [this, div_lt_div_iff₀ hB1 hA1]; nlinarith
  linarith

/-- A type-09 shape in the normal form, with the standing hypotheses.  `k-` is determined
by `k- = (1 - s-) h- / (1 - t-)`. -/
structure Shape09 where
  tp : ℝ
  tm : ℝ
  sp : ℝ
  sm : ℝ
  hp : ℝ
  hm : ℝ
  kp : ℝ
  tp_pos : 0 < tp
  tp_lt : tp < 1
  tm_pos : 0 < tm
  tm_lt : tm < 1
  sp_pos : 0 < sp
  sp_lt : sp < 1
  sm_pos : 0 < sm
  sm_lt : sm < 1
  hp_pos : 0 < hp
  hm_pos : 0 < hm
  kp_pos : 0 < kp
  /-- the roof `b+ < d+` of type 09 -/
  roof : hp / (1 - tp) < kp / (1 - sp)

namespace Shape09
variable (S : Shape09)

/-- `k- = (1 - s-) h- / (1 - t-)`. -/
noncomputable def km : ℝ := (1 - S.sm) * S.hm / (1 - S.tm)
noncomputable def ap : ℝ := S.hp / S.tp
noncomputable def bp : ℝ := S.hp / (1 - S.tp)
noncomputable def am : ℝ := S.hm / S.tm
noncomputable def bm : ℝ := S.hm / (1 - S.tm)
noncomputable def cp : ℝ := S.kp / S.sp
noncomputable def dp : ℝ := S.kp / (1 - S.sp)
noncomputable def cm : ℝ := S.km / S.sm
noncomputable def dm : ℝ := S.km / (1 - S.sm)
noncomputable def A1 : ℝ := S.ap + S.am
noncomputable def A2 : ℝ := S.cp + S.cm
noncomputable def B1 : ℝ := S.bp + S.bm
/-- `e± = ((1 - s±)/s±) (d± - b±)` (27.17). -/
noncomputable def ep : ℝ := (1 - S.sp) / S.sp * (S.dp - S.bp)
noncomputable def em : ℝ := (1 - S.sm) / S.sm * (S.dm - S.bm)

lemma km_pos : 0 < S.km := by
  unfold km
  have := S.tm_lt; have := S.sm_lt
  have := S.hm_pos
  apply div_pos (mul_pos (by linarith) S.hm_pos) (by linarith)

lemma ap_pos : 0 < S.ap := div_pos S.hp_pos S.tp_pos
lemma am_pos : 0 < S.am := div_pos S.hm_pos S.tm_pos
lemma bp_pos : 0 < S.bp := div_pos S.hp_pos (by linarith [S.tp_lt])
lemma bm_pos : 0 < S.bm := div_pos S.hm_pos (by linarith [S.tm_lt])
lemma cp_pos : 0 < S.cp := div_pos S.kp_pos S.sp_pos
lemma dp_pos : 0 < S.dp := div_pos S.kp_pos (by linarith [S.sp_lt])
lemma cm_pos : 0 < S.cm := div_pos S.km_pos S.sm_pos

lemma dm_eq : S.dm = S.bm := by
  have h1 : (1 - S.sm) ≠ 0 := by linarith [S.sm_lt]
  have h2 : (1 - S.tm) ≠ 0 := by linarith [S.tm_lt]
  unfold dm km bm
  field_simp

lemma em_eq : S.em = 0 := by
  unfold em; rw [S.dm_eq]; simp

lemma ap_mul : S.ap * S.tp = S.hp := by
  unfold ap; field_simp [S.tp_pos.ne']
lemma am_mul : S.am * S.tm = S.hm := by
  unfold am; field_simp [S.tm_pos.ne']
lemma bp_mul : S.bp * (1 - S.tp) = S.hp := by
  have : (1 - S.tp) ≠ 0 := by linarith [S.tp_lt]
  unfold bp; field_simp
lemma bm_mul : S.bm * (1 - S.tm) = S.hm := by
  have : (1 - S.tm) ≠ 0 := by linarith [S.tm_lt]
  unfold bm; field_simp
lemma cp_mul : S.cp * S.sp = S.kp := by
  unfold cp; field_simp [S.sp_pos.ne']
lemma dp_mul : S.dp * (1 - S.sp) = S.kp := by
  have : (1 - S.sp) ≠ 0 := by linarith [S.sp_lt]
  unfold dp; field_simp
lemma cm_mul : S.cm * S.sm = S.km := by
  unfold cm; field_simp [S.sm_pos.ne']
/-- `k- = b- (1 - s-)`. -/
lemma km_eq : S.km = S.bm * (1 - S.sm) := by
  have h2 : (1 - S.tm) ≠ 0 := by linarith [S.tm_lt]
  unfold km bm; field_simp
lemma cm_mul' : S.cm * S.sm = S.bm * (1 - S.sm) := by rw [S.cm_mul, S.km_eq]

lemma bp_lt_dp : S.bp < S.dp := S.roof


/-! ### The three failing hypotheses of "27.34 fails" in closed form -/

/-- Proposition 27.17 for `W = F1`: Theorem 5 holds with `W = F1` iff some `α` satisfies these
four inequalities (the geometry layer supplies the equivalence). -/
def T5F1 : Prop :=
  ∃ α : ℝ, S.A2 / S.A1 < α ∧ α < 1 - (S.ep + S.em) / S.B1 ∧
    (S.bp - S.am) * α < S.bp - S.cm - S.ep ∧ (S.bm - S.ap) * α < S.bm - S.cp - S.em

/-- Corollary 27.29, row `A^M` (type 09): the pair `0256/235-5 + 123/235-3` is a certificate if
`d+ > c-`, `h- < t-(k+ + s+ c-)` and `h- < k+ t- + d-(1 - s+ t-)`. -/
def AM : Prop :=
  S.cm < S.dp ∧ S.hm < S.tm * (S.kp + S.sp * S.cm) ∧
    S.hm < S.kp * S.tm + S.dm * (1 - S.sp * S.tm)

/-- 27.57: `f1 = f(m1+) = (1 - t+)(b+ + b-)`. -/
noncomputable def f1 : ℝ := (1 - S.tp) * (S.bp + S.bm)
/-- 27.57: `f2 = f(m2+) = (1 - s+)(d+ + b-)`. -/
noncomputable def f2 : ℝ := (1 - S.sp) * (S.dp + S.bm)
/-- 27.57: `M = min(1/b-, (1 - t+)/f1, (1 - s+)/f2)`. -/
noncomputable def M57 : ℝ := min (1 / S.bm) (min ((1 - S.tp) / S.f1) ((1 - S.sp) / S.f2))
/-- 27.57: `N = max(1/b-, (1 - t+/t-)/f1, (1 - s+/s-)/f2)`. -/
noncomputable def N57 : ℝ :=
  max (1 / S.bm) (max ((1 - S.tp / S.tm) / S.f1) ((1 - S.sp / S.sm) / S.f2))

/-- Theorem 5 with `W` the lower quad `3456 = (xa, m1-, xb, m2-)` (27.57): some `w` with
`w1, w2 > 0`, `w1 + w2 < M`, `w1/t- + w2/s- > N`. -/
def Q3456 : Prop :=
  ∃ w1 w2 : ℝ, 0 < w1 ∧ 0 < w2 ∧ w1 + w2 < S.M57 ∧ S.N57 < w1 / S.tm + w2 / S.sm

lemma f1_pos : 0 < S.f1 := by
  unfold f1; have := S.tp_lt; have := S.bp_pos; have := S.bm_pos
  exact mul_pos (by linarith) (by linarith)
lemma f2_pos : 0 < S.f2 := by
  unfold f2; have := S.sp_lt; have := S.dp_pos; have := S.bm_pos
  exact mul_pos (by linarith) (by linarith)


/-- The nine comparisons of 27.57: `t- N < M`. -/
lemma tm_N57_lt_M57 (hts : S.tm < S.sm) (had : S.dp < S.am) : S.tm * S.N57 < S.M57 := by
  have htm := S.tm_pos; have htm1 := S.tm_lt; have htp := S.tp_pos; have htp1 := S.tp_lt
  have hsm := S.sm_pos; have hsm1 := S.sm_lt; have hsp := S.sp_pos; have hsp1 := S.sp_lt
  have hbm := S.bm_pos; have hbp := S.bp_pos; have hdp := S.dp_pos; have hf1 := S.f1_pos
  have hf2 := S.f2_pos
  have R : S.bm * (1 - S.tm) = S.am * S.tm := by rw [S.bm_mul, S.am_mul]
  have hbpa : S.bp < S.am := lt_trans S.bp_lt_dp had
  have hf1d : S.f1 = (1 - S.tp) * (S.bp + S.bm) := rfl
  have hf2d : S.f2 = (1 - S.sp) * (S.dp + S.bm) := rfl
  have hsf2 : 0 < S.sm * S.f2 := mul_pos hsm hf2
  have hk := tmsm_lt htm hsp1 hsm1 hts
  have e2 : S.tm * ((1 - S.tp / S.tm) / S.f1) = (S.tm - S.tp) / S.f1 := by
    field_simp
  have e3 : S.tm * ((1 - S.sp / S.sm) / S.f2) = S.tm * (S.sm - S.sp) / (S.sm * S.f2) := by
    field_simp
  have e1 : S.tm * (1 / S.bm) = S.tm / S.bm := by ring
  have h11 : S.tm / S.bm < 1 / S.bm := by
    rw [div_lt_div_iff₀ hbm hbm]; nlinarith
  have h12 : S.tm / S.bm < (1 - S.tp) / S.f1 := by
    rw [div_lt_div_iff₀ hbm hf1, hf1d]
    exact cmp_12 htp1 htm hbpa R |>.trans_eq' (by ring) |>.trans_eq (by ring)
  have h13 : S.tm / S.bm < (1 - S.sp) / S.f2 := by
    rw [div_lt_div_iff₀ hbm hf2, hf2d]
    exact cmp_12 hsp1 htm had R |>.trans_eq' (by ring) |>.trans_eq (by ring)
  have h21 : (S.tm - S.tp) / S.f1 < 1 / S.bm := by
    rw [div_lt_div_iff₀ hf1 hbm, hf1d]
    nlinarith [cmp_21 htp1 htm1 hbp hbm]
  have h22 : (S.tm - S.tp) / S.f1 < (1 - S.tp) / S.f1 := by
    apply div_lt_div_of_pos_right (by linarith) hf1
  have h23 : (S.tm - S.tp) / S.f1 < (1 - S.sp) / S.f2 := by
    rw [div_lt_div_iff₀ hf1 hf2, hf1d, hf2d]
    nlinarith [cmp_23 htp htp1 htm htm1 hbp hbm hdp had R hsp1]
  have h31 : S.tm * (S.sm - S.sp) / (S.sm * S.f2) < 1 / S.bm := by
    rw [div_lt_div_iff₀ hsf2 hbm, hf2d]
    nlinarith [mul_pos hbm hdp, mul_lt_mul_of_pos_right hk hbm,
      mul_pos hsm (sub_pos.2 hsp1), mul_pos (mul_pos hsm (sub_pos.2 hsp1)) hdp]
  have h32 : S.tm * (S.sm - S.sp) / (S.sm * S.f2) < (1 - S.tp) / S.f1 := by
    rw [div_lt_div_iff₀ hsf2 hf1, hf1d, hf2d]
    have := x_lt_y (mul_pos hsm (sub_pos.2 hsp1)) (add_pos hbp hbm)
      hk (show S.bp + S.bm < S.dp + S.bm by linarith [S.bp_lt_dp])
    nlinarith [mul_lt_mul_of_pos_left this (sub_pos.2 htp1)]
  have h33 : S.tm * (S.sm - S.sp) / (S.sm * S.f2) < (1 - S.sp) / S.f2 := by
    rw [div_lt_div_iff₀ hsf2 hf2, hf2d]
    nlinarith [mul_lt_mul_of_pos_right hk hf2]
  unfold N57 M57
  rw [mul_max_of_nonneg _ _ htm.le, mul_max_of_nonneg _ _ htm.le, e1, e2, e3]
  simp only [max_lt_iff, lt_min_iff]
  tauto

lemma M57_pos : 0 < S.M57 := by
  have := S.bm_pos; have := S.f1_pos; have := S.f2_pos; have := S.tp_lt; have := S.sp_lt
  unfold M57
  simp only [lt_min_iff]
  refine ⟨by positivity, div_pos (by linarith) S.f1_pos, div_pos (by linarith) S.f2_pos⟩

/-- **27.57** (Theorem 5 with the lower quad; type 09).  If `t- < s-` and `a- > d+`, Theorem 5
holds with `W` the lower quad `3456 = (xa, m1-, xb, m2-)`, in the form of the paper's solvability
condition `t- N < M`. -/
theorem q3456_of_lt (hts : S.tm < S.sm) (had : S.dp < S.am) : S.Q3456 := by
  have hkey := S.tm_N57_lt_M57 hts had
  have htm := S.tm_pos; have hsm := S.sm_pos; have hM := S.M57_pos
  set M := S.M57 with hMdef
  set N := S.N57 with hNdef
  have hD : 0 < M / S.tm - N := by
    rw [sub_pos, lt_div_iff₀ htm]; linarith
  have hκ : 0 < 2 / S.tm - 1 / S.sm := by
    have : 1 / S.sm < 1 / S.tm := one_div_lt_one_div_of_lt htm hts
    have : 1 / S.tm < 2 / S.tm := by
      rw [div_lt_div_iff_of_pos_right htm]; norm_num
    linarith
  set ε := min (M / 4) ((M / S.tm - N) / (2 * (2 / S.tm - 1 / S.sm))) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hε1 : ε ≤ M / 4 := min_le_left _ _
  have hε2 : ε ≤ (M / S.tm - N) / (2 * (2 / S.tm - 1 / S.sm)) := min_le_right _ _
  have hε3 : ε * (2 / S.tm - 1 / S.sm) ≤ (M / S.tm - N) / 2 := by
    have := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * (2 / S.tm - 1 / S.sm))).1 hε2
    linarith
  refine ⟨M - 2 * ε, ε, by linarith, hε0, by linarith, ?_⟩
  have : (M - 2 * ε) / S.tm + ε / S.sm = M / S.tm - ε * (2 / S.tm - 1 / S.sm) := by ring
  rw [this]; linarith

lemma cm_lt_am (hts : S.tm < S.sm) : S.cm < S.am := by
  have htm := S.tm_pos; have hsm := S.sm_pos
  have h1 := S.am_mul; have h2 := S.cm_mul'; have h3 := S.bm_mul; have h4 := S.bm_pos
  have key : (S.am - S.cm) * (S.tm * S.sm) = S.bm * (S.sm - S.tm) := by
    have : S.am * S.tm = S.bm * (1 - S.tm) := by rw [h1, h3]
    linear_combination S.sm * this - S.tm * h2
  have : 0 < (S.am - S.cm) * (S.tm * S.sm) := by
    rw [key]; exact mul_pos h4 (sub_pos.2 hts)
  have := (pos_iff_pos_of_mul_pos this).2 (mul_pos htm hsm)
  linarith

lemma ep_eq : S.ep = S.cp + S.bp - S.bp / S.sp := by
  have h1 : (1 - S.sp) ≠ 0 := by linarith [S.sp_lt]
  have h2 := S.sp_pos.ne'
  have h3 := S.dp_mul
  unfold ep
  field_simp
  nlinarith [S.cp_mul, S.dp_mul]

lemma ep_pos : 0 < S.ep := by
  unfold ep
  have := S.bp_lt_dp; have := S.sp_pos; have := S.sp_lt
  exact mul_pos (div_pos (by linarith) S.sp_pos) (by linarith)

lemma sp_A2 : S.sp * S.A2 = S.kp + S.sp * S.cm := by
  unfold A2; nlinarith [S.cp_mul]

lemma bsp_mul : S.bp / S.sp * S.sp = S.bp := by
  field_simp [S.sp_pos.ne']

lemma t5_of (hlo : S.A2 / S.A1 < 1 - S.ep / S.B1)
    (hmid : (S.bp - S.am) * (S.A2 / S.A1) < S.bp - S.cm - S.ep)
    (hcb : S.cp ≤ S.bm) (hca : S.cp < S.ap) : S.T5F1 := by
  have hA1 : 0 < S.A1 := add_pos S.ap_pos S.am_pos
  have hB1 : 0 < S.B1 := add_pos S.bp_pos S.bm_pos
  have hA2 : 0 < S.A2 := add_pos S.cp_pos S.cm_pos
  obtain ⟨α, h1, h2, h3⟩ := alpha_exists hlo hmid
  have hlo0 : 0 < S.A2 / S.A1 := div_pos hA2 hA1
  have he : 0 < S.ep / S.B1 := div_pos S.ep_pos hB1
  refine ⟨α, h1, by rw [S.em_eq]; simpa using h2, h3, ?_⟩
  rw [S.em_eq]
  have hα0 : 0 < α := hlo0.trans h1
  have hα1 : α < 1 := by linarith
  rcases le_or_gt S.ap S.bm with h | h
  · nlinarith [mul_pos (sub_pos.2 (show 0 < S.bm - S.ap + 1 by linarith)) hα0]
  · nlinarith

/-- Case (I) of 27.58: `a- > b+` and `b+ > s+A2` give Theorem 5 with `W = F1`. -/
lemma t5_case_I (hts : S.tm < S.sm) (hca : S.cp < S.ap) (hcb : S.cp ≤ S.bm)
    (h1 : S.bp < S.am) (h2 : S.sp * S.A2 < S.bp) : S.T5F1 := by
  have hA1 : 0 < S.A1 := add_pos S.ap_pos S.am_pos
  have hB1 : 0 < S.B1 := add_pos S.bp_pos S.bm_pos
  have hA2 : 0 < S.A2 := add_pos S.cp_pos S.cm_pos
  have hcmam := S.cm_lt_am hts
  have hep := S.ep_eq
  have hu := S.bsp_mul
  have hsp := S.sp_pos; have hsp1 := S.sp_lt
  have hbp := S.bp_pos; have hbm := S.bm_pos; have hap := S.ap_pos; have hcp := S.cp_pos
  have hcm := S.cm_pos; have ham := S.am_pos
  have hu2 : S.A2 < S.bp / S.sp := by
    rw [lt_div_iff₀ hsp]; linarith
  have hq : S.ep ≤ S.bp - S.cm := by
    unfold A2 at hu2; rw [hep]; linarith
  have hP : (S.bp - S.cm) * S.A1 < S.B1 * (S.A1 - S.A2) := by
    have hid : S.B1 * (S.A1 - S.A2) - (S.bp - S.cm) * S.A1 =
        (S.bm * S.am - S.bp * S.cp) + S.bm * (S.ap - S.cp) + S.cm * (S.A1 - S.B1) := by
      unfold A1 A2 B1; ring
    have t1 : 0 < S.bm * S.am - S.bp * S.cp := by
      nlinarith [mul_pos hcp (sub_pos.2 h1), mul_nonneg ham.le (sub_nonneg.2 hcb)]
    have t2 : 0 < S.bm * (S.ap - S.cp) := mul_pos hbm (sub_pos.2 hca)
    rcases le_or_gt S.B1 S.A1 with h | h
    · nlinarith [mul_nonneg hcm.le (sub_nonneg.2 h)]
    · have hlt : S.B1 - S.A1 < S.bm - S.ap := by unfold A1 B1; linarith
      have hpos : 0 < S.bm - S.ap := by linarith
      have c1 : S.cm * (S.B1 - S.A1) < S.am * (S.bm - S.ap) := by
        nlinarith [mul_lt_mul_of_pos_left hlt hcm, mul_pos (sub_pos.2 hcmam) hpos]
      have c2 : 0 < S.ap * (S.am + S.bm) - S.cp * (S.bp + S.bm) := by
        nlinarith [mul_pos (sub_pos.2 hca) (add_pos ham hbm), mul_pos hcp (sub_pos.2 h1)]
      nlinarith
  have hlo := lo_lt_of hA1 hB1 hq hP
  have hmid : (S.bp - S.am) * (S.A2 / S.A1) < S.bp - S.cm - S.ep := by
    have : 0 < S.A2 / S.A1 := div_pos hA2 hA1
    have : S.bp - S.cm - S.ep = S.bp / S.sp - S.A2 := by unfold A2; rw [hep]; ring
    nlinarith [mul_pos (sub_pos.2 h1) ‹0 < S.A2 / S.A1›]
  exact S.t5_of hlo hmid hcb hca

/-- Case (III) of 27.58: `a- < b+`, `b+ > s+A2`, `a- ≥ s+A2` give Theorem 5 with `W = F1`. -/
lemma t5_case_III (hts : S.tm < S.sm) (hca : S.cp < S.ap) (hcb : S.cp ≤ S.bm)
    (h1 : S.am ≤ S.bp) (h2 : S.sp * S.A2 < S.bp) (h3 : S.sp * S.A2 ≤ S.am) : S.T5F1 := by
  have hA1 : 0 < S.A1 := add_pos S.ap_pos S.am_pos
  have hB1 : 0 < S.B1 := add_pos S.bp_pos S.bm_pos
  have hA2 : 0 < S.A2 := add_pos S.cp_pos S.cm_pos
  have hcmam := S.cm_lt_am hts
  have hep := S.ep_eq
  have hu := S.bsp_mul
  have hsp := S.sp_pos; have hsp1 := S.sp_lt
  have hbp := S.bp_pos; have hbm := S.bm_pos; have hap := S.ap_pos; have hcp := S.cp_pos
  have hcm := S.cm_pos; have ham := S.am_pos
  have hu2 : S.A2 < S.bp / S.sp := by
    rw [lt_div_iff₀ hsp]; linarith
  have hq : S.ep ≤ S.am - S.cm := by
    have : S.am - S.cm - S.ep = (S.am - S.sp * S.A2) + (1 - S.sp) * (S.bp / S.sp - S.A2) := by
      unfold A2; rw [hep]; nlinarith [hu]
    nlinarith [mul_pos (sub_pos.2 hsp1) (sub_pos.2 hu2)]
  have hP : (S.am - S.cm) * S.A1 < S.B1 * (S.A1 - S.A2) := by
    have hid : S.B1 * (S.A1 - S.A2) - (S.am - S.cm) * S.A1 =
        S.B1 * (S.ap - S.cp) + (S.am - S.cm) * (S.B1 - S.A1) := by
      unfold A1 A2 B1; ring
    have t1 : 0 < S.B1 * (S.ap - S.cp) := mul_pos hB1 (sub_pos.2 hca)
    rcases le_or_gt S.A1 S.B1 with h | h
    · nlinarith [mul_nonneg (sub_pos.2 hcmam).le (sub_nonneg.2 h)]
    · have hle : S.A1 - S.B1 ≤ S.ap - S.cp := by unfold A1 B1; linarith
      have hB : 0 < S.B1 - S.am + S.cm := by unfold B1; linarith
      nlinarith [mul_le_mul_of_nonneg_left hle (sub_pos.2 hcmam).le,
        mul_pos (sub_pos.2 hca) hB]
  have hlo := lo_lt_of hA1 hB1 hq hP
  have hmid : (S.bp - S.am) * (S.A2 / S.A1) < S.bp - S.cm - S.ep := by
    have e1 : S.bp - S.cm - S.ep = S.bp / S.sp - S.A2 := by unfold A2; rw [hep]; ring
    rw [e1, div_eq_mul_inv, ← mul_assoc]
    have hinv : 0 < S.A1⁻¹ := inv_pos.2 hA1
    -- clear `A1` and `s+`
    have key : (S.bp - S.am) * S.A2 < (S.bp / S.sp - S.A2) * S.A1 := by
      have k0 : S.sp * ((S.bp - S.am) * S.A2) < S.sp * ((S.bp / S.sp - S.A2) * S.A1) := by
        have : S.sp * ((S.bp / S.sp - S.A2) * S.A1) = (S.bp - S.sp * S.A2) * S.A1 := by
          rw [← mul_assoc, mul_sub, mul_div_cancel₀ _ hsp.ne']
        rw [this]
        unfold A1
        nlinarith [mul_pos hap (sub_pos.2 h2), mul_nonneg hbp.le (sub_nonneg.2 h1),
          mul_nonneg hbp.le (sub_nonneg.2 h3)]
      exact lt_of_mul_lt_mul_left k0 hsp.le
    calc (S.bp - S.am) * S.A2 * S.A1⁻¹ < (S.bp / S.sp - S.A2) * S.A1 * S.A1⁻¹ :=
          mul_lt_mul_of_pos_right key hinv
      _ = S.bp / S.sp - S.A2 := by field_simp
  exact S.t5_of hlo hmid hcb hca

/-- **Theorem 27.58** (type 09 is closed; the algebra).  Suppose "27.34 fails", in the form used by
the paper: `t- < s-` and `c+ < a+` (27.31 fails; type 09), `c+ < b-` (the `M`-image of 27.32
fails), the family `A^M` fails, Theorem 5 fails with `W = F1` (27.17) and with `W = 3456`
(27.57), and none of the special positions `a- = b+`, `a- = d+`, `b+ = s+A2` occurs.  Then the
five conditions of Theorem 27.48 hold:
`t- < s-`, `a- > b+`, `d+ > a-`, `d+ > c-`, `b+ < s+A2`. -/
theorem thm_27_58 (hts : S.tm < S.sm) (hca : S.cp < S.ap) (hcb : S.cp < S.bm)
    (hAM : ¬ S.AM) (hT5 : ¬ S.T5F1) (hQ : ¬ S.Q3456)
    (sp1 : S.am ≠ S.bp) (sp2 : S.am ≠ S.dp) (sp3 : S.bp ≠ S.sp * S.A2) :
    S.tm < S.sm ∧ S.bp < S.am ∧ S.am < S.dp ∧ S.cm < S.dp ∧ S.bp < S.sp * S.A2 := by
  have had : S.am < S.dp := by
    rcases lt_or_gt_of_ne sp2 with h | h
    · exact h
    · exact absurd (S.q3456_of_lt hts h) hQ
  have hcmam := S.cm_lt_am hts
  have hcmd : S.cm < S.dp := hcmam.trans had
  have hspA : S.sp * S.A2 = S.kp + S.sp * S.cm := S.sp_A2
  have hbm := S.bm_pos; have hbp := S.bp_pos; have hkp := S.kp_pos
  have hsp := S.sp_pos; have hsp1 := S.sp_lt; have htm := S.tm_pos
  have hmm : S.bm * (1 - S.tm) = S.hm := S.bm_mul
  have hamm : S.am * S.tm = S.hm := S.am_mul
  -- (A^M3) holds in type 09
  have hAM3 : S.hm < S.kp * S.tm + S.dm * (1 - S.sp * S.tm) := by
    rw [S.dm_eq]
    nlinarith [mul_pos hkp htm, mul_pos (mul_pos hbm htm) (sub_pos.2 hsp1)]
  have hAM1 : S.cm < S.dp := hcmd
  refine ⟨hts, ?_, had, hcmd, ?_⟩
  · -- a- > b+
    rcases lt_or_gt_of_ne sp1 with h | h
    · exfalso
      rcases lt_or_gt_of_ne sp3 with h3 | h3
      · -- (II)
        refine hAM ⟨hAM1, ?_, hAM3⟩
        nlinarith [mul_lt_mul_of_pos_right (h.trans h3) htm, hspA]
      · -- (III)
        have h2 : S.sp * S.A2 ≤ S.am := by
          by_contra hh
          rw [not_le] at hh
          refine hAM ⟨hAM1, ?_, hAM3⟩
          nlinarith [mul_lt_mul_of_pos_right hh htm, hspA]
        exact hT5 (S.t5_case_III hts hca hcb.le h.le h3 h2)
    · exact h
  · -- b+ < s+A2
    rcases lt_or_gt_of_ne sp3 with h3 | h3
    · exact h3
    · exfalso
      rcases lt_or_gt_of_ne sp1 with h | h
      · have h2 : S.sp * S.A2 ≤ S.am := by
          by_contra hh
          rw [not_le] at hh
          refine hAM ⟨hAM1, ?_, hAM3⟩
          nlinarith [mul_lt_mul_of_pos_right hh htm, hspA]
        exact hT5 (S.t5_case_III hts hca hcb.le h.le h3 h2)
      · exact hT5 (S.t5_case_I hts hca hcb.le h h3)

/-! ### Theorem 27.48: the rim comparisons and the contradiction of the two failures -/

/-- 27.48, T1's rim: in the screen `(y, h- x + t- z)`, `m1+ = (0, h- t+ + t- h+)` lies inside the
segment from `m1- = (0, 0)` to `xa = (0, h-)` iff `a- > b+`. -/
theorem t48_T1_m1p_inside : S.hp * S.tm + S.hm * S.tp < S.hm ↔ S.bp < S.am := by
  have h1 := S.bp_mul; have h2 := S.am_mul
  have htm := S.tm_pos; have htp := S.tp_lt
  have key : S.hm - (S.hp * S.tm + S.hm * S.tp) = (S.tm * (1 - S.tp)) * (S.am - S.bp) := by
    rw [← h1, ← h2]; ring
  rw [← sub_pos, key, mul_pos_iff_of_pos_left (mul_pos htm (sub_pos.2 htp)), sub_pos]

/-- 27.48, T1's rim: `m2+ = (s+, t- k+)` lies above the segment `xa xb`
(`w = h-(1 - y)`) iff `d+ > a-`. -/
theorem t48_T1_m2p_above : S.hm * (1 - S.sp) < S.tm * S.kp ↔ S.am < S.dp := by
  have h1 := S.dp_mul; have h2 := S.am_mul
  have htm := S.tm_pos; have hsp := S.sp_lt
  have key : S.tm * S.kp - S.hm * (1 - S.sp) = (S.tm * (1 - S.sp)) * (S.dp - S.am) := by
    rw [← h1, ← h2]; ring
  rw [← sub_pos, key, mul_pos_iff_of_pos_left (mul_pos htm (sub_pos.2 hsp)), sub_pos]

/-- 27.48, T2's rim: in the screen `(x, k- y + s- z)`, `m1+ = (t+, s- h+)` lies below the segment
from `m2+ = (0, k- s+ + s- k+)` to `xa = (1, 0)` iff `b+ < k+ + s+ c- (= s+ A2)`. -/
theorem t48_T2_m1p_below :
    S.sm * S.hp < (S.km * S.sp + S.sm * S.kp) * (1 - S.tp) ↔ S.bp < S.kp + S.sp * S.cm := by
  have h1 := S.bp_mul; have h2 := S.cm_mul
  have hsm := S.sm_pos; have htp := S.tp_lt
  have key : (S.km * S.sp + S.sm * S.kp) * (1 - S.tp) - S.sm * S.hp =
      (S.sm * (1 - S.tp)) * (S.kp + S.sp * S.cm - S.bp) := by
    rw [← h1, ← h2]; ring
  rw [← sub_pos, key, mul_pos_iff_of_pos_left (mul_pos hsm (sub_pos.2 htp)), sub_pos]

/-- 27.48, `h- > k-` (from `t- < s-`, type 09). -/
theorem km_lt_hm (hts : S.tm < S.sm) : S.km < S.hm := by
  have h := S.km_eq; have h2 := S.bm_mul
  have := S.bm_pos; have := S.sm_lt; have := S.tm_lt
  nlinarith [mul_pos S.bm_pos (sub_pos.2 hts)]

/-- 27.48, "T1 fails ⇒ D(xb) ≥ D(m2-)", the valley analysis.  With the depths scaled so that
`D(xb) = 1`, `D(xa) = x > 1`, `ζ = g h- / (A12 t-) > 0`: `D(m1-) = t- x + h- ζ`,
`D(m2+) = s+ - k+ ζ`, `D(m2-) = s- + k- ζ`.  A second valley besides `m2+` is `m2-` (needs
`D(m2-) ≤ 1`) or `m1-` (needs `D(m1-) ≤ D(xa) = x` and `D(m1-) ≤ D(m2-)`).  Conclusion:
`D(m2-) ≤ 1`, i.e. `s- + k- ζ ≤ 1`. -/
theorem t48_T1_valley (hts : S.tm < S.sm) {x ζ : ℝ} (hx : 1 < x)
    (hv : S.sm + S.km * ζ ≤ 1 ∨
      (S.tm * x + S.hm * ζ ≤ x ∧ S.tm * x + S.hm * ζ ≤ S.sm + S.km * ζ)) :
    S.sm + S.km * ζ ≤ 1 := by
  rcases hv with h | ⟨-, h2⟩
  · exact h
  · by_contra hh
    rw [not_le] at hh
    have hk := S.km_pos
    have hkh := S.km_lt_hm hts
    have hkm := S.km_eq; have hbm := S.bm_mul
    -- ζ > (1 - s-)/k-
    have hζ1 : (1 - S.sm) < S.km * ζ := by linarith
    -- t- x ≤ s- - (h- - k-) ζ < t-
    have e : S.hm * (1 - S.sm) = S.km * (1 - S.tm) := by
      rw [← hbm, hkm]; ring
    have h3 : S.tm * x < S.tm := by
      have : (S.hm - S.km) * ζ * S.km > (S.hm - S.km) * (1 - S.sm) := by
        nlinarith [mul_lt_mul_of_pos_left hζ1 (sub_pos.2 hkh)]
      nlinarith
    nlinarith [S.tm_pos]

/-- 27.48: with `ζ = g h- / (A12 t-)`, `s- + k- ζ ≤ 1` is `g h- k- ≤ A12 t-(1 - s-)`. -/
theorem t48_T1_fail {A12 g : ℝ} (hA : 0 < A12)
    (h : S.sm + S.km * (g * S.hm / (A12 * S.tm)) ≤ 1) :
    g * S.hm * S.km ≤ A12 * S.tm * (1 - S.sm) := by
  have htm := S.tm_pos
  have hd : 0 < A12 * S.tm := mul_pos hA htm
  have : S.km * (g * S.hm / (A12 * S.tm)) = g * S.hm * S.km / (A12 * S.tm) := by ring
  rw [this] at h
  have h' : g * S.hm * S.km / (A12 * S.tm) ≤ 1 - S.sm := by linarith
  rw [div_le_iff₀ hd] at h'
  linarith

/-- 27.48, "T2 fails ⇒ E(m1-) ≥ E(xa)", `E = ⟨m2-, ·⟩_G`: `E(m1-) = A12 s- t- + g k- h-`,
`E(xa) = A12 s-`.  Equivalent: `A12 s-(t- - 1) + g k- h- ≥ 0`. -/
theorem t48_T2_fail {A12 g : ℝ}
    (h : A12 * S.sm ≤ A12 * S.sm * S.tm + g * S.km * S.hm) :
    0 ≤ A12 * S.sm * (S.tm - 1) + g * S.km * S.hm := by
  linarith

/-- **27.48, the contradiction.**  The two failure inequalities of T1 and T2 sum to
`A12 (t- - s-) ≥ 0`, against `t- < s-`. -/
theorem t48_contra {A12 g : ℝ} (hA : 0 < A12) (hts : S.tm < S.sm)
    (h1 : g * S.hm * S.km ≤ A12 * S.tm * (1 - S.sm))
    (h2 : 0 ≤ A12 * S.sm * (S.tm - 1) + g * S.km * S.hm) : False := by
  nlinarith [mul_pos hA (sub_pos.2 hts)]

/-- **Theorem 27.48, the algebra of the proof in one statement.**  With `A12, g > 0` and the
depth scaling of the proof (`D(xb) = 1`, `D(xa) = x > 1`, `ζ = g h- / (A12 t-)`), if T1 fails
(a second valley: the disjunction `hv`) and T2 fails (`E(m1-) ≥ E(xa)`), then `False`, given
`t- < s-`. -/
theorem thm_27_48_contra {A12 g x : ℝ} (hA : 0 < A12) (hts : S.tm < S.sm) (hx : 1 < x)
    (hv : S.sm + S.km * (g * S.hm / (A12 * S.tm)) ≤ 1 ∨
      (S.tm * x + S.hm * (g * S.hm / (A12 * S.tm)) ≤ x ∧
        S.tm * x + S.hm * (g * S.hm / (A12 * S.tm)) ≤ S.sm + S.km * (g * S.hm / (A12 * S.tm))))
    (hE : A12 * S.sm ≤ A12 * S.sm * S.tm + g * S.km * S.hm) : False :=
  S.t48_contra hA hts (S.t48_T1_fail hA (S.t48_T1_valley hts hx hv)) (S.t48_T2_fail hE)

end Shape09
end Minimality.CaseC09

