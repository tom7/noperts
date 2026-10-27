module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Type 18, acute case (c): the shape parameters (`FEWER-FACES-PROOFS.md` §27, continued (4))

The normal form of §27, continued (2) §0 for type 18, labels
`(v, xa, m1+, m1-, xb, m2+, m2-) = (5, 3, 0, 6, 4, 1, 2)`:
`v = 0`, `xa = e₁`, `xb = e₂`, `m1± = (t±, 0, ±h±)`, `m2± = (0, s±, ±k±)`, with the slopes
`a± = h±/t±`, `b± = h±/(1 - t±)`, `c± = k±/s±`, `d± = k±/(1 - s±)`,
`A1 = a+ + a-`, `A2 = c+ + c-`, `B1 = b+ + b-`.  Type 18 has both roofs `d± < b±`.
-/

namespace Minimality.CaseC18

/-- A type-18 shape in the normal form, with the standing hypotheses. -/
structure Shape18 where
  tp : ℝ
  tm : ℝ
  sp : ℝ
  sm : ℝ
  hp : ℝ
  hm : ℝ
  kp : ℝ
  km : ℝ
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
  km_pos : 0 < km
  /-- the upper roof `d+ < b+` -/
  roof_p : kp / (1 - sp) < hp / (1 - tp)
  /-- the lower roof `d- < b-` -/
  roof_m : km / (1 - sm) < hm / (1 - tm)

namespace Shape18
variable (S : Shape18)

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

lemma ap_pos : 0 < S.ap := div_pos S.hp_pos S.tp_pos
lemma am_pos : 0 < S.am := div_pos S.hm_pos S.tm_pos
lemma bp_pos : 0 < S.bp := div_pos S.hp_pos (by linarith [S.tp_lt])
lemma bm_pos : 0 < S.bm := div_pos S.hm_pos (by linarith [S.tm_lt])
lemma cp_pos : 0 < S.cp := div_pos S.kp_pos S.sp_pos
lemma cm_pos : 0 < S.cm := div_pos S.km_pos S.sm_pos
lemma dp_pos : 0 < S.dp := div_pos S.kp_pos (by linarith [S.sp_lt])
lemma dm_pos : 0 < S.dm := div_pos S.km_pos (by linarith [S.sm_lt])

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
lemma cm_mul : S.cm * S.sm = S.km := by
  unfold cm; field_simp [S.sm_pos.ne']
lemma dp_mul : S.dp * (1 - S.sp) = S.kp := by
  have : (1 - S.sp) ≠ 0 := by linarith [S.sp_lt]
  unfold dp; field_simp
lemma dm_mul : S.dm * (1 - S.sm) = S.km := by
  have : (1 - S.sm) ≠ 0 := by linarith [S.sm_lt]
  unfold dm; field_simp

/-- The upper roof (C+): `d+ < b+`. -/
lemma dp_lt_bp : S.dp < S.bp := S.roof_p
/-- The lower roof: `d- < b-`. -/
lemma dm_lt_bm : S.dm < S.bm := S.roof_m

end Shape18

end Minimality.CaseC18

end
