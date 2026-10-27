module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Type 20, acute case (c): the shape parameters (`FEWER-FACES-PROOFS.md` §27, continued (6))

The normal form of §27, continued (2) §0 for type 20, labels
`(v, xa, m1+, m1-, xb, m2+, m2-) = (5, 1, 0, 3, 6, 2, 4)` of the faces
`0135, 016, 025, 026, 134, 146, 2456, 345`:
`v = 0`, `xa = e₁`, `xb = e₂`, `m1± = (t±, 0, ±h±)`, `m2± = (0, s±, ±k±)`, with the slopes
`a± = h±/t±`, `b± = h±/(1 - t±)`, `c± = k±/s±`, `d± = k±/(1 - s±)`,
`A1 = a+ + a-`, `A2 = c+ + c-`, `B1 = b+ + b-`.  Type 20 has the roofs `d+ < b+` (upper) and `b- < d-` (lower).
-/

namespace Minimality.CaseC20

/-- A type-20 shape in the normal form, with the standing hypotheses. -/
structure Shape20 where
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
  /-- the lower roof `b- < d-` -/
  roof_m : hm / (1 - tm) < km / (1 - sm)

namespace Shape20
variable (S : Shape20)

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
/-- The lower roof: `b- < d-`. -/
lemma bm_lt_dm : S.bm < S.dm := S.roof_m

/-- The upper roof `d+ < b+` cleared of denominators. -/
lemma roof_p' : S.kp * (1 - S.tp) < S.hp * (1 - S.sp) := by
  have h := S.dp_lt_bp
  have e1 := S.bp_mul; have e2 := S.dp_mul
  have hs := S.sp_lt; have ht := S.tp_lt
  nlinarith [mul_lt_mul_of_pos_right h (mul_pos (sub_pos.2 ht) (sub_pos.2 hs))]

/-- The lower roof `b- < d-` cleared of denominators. -/
lemma roof_m' : S.hm * (1 - S.sm) < S.km * (1 - S.tm) := by
  have h := S.bm_lt_dm
  have e1 := S.bm_mul; have e2 := S.dm_mul
  have hs := S.sm_lt; have ht := S.tm_lt
  nlinarith [mul_lt_mul_of_pos_right h (mul_pos (sub_pos.2 ht) (sub_pos.2 hs))]

end Shape20

end Minimality.CaseC20

end
