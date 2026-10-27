module

public import Minimality.CaseC20Bridge
public import Minimality.CaseC20ST
public import Minimality.CaseC20NR

@[expose] public section

/-!
# Type 20, acute case (c): the crossing tests at the shape's own metric
(`FEWER-FACES-PROOFS.md` §27, continued (4)--(6))

Each realizable test is a rim cycle of the seven points (labels `(v, xa, m1+, m1-, xb, m2+, m2-) =
(5, 1, 0, 3, 6, 2, 4)`) with a view `u` and a tilt `w` in frame coordinates.  The screen tests (`ST`:
all other points strictly inside the rim, or over a side and moved inside by the tilt) are
generated: one `linarith` per fact, with a hint list of products of the positive quantities of the
frame (`t±, 1 - t±, s±, 1 - s±, h±, k±`, the roof slacks and the hypotheses of the test), found by
a linear program.  The depth side is stated as the two strict disjunctions "no diagonal pair of
the rim weakly above the other" (`hA`, `hB`) in the depths `Frame20.dep` along the view, which is
the metric condition for unimodality of the tilted rim; the covering arguments of the case tree
supply them.

* `tA`   : `T_A = 0135/016-1`, edge `m1+ xa`, apex `m1+` (realizable for `b+ > a-`); rim `(m1+, xb, m2-, v)`.
* `tP`   : `T' = 0135/016-0`, apex `xa` (realizable for `b+ < a-`); rim `(xa, m1-, m2-, xb)`.
* `vRa4`, `vTri`, `vRv` : `V = 0135/026` of class Ra (4-cycle / triangle rim) and Rv.
* `tB`   : the edge crossing at `m1+ v` (27.32); its `R`-image is 27.32^R.
* `xX`   : `X = 016/134` (27.62), the vertex crossing at `xa` of the two roof triangles.
* `yY`, `yT2` : `Y = 016/026-0` (27.63) and `T2 = 016/026-6` (27.27), the edge `m1+ xb`.
* `eXa`, `eXb` : the edge crossing at `xa xb` (27.31), apex `xa` / `xb`.
-/

namespace Minimality.CaseC20

open Finset Filter Minimality.CaseC09 Minimality.CaseC18
open scoped RealInnerProductSpace Topology

namespace Shape20
variable (S : Shape20)

/-- the view of `tA` -/
def u_tA : C3 := ⟨S.tp - 1, 0, S.hp⟩

/-- the tilt of `tA` -/
def w_tA (_ : Shape20) : C3 := ⟨-3, 1, 0⟩

end Shape20

theorem tA_cyc (S : Shape20) (hA1 : 0 < S.hm*S.tp - S.hm + S.hp*S.tm) :
    Cyc4 1 S.u_tA S.w_tA (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_tA]; left; linarith [(mul_pos htp1 S.km_pos), (mul_pos hsm1 S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_tA]; left; linarith [S.hp_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_tA]; left; linarith [(mul_pos htp1 S.km_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_tA]; left; linarith [(mul_pos htp1 S.km_pos), (mul_pos hsm1 S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_tA]; left; linarith [(mul_pos S.sm_pos S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_tA]; left; linarith [(mul_pos htp1 S.km_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_tA]; left; linarith [S.hp_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_tA]; left; linarith [(mul_pos S.sm_pos S.hp_pos)])⟩

theorem tA_rest1 (S : Shape20) (hA1 : 0 < S.hm*S.tp - S.hm + S.hp*S.tm) :
    Rest4 1 S.u_tA S.w_tA (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ ⟨1, 0, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_tA]; right; refine ⟨by ring, ?_⟩; linarith [S.hp_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_tA]; left; linarith [(mul_pos htp1 S.km_pos), (mul_pos hsm1 S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_tA]; left; linarith [(mul_pos S.sm_pos S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_tA]; right; refine ⟨by ring, ?_⟩; linarith [S.hp_pos])⟩

theorem tA_rest2 (S : Shape20) (hA1 : 0 < S.hm*S.tp - S.hm + S.hp*S.tm) :
    Rest4 1 S.u_tA S.w_tA (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_tA]; left; linarith [rp]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_tA]; left; linarith [(mul_pos (mul_pos htp1 hsp1) S.km_pos), (mul_pos (mul_pos htp1 hsm1) S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_tA]; left; linarith [(mul_pos (mul_pos htp1 S.sp_pos) S.km_pos), (mul_pos (mul_pos htp1 S.sm_pos) S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_tA]; left; linarith [(mul_pos S.sp_pos S.hp_pos)])⟩

theorem tA_rest3 (S : Shape20) (hA1 : 0 < S.hm*S.tp - S.hm + S.hp*S.tm) :
    Rest4 1 S.u_tA S.w_tA (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_tA]; left; linarith [(mul_pos htp1 S.hm_pos), (mul_pos htm1 S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_tA]; left; linarith [(mul_pos htp1 S.km_pos), (mul_pos hsm1 hA1)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_tA]; left; linarith [(mul_pos S.sm_pos hA1)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_tA]; right; refine ⟨by ring, ?_⟩; linarith [S.hm_pos, hA1])⟩

/-- tA -/
theorem Frame20.tA {x : Fin 7 → ℝ³} (F : Frame20 x) (hA1 : 0 < F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm)
    (hA : F.dep F.S.u_tA 0 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 0 < F.dep F.S.u_tA 5 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 5) (hB : F.dep F.S.u_tA 6 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 6 < F.dep F.S.u_tA 4 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 4) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  refine F.toFrame7.rim4 0 6 4 5 _ _ _ _ (F.ptC_0) (F.ptC_6) (F.ptC_4) (F.ptC_5) 1 (Or.inl rfl) F.S.u_tA F.S.w_tA (Or.inl (by simp only [Shape20.u_tA]; intro h0; linarith [htp1, h0]))
    (tA_cyc F.S hA1) ?_ ?_ ?_
  · intro j' h0 h1 h2 h3
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [F.ptC_1]; exact tA_rest1 F.S hA1
    · rw [F.ptC_2]; exact tA_rest2 F.S hA1
    · rw [F.ptC_3]; exact tA_rest3 F.S hA1
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd rfl h1
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using hA
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using hB

namespace Shape20
variable (S : Shape20)

/-- the view of `tP` -/
def u_tP : C3 := ⟨S.tp - 1, 0, S.hp⟩

/-- the tilt of `tP` -/
def w_tP (_ : Shape20) : C3 := ⟨2, -1, 0⟩

end Shape20

theorem tP_cyc (S : Shape20) (hA1 : 0 < -S.hm*S.tp + S.hm - S.hp*S.tm) :
    Cyc4 (-1) S.u_tP S.w_tP (⟨1, 0, 0⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tP, Shape20.w_tP]; left; linarith [(mul_pos S.sm_pos S.hp_pos), (mul_pos S.sm_pos hA1)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tP, Shape20.w_tP]; left; linarith [S.hp_pos, hA1]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tP, Shape20.w_tP]; left; linarith [(mul_pos htp1 rm), (mul_pos (mul_pos htp1 S.tm_pos) S.km_pos), (mul_pos (mul_pos S.tm_pos hsm1) S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tP, Shape20.w_tP]; left; linarith [(mul_pos S.sm_pos S.hp_pos), (mul_pos S.sm_pos hA1)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tP, Shape20.w_tP]; left; linarith [(mul_pos htp1 S.km_pos), (mul_pos hsm1 S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tP, Shape20.w_tP]; left; linarith [(mul_pos htp1 rm), (mul_pos (mul_pos htp1 S.tm_pos) S.km_pos), (mul_pos (mul_pos S.tm_pos hsm1) S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tP, Shape20.w_tP]; left; linarith [S.hp_pos, hA1]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tP, Shape20.w_tP]; left; linarith [(mul_pos htp1 S.km_pos), (mul_pos hsm1 S.hp_pos)])⟩

theorem tP_rest0 (S : Shape20) (hA1 : 0 < -S.hm*S.tp + S.hm - S.hp*S.tm) :
    Rest4 (-1) S.u_tP S.w_tP (⟨1, 0, 0⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tP, Shape20.w_tP]; right; refine ⟨by ring, ?_⟩; linarith [S.hp_pos, hA1]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tP, Shape20.w_tP]; left; linarith [(mul_pos S.sm_pos S.hp_pos), (mul_pos S.sm_pos hA1)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tP, Shape20.w_tP]; left; linarith [(mul_pos htp1 S.km_pos), (mul_pos hsm1 S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tP, Shape20.w_tP]; right; refine ⟨by ring, ?_⟩; linarith [S.hp_pos])⟩

theorem tP_rest2 (S : Shape20) (hA1 : 0 < -S.hm*S.tp + S.hm - S.hp*S.tm) :
    Rest4 (-1) S.u_tP S.w_tP (⟨1, 0, 0⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tP, Shape20.w_tP]; left; linarith [(mul_pos (mul_pos htp1 S.sp_pos) S.hm_pos), (mul_pos (mul_pos htm1 S.sp_pos) S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tP, Shape20.w_tP]; left; linarith [(mul_pos (mul_pos htp1 S.sp_pos) rm), (mul_pos (mul_pos htp1 S.sm_pos) S.kp_pos), (mul_pos (mul_pos hsp1 S.sm_pos) hA1), (mul_pos (mul_pos (mul_pos htp1 S.tm_pos) S.sp_pos) S.km_pos), (mul_pos (mul_pos (mul_pos S.tm_pos S.sp_pos) hsm1) S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tP, Shape20.w_tP]; left; linarith [(mul_pos (mul_pos htp1 hsp1) S.km_pos), (mul_pos (mul_pos htp1 hsm1) S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tP, Shape20.w_tP]; left; linarith [rp])⟩

theorem tP_rest5 (S : Shape20) (hA1 : 0 < -S.hm*S.tp + S.hm - S.hp*S.tm) :
    Rest4 (-1) S.u_tP S.w_tP (⟨1, 0, 0⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨0, 0, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tP, Shape20.w_tP]; right; refine ⟨by ring, ?_⟩; linarith [S.hm_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tP, Shape20.w_tP]; left; linarith [(mul_pos S.sm_pos hA1)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tP, Shape20.w_tP]; left; linarith [(mul_pos htp1 S.km_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tP, Shape20.w_tP]; left; linarith [S.hp_pos])⟩

/-- tP -/
theorem Frame20.tP {x : Fin 7 → ℝ³} (F : Frame20 x) (hA1 : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm)
    (hA : F.dep F.S.u_tP 1 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 1 < F.dep F.S.u_tP 6 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 3 ∨ F.dep F.S.u_tP 4 < F.dep F.S.u_tP 6) (hB : F.dep F.S.u_tP 3 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 1 ∨ F.dep F.S.u_tP 3 < F.dep F.S.u_tP 4 ∨ F.dep F.S.u_tP 6 < F.dep F.S.u_tP 4) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  refine F.toFrame7.rim4 1 3 4 6 _ _ _ _ (F.ptC_1) (F.ptC_3) (F.ptC_4) (F.ptC_6) (-1) (Or.inr rfl) F.S.u_tP F.S.w_tP (Or.inl (by simp only [Shape20.u_tP]; intro h0; linarith [htp1, h0]))
    (tP_cyc F.S hA1) ?_ ?_ ?_
  · intro j' h0 h1 h2 h3
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [F.ptC_0]; exact tP_rest0 F.S hA1
    · exact absurd rfl h0
    · rw [F.ptC_2]; exact tP_rest2 F.S hA1
    · exact absurd rfl h1
    · exact absurd rfl h2
    · rw [F.ptC_5]; exact tP_rest5 F.S hA1
    · exact absurd rfl h3
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using hA
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using hB

namespace Shape20
variable (S : Shape20)

/-- the view of `vTri` -/
def u_vTri : C3 := ⟨-S.sp*S.tp + S.tp, 0, -S.hp*S.sp + S.hp - S.kp⟩

/-- the tilt of `vTri` -/
def w_vTri : C3 := ⟨-3*S.tp, 1, -3*S.hp⟩

end Shape20

theorem vTri_cyc (S : Shape20) (hW : 0 < -S.hp*S.sp + S.hp - S.kp) (hQ : 0 < S.hm*S.sp*S.tp - S.hm*S.tp + S.hp*S.sp*S.tm - S.hp*S.sp - S.hp*S.tm + S.hp + S.kp*S.tm - S.kp) (hD : 0 < S.hp*S.sm*S.sp - S.hp*S.sm - S.hp*S.sp + S.hp + S.km*S.sp*S.tp - S.km*S.tp + S.kp*S.sm - S.kp) :
    Cyc3 (-1) S.u_vTri S.w_vTri (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vTri, Shape20.w_vTri]; left; linarith [rp]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vTri, Shape20.w_vTri]; left; linarith [rp]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vTri, Shape20.w_vTri]; left; linarith [rp])⟩

theorem vTri_rest4 (S : Shape20) (hW : 0 < -S.hp*S.sp + S.hp - S.kp) (hQ : 0 < S.hm*S.sp*S.tp - S.hm*S.tp + S.hp*S.sp*S.tm - S.hp*S.sp - S.hp*S.tm + S.hp + S.kp*S.tm - S.kp) (hD : 0 < S.hp*S.sm*S.sp - S.hp*S.sm - S.hp*S.sp + S.hp + S.km*S.sp*S.tp - S.km*S.tp + S.kp*S.sm - S.kp) :
    Rest3 (-1) S.u_vTri S.w_vTri (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨0, S.sm, -S.km⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vTri, Shape20.w_vTri]; left; linarith [(mul_pos (mul_pos S.tp_pos hsp1) S.km_pos), (mul_pos (mul_pos S.tp_pos hsm1) S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vTri, Shape20.w_vTri]; left; linarith [hD]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vTri, Shape20.w_vTri]; left; linarith [(mul_pos S.sm_pos rp)])⟩

theorem vTri_rest5 (S : Shape20) (hW : 0 < -S.hp*S.sp + S.hp - S.kp) (hQ : 0 < S.hm*S.sp*S.tp - S.hm*S.tp + S.hp*S.sp*S.tm - S.hp*S.sp - S.hp*S.tm + S.hp + S.kp*S.tm - S.kp) (hD : 0 < S.hp*S.sm*S.sp - S.hp*S.sm - S.hp*S.sp + S.hp + S.km*S.sp*S.tp - S.km*S.tp + S.kp*S.sm - S.kp) :
    Rest3 (-1) S.u_vTri S.w_vTri (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨0, 0, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vTri, Shape20.w_vTri]; left; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vTri, Shape20.w_vTri]; left; linarith [hW]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vTri, Shape20.w_vTri]; right; refine ⟨by ring, ?_⟩; linarith [S.hp_pos])⟩

theorem vTri_rest3 (S : Shape20) (hW : 0 < -S.hp*S.sp + S.hp - S.kp) (hQ : 0 < S.hm*S.sp*S.tp - S.hm*S.tp + S.hp*S.sp*S.tm - S.hp*S.sp - S.hp*S.tm + S.hp + S.kp*S.tm - S.kp) (hD : 0 < S.hp*S.sm*S.sp - S.hp*S.sm - S.hp*S.sp + S.hp + S.km*S.sp*S.tp - S.km*S.tp + S.kp*S.sm - S.kp) :
    Rest3 (-1) S.u_vTri S.w_vTri (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vTri, Shape20.w_vTri]; left; linarith [(mul_pos S.tp_pos S.kp_pos), (mul_pos S.tm_pos hW), (mul_pos (mul_pos S.tp_pos hsp1) S.hm_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vTri, Shape20.w_vTri]; left; linarith [hQ]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vTri, Shape20.w_vTri]; right; refine ⟨by ring, ?_⟩; linarith [(mul_pos htp1 S.hm_pos), (mul_pos htm1 S.hp_pos)])⟩

theorem vTri_rest2 (S : Shape20) (hW : 0 < -S.hp*S.sp + S.hp - S.kp) (hQ : 0 < S.hm*S.sp*S.tp - S.hm*S.tp + S.hp*S.sp*S.tm - S.hp*S.sp - S.hp*S.tm + S.hp + S.kp*S.tm - S.kp) (hD : 0 < S.hp*S.sm*S.sp - S.hp*S.sm - S.hp*S.sp + S.hp + S.km*S.sp*S.tp - S.km*S.tp + S.kp*S.sm - S.kp) :
    Rest3 (-1) S.u_vTri S.w_vTri (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨0, S.sp, S.kp⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vTri, Shape20.w_vTri]; right; refine ⟨by ring, ?_⟩; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vTri, Shape20.w_vTri]; left; linarith [(mul_pos hsp1 rp)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vTri, Shape20.w_vTri]; left; linarith [(mul_pos S.sp_pos rp)])⟩

/-- vTri -/
theorem Frame20.vTri {x : Fin 7 → ℝ³} (F : Frame20 x) (hW : 0 < -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hQ : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp) (hD : 0 < F.S.hp*F.S.sm*F.S.sp - F.S.hp*F.S.sm - F.S.hp*F.S.sp + F.S.hp + F.S.km*F.S.sp*F.S.tp - F.S.km*F.S.tp + F.S.kp*F.S.sm - F.S.kp)
     :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  refine F.toFrame7.rim3 0 6 1 _ _ _ (F.ptC_0) (F.ptC_6) (F.ptC_1) (-1) (Or.inr rfl) F.S.u_vTri F.S.w_vTri (Or.inl (by simp only [Shape20.u_vTri]; intro h0; linarith [(mul_pos F.S.tp_pos hsp1), h0]))
    (vTri_cyc F.S hW hQ hD) ?_ 
  · intro j' h0 h1 h2
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd rfl h2
    · rw [F.ptC_2]; exact vTri_rest2 F.S hW hQ hD
    · rw [F.ptC_3]; exact vTri_rest3 F.S hW hQ hD
    · rw [F.ptC_4]; exact vTri_rest4 F.S hW hQ hD
    · rw [F.ptC_5]; exact vTri_rest5 F.S hW hQ hD
    · exact absurd rfl h1

namespace Shape20
variable (S : Shape20)

/-- the view of `vRa4` -/
def u_vRa4 : C3 := ⟨-S.sp*S.tp + S.tp, 0, -S.hp*S.sp + S.hp - S.kp⟩

/-- the tilt of `vRa4` -/
def w_vRa4 : C3 := ⟨-3*S.tp, 1, -3*S.hp⟩

end Shape20

theorem vRa4_cyc (S : Shape20) (hW : 0 < -S.hp*S.sp + S.hp - S.kp) (hQ : 0 < S.hm*S.sp*S.tp - S.hm*S.tp + S.hp*S.sp*S.tm - S.hp*S.sp - S.hp*S.tm + S.hp + S.kp*S.tm - S.kp) (hD : 0 < -S.hp*S.sm*S.sp + S.hp*S.sm + S.hp*S.sp - S.hp - S.km*S.sp*S.tp + S.km*S.tp - S.kp*S.sm + S.kp) :
    Cyc4 (-1) S.u_vRa4 S.w_vRa4 (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨1, 0, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [hD, (mul_pos hsm1 rp)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [rp]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [hD]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [hD, (mul_pos hsm1 rp)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_pos S.sm_pos rp)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [hD]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [rp]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_pos S.sm_pos rp)])⟩

theorem vRa4_rest5 (S : Shape20) (hW : 0 < -S.hp*S.sp + S.hp - S.kp) (hQ : 0 < S.hm*S.sp*S.tp - S.hm*S.tp + S.hp*S.sp*S.tm - S.hp*S.sp - S.hp*S.tm + S.hp + S.kp*S.tm - S.kp) (hD : 0 < -S.hp*S.sm*S.sp + S.hp*S.sm + S.hp*S.sp - S.hp - S.km*S.sp*S.tp + S.km*S.tp - S.kp*S.sm + S.kp) :
    Rest4 (-1) S.u_vRa4 S.w_vRa4 (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨1, 0, 0⟩ ⟨0, 0, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_pos (mul_pos S.tp_pos hsp1) S.km_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_pos S.sm_pos hW)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; right; refine ⟨by ring, ?_⟩; linarith [S.hp_pos])⟩

theorem vRa4_rest3 (S : Shape20) (hW : 0 < -S.hp*S.sp + S.hp - S.kp) (hQ : 0 < S.hm*S.sp*S.tp - S.hm*S.tp + S.hp*S.sp*S.tm - S.hp*S.sp - S.hp*S.tm + S.hp + S.kp*S.tm - S.kp) (hD : 0 < -S.hp*S.sm*S.sp + S.hp*S.sm + S.hp*S.sp - S.hp - S.km*S.sp*S.tp + S.km*S.tp - S.kp*S.sm + S.kp) :
    Rest4 (-1) S.u_vRa4 S.w_vRa4 (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨1, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_pos S.tp_pos S.kp_pos), (mul_pos S.tm_pos hW), (mul_pos (mul_pos S.tp_pos hsp1) S.hm_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_pos S.tm_pos hD), (mul_pos (mul_pos S.tp_pos hsp1) rm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_pos S.sm_pos hQ)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; right; refine ⟨by ring, ?_⟩; linarith [(mul_pos htp1 S.hm_pos), (mul_pos htm1 S.hp_pos)])⟩

theorem vRa4_rest2 (S : Shape20) (hW : 0 < -S.hp*S.sp + S.hp - S.kp) (hQ : 0 < S.hm*S.sp*S.tp - S.hm*S.tp + S.hp*S.sp*S.tm - S.hp*S.sp - S.hp*S.tm + S.hp + S.kp*S.tm - S.kp) (hD : 0 < -S.hp*S.sm*S.sp + S.hp*S.sm + S.hp*S.sp - S.hp - S.km*S.sp*S.tp + S.km*S.tp - S.kp*S.sm + S.kp) :
    Rest4 (-1) S.u_vRa4 S.w_vRa4 (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨1, 0, 0⟩ ⟨0, S.sp, S.kp⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; right; refine ⟨by ring, ?_⟩; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_pos hsp1 hD), (mul_pos (mul_pos hsp1 hsm1) rp)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_pos S.sp_pos hD), (mul_pos (mul_pos hsp1 S.sm_pos) rp)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRa4, Shape20.w_vRa4]; left; linarith [(mul_pos S.sp_pos rp)])⟩

/-- vRa4 -/
theorem Frame20.vRa4 {x : Fin 7 → ℝ³} (F : Frame20 x) (hW : 0 < -F.S.hp*F.S.sp + F.S.hp - F.S.kp) (hQ : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp) (hD : 0 < -F.S.hp*F.S.sm*F.S.sp + F.S.hp*F.S.sm + F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm + F.S.kp)
    (hA : F.dep F.S.u_vRa4 0 < F.dep F.S.u_vRa4 6 ∨ F.dep F.S.u_vRa4 0 < F.dep F.S.u_vRa4 1 ∨ F.dep F.S.u_vRa4 4 < F.dep F.S.u_vRa4 6 ∨ F.dep F.S.u_vRa4 4 < F.dep F.S.u_vRa4 1) (hB : F.dep F.S.u_vRa4 6 < F.dep F.S.u_vRa4 0 ∨ F.dep F.S.u_vRa4 1 < F.dep F.S.u_vRa4 0 ∨ F.dep F.S.u_vRa4 6 < F.dep F.S.u_vRa4 4 ∨ F.dep F.S.u_vRa4 1 < F.dep F.S.u_vRa4 4) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  refine F.toFrame7.rim4 0 6 4 1 _ _ _ _ (F.ptC_0) (F.ptC_6) (F.ptC_4) (F.ptC_1) (-1) (Or.inr rfl) F.S.u_vRa4 F.S.w_vRa4 (Or.inl (by simp only [Shape20.u_vRa4]; intro h0; linarith [(mul_pos F.S.tp_pos hsp1), h0]))
    (vRa4_cyc F.S hW hQ hD) ?_ ?_ ?_
  · intro j' h0 h1 h2 h3
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd rfl h3
    · rw [F.ptC_2]; exact vRa4_rest2 F.S hW hQ hD
    · rw [F.ptC_3]; exact vRa4_rest3 F.S hW hQ hD
    · exact absurd rfl h2
    · rw [F.ptC_5]; exact vRa4_rest5 F.S hW hQ hD
    · exact absurd rfl h1
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using hA
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using hB

namespace Shape20
variable (S : Shape20)

/-- the view of `vRv` -/
def u_vRv : C3 := ⟨-S.sp*S.tp + S.tp, 0, -S.hp*S.sp + S.hp - S.kp⟩

/-- the tilt of `vRv` -/
def w_vRv (_ : Shape20) : C3 := ⟨0, -3, 0⟩

end Shape20

theorem vRv_cyc (S : Shape20) (hW : 0 < S.hp*S.sp - S.hp + S.kp) (hV : 0 < S.hm*S.sp*S.tp - S.hm*S.tp + S.hp*S.sp*S.tm - S.hp*S.tm + S.kp*S.tm) :
    Cyc4 (-1) S.u_vRv S.w_vRv (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRv, Shape20.w_vRv]; left; linarith [(mul_pos (mul_pos S.tp_pos hsp1) S.km_pos), (mul_pos (mul_pos S.tp_pos hsm1) S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRv, Shape20.w_vRv]; left; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRv, Shape20.w_vRv]; left; linarith [(mul_pos (mul_pos S.tp_pos hsp1) S.km_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRv, Shape20.w_vRv]; left; linarith [(mul_pos (mul_pos S.tp_pos hsp1) S.km_pos), (mul_pos (mul_pos S.tp_pos hsm1) S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRv, Shape20.w_vRv]; left; linarith [(mul_pos (mul_pos S.tp_pos S.sm_pos) S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRv, Shape20.w_vRv]; left; linarith [(mul_pos (mul_pos S.tp_pos hsp1) S.km_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRv, Shape20.w_vRv]; left; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRv, Shape20.w_vRv]; left; linarith [(mul_pos (mul_pos S.tp_pos S.sm_pos) S.kp_pos)])⟩

theorem vRv_rest1 (S : Shape20) (hW : 0 < S.hp*S.sp - S.hp + S.kp) (hV : 0 < S.hm*S.sp*S.tp - S.hm*S.tp + S.hp*S.sp*S.tm - S.hp*S.tm + S.kp*S.tm) :
    Rest4 (-1) S.u_vRv S.w_vRv (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ ⟨1, 0, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRv, Shape20.w_vRv]; left; linarith [rp]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRv, Shape20.w_vRv]; left; linarith [(mul_pos hsm1 hW), (mul_pos (mul_pos S.tp_pos hsp1) S.km_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRv, Shape20.w_vRv]; left; linarith [(mul_pos S.sm_pos hW)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRv, Shape20.w_vRv]; right; refine ⟨by ring, ?_⟩; linarith [S.hp_pos])⟩

theorem vRv_rest3 (S : Shape20) (hW : 0 < S.hp*S.sp - S.hp + S.kp) (hV : 0 < S.hm*S.sp*S.tp - S.hm*S.tp + S.hp*S.sp*S.tm - S.hp*S.tm + S.kp*S.tm) :
    Rest4 (-1) S.u_vRv S.w_vRv (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRv, Shape20.w_vRv]; left; linarith [rp, (mul_pos htm1 hW), (mul_pos (mul_pos S.tp_pos hsp1) S.hm_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRv, Shape20.w_vRv]; left; linarith [(mul_pos hsm1 hV), (mul_pos (mul_pos S.tp_pos hsp1) S.km_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRv, Shape20.w_vRv]; left; linarith [(mul_pos S.sm_pos hV)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRv, Shape20.w_vRv]; right; refine ⟨by ring, ?_⟩; linarith [(mul_pos S.tp_pos S.hm_pos), (mul_pos S.tm_pos S.hp_pos)])⟩

theorem vRv_rest2 (S : Shape20) (hW : 0 < S.hp*S.sp - S.hp + S.kp) (hV : 0 < S.hm*S.sp*S.tp - S.hm*S.tp + S.hp*S.sp*S.tm - S.hp*S.tm + S.kp*S.tm) :
    Rest4 (-1) S.u_vRv S.w_vRv (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRv, Shape20.w_vRv]; right; refine ⟨by ring, ?_⟩; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRv, Shape20.w_vRv]; left; linarith [(mul_pos (mul_pos (mul_pos S.tp_pos hsp1) hsp1) S.km_pos), (mul_pos (mul_pos (mul_pos S.tp_pos hsp1) hsm1) S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRv, Shape20.w_vRv]; left; linarith [(mul_pos (mul_pos (mul_pos S.tp_pos S.sp_pos) hsp1) S.km_pos), (mul_pos (mul_pos (mul_pos S.tp_pos hsp1) S.sm_pos) S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_vRv, Shape20.w_vRv]; left; linarith [(mul_pos (mul_pos S.tp_pos S.sp_pos) S.kp_pos)])⟩

/-- vRv -/
theorem Frame20.vRv {x : Fin 7 → ℝ³} (F : Frame20 x) (hW : 0 < F.S.hp*F.S.sp - F.S.hp + F.S.kp) (hV : 0 < F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.tm + F.S.kp*F.S.tm)
    (hA : F.dep F.S.u_vRv 0 < F.dep F.S.u_vRv 6 ∨ F.dep F.S.u_vRv 0 < F.dep F.S.u_vRv 5 ∨ F.dep F.S.u_vRv 4 < F.dep F.S.u_vRv 6 ∨ F.dep F.S.u_vRv 4 < F.dep F.S.u_vRv 5) (hB : F.dep F.S.u_vRv 6 < F.dep F.S.u_vRv 0 ∨ F.dep F.S.u_vRv 5 < F.dep F.S.u_vRv 0 ∨ F.dep F.S.u_vRv 6 < F.dep F.S.u_vRv 4 ∨ F.dep F.S.u_vRv 5 < F.dep F.S.u_vRv 4) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  refine F.toFrame7.rim4 0 6 4 5 _ _ _ _ (F.ptC_0) (F.ptC_6) (F.ptC_4) (F.ptC_5) (-1) (Or.inr rfl) F.S.u_vRv F.S.w_vRv (Or.inl (by simp only [Shape20.u_vRv]; intro h0; linarith [(mul_pos F.S.tp_pos hsp1), h0]))
    (vRv_cyc F.S hW hV) ?_ ?_ ?_
  · intro j' h0 h1 h2 h3
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [F.ptC_1]; exact vRv_rest1 F.S hW hV
    · rw [F.ptC_2]; exact vRv_rest2 F.S hW hV
    · rw [F.ptC_3]; exact vRv_rest3 F.S hW hV
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd rfl h1
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using hA
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using hB

namespace Shape20
variable (S : Shape20)

/-- the view of `tB` -/
def u_tB : C3 := ⟨S.tp, 0, S.hp⟩

/-- the tilt of `tB` -/
def w_tB (_ : Shape20) : C3 := ⟨0, 1, 0⟩

end Shape20

theorem tB_cyc (S : Shape20) (hB2 : 0 < -S.hm*S.tp - S.hp*S.tm + S.hp) (hB3 : 0 < -S.hp*S.sm + S.hp - S.km*S.tp) :
    Cyc4 1 S.u_tB S.w_tB (⟨S.tp, 0, S.hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tB, Shape20.w_tB]; left; linarith [S.hp_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tB, Shape20.w_tB]; left; linarith [(mul_pos S.sp_pos S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tB, Shape20.w_tB]; left; linarith [(mul_pos S.tp_pos S.kp_pos), (mul_pos hsp1 S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tB, Shape20.w_tB]; left; linarith [S.hp_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tB, Shape20.w_tB]; left; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tB, Shape20.w_tB]; left; linarith [(mul_pos S.tp_pos S.kp_pos), (mul_pos hsp1 S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tB, Shape20.w_tB]; left; linarith [(mul_pos S.sp_pos S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tB, Shape20.w_tB]; left; linarith [(mul_pos S.tp_pos S.kp_pos)])⟩

theorem tB_rest4 (S : Shape20) (hB2 : 0 < -S.hm*S.tp - S.hp*S.tm + S.hp) (hB3 : 0 < -S.hp*S.sm + S.hp - S.km*S.tp) :
    Rest4 1 S.u_tB S.w_tB (⟨S.tp, 0, S.hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨0, S.sm, -S.km⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tB, Shape20.w_tB]; left; linarith [(mul_pos S.sm_pos S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tB, Shape20.w_tB]; left; linarith [hB3]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tB, Shape20.w_tB]; left; linarith [(mul_pos (mul_pos S.tp_pos hsp1) S.km_pos), (mul_pos (mul_pos S.tp_pos hsm1) S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tB, Shape20.w_tB]; left; linarith [(mul_pos (mul_pos S.tp_pos S.sp_pos) S.km_pos), (mul_pos (mul_pos S.tp_pos S.sm_pos) S.kp_pos)])⟩

theorem tB_rest5 (S : Shape20) (hB2 : 0 < -S.hm*S.tp - S.hp*S.tm + S.hp) (hB3 : 0 < -S.hp*S.sm + S.hp - S.km*S.tp) :
    Rest4 1 S.u_tB S.w_tB (⟨S.tp, 0, S.hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨0, 0, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tB, Shape20.w_tB]; right; refine ⟨by ring, ?_⟩; linarith [S.hp_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tB, Shape20.w_tB]; left; linarith [S.hp_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tB, Shape20.w_tB]; left; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tB, Shape20.w_tB]; right; refine ⟨by ring, ?_⟩; linarith [(mul_pos S.tp_pos S.kp_pos)])⟩

theorem tB_rest3 (S : Shape20) (hB2 : 0 < -S.hm*S.tp - S.hp*S.tm + S.hp) (hB3 : 0 < -S.hp*S.sm + S.hp - S.km*S.tp) :
    Rest4 1 S.u_tB S.w_tB (⟨S.tp, 0, S.hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tm, 0, -S.hm⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tB, Shape20.w_tB]; right; refine ⟨by ring, ?_⟩; linarith [(mul_pos htp1 S.hm_pos), (mul_pos htm1 S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tB, Shape20.w_tB]; left; linarith [hB2]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tB, Shape20.w_tB]; left; linarith [(mul_pos S.tp_pos S.kp_pos), (mul_pos (mul_pos S.tp_pos hsp1) S.hm_pos), (mul_pos (mul_pos S.tm_pos hsp1) S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tB, Shape20.w_tB]; left; linarith [(mul_pos (mul_pos S.tp_pos S.sp_pos) S.hm_pos), (mul_pos (mul_pos S.tm_pos S.sp_pos) S.hp_pos)])⟩

/-- tB -/
theorem Frame20.tB {x : Fin 7 → ℝ³} (F : Frame20 x) (hB2 : 0 < -F.S.hm*F.S.tp - F.S.hp*F.S.tm + F.S.hp) (hB3 : 0 < -F.S.hp*F.S.sm + F.S.hp - F.S.km*F.S.tp)
    (hA : F.dep F.S.u_tB 0 < F.dep F.S.u_tB 1 ∨ F.dep F.S.u_tB 0 < F.dep F.S.u_tB 2 ∨ F.dep F.S.u_tB 6 < F.dep F.S.u_tB 1 ∨ F.dep F.S.u_tB 6 < F.dep F.S.u_tB 2) (hB : F.dep F.S.u_tB 1 < F.dep F.S.u_tB 0 ∨ F.dep F.S.u_tB 2 < F.dep F.S.u_tB 0 ∨ F.dep F.S.u_tB 1 < F.dep F.S.u_tB 6 ∨ F.dep F.S.u_tB 2 < F.dep F.S.u_tB 6) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  refine F.toFrame7.rim4 0 1 6 2 _ _ _ _ (F.ptC_0) (F.ptC_1) (F.ptC_6) (F.ptC_2) 1 (Or.inl rfl) F.S.u_tB F.S.w_tB (Or.inl (by simp only [Shape20.u_tB]; intro h0; linarith [F.S.tp_pos, h0]))
    (tB_cyc F.S hB2 hB3) ?_ ?_ ?_
  · intro j' h0 h1 h2 h3
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd rfl h1
    · exact absurd rfl h3
    · rw [F.ptC_3]; exact tB_rest3 F.S hB2 hB3
    · rw [F.ptC_4]; exact tB_rest4 F.S hB2 hB3
    · rw [F.ptC_5]; exact tB_rest5 F.S hB2 hB3
    · exact absurd rfl h2
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using hA
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using hB

namespace Shape20
variable (S : Shape20)

/-- the view of `xX` -/
def u_xX : C3 := ⟨S.hm*S.tp - S.hm + S.hp*S.sm*S.tm - S.hp*S.sm + S.km*S.tm*S.tp - S.km*S.tm - S.km*S.tp + S.km, -S.hm*S.sm*S.tp + S.hm*S.sm - S.hp*S.sm*S.tm + S.hp*S.sm, -S.hm*S.hp*S.sm + S.hm*S.hp + S.hp*S.km*S.tm - S.hp*S.km⟩

/-- the tilt of `xX` -/
def w_xX (_ : Shape20) : C3 := ⟨0, 0, -3⟩

end Shape20

theorem xX_cyc (S : Shape20) (hA3 : 0 < S.hm*S.sm*S.tp - S.hm + S.hp*S.sm*S.tm - S.hp*S.sm - S.km*S.tm + S.km) (hBm : 0 < -S.hm*S.tp + S.hm - S.hp*S.tm) (hCm : 0 < S.hp*S.sm + S.km*S.tp - S.km) :
    Cyc5 1 S.u_xX S.w_xX (⟨1, 0, 0⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨0, 1, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos S.sm_pos S.hp_pos) S.hm_pos), (mul_pos (mul_pos S.sm_pos S.hm_pos) hBm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos (mul_pos htp1 S.sp_pos) S.hm_pos) rm), (mul_pos (mul_pos (mul_pos htm1 S.sp_pos) S.hp_pos) rm), (mul_pos (mul_pos (mul_pos htm1 S.sm_pos) S.hp_pos) S.kp_pos), (mul_pos (mul_pos (mul_pos htm1 S.sm_pos) S.kp_pos) hBm), (mul_pos (mul_pos (mul_pos hsp1 S.sm_pos) S.hp_pos) S.hm_pos), (mul_pos (mul_pos (mul_pos hsp1 S.sm_pos) S.hm_pos) hBm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos S.hp_pos rm), (mul_pos rm hBm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos (mul_pos htp1 S.sp_pos) S.hm_pos) S.hm_pos), (mul_pos (mul_pos (mul_pos S.tm_pos S.sp_pos) S.hp_pos) rm), (mul_pos (mul_pos (mul_pos S.tm_pos S.sm_pos) S.hp_pos) S.kp_pos), (mul_pos (mul_pos (mul_pos S.tm_pos S.sm_pos) S.kp_pos) hBm), (mul_pos (mul_pos (mul_pos htm1 S.sp_pos) S.hm_pos) hCm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos htp1 S.hm_pos) S.hm_pos), (mul_pos (mul_pos S.tm_pos S.hp_pos) rm), (mul_pos (mul_pos htm1 S.hm_pos) hCm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos S.sm_pos S.hp_pos) S.hm_pos), (mul_pos (mul_pos S.sm_pos S.hm_pos) hBm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos htp1 S.hm_pos) S.kp_pos), (mul_pos (mul_pos htm1 S.kp_pos) hCm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos S.sp_pos S.hp_pos) rm), (mul_pos (mul_pos S.sm_pos S.hp_pos) S.kp_pos), (mul_pos (mul_pos S.sm_pos S.kp_pos) hBm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos (mul_pos htp1 S.sp_pos) S.hm_pos) S.hm_pos), (mul_pos (mul_pos (mul_pos S.tm_pos S.sp_pos) S.hp_pos) rm), (mul_pos (mul_pos (mul_pos S.tm_pos S.sm_pos) S.hp_pos) S.kp_pos), (mul_pos (mul_pos (mul_pos S.tm_pos S.sm_pos) S.kp_pos) hBm), (mul_pos (mul_pos (mul_pos htm1 S.sp_pos) S.hm_pos) hCm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos rp rm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos S.tm_pos rp) rm), (mul_pos (mul_pos (mul_pos htp1 htm1) S.hm_pos) S.kp_pos), (mul_pos (mul_pos (mul_pos htp1 hsp1) S.hm_pos) S.hm_pos), (mul_pos (mul_pos (mul_pos htm1 htm1) S.kp_pos) hCm), (mul_pos (mul_pos (mul_pos htm1 hsp1) S.hm_pos) hCm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos htp1 S.hm_pos) S.kp_pos), (mul_pos (mul_pos htm1 S.kp_pos) hCm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos S.hp_pos rm), (mul_pos rm hBm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos S.hp_pos rm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos rp rm)])⟩

theorem xX_rest0 (S : Shape20) (hA3 : 0 < S.hm*S.sm*S.tp - S.hm + S.hp*S.sm*S.tm - S.hp*S.sm - S.km*S.tm + S.km) (hBm : 0 < -S.hm*S.tp + S.hm - S.hp*S.tm) (hCm : 0 < S.hp*S.sm + S.km*S.tp - S.km) :
    Rest5 1 S.u_xX S.w_xX (⟨1, 0, 0⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos S.sm_pos S.hp_pos) S.hp_pos), (mul_pos (mul_pos S.sm_pos S.hp_pos) hBm), (mul_pos (mul_pos S.sm_pos hBm) hBm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos hA3 hBm), (mul_pos (mul_pos htp1 S.hm_pos) S.hm_pos), (mul_pos (mul_pos S.tm_pos S.hp_pos) rm), (mul_pos (mul_pos htm1 S.hm_pos) hCm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos htp1 S.hm_pos) S.kp_pos), (mul_pos (mul_pos htp1 S.kp_pos) hA3), (mul_pos (mul_pos htm1 S.kp_pos) hCm), (mul_pos (mul_pos S.sp_pos S.hp_pos) hA3)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos rp hA3)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; right; refine ⟨by ring, ?_⟩; linarith [htp1])⟩

theorem xX_rest4 (S : Shape20) (hA3 : 0 < S.hm*S.sm*S.tp - S.hm + S.hp*S.sm*S.tm - S.hp*S.sm - S.km*S.tm + S.km) (hBm : 0 < -S.hm*S.tp + S.hm - S.hp*S.tm) (hCm : 0 < S.hp*S.sm + S.km*S.tp - S.km) :
    Rest5 1 S.u_xX S.w_xX (⟨1, 0, 0⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; right; refine ⟨by ring, ?_⟩; linarith [(mul_pos htm1 S.sm_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos S.sm_pos S.hm_pos) hBm), (mul_pos (mul_pos S.sm_pos S.hm_pos) hCm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos (mul_pos htp1 S.sp_pos) S.hm_pos) S.km_pos), (mul_pos (mul_pos (mul_pos htp1 S.sm_pos) S.hm_pos) S.kp_pos), (mul_pos (mul_pos (mul_pos htm1 S.sp_pos) S.km_pos) hCm), (mul_pos (mul_pos (mul_pos htm1 S.sm_pos) S.kp_pos) hCm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos (mul_pos htp1 hsp1) S.hm_pos) S.km_pos), (mul_pos (mul_pos (mul_pos htp1 hsm1) S.hm_pos) S.kp_pos), (mul_pos (mul_pos (mul_pos htm1 hsp1) S.km_pos) hCm), (mul_pos (mul_pos (mul_pos htm1 hsm1) S.kp_pos) hCm)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_xX, Shape20.w_xX]; left; linarith [(mul_pos (mul_pos htp1 S.km_pos) rm), (mul_pos (mul_pos hsm1 S.hp_pos) rm)])⟩

/-- xX -/
theorem Frame20.xX {x : Fin 7 → ℝ³} (F : Frame20 x) (hA3 : 0 < F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km) (hBm : 0 < -F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.tm) (hCm : 0 < F.S.hp*F.S.sm + F.S.km*F.S.tp - F.S.km)
    (h0 : F.dep F.S.u_xX 1 < F.dep F.S.u_xX 6 ∨ F.dep F.S.u_xX 1 < F.dep F.S.u_xX 3 ∨ F.dep F.S.u_xX 5 < F.dep F.S.u_xX 3 ∨ F.dep F.S.u_xX 5 < F.dep F.S.u_xX 2) (h1 : F.dep F.S.u_xX 3 < F.dep F.S.u_xX 1 ∨ F.dep F.S.u_xX 3 < F.dep F.S.u_xX 5 ∨ F.dep F.S.u_xX 2 < F.dep F.S.u_xX 5 ∨ F.dep F.S.u_xX 2 < F.dep F.S.u_xX 6) (h2 : F.dep F.S.u_xX 5 < F.dep F.S.u_xX 3 ∨ F.dep F.S.u_xX 5 < F.dep F.S.u_xX 2 ∨ F.dep F.S.u_xX 6 < F.dep F.S.u_xX 2 ∨ F.dep F.S.u_xX 6 < F.dep F.S.u_xX 1) (h3 : F.dep F.S.u_xX 2 < F.dep F.S.u_xX 5 ∨ F.dep F.S.u_xX 2 < F.dep F.S.u_xX 6 ∨ F.dep F.S.u_xX 1 < F.dep F.S.u_xX 6 ∨ F.dep F.S.u_xX 1 < F.dep F.S.u_xX 3) (h4 : F.dep F.S.u_xX 6 < F.dep F.S.u_xX 2 ∨ F.dep F.S.u_xX 6 < F.dep F.S.u_xX 1 ∨ F.dep F.S.u_xX 3 < F.dep F.S.u_xX 1 ∨ F.dep F.S.u_xX 3 < F.dep F.S.u_xX 5) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  refine F.toFrame7.rim5p 1 3 5 2 6 _ _ _ _ _ (F.ptC_1) (F.ptC_3) (F.ptC_5) (F.ptC_2) (F.ptC_6) 1 (Or.inl rfl) F.S.u_xX F.S.w_xX (Or.inl (by simp only [Shape20.u_xX]; intro h0; linarith [(mul_pos htp1 F.S.hm_pos), (mul_pos htm1 hCm), h0]))
    (xX_cyc F.S hA3 hBm hCm) ?_ ?_ ?_ ?_ ?_ ?_
  · intro j' h0 h1 h2 h3 h4
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [F.ptC_0]; exact xX_rest0 F.S hA3 hBm hCm
    · exact absurd rfl h0
    · exact absurd rfl h3
    · exact absurd rfl h1
    · rw [F.ptC_4]; exact xX_rest4 F.S hA3 hBm hCm
    · exact absurd rfl h2
    · exact absurd rfl h4
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h0
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h1
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h2
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h3
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h4

namespace Shape20
variable (S : Shape20)

/-- the view of `yY` -/
def u_yY : C3 := ⟨S.tp, -1, S.hp⟩

/-- the tilt of `yY` -/
def w_yY (_ : Shape20) : C3 := ⟨0, 1, 0⟩

end Shape20

theorem yY_cyc (S : Shape20) (hA2 : 0 < S.hm*S.sm*S.tp + S.hp*S.sm*S.tm - S.km*S.tm) (hA3 : 0 < -S.hm*S.sm*S.tp + S.hm - S.hp*S.sm*S.tm + S.hp*S.sm + S.km*S.tm - S.km) :
    Cyc5 1 S.u_yY S.w_yY (⟨1, 0, 0⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [rp]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [S.hp_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [(mul_pos htp1 S.hm_pos), (mul_pos htm1 S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [(mul_pos S.tm_pos rp), (mul_pos (mul_pos S.tp_pos htm1) S.kp_pos), (mul_pos (mul_pos S.tp_pos hsp1) S.hm_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [rp]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [(mul_pos S.tm_pos S.kp_pos), (mul_pos (mul_pos S.tp_pos S.sp_pos) S.hm_pos), (mul_pos (mul_pos S.tm_pos S.sp_pos) S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [S.kp_pos, (mul_pos S.sp_pos S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [S.hm_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [(mul_pos S.tp_pos S.hm_pos), (mul_pos S.tm_pos S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [(mul_pos S.tm_pos S.kp_pos), (mul_pos (mul_pos S.tp_pos S.sp_pos) S.hm_pos), (mul_pos (mul_pos S.tm_pos S.sp_pos) S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [(mul_pos htp1 S.hm_pos), (mul_pos htm1 S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [(mul_pos htp1 S.hm_pos), (mul_pos htm1 S.kp_pos), (mul_pos (mul_pos S.tp_pos hsp1) S.hm_pos), (mul_pos (mul_pos htm1 S.sp_pos) S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [S.hm_pos])⟩

theorem yY_rest0 (S : Shape20) (hA2 : 0 < S.hm*S.sm*S.tp + S.hp*S.sm*S.tm - S.km*S.tm) (hA3 : 0 < -S.hm*S.sm*S.tp + S.hm - S.hp*S.sm*S.tm + S.hp*S.sm + S.km*S.tm - S.km) :
    Rest5 1 S.u_yY S.w_yY (⟨1, 0, 0⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨S.tp, 0, S.hp⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; right; refine ⟨by ring, ?_⟩; linarith [S.hp_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; right; refine ⟨by ring, ?_⟩; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [(mul_pos S.tp_pos S.hm_pos), (mul_pos S.tm_pos S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [(mul_pos htp1 S.hm_pos), (mul_pos htm1 S.hp_pos)])⟩

theorem yY_rest4 (S : Shape20) (hA2 : 0 < S.hm*S.sm*S.tp + S.hp*S.sm*S.tm - S.km*S.tm) (hA3 : 0 < -S.hm*S.sm*S.tp + S.hm - S.hp*S.sm*S.tm + S.hp*S.sm + S.km*S.tm - S.km) :
    Rest5 1 S.u_yY S.w_yY (⟨1, 0, 0⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [(mul_pos htp1 S.km_pos), (mul_pos hsm1 S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [(mul_pos (mul_pos S.tp_pos hsp1) S.km_pos), (mul_pos (mul_pos S.tp_pos hsm1) S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [(mul_pos (mul_pos S.tp_pos S.sp_pos) S.km_pos), (mul_pos (mul_pos S.tp_pos S.sm_pos) S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [hA2]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yY, Shape20.w_yY]; left; linarith [hA3])⟩

/-- yY -/
theorem Frame20.yY {x : Fin 7 → ℝ³} (F : Frame20 x) (hA2 : 0 < F.S.hm*F.S.sm*F.S.tp + F.S.hp*F.S.sm*F.S.tm - F.S.km*F.S.tm) (hA3 : 0 < -F.S.hm*F.S.sm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm + F.S.km*F.S.tm - F.S.km)
    (h0 : F.dep F.S.u_yY 1 < F.dep F.S.u_yY 3 ∨ F.dep F.S.u_yY 1 < F.dep F.S.u_yY 6 ∨ F.dep F.S.u_yY 2 < F.dep F.S.u_yY 6 ∨ F.dep F.S.u_yY 2 < F.dep F.S.u_yY 5) (h1 : F.dep F.S.u_yY 6 < F.dep F.S.u_yY 1 ∨ F.dep F.S.u_yY 6 < F.dep F.S.u_yY 2 ∨ F.dep F.S.u_yY 5 < F.dep F.S.u_yY 2 ∨ F.dep F.S.u_yY 5 < F.dep F.S.u_yY 3) (h2 : F.dep F.S.u_yY 2 < F.dep F.S.u_yY 6 ∨ F.dep F.S.u_yY 2 < F.dep F.S.u_yY 5 ∨ F.dep F.S.u_yY 3 < F.dep F.S.u_yY 5 ∨ F.dep F.S.u_yY 3 < F.dep F.S.u_yY 1) (h3 : F.dep F.S.u_yY 5 < F.dep F.S.u_yY 2 ∨ F.dep F.S.u_yY 5 < F.dep F.S.u_yY 3 ∨ F.dep F.S.u_yY 1 < F.dep F.S.u_yY 3 ∨ F.dep F.S.u_yY 1 < F.dep F.S.u_yY 6) (h4 : F.dep F.S.u_yY 3 < F.dep F.S.u_yY 5 ∨ F.dep F.S.u_yY 3 < F.dep F.S.u_yY 1 ∨ F.dep F.S.u_yY 6 < F.dep F.S.u_yY 1 ∨ F.dep F.S.u_yY 6 < F.dep F.S.u_yY 2) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  refine F.toFrame7.rim5p 1 6 2 5 3 _ _ _ _ _ (F.ptC_1) (F.ptC_6) (F.ptC_2) (F.ptC_5) (F.ptC_3) 1 (Or.inl rfl) F.S.u_yY F.S.w_yY (Or.inl (by simp only [Shape20.u_yY]; intro h0; linarith [F.S.tp_pos, h0]))
    (yY_cyc F.S hA2 hA3) ?_ ?_ ?_ ?_ ?_ ?_
  · intro j' h0 h1 h2 h3 h4
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [F.ptC_0]; exact yY_rest0 F.S hA2 hA3
    · exact absurd rfl h0
    · exact absurd rfl h2
    · exact absurd rfl h4
    · rw [F.ptC_4]; exact yY_rest4 F.S hA2 hA3
    · exact absurd rfl h3
    · exact absurd rfl h1
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h0
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h1
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h2
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h3
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h4

namespace Shape20
variable (S : Shape20)

/-- the view of `yT2` -/
def u_yT2 : C3 := ⟨S.tp, -1, S.hp⟩

/-- the tilt of `yT2` -/
def w_yT2 (_ : Shape20) : C3 := ⟨0, -3, 0⟩

end Shape20

theorem yT2_cyc (S : Shape20) (hA2 : 0 < S.hm*S.sm*S.tp + S.hp*S.sm*S.tm - S.km*S.tm) (hA3 : 0 < -S.hm*S.sm*S.tp + S.hm - S.hp*S.sm*S.tm + S.hp*S.sm + S.km*S.tm - S.km) :
    Cyc5 1 S.u_yT2 S.w_yT2 (⟨1, 0, 0⟩ : C3) ⟨S.tp, 0, S.hp⟩ ⟨0, S.sp, S.kp⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [rp]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [S.hp_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [(mul_pos htp1 S.hm_pos), (mul_pos htm1 S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [(mul_pos S.tm_pos rp), (mul_pos (mul_pos S.tp_pos htm1) S.kp_pos), (mul_pos (mul_pos S.tp_pos hsp1) S.hm_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [rp]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [(mul_pos S.tm_pos S.kp_pos), (mul_pos (mul_pos S.tp_pos S.sp_pos) S.hm_pos), (mul_pos (mul_pos S.tm_pos S.sp_pos) S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [S.kp_pos, (mul_pos S.sp_pos S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [S.hm_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [(mul_pos S.tp_pos S.hm_pos), (mul_pos S.tm_pos S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [(mul_pos S.tm_pos S.kp_pos), (mul_pos (mul_pos S.tp_pos S.sp_pos) S.hm_pos), (mul_pos (mul_pos S.tm_pos S.sp_pos) S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [(mul_pos htp1 S.hm_pos), (mul_pos htm1 S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [(mul_pos htp1 S.hm_pos), (mul_pos htm1 S.kp_pos), (mul_pos (mul_pos S.tp_pos hsp1) S.hm_pos), (mul_pos (mul_pos htm1 S.sp_pos) S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [S.hm_pos])⟩

theorem yT2_rest6 (S : Shape20) (hA2 : 0 < S.hm*S.sm*S.tp + S.hp*S.sm*S.tm - S.km*S.tm) (hA3 : 0 < -S.hm*S.sm*S.tp + S.hm - S.hp*S.sm*S.tm + S.hp*S.sm + S.km*S.tm - S.km) :
    Rest5 1 S.u_yT2 S.w_yT2 (⟨1, 0, 0⟩ : C3) ⟨S.tp, 0, S.hp⟩ ⟨0, S.sp, S.kp⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; right; refine ⟨by ring, ?_⟩; linarith [S.hp_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; right; refine ⟨by ring, ?_⟩; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [(mul_pos S.tp_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [(mul_pos S.tp_pos S.hm_pos), (mul_pos S.tm_pos S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [(mul_pos htp1 S.hm_pos), (mul_pos htm1 S.hp_pos)])⟩

theorem yT2_rest4 (S : Shape20) (hA2 : 0 < S.hm*S.sm*S.tp + S.hp*S.sm*S.tm - S.km*S.tm) (hA3 : 0 < -S.hm*S.sm*S.tp + S.hm - S.hp*S.sm*S.tm + S.hp*S.sm + S.km*S.tm - S.km) :
    Rest5 1 S.u_yT2 S.w_yT2 (⟨1, 0, 0⟩ : C3) ⟨S.tp, 0, S.hp⟩ ⟨0, S.sp, S.kp⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [(mul_pos htp1 S.km_pos), (mul_pos hsm1 S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [(mul_pos (mul_pos S.tp_pos hsp1) S.km_pos), (mul_pos (mul_pos S.tp_pos hsm1) S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [(mul_pos (mul_pos S.tp_pos S.sp_pos) S.km_pos), (mul_pos (mul_pos S.tp_pos S.sm_pos) S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [hA2]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_yT2, Shape20.w_yT2]; left; linarith [hA3])⟩

/-- yT2 -/
theorem Frame20.yT2 {x : Fin 7 → ℝ³} (F : Frame20 x) (hA2 : 0 < F.S.hm*F.S.sm*F.S.tp + F.S.hp*F.S.sm*F.S.tm - F.S.km*F.S.tm) (hA3 : 0 < -F.S.hm*F.S.sm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm + F.S.km*F.S.tm - F.S.km)
    (h0 : F.dep F.S.u_yT2 1 < F.dep F.S.u_yT2 3 ∨ F.dep F.S.u_yT2 1 < F.dep F.S.u_yT2 0 ∨ F.dep F.S.u_yT2 2 < F.dep F.S.u_yT2 0 ∨ F.dep F.S.u_yT2 2 < F.dep F.S.u_yT2 5) (h1 : F.dep F.S.u_yT2 0 < F.dep F.S.u_yT2 1 ∨ F.dep F.S.u_yT2 0 < F.dep F.S.u_yT2 2 ∨ F.dep F.S.u_yT2 5 < F.dep F.S.u_yT2 2 ∨ F.dep F.S.u_yT2 5 < F.dep F.S.u_yT2 3) (h2 : F.dep F.S.u_yT2 2 < F.dep F.S.u_yT2 0 ∨ F.dep F.S.u_yT2 2 < F.dep F.S.u_yT2 5 ∨ F.dep F.S.u_yT2 3 < F.dep F.S.u_yT2 5 ∨ F.dep F.S.u_yT2 3 < F.dep F.S.u_yT2 1) (h3 : F.dep F.S.u_yT2 5 < F.dep F.S.u_yT2 2 ∨ F.dep F.S.u_yT2 5 < F.dep F.S.u_yT2 3 ∨ F.dep F.S.u_yT2 1 < F.dep F.S.u_yT2 3 ∨ F.dep F.S.u_yT2 1 < F.dep F.S.u_yT2 0) (h4 : F.dep F.S.u_yT2 3 < F.dep F.S.u_yT2 5 ∨ F.dep F.S.u_yT2 3 < F.dep F.S.u_yT2 1 ∨ F.dep F.S.u_yT2 0 < F.dep F.S.u_yT2 1 ∨ F.dep F.S.u_yT2 0 < F.dep F.S.u_yT2 2) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  refine F.toFrame7.rim5p 1 0 2 5 3 _ _ _ _ _ (F.ptC_1) (F.ptC_0) (F.ptC_2) (F.ptC_5) (F.ptC_3) 1 (Or.inl rfl) F.S.u_yT2 F.S.w_yT2 (Or.inl (by simp only [Shape20.u_yT2]; intro h0; linarith [F.S.tp_pos, h0]))
    (yT2_cyc F.S hA2 hA3) ?_ ?_ ?_ ?_ ?_ ?_
  · intro j' h0 h1 h2 h3 h4
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h1
    · exact absurd rfl h0
    · exact absurd rfl h2
    · exact absurd rfl h4
    · rw [F.ptC_4]; exact yT2_rest4 F.S hA2 hA3
    · exact absurd rfl h3
    · rw [F.ptC_6]; exact yT2_rest6 F.S hA2 hA3
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h0
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h1
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h2
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h3
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h4

namespace Shape20
variable (S : Shape20)

/-- the view of `eXb` -/
def u_eXb (_ : Shape20) : C3 := ⟨1, -1, 0⟩

/-- the tilt of `eXb` -/
def w_eXb (_ : Shape20) : C3 := ⟨1, 0, 0⟩

end Shape20

theorem eXb_cyc (S : Shape20) (hEa : 0 < S.hp*S.sp - S.kp*S.tp) (hEb : 0 < -S.hm*S.sm + S.km*S.tm) :
    Cyc4 1 S.u_eXb S.w_eXb (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXb, Shape20.w_eXb]; left; linarith [(mul_pos S.tp_pos S.km_pos), (mul_pos S.sm_pos S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXb, Shape20.w_eXb]; left; linarith [S.hp_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXb, Shape20.w_eXb]; left; linarith [S.km_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXb, Shape20.w_eXb]; left; linarith [(mul_pos S.tp_pos S.km_pos), (mul_pos S.sm_pos S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXb, Shape20.w_eXb]; left; linarith [(mul_pos htp1 S.km_pos), (mul_pos hsm1 S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXb, Shape20.w_eXb]; left; linarith [S.km_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXb, Shape20.w_eXb]; left; linarith [S.hp_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXb, Shape20.w_eXb]; left; linarith [(mul_pos htp1 S.km_pos), (mul_pos hsm1 S.hp_pos)])⟩

theorem eXb_rest1 (S : Shape20) (hEa : 0 < S.hp*S.sp - S.kp*S.tp) (hEb : 0 < -S.hm*S.sm + S.km*S.tm) :
    Rest4 1 S.u_eXb S.w_eXb (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXb, Shape20.w_eXb]; left; linarith [S.hp_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXb, Shape20.w_eXb]; left; linarith [S.km_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXb, Shape20.w_eXb]; right; refine ⟨by ring, ?_⟩; linarith [S.km_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXb, Shape20.w_eXb]; right; refine ⟨by ring, ?_⟩; linarith [S.hp_pos])⟩

theorem eXb_rest2 (S : Shape20) (hEa : 0 < S.hp*S.sp - S.kp*S.tp) (hEb : 0 < -S.hm*S.sm + S.km*S.tm) :
    Rest4 1 S.u_eXb S.w_eXb (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXb, Shape20.w_eXb]; left; linarith [hEa]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXb, Shape20.w_eXb]; left; linarith [(mul_pos S.sp_pos S.km_pos), (mul_pos S.sm_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXb, Shape20.w_eXb]; left; linarith [(mul_pos hsp1 S.km_pos), (mul_pos hsm1 S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXb, Shape20.w_eXb]; left; linarith [rp])⟩

theorem eXb_rest3 (S : Shape20) (hEa : 0 < S.hp*S.sp - S.kp*S.tp) (hEb : 0 < -S.hm*S.sm + S.km*S.tm) :
    Rest4 1 S.u_eXb S.w_eXb (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tm, 0, -S.hm⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXb, Shape20.w_eXb]; left; linarith [(mul_pos S.tp_pos S.hm_pos), (mul_pos S.tm_pos S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXb, Shape20.w_eXb]; left; linarith [hEb]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXb, Shape20.w_eXb]; left; linarith [rm]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXb, Shape20.w_eXb]; left; linarith [(mul_pos htp1 S.hm_pos), (mul_pos htm1 S.hp_pos)])⟩

/-- eXb -/
theorem Frame20.eXb {x : Fin 7 → ℝ³} (F : Frame20 x) (hEa : 0 < F.S.hp*F.S.sp - F.S.kp*F.S.tp) (hEb : 0 < -F.S.hm*F.S.sm + F.S.km*F.S.tm)
    (hA : F.dep F.S.u_eXb 0 < F.dep F.S.u_eXb 5 ∨ F.dep F.S.u_eXb 0 < F.dep F.S.u_eXb 6 ∨ F.dep F.S.u_eXb 4 < F.dep F.S.u_eXb 5 ∨ F.dep F.S.u_eXb 4 < F.dep F.S.u_eXb 6) (hB : F.dep F.S.u_eXb 5 < F.dep F.S.u_eXb 0 ∨ F.dep F.S.u_eXb 6 < F.dep F.S.u_eXb 0 ∨ F.dep F.S.u_eXb 5 < F.dep F.S.u_eXb 4 ∨ F.dep F.S.u_eXb 6 < F.dep F.S.u_eXb 4) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  refine F.toFrame7.rim4 0 5 4 6 _ _ _ _ (F.ptC_0) (F.ptC_5) (F.ptC_4) (F.ptC_6) 1 (Or.inl rfl) F.S.u_eXb F.S.w_eXb (Or.inl (by simp only [Shape20.u_eXb]; intro h0; linarith [F.S.tp_pos, htp1, h0]))
    (eXb_cyc F.S hEa hEb) ?_ ?_ ?_
  · intro j' h0 h1 h2 h3
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [F.ptC_1]; exact eXb_rest1 F.S hEa hEb
    · rw [F.ptC_2]; exact eXb_rest2 F.S hEa hEb
    · rw [F.ptC_3]; exact eXb_rest3 F.S hEa hEb
    · exact absurd rfl h2
    · exact absurd rfl h1
    · exact absurd rfl h3
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using hA
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using hB

namespace Shape20
variable (S : Shape20)

/-- the view of `eXa` -/
def u_eXa (_ : Shape20) : C3 := ⟨1, -1, 0⟩

/-- the tilt of `eXa` -/
def w_eXa (_ : Shape20) : C3 := ⟨-3, 0, 0⟩

end Shape20

theorem eXa_cyc (S : Shape20) (hEa : 0 < S.hp*S.sp - S.kp*S.tp) (hEb : 0 < -S.hm*S.sm + S.km*S.tm) :
    Cyc4 1 S.u_eXa S.w_eXa (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨1, 0, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXa, Shape20.w_eXa]; left; linarith [(mul_pos S.tp_pos S.km_pos), (mul_pos S.sm_pos S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXa, Shape20.w_eXa]; left; linarith [S.hp_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXa, Shape20.w_eXa]; left; linarith [S.km_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXa, Shape20.w_eXa]; left; linarith [(mul_pos S.tp_pos S.km_pos), (mul_pos S.sm_pos S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXa, Shape20.w_eXa]; left; linarith [(mul_pos htp1 S.km_pos), (mul_pos hsm1 S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXa, Shape20.w_eXa]; left; linarith [S.km_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXa, Shape20.w_eXa]; left; linarith [S.hp_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXa, Shape20.w_eXa]; left; linarith [(mul_pos htp1 S.km_pos), (mul_pos hsm1 S.hp_pos)])⟩

theorem eXa_rest6 (S : Shape20) (hEa : 0 < S.hp*S.sp - S.kp*S.tp) (hEb : 0 < -S.hm*S.sm + S.km*S.tm) :
    Rest4 1 S.u_eXa S.w_eXa (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXa, Shape20.w_eXa]; left; linarith [S.hp_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXa, Shape20.w_eXa]; left; linarith [S.km_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXa, Shape20.w_eXa]; right; refine ⟨by ring, ?_⟩; linarith [S.km_pos]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXa, Shape20.w_eXa]; right; refine ⟨by ring, ?_⟩; linarith [S.hp_pos])⟩

theorem eXa_rest2 (S : Shape20) (hEa : 0 < S.hp*S.sp - S.kp*S.tp) (hEb : 0 < -S.hm*S.sm + S.km*S.tm) :
    Rest4 1 S.u_eXa S.w_eXa (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨1, 0, 0⟩ ⟨0, S.sp, S.kp⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXa, Shape20.w_eXa]; left; linarith [hEa]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXa, Shape20.w_eXa]; left; linarith [(mul_pos S.sp_pos S.km_pos), (mul_pos S.sm_pos S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXa, Shape20.w_eXa]; left; linarith [(mul_pos hsp1 S.km_pos), (mul_pos hsm1 S.kp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXa, Shape20.w_eXa]; left; linarith [rp])⟩

theorem eXa_rest3 (S : Shape20) (hEa : 0 < S.hp*S.sp - S.kp*S.tp) (hEb : 0 < -S.hm*S.sm + S.km*S.tm) :
    Rest4 1 S.u_eXa S.w_eXa (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨1, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨(by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXa, Shape20.w_eXa]; left; linarith [(mul_pos S.tp_pos S.hm_pos), (mul_pos S.tm_pos S.hp_pos)]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXa, Shape20.w_eXa]; left; linarith [hEb]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXa, Shape20.w_eXa]; left; linarith [rm]),
    (by simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_eXa, Shape20.w_eXa]; left; linarith [(mul_pos htp1 S.hm_pos), (mul_pos htm1 S.hp_pos)])⟩

/-- eXa -/
theorem Frame20.eXa {x : Fin 7 → ℝ³} (F : Frame20 x) (hEa : 0 < F.S.hp*F.S.sp - F.S.kp*F.S.tp) (hEb : 0 < -F.S.hm*F.S.sm + F.S.km*F.S.tm)
    (hA : F.dep F.S.u_eXa 0 < F.dep F.S.u_eXa 5 ∨ F.dep F.S.u_eXa 0 < F.dep F.S.u_eXa 1 ∨ F.dep F.S.u_eXa 4 < F.dep F.S.u_eXa 5 ∨ F.dep F.S.u_eXa 4 < F.dep F.S.u_eXa 1) (hB : F.dep F.S.u_eXa 5 < F.dep F.S.u_eXa 0 ∨ F.dep F.S.u_eXa 1 < F.dep F.S.u_eXa 0 ∨ F.dep F.S.u_eXa 5 < F.dep F.S.u_eXa 4 ∨ F.dep F.S.u_eXa 1 < F.dep F.S.u_eXa 4) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  refine F.toFrame7.rim4 0 5 4 1 _ _ _ _ (F.ptC_0) (F.ptC_5) (F.ptC_4) (F.ptC_1) 1 (Or.inl rfl) F.S.u_eXa F.S.w_eXa (Or.inl (by simp only [Shape20.u_eXa]; intro h0; linarith [F.S.tp_pos, htp1, h0]))
    (eXa_cyc F.S hEa hEb) ?_ ?_ ?_
  · intro j' h0 h1 h2 h3
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd rfl h3
    · rw [F.ptC_2]; exact eXa_rest2 F.S hEa hEb
    · rw [F.ptC_3]; exact eXa_rest3 F.S hEa hEb
    · exact absurd rfl h2
    · exact absurd rfl h1
    · rw [F.ptC_6]; exact eXa_rest6 F.S hEa hEb
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using hA
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using hB

end Minimality.CaseC20

end
