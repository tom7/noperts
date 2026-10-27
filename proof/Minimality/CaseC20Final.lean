module

public import Minimality.CaseC20Leaves

@[expose] public section

/-!
# Type 20, acute case (c): Theorem 27.79 off the special positions
(`FEWER-FACES-PROOFS.md` §27, continued (6))

`CaseC20Special x`: the special positions of the proof (for some frame of `x`).  Off them, a type-20
frame (`Frame20 x`, from `TriGenPar ∧ ¬TriGenTieO`) is Rupert at its own metric:
`Frame20.isRupert_of_not_special`.

The case tree is that of Theorem 27.79: first the class of `V` (`0135/026`) and of `V^R`; a realizable
`V` or `V^R` (class Ra) is closed by 27.64 (`V` alone, `Q_A = V + T_A`, 27.32^R, `V + X`, `V + Y`);
otherwise (class Ω) by the sign split of 27.79 (`b+ ≷ a−`, `t+ ≤ t−`, `h+ ≥ d+`, the pairs
`{T_A, T′}`, `{T_A, V}`, `{T′, T_A^R, V^R}`, family A, the edge `xa xb`), each leaf a covering
lemma of `CaseC20Leaves` (two or three tests, one linear-programming certificate per pair of failure
patterns).

The special positions are: the right angles `A12 = A11`, `A12 = A22`; the equalities
`Wp = 0, Vp = 0, Qra = 0` (`h+ = d+`, the class boundaries of `V`), `Dtri = 0` (`d− = e+`),
`A1 = 0` (`b+ = a−`), `LC = 0` (`c− = b+`), `A3 = 0` and the `R`-images; the metric lines of the
covering (`ω = 0` with `ℓ1`, `ν = 0` with `ℓν`, and their images; codimension 2 in the metric);
and the two hyperplanes `ClassH`, `ClassHR` (`CaseC20VSlide`): the persistent horizontal double normals
of `V`'s rim along the circle of `F1` (the same hyperplane for `T_A`'s rim along the slid views of
`0135`), and their `R`-images.  Off them, `V` and `T_A` are Rupert by sliding the view
(`vN4_slide`, `tANR_slide`), with no hypothesis about double normals at the view itself.
-/

namespace Minimality.CaseC20

open Finset Filter Minimality.CaseC09 Minimality.CaseC18
open scoped RealInnerProductSpace Topology

/-- **The special positions of type 20's acute case (c)** (on `x`, for some frame). -/
def CaseC20Special (x : Fin 7 → ℝ³) : Prop :=
  ∃ F : Frame20 x,
    (F.a12 = F.a11) ∨
    (F.a12 = F.a22) ∨
    F.ClassH ∨
    F.ClassHR ∨
    (-F.S.hp*F.S.sp + F.S.hp - F.S.kp = 0) ∨
    (-F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm = 0) ∨
    (-F.S.hm - F.S.km*F.S.tm + F.S.km = 0) ∨
    (-F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm = 0) ∨
    (F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm = 0) ∨
    (F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.km*F.S.tm) * (F.a11 - F.a12) + (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12 = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12 = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    ((-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg = 0 ∧ (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * (F.a22 - F.a12) + (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * F.a12 + (-F.S.km*F.S.kp) * F.gg = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12 = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    (F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12 = 0) ∨
    (-F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm - F.S.km*F.S.tm*F.S.tp + F.S.km*F.S.tm + F.S.km*F.S.tp - F.S.km = 0) ∨
    (-F.S.hp*F.S.sm + F.S.hp - F.S.km*F.S.tp = 0) ∨
    (F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm*F.S.tp + F.S.kp = 0) ∨
    ((-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg = 0 ∧ (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * (F.a22 - F.a12) + (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * F.a12 + (-F.S.km*F.S.kp) * F.gg = 0) ∨
    (F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.km*F.S.tm) * (F.a11 - F.a12) + (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12 = 0) ∨
    (-F.S.hp*F.S.sm*F.S.sp + F.S.hp*F.S.sm + F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm + F.S.kp = 0) ∨
    (-F.S.hp*F.S.sm - F.S.km*F.S.tp + F.S.km = 0) ∨
    (-F.S.hm*F.S.sm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm + F.S.km*F.S.tm - F.S.km = 0)

set_option maxHeartbeats 1600000 in
theorem Frame20.isRupert_of_not_special {x : Fin 7 → ℝ³} (F : Frame20 x)
    (hx : Function.Injective x) (h : ¬ CaseC20Special x) :
    IsRupert (Finset.univ.image x) := by
  have hF : ¬ ((F.a12 = F.a11) ∨
    (F.a12 = F.a22) ∨
    F.ClassH ∨
    F.ClassHR ∨
    (-F.S.hp*F.S.sp + F.S.hp - F.S.kp = 0) ∨
    (-F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm = 0) ∨
    (-F.S.hm - F.S.km*F.S.tm + F.S.km = 0) ∨
    (-F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm = 0) ∨
    (F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm = 0) ∨
    (F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.km*F.S.tm) * (F.a11 - F.a12) + (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12 = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12 = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    ((-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg = 0 ∧ (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * (F.a22 - F.a12) + (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * F.a12 + (-F.S.km*F.S.kp) * F.gg = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12 = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    (F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12 = 0) ∨
    (-F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm - F.S.km*F.S.tm*F.S.tp + F.S.km*F.S.tm + F.S.km*F.S.tp - F.S.km = 0) ∨
    (-F.S.hp*F.S.sm + F.S.hp - F.S.km*F.S.tp = 0) ∨
    (F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm*F.S.tp + F.S.kp = 0) ∨
    ((-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg = 0 ∧ (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * (F.a22 - F.a12) + (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * F.a12 + (-F.S.km*F.S.kp) * F.gg = 0) ∨
    (F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.km*F.S.tm) * (F.a11 - F.a12) + (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12 = 0) ∨
    (-F.S.hp*F.S.sm*F.S.sp + F.S.hp*F.S.sm + F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm + F.S.kp = 0) ∨
    (-F.S.hp*F.S.sm - F.S.km*F.S.tp + F.S.km = 0) ∨
    (-F.S.hm*F.S.sm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm + F.S.km*F.S.tm - F.S.km = 0)) := fun hs => h ⟨F, hs⟩
  simp only [not_or] at hF
  obtain ⟨m1, m2, hH, hHR, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25⟩ := hF
  have hα : F.a12 < F.a11 := lt_of_le_of_ne F.A12_le_A11 m1
  have hβ : F.a12 < F.a22 := lt_of_le_of_ne F.A12_le_A22 m2
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsp1 : 0 < 1 - F.S.sp := sub_pos.2 F.S.sp_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rp : 0 < F.S.hp * (1 - F.S.sp) - F.S.kp * (1 - F.S.tp) := sub_pos.2 F.S.roof_p'
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  rcases lt_or_gt_of_ne n1 with c1 | c1
  · have c1p : 0 < -(-F.S.hp*F.S.sp + F.S.hp - F.S.kp) := neg_pos.2 c1
    rcases lt_or_gt_of_ne n2 with c2 | c2
    · have c2p : 0 < -(-F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm) := neg_pos.2 c2
      rcases lt_or_gt_of_ne n3 with c3 | c3
      · have c3p : 0 < -(-F.S.hm - F.S.km*F.S.tm + F.S.km) := neg_pos.2 c3
        rcases lt_or_gt_of_ne n4 with c4 | c4
        · have c4p : 0 < -(-F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) := neg_pos.2 c4
          rcases lt_or_gt_of_ne n5 with c5 | c5
          · have c5p : 0 < -(F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) := neg_pos.2 c5
            rcases lt_or_gt_of_ne n6 with c6 | c6
            · have c6p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c6
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c7 | c7
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c8 | c8 | c8
                · 
                  exact Frame20.om1n F hx hα hβ (by linarith only [c5p]) (by linarith only [c7]) (by linarith only [(neg_pos.2 c8)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n7 ⟨c8, hl⟩) with c9 | c9
                  · 
                    exact Frame20.om1z2 F hx hα hβ (by linarith only [c5p]) (by linarith only [c7]) (by linarith only [c8, (neg_pos.2 c9)]) (by linarith only [c8, (neg_pos.2 c9)]) (by linarith only [c8, (neg_pos.2 c9)]) hH
                  · 
                    exact Frame20.om1z1 F hx hα hβ (by linarith only [c5p]) (by linarith only [c7]) (by linarith only [c8, c9]) (by linarith only [c8, c9]) (by linarith only [c8, c9]) hH
                · 
                  exact Frame20.om1p F hx hα hβ (by linarith only [c5p]) (by linarith only [c7]) (by linarith only [c8]) hH
              · have c7p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c7]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c10 | c10
                · 
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c11 | c11 | c11
                  · 
                    exact Frame20.om1n_R F hx hα hβ (by linarith only [c6p]) (by linarith only [c10]) (by linarith only [(neg_pos.2 c11)]) hHR
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n8 ⟨c11, hl⟩) with c12 | c12
                    · 
                      exact Frame20.om1z2_R F hx hα hβ (by linarith only [c6p]) (by linarith only [c10]) (by linarith only [c11, (neg_pos.2 c12)]) (by linarith only [c11, (neg_pos.2 c12)]) (by linarith only [c11, (neg_pos.2 c12)]) hHR
                    · 
                      exact Frame20.om1z1_R F hx hα hβ (by linarith only [c6p]) (by linarith only [c10]) (by linarith only [c11, c12]) (by linarith only [c11, c12]) (by linarith only [c11, c12]) hHR
                  · 
                    exact Frame20.om1p_R F hx hα hβ (by linarith only [c6p]) (by linarith only [c10]) (by linarith only [c11]) hHR
                · have c10p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c10]
                  rcases lt_trichotomy ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) 0 with c13 | c13 | c13
                  · 
                    exact Frame20.om4dn F hx hα hβ (by linarith only [c5p]) (by linarith only [c6p]) (by linarith only [c4p]) (by linarith only [c3p]) (by linarith only [(neg_pos.2 c13)]) hHR
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n9 ⟨c13, hl⟩) with c14 | c14
                    · 
                      exact Frame20.om4dz2 F hx hα hβ (by linarith only [c5p]) (by linarith only [c6p]) (by linarith only [c4p]) (by linarith only [c3p]) (by linarith only [c13, (neg_pos.2 c14)]) (by linarith only [c13, (neg_pos.2 c14)]) (by linarith only [c13, (neg_pos.2 c14)]) hHR
                    · 
                      exact Frame20.om4dz1 F hx hα hβ (by linarith only [c5p]) (by linarith only [c6p]) (by linarith only [c4p]) (by linarith only [c3p]) (by linarith only [c13, c14]) (by linarith only [c13, c14]) (by linarith only [c13, c14]) hHR
                  · 
                    exact Frame20.om4dp F hx hα hβ (by linarith only [c5p]) (by linarith only [c6p]) (by linarith only [c4p]) (by linarith only [c3p]) (by linarith only [c13]) hHR
            · 
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c15 | c15
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c16 | c16 | c16
                · 
                  exact Frame20.om1n F hx hα hβ (by linarith only [c5p]) (by linarith only [c15]) (by linarith only [(neg_pos.2 c16)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n7 ⟨c16, hl⟩) with c17 | c17
                  · 
                    exact Frame20.om1z2 F hx hα hβ (by linarith only [c5p]) (by linarith only [c15]) (by linarith only [c16, (neg_pos.2 c17)]) (by linarith only [c16, (neg_pos.2 c17)]) (by linarith only [c16, (neg_pos.2 c17)]) hH
                  · 
                    exact Frame20.om1z1 F hx hα hβ (by linarith only [c5p]) (by linarith only [c15]) (by linarith only [c16, c17]) (by linarith only [c16, c17]) (by linarith only [c16, c17]) hH
                · 
                  exact Frame20.om1p F hx hα hβ (by linarith only [c5p]) (by linarith only [c15]) (by linarith only [c16]) hH
              · have c15p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c15]
                rcases lt_trichotomy ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) 0 with c18 | c18 | c18
                · 
                  exact Frame20.om4bn F hx hα hβ (by linarith only [c5p]) (by linarith only [c6]) (by linarith only [c4p]) (by linarith only [c3p]) (by linarith only [(neg_pos.2 c18)])
                · 
                  rcases lt_or_gt_of_ne (fun hl => n10 ⟨c18, hl⟩) with c19 | c19
                  · 
                    exact Frame20.om4bz2 F hx hα hβ (by linarith only [c5p]) (by linarith only [c6]) (by linarith only [c4p]) (by linarith only [c3p]) (by linarith only [c18, (neg_pos.2 c19)]) (by linarith only [c18, (neg_pos.2 c19)]) (by linarith only [c18, (neg_pos.2 c19)])
                  · 
                    exact Frame20.om4bz1 F hx hα hβ (by linarith only [c5p]) (by linarith only [c6]) (by linarith only [c4p]) (by linarith only [c3p]) (by linarith only [c18, c19]) (by linarith only [c18, c19]) (by linarith only [c18, c19])
                · 
                  exact Frame20.om4bp F hx hα hβ (by linarith only [c5p]) (by linarith only [c6]) (by linarith only [c4p]) (by linarith only [c3p]) (by linarith only [c18])
          · 
            rcases lt_or_gt_of_ne n6 with c20 | c20
            · have c20p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c20
              rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c21 | c21
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c22 | c22 | c22
                · 
                  exact Frame20.om1n_R F hx hα hβ (by linarith only [c20p]) (by linarith only [c21]) (by linarith only [(neg_pos.2 c22)]) hHR
                · 
                  rcases lt_or_gt_of_ne (fun hl => n8 ⟨c22, hl⟩) with c23 | c23
                  · 
                    exact Frame20.om1z2_R F hx hα hβ (by linarith only [c20p]) (by linarith only [c21]) (by linarith only [c22, (neg_pos.2 c23)]) (by linarith only [c22, (neg_pos.2 c23)]) (by linarith only [c22, (neg_pos.2 c23)]) hHR
                  · 
                    exact Frame20.om1z1_R F hx hα hβ (by linarith only [c20p]) (by linarith only [c21]) (by linarith only [c22, c23]) (by linarith only [c22, c23]) (by linarith only [c22, c23]) hHR
                · 
                  exact Frame20.om1p_R F hx hα hβ (by linarith only [c20p]) (by linarith only [c21]) (by linarith only [c22]) hHR
              · have c21p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c21]
                rcases lt_trichotomy ((-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) 0 with c24 | c24 | c24
                · 
                  exact Frame20.om4bn_R F hx hα hβ (by linarith only [c20p]) (by linarith only [c5]) (by linarith only [c2p]) (by linarith only [c1p]) (by linarith only [(neg_pos.2 c24)])
                · 
                  rcases lt_or_gt_of_ne (fun hl => n11 ⟨c24, hl⟩) with c25 | c25
                  · 
                    exact Frame20.om4bz2_R F hx hα hβ (by linarith only [c20p]) (by linarith only [c5]) (by linarith only [c2p]) (by linarith only [c1p]) (by linarith only [c24, (neg_pos.2 c25)]) (by linarith only [c24, (neg_pos.2 c25)]) (by linarith only [c24, (neg_pos.2 c25)])
                  · 
                    exact Frame20.om4bz1_R F hx hα hβ (by linarith only [c20p]) (by linarith only [c5]) (by linarith only [c2p]) (by linarith only [c1p]) (by linarith only [c24, c25]) (by linarith only [c24, c25]) (by linarith only [c24, c25])
                · 
                  exact Frame20.om4bp_R F hx hα hβ (by linarith only [c20p]) (by linarith only [c5]) (by linarith only [c2p]) (by linarith only [c1p]) (by linarith only [c24])
            · 
              rcases le_or_gt 0 (F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km) with c26 | c26
              · 
                rcases lt_or_ge 0 ((F.S.sm^2 - F.S.sm) * (F.a22 - F.a12) + (F.S.sm^2 - 2*F.S.sm + 1) * F.a12 + (F.S.km^2) * F.gg) with c27 | c27
                · 
                  exact Frame20.famA1_R F hx hα hβ (by linarith only [c20]) (by refine pos_of_pos_mul rm ?_; linarith only [(mul_pos F.S.kp_pos rm), (mul_nonneg (c20).le c26), (mul_pos (mul_pos htp1 F.S.km_pos) c4p), (mul_pos (mul_pos hsm1 F.S.hp_pos) c4p)]) (by refine pos_of_pos_mul htm1 ?_; linarith only [(mul_nonneg (hsp1).le c26), (mul_pos (mul_pos htp1 hsp1) c3p), (mul_pos (mul_pos htm1 hsm1) c1p), (mul_pos (mul_pos (mul_pos F.S.tp_pos hsp1) hsm1) F.S.hm_pos), (mul_pos (mul_pos (mul_pos htp1 htm1) F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c27])
                · 
                  exact Frame20.famA2_R F hx hα hβ (by linarith only [c20]) (by refine pos_of_pos_mul rm ?_; linarith only [(mul_pos F.S.kp_pos rm), (mul_nonneg (c20).le c26), (mul_pos (mul_pos htp1 F.S.km_pos) c4p), (mul_pos (mul_pos hsm1 F.S.hp_pos) c4p)]) (by refine pos_of_pos_mul htm1 ?_; linarith only [(mul_nonneg (hsp1).le c26), (mul_pos (mul_pos htp1 hsp1) c3p), (mul_pos (mul_pos htm1 hsm1) c1p), (mul_pos (mul_pos (mul_pos F.S.tp_pos hsp1) hsm1) F.S.hm_pos), (mul_pos (mul_pos (mul_pos htp1 htm1) F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c27])
              · have c26p : 0 < -(F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km) := by linarith only [c26]
                rcases le_or_gt 0 (-F.S.hp*F.S.sp + F.S.hp + F.S.km*F.S.sp*F.S.tp - F.S.km*F.S.tp + F.S.kp*F.S.sm*F.S.tp - F.S.kp) with c28 | c28
                · 
                  rcases lt_or_ge 0 ((F.S.tp^2 - F.S.tp) * (F.a11 - F.a12) + (F.S.tp^2 - 2*F.S.tp + 1) * F.a12 + (F.S.hp^2) * F.gg) with c29 | c29
                  · 
                    exact Frame20.famA1 F hx hα hβ (by linarith only [c5]) (by refine pos_of_pos_mul rp ?_; linarith only [(mul_nonneg (c5).le c28), (mul_pos (mul_pos htp1 F.S.km_pos) c2p), (mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) rp), (mul_pos (mul_pos hsm1 c1p) c5)]) (by linarith only [c26p]) (by linarith only [c29])
                  · 
                    exact Frame20.famA2 F hx hα hβ (by linarith only [c5]) (by refine pos_of_pos_mul rp ?_; linarith only [(mul_nonneg (c5).le c28), (mul_pos (mul_pos htp1 F.S.km_pos) c2p), (mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) rp), (mul_pos (mul_pos hsm1 c1p) c5)]) (by linarith only [c26p]) (by linarith only [c29])
                · have c28p : 0 < -(-F.S.hp*F.S.sp + F.S.hp + F.S.km*F.S.sp*F.S.tp - F.S.km*F.S.tp + F.S.kp*F.S.sm*F.S.tp - F.S.kp) := by linarith only [c28]
                  rcases le_or_gt 0 (-F.S.hm*F.S.sm*F.S.tp - F.S.hp*F.S.sm*F.S.tm + F.S.km*F.S.tm) with c30 | c30
                  · 
                    rcases le_or_gt 0 (F.S.hp*F.S.sp - F.S.km*F.S.sp*F.S.tp - F.S.kp*F.S.sm*F.S.tp) with c31 | c31
                    · 
                      exact Frame20.famE F hx hα hβ (by linarith only [c5]) (by linarith only [c20]) (by linarith only [c30]) (by linarith only [c31])
                    · have c31p : 0 < -(F.S.hp*F.S.sp - F.S.km*F.S.sp*F.S.tp - F.S.kp*F.S.sm*F.S.tp) := by linarith only [c31]
                      rcases lt_or_ge 0 ((F.S.sm^2 - F.S.sm) * (F.a22 - F.a12) + (F.S.sm^2 - 2*F.S.sm + 1) * F.a12 + (F.S.km^2) * F.gg) with c32 | c32
                      · 
                        exact Frame20.famA1_R F hx hα hβ (by linarith only [c20]) (by linarith only [c31p]) (by linarith only [c28p]) (by linarith only [c32])
                      · 
                        exact Frame20.famA2_R F hx hα hβ (by linarith only [c20]) (by linarith only [c31p]) (by linarith only [c28p]) (by linarith only [c32])
                  · have c30p : 0 < -(-F.S.hm*F.S.sm*F.S.tp - F.S.hp*F.S.sm*F.S.tm + F.S.km*F.S.tm) := by linarith only [c30]
                    rcases lt_or_ge 0 ((F.S.tp^2 - F.S.tp) * (F.a11 - F.a12) + (F.S.tp^2 - 2*F.S.tp + 1) * F.a12 + (F.S.hp^2) * F.gg) with c33 | c33
                    · 
                      exact Frame20.famA1 F hx hα hβ (by linarith only [c5]) (by linarith only [c30p]) (by linarith only [c26p]) (by linarith only [c33])
                    · 
                      exact Frame20.famA2 F hx hα hβ (by linarith only [c5]) (by linarith only [c30p]) (by linarith only [c26p]) (by linarith only [c33])
        · 
          rcases lt_or_gt_of_ne n5 with c34 | c34
          · have c34p : 0 < -(F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) := neg_pos.2 c34
            rcases lt_or_gt_of_ne n6 with c35 | c35
            · have c35p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c35
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c36 | c36
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c37 | c37 | c37
                · 
                  exact Frame20.om1n F hx hα hβ (by linarith only [c34p]) (by linarith only [c36]) (by linarith only [(neg_pos.2 c37)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n7 ⟨c37, hl⟩) with c38 | c38
                  · 
                    exact Frame20.om1z2 F hx hα hβ (by linarith only [c34p]) (by linarith only [c36]) (by linarith only [c37, (neg_pos.2 c38)]) (by linarith only [c37, (neg_pos.2 c38)]) (by linarith only [c37, (neg_pos.2 c38)]) hH
                  · 
                    exact Frame20.om1z1 F hx hα hβ (by linarith only [c34p]) (by linarith only [c36]) (by linarith only [c37, c38]) (by linarith only [c37, c38]) (by linarith only [c37, c38]) hH
                · 
                  exact Frame20.om1p F hx hα hβ (by linarith only [c34p]) (by linarith only [c36]) (by linarith only [c37]) hH
              · have c36p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c36]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c39 | c39
                · 
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c40 | c40 | c40
                  · 
                    exact Frame20.om1n_R F hx hα hβ (by linarith only [c35p]) (by linarith only [c39]) (by linarith only [(neg_pos.2 c40)]) hHR
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n8 ⟨c40, hl⟩) with c41 | c41
                    · 
                      exact Frame20.om1z2_R F hx hα hβ (by linarith only [c35p]) (by linarith only [c39]) (by linarith only [c40, (neg_pos.2 c41)]) (by linarith only [c40, (neg_pos.2 c41)]) (by linarith only [c40, (neg_pos.2 c41)]) hHR
                    · 
                      exact Frame20.om1z1_R F hx hα hβ (by linarith only [c35p]) (by linarith only [c39]) (by linarith only [c40, c41]) (by linarith only [c40, c41]) (by linarith only [c40, c41]) hHR
                  · 
                    exact Frame20.om1p_R F hx hα hβ (by linarith only [c35p]) (by linarith only [c39]) (by linarith only [c40]) hHR
                · have c39p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c39]
                  rcases lt_trichotomy ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) 0 with c42 | c42 | c42
                  · 
                    rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c43 | c43 | c43
                    · 
                      exact Frame20.om4cnom F hx hα hβ (by linarith only [c34p]) (by linarith only [c35p]) (by linarith only [c4]) (by linarith only [(mul_pos hsp1 c3p), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c3p]) (by linarith only [c39p]) (by linarith only [(neg_pos.2 c42), (neg_pos.2 c43)]) (by linarith only [(neg_pos.2 c42), (neg_pos.2 c43)]) hHR
                    · 
                      rcases lt_or_gt_of_ne (fun hl => n13 ⟨c43, hl⟩) with c44 | c44
                      · 
                        exact Frame20.om4cnoz2 F hx hα hβ (by linarith only [c34p]) (by linarith only [c35p]) (by linarith only [c4]) (by linarith only [(mul_pos hsp1 c3p), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c3p]) (by linarith only [c39p]) (by linarith only [(neg_pos.2 c42), c43, (neg_pos.2 c44)]) (by linarith only [(neg_pos.2 c42), c43, (neg_pos.2 c44)]) (by linarith only [(neg_pos.2 c42), c43, (neg_pos.2 c44)]) (by linarith only [(neg_pos.2 c42), c43, (neg_pos.2 c44)]) hHR
                      · 
                        exact Frame20.om4cnoz1 F hx hα hβ (by linarith only [c34p]) (by linarith only [c35p]) (by linarith only [c4]) (by linarith only [(mul_pos hsp1 c3p), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c3p]) (by linarith only [c39p]) (by linarith only [(neg_pos.2 c42), c43, c44]) (by linarith only [(neg_pos.2 c42), c43, c44]) (by linarith only [(neg_pos.2 c42), c43, c44]) (by linarith only [(neg_pos.2 c42), c43, c44]) hHR
                    · 
                      exact Frame20.om4cnop F hx hα hβ (by linarith only [c34p]) (by linarith only [c35p]) (by linarith only [c4]) (by linarith only [(mul_pos hsp1 c3p), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c3p]) (by linarith only [c39p]) (by linarith only [(neg_pos.2 c42), c43]) (by linarith only [(neg_pos.2 c42), c43]) hHR
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n12 ⟨c42, hl⟩) with c45 | c45
                    · 
                      exact Frame20.om4cz2 F hx hα hβ (by linarith only [c34p]) (by linarith only [c35p]) (by linarith only [c4]) (by linarith only [(mul_pos hsp1 c3p), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c3p]) (by linarith only [c39p]) (by linarith only [c42, (neg_pos.2 c45)]) (by linarith only [c42, (neg_pos.2 c45)]) (by linarith only [c42, (neg_pos.2 c45)]) hHR
                    · 
                      exact Frame20.om4cz1 F hx hα hβ (by linarith only [c34p]) (by linarith only [c35p]) (by linarith only [c4]) (by linarith only [(mul_pos hsp1 c3p), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c3p]) (by linarith only [c39p]) (by linarith only [c42, c45]) (by linarith only [c42, c45]) (by linarith only [c42, c45]) hHR
                  · 
                    exact Frame20.om4cp F hx hα hβ (by linarith only [c34p]) (by linarith only [c35p]) (by linarith only [c4]) (by linarith only [(mul_pos hsp1 c3p), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c3p]) (by linarith only [c39p]) (by linarith only [c42]) hHR
            · 
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c46 | c46
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c47 | c47 | c47
                · 
                  exact Frame20.om1n F hx hα hβ (by linarith only [c34p]) (by linarith only [c46]) (by linarith only [(neg_pos.2 c47)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n7 ⟨c47, hl⟩) with c48 | c48
                  · 
                    exact Frame20.om1z2 F hx hα hβ (by linarith only [c34p]) (by linarith only [c46]) (by linarith only [c47, (neg_pos.2 c48)]) (by linarith only [c47, (neg_pos.2 c48)]) (by linarith only [c47, (neg_pos.2 c48)]) hH
                  · 
                    exact Frame20.om1z1 F hx hα hβ (by linarith only [c34p]) (by linarith only [c46]) (by linarith only [c47, c48]) (by linarith only [c47, c48]) (by linarith only [c47, c48]) hH
                · 
                  exact Frame20.om1p F hx hα hβ (by linarith only [c34p]) (by linarith only [c46]) (by linarith only [c47]) hH
              · have c46p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c46]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c49 | c49
                · 
                  exact Frame20.om2b_R F hx hα hβ (by linarith only [c35]) (by linarith only [c4]) (by linarith only [c3p, c4]) (by linarith only [c49]) (by linarith only [c3p]) hHR
                · have c49p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c49]
                  rcases lt_trichotomy ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) 0 with c50 | c50 | c50
                  · 
                    exact Frame20.om4an F hx hα hβ (by linarith only [c34p]) (by linarith only [c35]) (by linarith only [c4]) (by linarith only [c3p, c4]) (by linarith only [c3p]) (by linarith only [c49p]) (by linarith only [(neg_pos.2 c50)]) hHR
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n14 ⟨c50, hl⟩) with c51 | c51
                    · 
                      exact Frame20.om4az2 F hx hα hβ (by linarith only [c34p]) (by linarith only [c35]) (by linarith only [c4]) (by linarith only [c3p, c4]) (by linarith only [c3p]) (by linarith only [c49p]) (by linarith only [c50, (neg_pos.2 c51)]) (by linarith only [c50, (neg_pos.2 c51)]) (by linarith only [c50, (neg_pos.2 c51)]) hHR
                    · 
                      exact Frame20.om4az1 F hx hα hβ (by linarith only [c34p]) (by linarith only [c35]) (by linarith only [c4]) (by linarith only [c3p, c4]) (by linarith only [c3p]) (by linarith only [c49p]) (by linarith only [c50, c51]) (by linarith only [c50, c51]) (by linarith only [c50, c51]) hHR
                  · 
                    exact Frame20.om4ap F hx hα hβ (by linarith only [c34p]) (by linarith only [c35]) (by linarith only [c4]) (by linarith only [c3p, c4]) (by linarith only [c3p]) (by linarith only [c49p]) (by linarith only [c50]) hHR
          · 
            rcases lt_or_gt_of_ne n6 with c52 | c52
            · have c52p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c52
              rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c53 | c53
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c54 | c54 | c54
                · 
                  exact Frame20.om1n_R F hx hα hβ (by linarith only [c52p]) (by linarith only [c53]) (by linarith only [(neg_pos.2 c54)]) hHR
                · 
                  rcases lt_or_gt_of_ne (fun hl => n8 ⟨c54, hl⟩) with c55 | c55
                  · 
                    exact Frame20.om1z2_R F hx hα hβ (by linarith only [c52p]) (by linarith only [c53]) (by linarith only [c54, (neg_pos.2 c55)]) (by linarith only [c54, (neg_pos.2 c55)]) (by linarith only [c54, (neg_pos.2 c55)]) hHR
                  · 
                    exact Frame20.om1z1_R F hx hα hβ (by linarith only [c52p]) (by linarith only [c53]) (by linarith only [c54, c55]) (by linarith only [c54, c55]) (by linarith only [c54, c55]) hHR
                · 
                  exact Frame20.om1p_R F hx hα hβ (by linarith only [c52p]) (by linarith only [c53]) (by linarith only [c54]) hHR
              · have c53p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c53]
                rcases lt_trichotomy ((-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) 0 with c56 | c56 | c56
                · 
                  exact Frame20.om4bn_R F hx hα hβ (by linarith only [c52p]) (by linarith only [c34]) (by linarith only [c2p]) (by linarith only [c1p]) (by linarith only [(neg_pos.2 c56)])
                · 
                  rcases lt_or_gt_of_ne (fun hl => n11 ⟨c56, hl⟩) with c57 | c57
                  · 
                    exact Frame20.om4bz2_R F hx hα hβ (by linarith only [c52p]) (by linarith only [c34]) (by linarith only [c2p]) (by linarith only [c1p]) (by linarith only [c56, (neg_pos.2 c57)]) (by linarith only [c56, (neg_pos.2 c57)]) (by linarith only [c56, (neg_pos.2 c57)])
                  · 
                    exact Frame20.om4bz1_R F hx hα hβ (by linarith only [c52p]) (by linarith only [c34]) (by linarith only [c2p]) (by linarith only [c1p]) (by linarith only [c56, c57]) (by linarith only [c56, c57]) (by linarith only [c56, c57])
                · 
                  exact Frame20.om4bp_R F hx hα hβ (by linarith only [c52p]) (by linarith only [c34]) (by linarith only [c2p]) (by linarith only [c1p]) (by linarith only [c56])
            · 
              rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c58 | c58
              · 
                exact Frame20.om2b_R F hx hα hβ (by linarith only [c52]) (by linarith only [c4]) (by linarith only [(mul_pos hsp1 c3p), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c58]) (by linarith only [c3p]) hHR
              · have c58p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c58]
                rcases le_or_gt 0 (F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km) with c59 | c59
                · 
                  rcases lt_or_ge 0 ((F.S.sm^2 - F.S.sm) * (F.a22 - F.a12) + (F.S.sm^2 - 2*F.S.sm + 1) * F.a12 + (F.S.km^2) * F.gg) with c60 | c60
                  · 
                    exact Frame20.famA1_R F hx hα hβ (by linarith only [c52]) (by refine pos_of_pos_mul rm ?_; linarith only [(mul_nonneg (F.S.kp_pos).le c59), (mul_nonneg (c52).le c59), (mul_pos (mul_pos htp1 F.S.kp_pos) c3p), (mul_pos (mul_pos htp1 c3p) c52), (mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) c3p), (mul_pos (mul_pos F.S.sm_pos F.S.hp_pos) c4)]) (by refine pos_of_pos_mul rm ?_; linarith only [(mul_pos (mul_pos htp1 F.S.km_pos) c3p), (mul_pos (mul_pos htp1 F.S.km_pos) c4), (mul_nonneg (mul_nonneg (hsp1).le (F.S.km_pos).le) c59), (mul_pos (mul_pos hsm1 rp) rm), (mul_pos (mul_pos hsm1 rp) c3p), (mul_pos (mul_pos hsm1 rm) c1p)]) (by linarith only [c60])
                  · 
                    exact Frame20.famA2_R F hx hα hβ (by linarith only [c52]) (by refine pos_of_pos_mul rm ?_; linarith only [(mul_nonneg (F.S.kp_pos).le c59), (mul_nonneg (c52).le c59), (mul_pos (mul_pos htp1 F.S.kp_pos) c3p), (mul_pos (mul_pos htp1 c3p) c52), (mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) c3p), (mul_pos (mul_pos F.S.sm_pos F.S.hp_pos) c4)]) (by refine pos_of_pos_mul rm ?_; linarith only [(mul_pos (mul_pos htp1 F.S.km_pos) c3p), (mul_pos (mul_pos htp1 F.S.km_pos) c4), (mul_nonneg (mul_nonneg (hsp1).le (F.S.km_pos).le) c59), (mul_pos (mul_pos hsm1 rp) rm), (mul_pos (mul_pos hsm1 rp) c3p), (mul_pos (mul_pos hsm1 rm) c1p)]) (by linarith only [c60])
                · have c59p : 0 < -(F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km) := by linarith only [c59]
                  rcases le_or_gt 0 (-F.S.hp*F.S.sp + F.S.hp + F.S.km*F.S.sp*F.S.tp - F.S.km*F.S.tp + F.S.kp*F.S.sm*F.S.tp - F.S.kp) with c61 | c61
                  · 
                    rcases lt_or_ge 0 ((F.S.tp^2 - F.S.tp) * (F.a11 - F.a12) + (F.S.tp^2 - 2*F.S.tp + 1) * F.a12 + (F.S.hp^2) * F.gg) with c62 | c62
                    · 
                      exact Frame20.famA1 F hx hα hβ (by linarith only [c34]) (by refine pos_of_pos_mul rp ?_; linarith only [(mul_nonneg (c34).le c61), (mul_pos (mul_pos htp1 F.S.km_pos) c2p), (mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) rp), (mul_pos (mul_pos hsm1 c1p) c34)]) (by linarith only [c59p]) (by linarith only [c62])
                    · 
                      exact Frame20.famA2 F hx hα hβ (by linarith only [c34]) (by refine pos_of_pos_mul rp ?_; linarith only [(mul_nonneg (c34).le c61), (mul_pos (mul_pos htp1 F.S.km_pos) c2p), (mul_pos (mul_pos F.S.sm_pos F.S.hm_pos) rp), (mul_pos (mul_pos hsm1 c1p) c34)]) (by linarith only [c59p]) (by linarith only [c62])
                  · have c61p : 0 < -(-F.S.hp*F.S.sp + F.S.hp + F.S.km*F.S.sp*F.S.tp - F.S.km*F.S.tp + F.S.kp*F.S.sm*F.S.tp - F.S.kp) := by linarith only [c61]
                    rcases le_or_gt 0 (-F.S.hm*F.S.sm*F.S.tp - F.S.hp*F.S.sm*F.S.tm + F.S.km*F.S.tm) with c63 | c63
                    · 
                      rcases le_or_gt 0 (F.S.hp*F.S.sp - F.S.km*F.S.sp*F.S.tp - F.S.kp*F.S.sm*F.S.tp) with c64 | c64
                      · 
                        exact Frame20.famE F hx hα hβ (by linarith only [c34]) (by linarith only [c52]) (by linarith only [c63]) (by linarith only [c64])
                      · have c64p : 0 < -(F.S.hp*F.S.sp - F.S.km*F.S.sp*F.S.tp - F.S.kp*F.S.sm*F.S.tp) := by linarith only [c64]
                        rcases lt_or_ge 0 ((F.S.sm^2 - F.S.sm) * (F.a22 - F.a12) + (F.S.sm^2 - 2*F.S.sm + 1) * F.a12 + (F.S.km^2) * F.gg) with c65 | c65
                        · 
                          exact Frame20.famA1_R F hx hα hβ (by linarith only [c52]) (by linarith only [c64p]) (by linarith only [c61p]) (by linarith only [c65])
                        · 
                          exact Frame20.famA2_R F hx hα hβ (by linarith only [c52]) (by linarith only [c64p]) (by linarith only [c61p]) (by linarith only [c65])
                    · have c63p : 0 < -(-F.S.hm*F.S.sm*F.S.tp - F.S.hp*F.S.sm*F.S.tm + F.S.km*F.S.tm) := by linarith only [c63]
                      rcases lt_or_ge 0 ((F.S.tp^2 - F.S.tp) * (F.a11 - F.a12) + (F.S.tp^2 - 2*F.S.tp + 1) * F.a12 + (F.S.hp^2) * F.gg) with c66 | c66
                      · 
                        exact Frame20.famA1 F hx hα hβ (by linarith only [c34]) (by linarith only [c63p]) (by linarith only [c59p]) (by linarith only [c66])
                      · 
                        exact Frame20.famA2 F hx hα hβ (by linarith only [c34]) (by linarith only [c63p]) (by linarith only [c59p]) (by linarith only [c66])
      · 
        rcases lt_or_gt_of_ne n15 with c67 | c67
        · have c67p : 0 < -(F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) := neg_pos.2 c67
          rcases lt_or_gt_of_ne n5 with c68 | c68
          · have c68p : 0 < -(F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) := neg_pos.2 c68
            rcases lt_or_gt_of_ne n6 with c69 | c69
            · have c69p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c69
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c70 | c70
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c71 | c71 | c71
                · 
                  exact Frame20.om1n F hx hα hβ (by linarith only [c68p]) (by linarith only [c70]) (by linarith only [(neg_pos.2 c71)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n7 ⟨c71, hl⟩) with c72 | c72
                  · 
                    exact Frame20.om1z2 F hx hα hβ (by linarith only [c68p]) (by linarith only [c70]) (by linarith only [c71, (neg_pos.2 c72)]) (by linarith only [c71, (neg_pos.2 c72)]) (by linarith only [c71, (neg_pos.2 c72)]) hH
                  · 
                    exact Frame20.om1z1 F hx hα hβ (by linarith only [c68p]) (by linarith only [c70]) (by linarith only [c71, c72]) (by linarith only [c71, c72]) (by linarith only [c71, c72]) hH
                · 
                  exact Frame20.om1p F hx hα hβ (by linarith only [c68p]) (by linarith only [c70]) (by linarith only [c71]) hH
              · have c70p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c70]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c73 | c73
                · 
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c74 | c74 | c74
                  · 
                    exact Frame20.om1n_R F hx hα hβ (by linarith only [c69p]) (by linarith only [c73]) (by linarith only [(neg_pos.2 c74)]) hHR
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n8 ⟨c74, hl⟩) with c75 | c75
                    · 
                      exact Frame20.om1z2_R F hx hα hβ (by linarith only [c69p]) (by linarith only [c73]) (by linarith only [c74, (neg_pos.2 c75)]) (by linarith only [c74, (neg_pos.2 c75)]) (by linarith only [c74, (neg_pos.2 c75)]) hHR
                    · 
                      exact Frame20.om1z1_R F hx hα hβ (by linarith only [c69p]) (by linarith only [c73]) (by linarith only [c74, c75]) (by linarith only [c74, c75]) (by linarith only [c74, c75]) hHR
                  · 
                    exact Frame20.om1p_R F hx hα hβ (by linarith only [c69p]) (by linarith only [c73]) (by linarith only [c74]) hHR
                · have c73p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c73]
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c76 | c76 | c76
                  · 
                    exact Frame20.om3n_R F hx hα hβ (by linarith only [c69p]) (by linarith only [c3, c67p]) (by linarith only [c67p]) (by linarith only [c3]) (by linarith only [(neg_pos.2 c76)]) hHR
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n16 ⟨c76, hl⟩) with c77 | c77
                    · 
                      exact Frame20.om3z2_R F hx hα hβ (by linarith only [c69p]) (by linarith only [c3, c67p]) (by linarith only [c67p]) (by linarith only [c3]) (by linarith only [c76, (neg_pos.2 c77)]) (by linarith only [c76, (neg_pos.2 c77)]) (by linarith only [c76, (neg_pos.2 c77)]) hHR
                    · 
                      exact Frame20.om3z1_R F hx hα hβ (by linarith only [c69p]) (by linarith only [c3, c67p]) (by linarith only [c67p]) (by linarith only [c3]) (by linarith only [c76, c77]) (by linarith only [c76, c77]) (by linarith only [c76, c77]) hHR
                  · 
                    exact Frame20.om3p_R F hx hα hβ (by linarith only [c69p]) (by linarith only [c3, c67p]) (by linarith only [c67p]) (by linarith only [c3]) (by linarith only [c76]) hHR
            · 
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c78 | c78
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c79 | c79 | c79
                · 
                  exact Frame20.om1n F hx hα hβ (by linarith only [c68p]) (by linarith only [c78]) (by linarith only [(neg_pos.2 c79)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n7 ⟨c79, hl⟩) with c80 | c80
                  · 
                    exact Frame20.om1z2 F hx hα hβ (by linarith only [c68p]) (by linarith only [c78]) (by linarith only [c79, (neg_pos.2 c80)]) (by linarith only [c79, (neg_pos.2 c80)]) (by linarith only [c79, (neg_pos.2 c80)]) hH
                  · 
                    exact Frame20.om1z1 F hx hα hβ (by linarith only [c68p]) (by linarith only [c78]) (by linarith only [c79, c80]) (by linarith only [c79, c80]) (by linarith only [c79, c80]) hH
                · 
                  exact Frame20.om1p F hx hα hβ (by linarith only [c68p]) (by linarith only [c78]) (by linarith only [c79]) hH
              · have c78p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c78]
                exact Frame20.om2a_R F hx hα hβ (by linarith only [c69]) (by linarith only [(mul_pos F.S.sp_pos c3), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c67p]) (by linarith only [c3]) hHR
          · 
            rcases lt_or_gt_of_ne n6 with c81 | c81
            · have c81p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c81
              rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c82 | c82
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c83 | c83 | c83
                · 
                  exact Frame20.om1n_R F hx hα hβ (by linarith only [c81p]) (by linarith only [c82]) (by linarith only [(neg_pos.2 c83)]) hHR
                · 
                  rcases lt_or_gt_of_ne (fun hl => n8 ⟨c83, hl⟩) with c84 | c84
                  · 
                    exact Frame20.om1z2_R F hx hα hβ (by linarith only [c81p]) (by linarith only [c82]) (by linarith only [c83, (neg_pos.2 c84)]) (by linarith only [c83, (neg_pos.2 c84)]) (by linarith only [c83, (neg_pos.2 c84)]) hHR
                  · 
                    exact Frame20.om1z1_R F hx hα hβ (by linarith only [c81p]) (by linarith only [c82]) (by linarith only [c83, c84]) (by linarith only [c83, c84]) (by linarith only [c83, c84]) hHR
                · 
                  exact Frame20.om1p_R F hx hα hβ (by linarith only [c81p]) (by linarith only [c82]) (by linarith only [c83]) hHR
              · have c82p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c82]
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c85 | c85 | c85
                · 
                  exact Frame20.om3n_R F hx hα hβ (by linarith only [c81p]) (by linarith only [c3, c67p]) (by linarith only [c67p]) (by linarith only [c3]) (by linarith only [(neg_pos.2 c85)]) hHR
                · 
                  rcases lt_or_gt_of_ne (fun hl => n16 ⟨c85, hl⟩) with c86 | c86
                  · 
                    exact Frame20.om3z2_R F hx hα hβ (by linarith only [c81p]) (by linarith only [c3, c67p]) (by linarith only [c67p]) (by linarith only [c3]) (by linarith only [c85, (neg_pos.2 c86)]) (by linarith only [c85, (neg_pos.2 c86)]) (by linarith only [c85, (neg_pos.2 c86)]) hHR
                  · 
                    exact Frame20.om3z1_R F hx hα hβ (by linarith only [c81p]) (by linarith only [c3, c67p]) (by linarith only [c67p]) (by linarith only [c3]) (by linarith only [c85, c86]) (by linarith only [c85, c86]) (by linarith only [c85, c86]) hHR
                · 
                  exact Frame20.om3p_R F hx hα hβ (by linarith only [c81p]) (by linarith only [c3, c67p]) (by linarith only [c67p]) (by linarith only [c3]) (by linarith only [c85]) hHR
            · 
              exact Frame20.om2a_R F hx hα hβ (by linarith only [c81]) (by linarith only [(mul_pos F.S.sp_pos c3), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c67p]) (by linarith only [c3]) hHR
        · 
          rcases lt_or_gt_of_ne n17 with c87 | c87
          · have c87p : 0 < -(-F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm - F.S.km*F.S.tm*F.S.tp + F.S.km*F.S.tm + F.S.km*F.S.tp - F.S.km) := neg_pos.2 c87
            exact rupert_of_r (F.rFrame.vTri (by simp only [rFrame_S, Shape20.swap]; exact (by linarith only [c3])) (by simp only [rFrame_S, Shape20.swap]; exact (by linarith only [c67])) (by simp only [rFrame_S, Shape20.swap]; exact (by linarith only [c87p])))
          · 
            rcases lt_or_gt_of_ne n6 with c88 | c88
            · have c88p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c88
              rcases lt_or_gt_of_ne n18 with c89 | c89
              · have c89p : 0 < -(-F.S.hp*F.S.sm + F.S.hp - F.S.km*F.S.tp) := neg_pos.2 c89
                rcases lt_or_gt_of_ne n19 with c90 | c90
                · have c90p : 0 < -(F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm*F.S.tp + F.S.kp) := neg_pos.2 c90
                  exact Frame20.ra4_X_R F hx hα hβ (by linarith only [c3]) (by linarith only [c67]) (by linarith only [c87]) (by linarith only [c88p]) (by linarith only [c89p]) (by linarith only [c90p])
                · 
                  exact Frame20.ra4_Y_R F hx hα hβ (by linarith only [c3]) (by linarith only [c67]) (by linarith only [c87]) (by linarith only [c88p]) (by linarith only [c89p]) (by linarith only [c90])
              · 
                exact Frame20.ra4_tBR_R F hx hα hβ (by linarith only [c88p]) (by linarith only [c89])
            · 
              exact Frame20.ra4_A_R F hx hα hβ (by linarith only [c3]) (by linarith only [c67]) (by linarith only [c87]) (by linarith only [c88])
    · 
      rcases lt_or_gt_of_ne n3 with c91 | c91
      · have c91p : 0 < -(-F.S.hm - F.S.km*F.S.tm + F.S.km) := neg_pos.2 c91
        rcases lt_or_gt_of_ne n4 with c92 | c92
        · have c92p : 0 < -(-F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) := neg_pos.2 c92
          rcases lt_or_gt_of_ne n5 with c93 | c93
          · have c93p : 0 < -(F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) := neg_pos.2 c93
            rcases lt_or_gt_of_ne n6 with c94 | c94
            · have c94p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c94
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c95 | c95
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c96 | c96 | c96
                · 
                  exact Frame20.om1n F hx hα hβ (by linarith only [c93p]) (by linarith only [c95]) (by linarith only [(neg_pos.2 c96)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n7 ⟨c96, hl⟩) with c97 | c97
                  · 
                    exact Frame20.om1z2 F hx hα hβ (by linarith only [c93p]) (by linarith only [c95]) (by linarith only [c96, (neg_pos.2 c97)]) (by linarith only [c96, (neg_pos.2 c97)]) (by linarith only [c96, (neg_pos.2 c97)]) hH
                  · 
                    exact Frame20.om1z1 F hx hα hβ (by linarith only [c93p]) (by linarith only [c95]) (by linarith only [c96, c97]) (by linarith only [c96, c97]) (by linarith only [c96, c97]) hH
                · 
                  exact Frame20.om1p F hx hα hβ (by linarith only [c93p]) (by linarith only [c95]) (by linarith only [c96]) hH
              · have c95p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c95]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c98 | c98
                · 
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c99 | c99 | c99
                  · 
                    exact Frame20.om1n_R F hx hα hβ (by linarith only [c94p]) (by linarith only [c98]) (by linarith only [(neg_pos.2 c99)]) hHR
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n8 ⟨c99, hl⟩) with c100 | c100
                    · 
                      exact Frame20.om1z2_R F hx hα hβ (by linarith only [c94p]) (by linarith only [c98]) (by linarith only [c99, (neg_pos.2 c100)]) (by linarith only [c99, (neg_pos.2 c100)]) (by linarith only [c99, (neg_pos.2 c100)]) hHR
                    · 
                      exact Frame20.om1z1_R F hx hα hβ (by linarith only [c94p]) (by linarith only [c98]) (by linarith only [c99, c100]) (by linarith only [c99, c100]) (by linarith only [c99, c100]) hHR
                  · 
                    exact Frame20.om1p_R F hx hα hβ (by linarith only [c94p]) (by linarith only [c98]) (by linarith only [c99]) hHR
                · have c98p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c98]
                  rcases lt_trichotomy ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) 0 with c101 | c101 | c101
                  · 
                    exact Frame20.om4dn F hx hα hβ (by linarith only [c93p]) (by linarith only [c94p]) (by linarith only [c92p]) (by linarith only [c91p]) (by linarith only [(neg_pos.2 c101)]) hHR
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n9 ⟨c101, hl⟩) with c102 | c102
                    · 
                      exact Frame20.om4dz2 F hx hα hβ (by linarith only [c93p]) (by linarith only [c94p]) (by linarith only [c92p]) (by linarith only [c91p]) (by linarith only [c101, (neg_pos.2 c102)]) (by linarith only [c101, (neg_pos.2 c102)]) (by linarith only [c101, (neg_pos.2 c102)]) hHR
                    · 
                      exact Frame20.om4dz1 F hx hα hβ (by linarith only [c93p]) (by linarith only [c94p]) (by linarith only [c92p]) (by linarith only [c91p]) (by linarith only [c101, c102]) (by linarith only [c101, c102]) (by linarith only [c101, c102]) hHR
                  · 
                    exact Frame20.om4dp F hx hα hβ (by linarith only [c93p]) (by linarith only [c94p]) (by linarith only [c92p]) (by linarith only [c91p]) (by linarith only [c101]) hHR
            · 
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c103 | c103
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c104 | c104 | c104
                · 
                  exact Frame20.om1n F hx hα hβ (by linarith only [c93p]) (by linarith only [c103]) (by linarith only [(neg_pos.2 c104)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n7 ⟨c104, hl⟩) with c105 | c105
                  · 
                    exact Frame20.om1z2 F hx hα hβ (by linarith only [c93p]) (by linarith only [c103]) (by linarith only [c104, (neg_pos.2 c105)]) (by linarith only [c104, (neg_pos.2 c105)]) (by linarith only [c104, (neg_pos.2 c105)]) hH
                  · 
                    exact Frame20.om1z1 F hx hα hβ (by linarith only [c93p]) (by linarith only [c103]) (by linarith only [c104, c105]) (by linarith only [c104, c105]) (by linarith only [c104, c105]) hH
                · 
                  exact Frame20.om1p F hx hα hβ (by linarith only [c93p]) (by linarith only [c103]) (by linarith only [c104]) hH
              · have c103p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c103]
                rcases lt_trichotomy ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) 0 with c106 | c106 | c106
                · 
                  exact Frame20.om4bn F hx hα hβ (by linarith only [c93p]) (by linarith only [c94]) (by linarith only [c92p]) (by linarith only [c91p]) (by linarith only [(neg_pos.2 c106)])
                · 
                  rcases lt_or_gt_of_ne (fun hl => n10 ⟨c106, hl⟩) with c107 | c107
                  · 
                    exact Frame20.om4bz2 F hx hα hβ (by linarith only [c93p]) (by linarith only [c94]) (by linarith only [c92p]) (by linarith only [c91p]) (by linarith only [c106, (neg_pos.2 c107)]) (by linarith only [c106, (neg_pos.2 c107)]) (by linarith only [c106, (neg_pos.2 c107)])
                  · 
                    exact Frame20.om4bz1 F hx hα hβ (by linarith only [c93p]) (by linarith only [c94]) (by linarith only [c92p]) (by linarith only [c91p]) (by linarith only [c106, c107]) (by linarith only [c106, c107]) (by linarith only [c106, c107])
                · 
                  exact Frame20.om4bp F hx hα hβ (by linarith only [c93p]) (by linarith only [c94]) (by linarith only [c92p]) (by linarith only [c91p]) (by linarith only [c106])
          · 
            rcases lt_or_gt_of_ne n6 with c108 | c108
            · have c108p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c108
              rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c109 | c109
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c110 | c110 | c110
                · 
                  exact Frame20.om1n_R F hx hα hβ (by linarith only [c108p]) (by linarith only [c109]) (by linarith only [(neg_pos.2 c110)]) hHR
                · 
                  rcases lt_or_gt_of_ne (fun hl => n8 ⟨c110, hl⟩) with c111 | c111
                  · 
                    exact Frame20.om1z2_R F hx hα hβ (by linarith only [c108p]) (by linarith only [c109]) (by linarith only [c110, (neg_pos.2 c111)]) (by linarith only [c110, (neg_pos.2 c111)]) (by linarith only [c110, (neg_pos.2 c111)]) hHR
                  · 
                    exact Frame20.om1z1_R F hx hα hβ (by linarith only [c108p]) (by linarith only [c109]) (by linarith only [c110, c111]) (by linarith only [c110, c111]) (by linarith only [c110, c111]) hHR
                · 
                  exact Frame20.om1p_R F hx hα hβ (by linarith only [c108p]) (by linarith only [c109]) (by linarith only [c110]) hHR
              · have c109p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c109]
                rcases le_or_gt 0 (F.S.tm - F.S.tp) with c112 | c112
                · 
                  exact Frame20.om2b F hx hα hβ (by linarith only [c93]) (by linarith only [c2]) (by linarith only [c1p, c2]) (by linarith only [c112]) (by linarith only [c1p]) hH
                · have c112p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c112]
                  rcases lt_trichotomy ((-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) 0 with c113 | c113 | c113
                  · 
                    exact Frame20.om4an_R F hx hα hβ (by linarith only [c108p]) (by linarith only [c93]) (by linarith only [c2]) (by linarith only [(mul_pos htm1 c1p), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c1p]) (by linarith only [c112p]) (by linarith only [(neg_pos.2 c113)]) hH
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n20 ⟨c113, hl⟩) with c114 | c114
                    · 
                      exact Frame20.om4az2_R F hx hα hβ (by linarith only [c108p]) (by linarith only [c93]) (by linarith only [c2]) (by linarith only [(mul_pos htm1 c1p), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c1p]) (by linarith only [c112p]) (by linarith only [c113, (neg_pos.2 c114)]) (by linarith only [c113, (neg_pos.2 c114)]) (by linarith only [c113, (neg_pos.2 c114)]) hH
                    · 
                      exact Frame20.om4az1_R F hx hα hβ (by linarith only [c108p]) (by linarith only [c93]) (by linarith only [c2]) (by linarith only [(mul_pos htm1 c1p), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c1p]) (by linarith only [c112p]) (by linarith only [c113, c114]) (by linarith only [c113, c114]) (by linarith only [c113, c114]) hH
                  · 
                    exact Frame20.om4ap_R F hx hα hβ (by linarith only [c108p]) (by linarith only [c93]) (by linarith only [c2]) (by linarith only [(mul_pos htm1 c1p), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c1p]) (by linarith only [c112p]) (by linarith only [c113]) hH
            · 
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c115 | c115
              · 
                exact Frame20.om2b F hx hα hβ (by linarith only [c93]) (by linarith only [c2]) (by linarith only [c1p, c2]) (by linarith only [c115]) (by linarith only [c1p]) hH
              · have c115p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c115]
                rcases le_or_gt 0 (F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km) with c116 | c116
                · 
                  rcases lt_or_ge 0 ((F.S.sm^2 - F.S.sm) * (F.a22 - F.a12) + (F.S.sm^2 - 2*F.S.sm + 1) * F.a12 + (F.S.km^2) * F.gg) with c117 | c117
                  · 
                    exact Frame20.famA1_R F hx hα hβ (by linarith only [c108]) (by refine pos_of_pos_mul rm ?_; linarith only [(mul_pos F.S.kp_pos rm), (mul_nonneg (c108).le c116), (mul_pos (mul_pos htp1 F.S.km_pos) c92p), (mul_pos (mul_pos hsm1 F.S.hp_pos) c92p)]) (by refine pos_of_pos_mul htm1 ?_; linarith only [(mul_pos htp1 c1p), (mul_pos htp1 c2), (mul_nonneg (mul_nonneg (F.S.tp_pos).le (hsp1).le) c116), (mul_pos (mul_pos F.S.tp_pos hsm1) c1p), (mul_pos (mul_pos F.S.tp_pos hsm1) c2)]) (by linarith only [c117])
                  · 
                    exact Frame20.famA2_R F hx hα hβ (by linarith only [c108]) (by refine pos_of_pos_mul rm ?_; linarith only [(mul_pos F.S.kp_pos rm), (mul_nonneg (c108).le c116), (mul_pos (mul_pos htp1 F.S.km_pos) c92p), (mul_pos (mul_pos hsm1 F.S.hp_pos) c92p)]) (by refine pos_of_pos_mul htm1 ?_; linarith only [(mul_pos htp1 c1p), (mul_pos htp1 c2), (mul_nonneg (mul_nonneg (F.S.tp_pos).le (hsp1).le) c116), (mul_pos (mul_pos F.S.tp_pos hsm1) c1p), (mul_pos (mul_pos F.S.tp_pos hsm1) c2)]) (by linarith only [c117])
                · have c116p : 0 < -(F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km) := by linarith only [c116]
                  rcases le_or_gt 0 (-F.S.hp*F.S.sp + F.S.hp + F.S.km*F.S.sp*F.S.tp - F.S.km*F.S.tp + F.S.kp*F.S.sm*F.S.tp - F.S.kp) with c118 | c118
                  · 
                    rcases lt_or_ge 0 ((F.S.tp^2 - F.S.tp) * (F.a11 - F.a12) + (F.S.tp^2 - 2*F.S.tp + 1) * F.a12 + (F.S.hp^2) * F.gg) with c119 | c119
                    · 
                      exact Frame20.famA1 F hx hα hβ (by linarith only [c93]) (by refine pos_of_pos_mul rp ?_; linarith only [(mul_nonneg (F.S.hm_pos).le c118), (mul_nonneg (c93).le c118), (mul_pos (mul_pos F.S.tp_pos F.S.km_pos) c2), (mul_pos (mul_pos F.S.tm_pos F.S.km_pos) c1p), (mul_pos (mul_pos hsm1 F.S.hm_pos) c1p), (mul_pos (mul_pos hsm1 c1p) c93)]) (by linarith only [c116p]) (by linarith only [c119])
                    · 
                      exact Frame20.famA2 F hx hα hβ (by linarith only [c93]) (by refine pos_of_pos_mul rp ?_; linarith only [(mul_nonneg (F.S.hm_pos).le c118), (mul_nonneg (c93).le c118), (mul_pos (mul_pos F.S.tp_pos F.S.km_pos) c2), (mul_pos (mul_pos F.S.tm_pos F.S.km_pos) c1p), (mul_pos (mul_pos hsm1 F.S.hm_pos) c1p), (mul_pos (mul_pos hsm1 c1p) c93)]) (by linarith only [c116p]) (by linarith only [c119])
                  · have c118p : 0 < -(-F.S.hp*F.S.sp + F.S.hp + F.S.km*F.S.sp*F.S.tp - F.S.km*F.S.tp + F.S.kp*F.S.sm*F.S.tp - F.S.kp) := by linarith only [c118]
                    rcases le_or_gt 0 (-F.S.hm*F.S.sm*F.S.tp - F.S.hp*F.S.sm*F.S.tm + F.S.km*F.S.tm) with c120 | c120
                    · 
                      rcases le_or_gt 0 (F.S.hp*F.S.sp - F.S.km*F.S.sp*F.S.tp - F.S.kp*F.S.sm*F.S.tp) with c121 | c121
                      · 
                        exact Frame20.famE F hx hα hβ (by linarith only [c93]) (by linarith only [c108]) (by linarith only [c120]) (by linarith only [c121])
                      · have c121p : 0 < -(F.S.hp*F.S.sp - F.S.km*F.S.sp*F.S.tp - F.S.kp*F.S.sm*F.S.tp) := by linarith only [c121]
                        rcases lt_or_ge 0 ((F.S.sm^2 - F.S.sm) * (F.a22 - F.a12) + (F.S.sm^2 - 2*F.S.sm + 1) * F.a12 + (F.S.km^2) * F.gg) with c122 | c122
                        · 
                          exact Frame20.famA1_R F hx hα hβ (by linarith only [c108]) (by linarith only [c121p]) (by linarith only [c118p]) (by linarith only [c122])
                        · 
                          exact Frame20.famA2_R F hx hα hβ (by linarith only [c108]) (by linarith only [c121p]) (by linarith only [c118p]) (by linarith only [c122])
                    · have c120p : 0 < -(-F.S.hm*F.S.sm*F.S.tp - F.S.hp*F.S.sm*F.S.tm + F.S.km*F.S.tm) := by linarith only [c120]
                      rcases lt_or_ge 0 ((F.S.tp^2 - F.S.tp) * (F.a11 - F.a12) + (F.S.tp^2 - 2*F.S.tp + 1) * F.a12 + (F.S.hp^2) * F.gg) with c123 | c123
                      · 
                        exact Frame20.famA1 F hx hα hβ (by linarith only [c93]) (by linarith only [c120p]) (by linarith only [c116p]) (by linarith only [c123])
                      · 
                        exact Frame20.famA2 F hx hα hβ (by linarith only [c93]) (by linarith only [c120p]) (by linarith only [c116p]) (by linarith only [c123])
        · 
          rcases lt_or_gt_of_ne n5 with c124 | c124
          · have c124p : 0 < -(F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) := neg_pos.2 c124
            rcases lt_or_gt_of_ne n6 with c125 | c125
            · have c125p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c125
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c126 | c126
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c127 | c127 | c127
                · 
                  exact Frame20.om1n F hx hα hβ (by linarith only [c124p]) (by linarith only [c126]) (by linarith only [(neg_pos.2 c127)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n7 ⟨c127, hl⟩) with c128 | c128
                  · 
                    exact Frame20.om1z2 F hx hα hβ (by linarith only [c124p]) (by linarith only [c126]) (by linarith only [c127, (neg_pos.2 c128)]) (by linarith only [c127, (neg_pos.2 c128)]) (by linarith only [c127, (neg_pos.2 c128)]) hH
                  · 
                    exact Frame20.om1z1 F hx hα hβ (by linarith only [c124p]) (by linarith only [c126]) (by linarith only [c127, c128]) (by linarith only [c127, c128]) (by linarith only [c127, c128]) hH
                · 
                  exact Frame20.om1p F hx hα hβ (by linarith only [c124p]) (by linarith only [c126]) (by linarith only [c127]) hH
              · have c126p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c126]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c129 | c129
                · 
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c130 | c130 | c130
                  · 
                    exact Frame20.om1n_R F hx hα hβ (by linarith only [c125p]) (by linarith only [c129]) (by linarith only [(neg_pos.2 c130)]) hHR
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n8 ⟨c130, hl⟩) with c131 | c131
                    · 
                      exact Frame20.om1z2_R F hx hα hβ (by linarith only [c125p]) (by linarith only [c129]) (by linarith only [c130, (neg_pos.2 c131)]) (by linarith only [c130, (neg_pos.2 c131)]) (by linarith only [c130, (neg_pos.2 c131)]) hHR
                    · 
                      exact Frame20.om1z1_R F hx hα hβ (by linarith only [c125p]) (by linarith only [c129]) (by linarith only [c130, c131]) (by linarith only [c130, c131]) (by linarith only [c130, c131]) hHR
                  · 
                    exact Frame20.om1p_R F hx hα hβ (by linarith only [c125p]) (by linarith only [c129]) (by linarith only [c130]) hHR
                · have c129p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c129]
                  rcases lt_trichotomy ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) 0 with c132 | c132 | c132
                  · 
                    rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c133 | c133 | c133
                    · 
                      exact Frame20.om4cnom F hx hα hβ (by linarith only [c124p]) (by linarith only [c125p]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c129p]) (by linarith only [(neg_pos.2 c132), (neg_pos.2 c133)]) (by linarith only [(neg_pos.2 c132), (neg_pos.2 c133)]) hHR
                    · 
                      rcases lt_or_gt_of_ne (fun hl => n13 ⟨c133, hl⟩) with c134 | c134
                      · 
                        exact Frame20.om4cnoz2 F hx hα hβ (by linarith only [c124p]) (by linarith only [c125p]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c129p]) (by linarith only [(neg_pos.2 c132), c133, (neg_pos.2 c134)]) (by linarith only [(neg_pos.2 c132), c133, (neg_pos.2 c134)]) (by linarith only [(neg_pos.2 c132), c133, (neg_pos.2 c134)]) (by linarith only [(neg_pos.2 c132), c133, (neg_pos.2 c134)]) hHR
                      · 
                        exact Frame20.om4cnoz1 F hx hα hβ (by linarith only [c124p]) (by linarith only [c125p]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c129p]) (by linarith only [(neg_pos.2 c132), c133, c134]) (by linarith only [(neg_pos.2 c132), c133, c134]) (by linarith only [(neg_pos.2 c132), c133, c134]) (by linarith only [(neg_pos.2 c132), c133, c134]) hHR
                    · 
                      exact Frame20.om4cnop F hx hα hβ (by linarith only [c124p]) (by linarith only [c125p]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c129p]) (by linarith only [(neg_pos.2 c132), c133]) (by linarith only [(neg_pos.2 c132), c133]) hHR
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n12 ⟨c132, hl⟩) with c135 | c135
                    · 
                      exact Frame20.om4cz2 F hx hα hβ (by linarith only [c124p]) (by linarith only [c125p]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c129p]) (by linarith only [c132, (neg_pos.2 c135)]) (by linarith only [c132, (neg_pos.2 c135)]) (by linarith only [c132, (neg_pos.2 c135)]) hHR
                    · 
                      exact Frame20.om4cz1 F hx hα hβ (by linarith only [c124p]) (by linarith only [c125p]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c129p]) (by linarith only [c132, c135]) (by linarith only [c132, c135]) (by linarith only [c132, c135]) hHR
                  · 
                    exact Frame20.om4cp F hx hα hβ (by linarith only [c124p]) (by linarith only [c125p]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c129p]) (by linarith only [c132]) hHR
            · 
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c136 | c136
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c137 | c137 | c137
                · 
                  exact Frame20.om1n F hx hα hβ (by linarith only [c124p]) (by linarith only [c136]) (by linarith only [(neg_pos.2 c137)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n7 ⟨c137, hl⟩) with c138 | c138
                  · 
                    exact Frame20.om1z2 F hx hα hβ (by linarith only [c124p]) (by linarith only [c136]) (by linarith only [c137, (neg_pos.2 c138)]) (by linarith only [c137, (neg_pos.2 c138)]) (by linarith only [c137, (neg_pos.2 c138)]) hH
                  · 
                    exact Frame20.om1z1 F hx hα hβ (by linarith only [c124p]) (by linarith only [c136]) (by linarith only [c137, c138]) (by linarith only [c137, c138]) (by linarith only [c137, c138]) hH
                · 
                  exact Frame20.om1p F hx hα hβ (by linarith only [c124p]) (by linarith only [c136]) (by linarith only [c137]) hH
              · have c136p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c136]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c139 | c139
                · 
                  exact Frame20.om2b_R F hx hα hβ (by linarith only [c125]) (by linarith only [c92]) (by linarith only [(mul_pos hsp1 c91p), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c139]) (by linarith only [c91p]) hHR
                · have c139p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c139]
                  rcases lt_trichotomy ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg) 0 with c140 | c140 | c140
                  · 
                    exact Frame20.om4an F hx hα hβ (by linarith only [c124p]) (by linarith only [c125]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c139p]) (by linarith only [(neg_pos.2 c140)]) hHR
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n14 ⟨c140, hl⟩) with c141 | c141
                    · 
                      exact Frame20.om4az2 F hx hα hβ (by linarith only [c124p]) (by linarith only [c125]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c139p]) (by linarith only [c140, (neg_pos.2 c141)]) (by linarith only [c140, (neg_pos.2 c141)]) (by linarith only [c140, (neg_pos.2 c141)]) hHR
                    · 
                      exact Frame20.om4az1 F hx hα hβ (by linarith only [c124p]) (by linarith only [c125]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c139p]) (by linarith only [c140, c141]) (by linarith only [c140, c141]) (by linarith only [c140, c141]) hHR
                  · 
                    exact Frame20.om4ap F hx hα hβ (by linarith only [c124p]) (by linarith only [c125]) (by linarith only [c92]) (by linarith only [c91p, c92]) (by linarith only [c91p]) (by linarith only [c139p]) (by linarith only [c140]) hHR
          · 
            rcases lt_or_gt_of_ne n6 with c142 | c142
            · have c142p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c142
              rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c143 | c143
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c144 | c144 | c144
                · 
                  exact Frame20.om1n_R F hx hα hβ (by linarith only [c142p]) (by linarith only [c143]) (by linarith only [(neg_pos.2 c144)]) hHR
                · 
                  rcases lt_or_gt_of_ne (fun hl => n8 ⟨c144, hl⟩) with c145 | c145
                  · 
                    exact Frame20.om1z2_R F hx hα hβ (by linarith only [c142p]) (by linarith only [c143]) (by linarith only [c144, (neg_pos.2 c145)]) (by linarith only [c144, (neg_pos.2 c145)]) (by linarith only [c144, (neg_pos.2 c145)]) hHR
                  · 
                    exact Frame20.om1z1_R F hx hα hβ (by linarith only [c142p]) (by linarith only [c143]) (by linarith only [c144, c145]) (by linarith only [c144, c145]) (by linarith only [c144, c145]) hHR
                · 
                  exact Frame20.om1p_R F hx hα hβ (by linarith only [c142p]) (by linarith only [c143]) (by linarith only [c144]) hHR
              · have c143p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c143]
                rcases le_or_gt 0 (F.S.tm - F.S.tp) with c146 | c146
                · 
                  exact Frame20.om2b F hx hα hβ (by linarith only [c124]) (by linarith only [c2]) (by linarith only [(mul_pos htm1 c1p), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c146]) (by linarith only [c1p]) hH
                · have c146p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c146]
                  rcases lt_trichotomy ((-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg) 0 with c147 | c147 | c147
                  · 
                    exact Frame20.om4an_R F hx hα hβ (by linarith only [c142p]) (by linarith only [c124]) (by linarith only [c2]) (by linarith only [c1p, c2]) (by linarith only [c1p]) (by linarith only [c146p]) (by linarith only [(neg_pos.2 c147)]) hH
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n20 ⟨c147, hl⟩) with c148 | c148
                    · 
                      exact Frame20.om4az2_R F hx hα hβ (by linarith only [c142p]) (by linarith only [c124]) (by linarith only [c2]) (by linarith only [c1p, c2]) (by linarith only [c1p]) (by linarith only [c146p]) (by linarith only [c147, (neg_pos.2 c148)]) (by linarith only [c147, (neg_pos.2 c148)]) (by linarith only [c147, (neg_pos.2 c148)]) hH
                    · 
                      exact Frame20.om4az1_R F hx hα hβ (by linarith only [c142p]) (by linarith only [c124]) (by linarith only [c2]) (by linarith only [c1p, c2]) (by linarith only [c1p]) (by linarith only [c146p]) (by linarith only [c147, c148]) (by linarith only [c147, c148]) (by linarith only [c147, c148]) hH
                  · 
                    exact Frame20.om4ap_R F hx hα hβ (by linarith only [c142p]) (by linarith only [c124]) (by linarith only [c2]) (by linarith only [c1p, c2]) (by linarith only [c1p]) (by linarith only [c146p]) (by linarith only [c147]) hH
            · 
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c149 | c149
              · 
                exact Frame20.om2b F hx hα hβ (by linarith only [c124]) (by linarith only [c2]) (by linarith only [c1p, c2]) (by linarith only [c149]) (by linarith only [c1p]) hH
              · have c149p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c149]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c150 | c150
                · 
                  exact Frame20.om2b_R F hx hα hβ (by linarith only [c142]) (by linarith only [c92]) (by linarith only [(mul_pos hsp1 c91p), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c150]) (by linarith only [c91p]) hHR
                · have c150p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c150]
                  rcases le_or_gt 0 (F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km) with c151 | c151
                  · 
                    rcases lt_or_ge 0 ((F.S.sm^2 - F.S.sm) * (F.a22 - F.a12) + (F.S.sm^2 - 2*F.S.sm + 1) * F.a12 + (F.S.km^2) * F.gg) with c152 | c152
                    · 
                      exact Frame20.famA1_R F hx hα hβ (by linarith only [c142]) (by refine pos_of_pos_mul rm ?_; linarith only [(mul_pos (mul_pos htp1 F.S.kp_pos) c91p), (mul_pos (mul_pos htp1 c91p) c142), (mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) c91p), (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.km_pos).le) c151), (mul_pos (mul_pos F.S.sm_pos F.S.hp_pos) c92), (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.kp_pos).le) c151)]) (by refine pos_of_pos_mul htm1 ?_; linarith only [(mul_pos htp1 c1p), (mul_pos hsm1 c2), (mul_nonneg (mul_nonneg (F.S.tp_pos).le (hsp1).le) c151), (mul_pos (mul_pos F.S.tp_pos hsm1) c1p), (mul_pos (mul_pos htp1 F.S.sm_pos) c2)]) (by linarith only [c152])
                    · 
                      exact Frame20.famA2_R F hx hα hβ (by linarith only [c142]) (by refine pos_of_pos_mul rm ?_; linarith only [(mul_pos (mul_pos htp1 F.S.kp_pos) c91p), (mul_pos (mul_pos htp1 c91p) c142), (mul_pos (mul_pos F.S.sp_pos F.S.hp_pos) c91p), (mul_nonneg (mul_nonneg (F.S.sp_pos).le (F.S.km_pos).le) c151), (mul_pos (mul_pos F.S.sm_pos F.S.hp_pos) c92), (mul_nonneg (mul_nonneg (F.S.sm_pos).le (F.S.kp_pos).le) c151)]) (by refine pos_of_pos_mul htm1 ?_; linarith only [(mul_pos htp1 c1p), (mul_pos hsm1 c2), (mul_nonneg (mul_nonneg (F.S.tp_pos).le (hsp1).le) c151), (mul_pos (mul_pos F.S.tp_pos hsm1) c1p), (mul_pos (mul_pos htp1 F.S.sm_pos) c2)]) (by linarith only [c152])
                  · have c151p : 0 < -(F.S.hm*F.S.sm*F.S.tp - F.S.hm + F.S.hp*F.S.sm*F.S.tm - F.S.hp*F.S.sm - F.S.km*F.S.tm + F.S.km) := by linarith only [c151]
                    rcases le_or_gt 0 (-F.S.hp*F.S.sp + F.S.hp + F.S.km*F.S.sp*F.S.tp - F.S.km*F.S.tp + F.S.kp*F.S.sm*F.S.tp - F.S.kp) with c153 | c153
                    · 
                      rcases lt_or_ge 0 ((F.S.tp^2 - F.S.tp) * (F.a11 - F.a12) + (F.S.tp^2 - 2*F.S.tp + 1) * F.a12 + (F.S.hp^2) * F.gg) with c154 | c154
                      · 
                        exact Frame20.famA1 F hx hα hβ (by linarith only [c124]) (by refine pos_of_pos_mul rp ?_; linarith only [(mul_nonneg (F.S.hm_pos).le c153), (mul_nonneg (c124).le c153), (mul_pos (mul_pos F.S.tp_pos F.S.km_pos) c2), (mul_pos (mul_pos F.S.tm_pos F.S.km_pos) c1p), (mul_pos (mul_pos hsm1 F.S.hm_pos) c1p), (mul_pos (mul_pos hsm1 c1p) c124)]) (by linarith only [c151p]) (by linarith only [c154])
                      · 
                        exact Frame20.famA2 F hx hα hβ (by linarith only [c124]) (by refine pos_of_pos_mul rp ?_; linarith only [(mul_nonneg (F.S.hm_pos).le c153), (mul_nonneg (c124).le c153), (mul_pos (mul_pos F.S.tp_pos F.S.km_pos) c2), (mul_pos (mul_pos F.S.tm_pos F.S.km_pos) c1p), (mul_pos (mul_pos hsm1 F.S.hm_pos) c1p), (mul_pos (mul_pos hsm1 c1p) c124)]) (by linarith only [c151p]) (by linarith only [c154])
                    · have c153p : 0 < -(-F.S.hp*F.S.sp + F.S.hp + F.S.km*F.S.sp*F.S.tp - F.S.km*F.S.tp + F.S.kp*F.S.sm*F.S.tp - F.S.kp) := by linarith only [c153]
                      rcases le_or_gt 0 (-F.S.hm*F.S.sm*F.S.tp - F.S.hp*F.S.sm*F.S.tm + F.S.km*F.S.tm) with c155 | c155
                      · 
                        rcases le_or_gt 0 (F.S.hp*F.S.sp - F.S.km*F.S.sp*F.S.tp - F.S.kp*F.S.sm*F.S.tp) with c156 | c156
                        · 
                          exact Frame20.famE F hx hα hβ (by linarith only [c124]) (by linarith only [c142]) (by linarith only [c155]) (by linarith only [c156])
                        · have c156p : 0 < -(F.S.hp*F.S.sp - F.S.km*F.S.sp*F.S.tp - F.S.kp*F.S.sm*F.S.tp) := by linarith only [c156]
                          rcases lt_or_ge 0 ((F.S.sm^2 - F.S.sm) * (F.a22 - F.a12) + (F.S.sm^2 - 2*F.S.sm + 1) * F.a12 + (F.S.km^2) * F.gg) with c157 | c157
                          · 
                            exact Frame20.famA1_R F hx hα hβ (by linarith only [c142]) (by linarith only [c156p]) (by linarith only [c153p]) (by linarith only [c157])
                          · 
                            exact Frame20.famA2_R F hx hα hβ (by linarith only [c142]) (by linarith only [c156p]) (by linarith only [c153p]) (by linarith only [c157])
                      · have c155p : 0 < -(-F.S.hm*F.S.sm*F.S.tp - F.S.hp*F.S.sm*F.S.tm + F.S.km*F.S.tm) := by linarith only [c155]
                        rcases lt_or_ge 0 ((F.S.tp^2 - F.S.tp) * (F.a11 - F.a12) + (F.S.tp^2 - 2*F.S.tp + 1) * F.a12 + (F.S.hp^2) * F.gg) with c158 | c158
                        · 
                          exact Frame20.famA1 F hx hα hβ (by linarith only [c124]) (by linarith only [c155p]) (by linarith only [c151p]) (by linarith only [c158])
                        · 
                          exact Frame20.famA2 F hx hα hβ (by linarith only [c124]) (by linarith only [c155p]) (by linarith only [c151p]) (by linarith only [c158])
      · 
        rcases lt_or_gt_of_ne n15 with c159 | c159
        · have c159p : 0 < -(F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) := neg_pos.2 c159
          rcases lt_or_gt_of_ne n5 with c160 | c160
          · have c160p : 0 < -(F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) := neg_pos.2 c160
            rcases lt_or_gt_of_ne n6 with c161 | c161
            · have c161p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c161
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c162 | c162
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c163 | c163 | c163
                · 
                  exact Frame20.om1n F hx hα hβ (by linarith only [c160p]) (by linarith only [c162]) (by linarith only [(neg_pos.2 c163)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n7 ⟨c163, hl⟩) with c164 | c164
                  · 
                    exact Frame20.om1z2 F hx hα hβ (by linarith only [c160p]) (by linarith only [c162]) (by linarith only [c163, (neg_pos.2 c164)]) (by linarith only [c163, (neg_pos.2 c164)]) (by linarith only [c163, (neg_pos.2 c164)]) hH
                  · 
                    exact Frame20.om1z1 F hx hα hβ (by linarith only [c160p]) (by linarith only [c162]) (by linarith only [c163, c164]) (by linarith only [c163, c164]) (by linarith only [c163, c164]) hH
                · 
                  exact Frame20.om1p F hx hα hβ (by linarith only [c160p]) (by linarith only [c162]) (by linarith only [c163]) hH
              · have c162p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c162]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c165 | c165
                · 
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c166 | c166 | c166
                  · 
                    exact Frame20.om1n_R F hx hα hβ (by linarith only [c161p]) (by linarith only [c165]) (by linarith only [(neg_pos.2 c166)]) hHR
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n8 ⟨c166, hl⟩) with c167 | c167
                    · 
                      exact Frame20.om1z2_R F hx hα hβ (by linarith only [c161p]) (by linarith only [c165]) (by linarith only [c166, (neg_pos.2 c167)]) (by linarith only [c166, (neg_pos.2 c167)]) (by linarith only [c166, (neg_pos.2 c167)]) hHR
                    · 
                      exact Frame20.om1z1_R F hx hα hβ (by linarith only [c161p]) (by linarith only [c165]) (by linarith only [c166, c167]) (by linarith only [c166, c167]) (by linarith only [c166, c167]) hHR
                  · 
                    exact Frame20.om1p_R F hx hα hβ (by linarith only [c161p]) (by linarith only [c165]) (by linarith only [c166]) hHR
                · have c165p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c165]
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c168 | c168 | c168
                  · 
                    exact Frame20.om3n_R F hx hα hβ (by linarith only [c161p]) (by linarith only [(mul_pos F.S.sp_pos c91), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c159p]) (by linarith only [c91]) (by linarith only [(neg_pos.2 c168)]) hHR
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n16 ⟨c168, hl⟩) with c169 | c169
                    · 
                      exact Frame20.om3z2_R F hx hα hβ (by linarith only [c161p]) (by linarith only [(mul_pos F.S.sp_pos c91), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c159p]) (by linarith only [c91]) (by linarith only [c168, (neg_pos.2 c169)]) (by linarith only [c168, (neg_pos.2 c169)]) (by linarith only [c168, (neg_pos.2 c169)]) hHR
                    · 
                      exact Frame20.om3z1_R F hx hα hβ (by linarith only [c161p]) (by linarith only [(mul_pos F.S.sp_pos c91), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c159p]) (by linarith only [c91]) (by linarith only [c168, c169]) (by linarith only [c168, c169]) (by linarith only [c168, c169]) hHR
                  · 
                    exact Frame20.om3p_R F hx hα hβ (by linarith only [c161p]) (by linarith only [(mul_pos F.S.sp_pos c91), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c159p]) (by linarith only [c91]) (by linarith only [c168]) hHR
            · 
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c170 | c170
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c171 | c171 | c171
                · 
                  exact Frame20.om1n F hx hα hβ (by linarith only [c160p]) (by linarith only [c170]) (by linarith only [(neg_pos.2 c171)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n7 ⟨c171, hl⟩) with c172 | c172
                  · 
                    exact Frame20.om1z2 F hx hα hβ (by linarith only [c160p]) (by linarith only [c170]) (by linarith only [c171, (neg_pos.2 c172)]) (by linarith only [c171, (neg_pos.2 c172)]) (by linarith only [c171, (neg_pos.2 c172)]) hH
                  · 
                    exact Frame20.om1z1 F hx hα hβ (by linarith only [c160p]) (by linarith only [c170]) (by linarith only [c171, c172]) (by linarith only [c171, c172]) (by linarith only [c171, c172]) hH
                · 
                  exact Frame20.om1p F hx hα hβ (by linarith only [c160p]) (by linarith only [c170]) (by linarith only [c171]) hH
              · have c170p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c170]
                exact Frame20.om2a_R F hx hα hβ (by linarith only [c161]) (by linarith only [(mul_pos F.S.sp_pos c91), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c159p]) (by linarith only [c91]) hHR
          · 
            rcases lt_or_gt_of_ne n6 with c173 | c173
            · have c173p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c173
              rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c174 | c174
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c175 | c175 | c175
                · 
                  exact Frame20.om1n_R F hx hα hβ (by linarith only [c173p]) (by linarith only [c174]) (by linarith only [(neg_pos.2 c175)]) hHR
                · 
                  rcases lt_or_gt_of_ne (fun hl => n8 ⟨c175, hl⟩) with c176 | c176
                  · 
                    exact Frame20.om1z2_R F hx hα hβ (by linarith only [c173p]) (by linarith only [c174]) (by linarith only [c175, (neg_pos.2 c176)]) (by linarith only [c175, (neg_pos.2 c176)]) (by linarith only [c175, (neg_pos.2 c176)]) hHR
                  · 
                    exact Frame20.om1z1_R F hx hα hβ (by linarith only [c173p]) (by linarith only [c174]) (by linarith only [c175, c176]) (by linarith only [c175, c176]) (by linarith only [c175, c176]) hHR
                · 
                  exact Frame20.om1p_R F hx hα hβ (by linarith only [c173p]) (by linarith only [c174]) (by linarith only [c175]) hHR
              · have c174p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c174]
                rcases le_or_gt 0 (F.S.tm - F.S.tp) with c177 | c177
                · 
                  exact Frame20.om2b F hx hα hβ (by linarith only [c160]) (by linarith only [c2]) (by linarith only [c1p, c2]) (by linarith only [c177]) (by linarith only [c1p]) hH
                · have c177p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c177]
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c178 | c178 | c178
                  · 
                    exact Frame20.om3n_R F hx hα hβ (by linarith only [c173p]) (by linarith only [(mul_pos F.S.sp_pos c91), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c159p]) (by linarith only [c91]) (by linarith only [(neg_pos.2 c178)]) hHR
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n16 ⟨c178, hl⟩) with c179 | c179
                    · 
                      exact Frame20.om3z2_R F hx hα hβ (by linarith only [c173p]) (by linarith only [(mul_pos F.S.sp_pos c91), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c159p]) (by linarith only [c91]) (by linarith only [c178, (neg_pos.2 c179)]) (by linarith only [c178, (neg_pos.2 c179)]) (by linarith only [c178, (neg_pos.2 c179)]) hHR
                    · 
                      exact Frame20.om3z1_R F hx hα hβ (by linarith only [c173p]) (by linarith only [(mul_pos F.S.sp_pos c91), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c159p]) (by linarith only [c91]) (by linarith only [c178, c179]) (by linarith only [c178, c179]) (by linarith only [c178, c179]) hHR
                  · 
                    exact Frame20.om3p_R F hx hα hβ (by linarith only [c173p]) (by linarith only [(mul_pos F.S.sp_pos c91), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c159p]) (by linarith only [c91]) (by linarith only [c178]) hHR
            · 
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c180 | c180
              · 
                exact Frame20.om2b F hx hα hβ (by linarith only [c160]) (by linarith only [c2]) (by linarith only [(mul_pos htm1 c1p), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c180]) (by linarith only [c1p]) hH
              · have c180p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c180]
                exact Frame20.om2a_R F hx hα hβ (by linarith only [c173]) (by linarith only [(mul_pos F.S.sp_pos c91), (mul_pos (mul_pos htm1 F.S.sm_pos) F.S.kp_pos)]) (by linarith only [c159p]) (by linarith only [c91]) hHR
        · 
          rcases lt_or_gt_of_ne n17 with c181 | c181
          · have c181p : 0 < -(-F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm - F.S.km*F.S.tm*F.S.tp + F.S.km*F.S.tm + F.S.km*F.S.tp - F.S.km) := neg_pos.2 c181
            exact rupert_of_r (F.rFrame.vTri (by simp only [rFrame_S, Shape20.swap]; exact (by linarith only [c91])) (by simp only [rFrame_S, Shape20.swap]; exact (by linarith only [c159])) (by simp only [rFrame_S, Shape20.swap]; exact (by linarith only [c181p])))
          · 
            rcases lt_or_gt_of_ne n6 with c182 | c182
            · have c182p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c182
              rcases lt_or_gt_of_ne n18 with c183 | c183
              · have c183p : 0 < -(-F.S.hp*F.S.sm + F.S.hp - F.S.km*F.S.tp) := neg_pos.2 c183
                rcases lt_or_gt_of_ne n19 with c184 | c184
                · have c184p : 0 < -(F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm*F.S.tp + F.S.kp) := neg_pos.2 c184
                  exact Frame20.ra4_X_R F hx hα hβ (by linarith only [c91]) (by linarith only [c159]) (by linarith only [c181]) (by linarith only [c182p]) (by linarith only [c183p]) (by linarith only [c184p])
                · 
                  exact Frame20.ra4_Y_R F hx hα hβ (by linarith only [c91]) (by linarith only [c159]) (by linarith only [c181]) (by linarith only [c182p]) (by linarith only [c183p]) (by linarith only [c184])
              · 
                exact Frame20.ra4_tBR_R F hx hα hβ (by linarith only [c182p]) (by linarith only [c183])
            · 
              exact Frame20.ra4_A_R F hx hα hβ (by linarith only [c91]) (by linarith only [c159]) (by linarith only [c181]) (by linarith only [c182])
  · 
    rcases lt_or_gt_of_ne n21 with c185 | c185
    · have c185p : 0 < -(F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp) := neg_pos.2 c185
      rcases lt_or_gt_of_ne n3 with c186 | c186
      · have c186p : 0 < -(-F.S.hm - F.S.km*F.S.tm + F.S.km) := neg_pos.2 c186
        rcases lt_or_gt_of_ne n4 with c187 | c187
        · have c187p : 0 < -(-F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm) := neg_pos.2 c187
          rcases lt_or_gt_of_ne n5 with c188 | c188
          · have c188p : 0 < -(F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) := neg_pos.2 c188
            rcases lt_or_gt_of_ne n6 with c189 | c189
            · have c189p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c189
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c190 | c190
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c191 | c191 | c191
                · 
                  exact Frame20.om1n F hx hα hβ (by linarith only [c188p]) (by linarith only [c190]) (by linarith only [(neg_pos.2 c191)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n7 ⟨c191, hl⟩) with c192 | c192
                  · 
                    exact Frame20.om1z2 F hx hα hβ (by linarith only [c188p]) (by linarith only [c190]) (by linarith only [c191, (neg_pos.2 c192)]) (by linarith only [c191, (neg_pos.2 c192)]) (by linarith only [c191, (neg_pos.2 c192)]) hH
                  · 
                    exact Frame20.om1z1 F hx hα hβ (by linarith only [c188p]) (by linarith only [c190]) (by linarith only [c191, c192]) (by linarith only [c191, c192]) (by linarith only [c191, c192]) hH
                · 
                  exact Frame20.om1p F hx hα hβ (by linarith only [c188p]) (by linarith only [c190]) (by linarith only [c191]) hH
              · have c190p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c190]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c193 | c193
                · 
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c194 | c194 | c194
                  · 
                    exact Frame20.om1n_R F hx hα hβ (by linarith only [c189p]) (by linarith only [c193]) (by linarith only [(neg_pos.2 c194)]) hHR
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n8 ⟨c194, hl⟩) with c195 | c195
                    · 
                      exact Frame20.om1z2_R F hx hα hβ (by linarith only [c189p]) (by linarith only [c193]) (by linarith only [c194, (neg_pos.2 c195)]) (by linarith only [c194, (neg_pos.2 c195)]) (by linarith only [c194, (neg_pos.2 c195)]) hHR
                    · 
                      exact Frame20.om1z1_R F hx hα hβ (by linarith only [c189p]) (by linarith only [c193]) (by linarith only [c194, c195]) (by linarith only [c194, c195]) (by linarith only [c194, c195]) hHR
                  · 
                    exact Frame20.om1p_R F hx hα hβ (by linarith only [c189p]) (by linarith only [c193]) (by linarith only [c194]) hHR
                · have c193p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c193]
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c196 | c196 | c196
                  · 
                    exact Frame20.om3n F hx hα hβ (by linarith only [c188p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [(neg_pos.2 c196)]) hH
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n22 ⟨c196, hl⟩) with c197 | c197
                    · 
                      exact Frame20.om3z2 F hx hα hβ (by linarith only [c188p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c196, (neg_pos.2 c197)]) (by linarith only [c196, (neg_pos.2 c197)]) (by linarith only [c196, (neg_pos.2 c197)]) hH
                    · 
                      exact Frame20.om3z1 F hx hα hβ (by linarith only [c188p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c196, c197]) (by linarith only [c196, c197]) (by linarith only [c196, c197]) hH
                  · 
                    exact Frame20.om3p F hx hα hβ (by linarith only [c188p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c196]) hH
            · 
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c198 | c198
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c199 | c199 | c199
                · 
                  exact Frame20.om1n F hx hα hβ (by linarith only [c188p]) (by linarith only [c198]) (by linarith only [(neg_pos.2 c199)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n7 ⟨c199, hl⟩) with c200 | c200
                  · 
                    exact Frame20.om1z2 F hx hα hβ (by linarith only [c188p]) (by linarith only [c198]) (by linarith only [c199, (neg_pos.2 c200)]) (by linarith only [c199, (neg_pos.2 c200)]) (by linarith only [c199, (neg_pos.2 c200)]) hH
                  · 
                    exact Frame20.om1z1 F hx hα hβ (by linarith only [c188p]) (by linarith only [c198]) (by linarith only [c199, c200]) (by linarith only [c199, c200]) (by linarith only [c199, c200]) hH
                · 
                  exact Frame20.om1p F hx hα hβ (by linarith only [c188p]) (by linarith only [c198]) (by linarith only [c199]) hH
              · have c198p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c198]
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c201 | c201 | c201
                · 
                  exact Frame20.om3n F hx hα hβ (by linarith only [c188p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [(neg_pos.2 c201)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n22 ⟨c201, hl⟩) with c202 | c202
                  · 
                    exact Frame20.om3z2 F hx hα hβ (by linarith only [c188p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c201, (neg_pos.2 c202)]) (by linarith only [c201, (neg_pos.2 c202)]) (by linarith only [c201, (neg_pos.2 c202)]) hH
                  · 
                    exact Frame20.om3z1 F hx hα hβ (by linarith only [c188p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c201, c202]) (by linarith only [c201, c202]) (by linarith only [c201, c202]) hH
                · 
                  exact Frame20.om3p F hx hα hβ (by linarith only [c188p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c201]) hH
          · 
            rcases lt_or_gt_of_ne n6 with c203 | c203
            · have c203p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c203
              rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c204 | c204
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c205 | c205 | c205
                · 
                  exact Frame20.om1n_R F hx hα hβ (by linarith only [c203p]) (by linarith only [c204]) (by linarith only [(neg_pos.2 c205)]) hHR
                · 
                  rcases lt_or_gt_of_ne (fun hl => n8 ⟨c205, hl⟩) with c206 | c206
                  · 
                    exact Frame20.om1z2_R F hx hα hβ (by linarith only [c203p]) (by linarith only [c204]) (by linarith only [c205, (neg_pos.2 c206)]) (by linarith only [c205, (neg_pos.2 c206)]) (by linarith only [c205, (neg_pos.2 c206)]) hHR
                  · 
                    exact Frame20.om1z1_R F hx hα hβ (by linarith only [c203p]) (by linarith only [c204]) (by linarith only [c205, c206]) (by linarith only [c205, c206]) (by linarith only [c205, c206]) hHR
                · 
                  exact Frame20.om1p_R F hx hα hβ (by linarith only [c203p]) (by linarith only [c204]) (by linarith only [c205]) hHR
              · have c204p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c204]
                exact Frame20.om2a F hx hα hβ (by linarith only [c188]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) hH
            · 
              exact Frame20.om2a F hx hα hβ (by linarith only [c188]) (by linarith only [(mul_pos F.S.tm_pos c1), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c185p]) (by linarith only [c1]) hH
        · 
          rcases lt_or_gt_of_ne n5 with c207 | c207
          · have c207p : 0 < -(F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) := neg_pos.2 c207
            rcases lt_or_gt_of_ne n6 with c208 | c208
            · have c208p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c208
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c209 | c209
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c210 | c210 | c210
                · 
                  exact Frame20.om1n F hx hα hβ (by linarith only [c207p]) (by linarith only [c209]) (by linarith only [(neg_pos.2 c210)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n7 ⟨c210, hl⟩) with c211 | c211
                  · 
                    exact Frame20.om1z2 F hx hα hβ (by linarith only [c207p]) (by linarith only [c209]) (by linarith only [c210, (neg_pos.2 c211)]) (by linarith only [c210, (neg_pos.2 c211)]) (by linarith only [c210, (neg_pos.2 c211)]) hH
                  · 
                    exact Frame20.om1z1 F hx hα hβ (by linarith only [c207p]) (by linarith only [c209]) (by linarith only [c210, c211]) (by linarith only [c210, c211]) (by linarith only [c210, c211]) hH
                · 
                  exact Frame20.om1p F hx hα hβ (by linarith only [c207p]) (by linarith only [c209]) (by linarith only [c210]) hH
              · have c209p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c209]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c212 | c212
                · 
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c213 | c213 | c213
                  · 
                    exact Frame20.om1n_R F hx hα hβ (by linarith only [c208p]) (by linarith only [c212]) (by linarith only [(neg_pos.2 c213)]) hHR
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n8 ⟨c213, hl⟩) with c214 | c214
                    · 
                      exact Frame20.om1z2_R F hx hα hβ (by linarith only [c208p]) (by linarith only [c212]) (by linarith only [c213, (neg_pos.2 c214)]) (by linarith only [c213, (neg_pos.2 c214)]) (by linarith only [c213, (neg_pos.2 c214)]) hHR
                    · 
                      exact Frame20.om1z1_R F hx hα hβ (by linarith only [c208p]) (by linarith only [c212]) (by linarith only [c213, c214]) (by linarith only [c213, c214]) (by linarith only [c213, c214]) hHR
                  · 
                    exact Frame20.om1p_R F hx hα hβ (by linarith only [c208p]) (by linarith only [c212]) (by linarith only [c213]) hHR
                · have c212p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c212]
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c215 | c215 | c215
                  · 
                    exact Frame20.om3n F hx hα hβ (by linarith only [c207p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [(neg_pos.2 c215)]) hH
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n22 ⟨c215, hl⟩) with c216 | c216
                    · 
                      exact Frame20.om3z2 F hx hα hβ (by linarith only [c207p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c215, (neg_pos.2 c216)]) (by linarith only [c215, (neg_pos.2 c216)]) (by linarith only [c215, (neg_pos.2 c216)]) hH
                    · 
                      exact Frame20.om3z1 F hx hα hβ (by linarith only [c207p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c215, c216]) (by linarith only [c215, c216]) (by linarith only [c215, c216]) hH
                  · 
                    exact Frame20.om3p F hx hα hβ (by linarith only [c207p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c215]) hH
            · 
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c217 | c217
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c218 | c218 | c218
                · 
                  exact Frame20.om1n F hx hα hβ (by linarith only [c207p]) (by linarith only [c217]) (by linarith only [(neg_pos.2 c218)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n7 ⟨c218, hl⟩) with c219 | c219
                  · 
                    exact Frame20.om1z2 F hx hα hβ (by linarith only [c207p]) (by linarith only [c217]) (by linarith only [c218, (neg_pos.2 c219)]) (by linarith only [c218, (neg_pos.2 c219)]) (by linarith only [c218, (neg_pos.2 c219)]) hH
                  · 
                    exact Frame20.om1z1 F hx hα hβ (by linarith only [c207p]) (by linarith only [c217]) (by linarith only [c218, c219]) (by linarith only [c218, c219]) (by linarith only [c218, c219]) hH
                · 
                  exact Frame20.om1p F hx hα hβ (by linarith only [c207p]) (by linarith only [c217]) (by linarith only [c218]) hH
              · have c217p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c217]
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c220 | c220 | c220
                · 
                  exact Frame20.om3n F hx hα hβ (by linarith only [c207p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [(neg_pos.2 c220)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n22 ⟨c220, hl⟩) with c221 | c221
                  · 
                    exact Frame20.om3z2 F hx hα hβ (by linarith only [c207p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c220, (neg_pos.2 c221)]) (by linarith only [c220, (neg_pos.2 c221)]) (by linarith only [c220, (neg_pos.2 c221)]) hH
                  · 
                    exact Frame20.om3z1 F hx hα hβ (by linarith only [c207p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c220, c221]) (by linarith only [c220, c221]) (by linarith only [c220, c221]) hH
                · 
                  exact Frame20.om3p F hx hα hβ (by linarith only [c207p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c220]) hH
          · 
            rcases lt_or_gt_of_ne n6 with c222 | c222
            · have c222p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c222
              rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c223 | c223
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c224 | c224 | c224
                · 
                  exact Frame20.om1n_R F hx hα hβ (by linarith only [c222p]) (by linarith only [c223]) (by linarith only [(neg_pos.2 c224)]) hHR
                · 
                  rcases lt_or_gt_of_ne (fun hl => n8 ⟨c224, hl⟩) with c225 | c225
                  · 
                    exact Frame20.om1z2_R F hx hα hβ (by linarith only [c222p]) (by linarith only [c223]) (by linarith only [c224, (neg_pos.2 c225)]) (by linarith only [c224, (neg_pos.2 c225)]) (by linarith only [c224, (neg_pos.2 c225)]) hHR
                  · 
                    exact Frame20.om1z1_R F hx hα hβ (by linarith only [c222p]) (by linarith only [c223]) (by linarith only [c224, c225]) (by linarith only [c224, c225]) (by linarith only [c224, c225]) hHR
                · 
                  exact Frame20.om1p_R F hx hα hβ (by linarith only [c222p]) (by linarith only [c223]) (by linarith only [c224]) hHR
              · have c223p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c223]
                exact Frame20.om2a F hx hα hβ (by linarith only [c207]) (by linarith only [(mul_pos F.S.tm_pos c1), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c185p]) (by linarith only [c1]) hH
            · 
              exact Frame20.om2a F hx hα hβ (by linarith only [c207]) (by linarith only [(mul_pos F.S.tm_pos c1), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c185p]) (by linarith only [c1]) hH
      · 
        rcases lt_or_gt_of_ne n15 with c226 | c226
        · have c226p : 0 < -(F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm) := neg_pos.2 c226
          rcases lt_or_gt_of_ne n5 with c227 | c227
          · have c227p : 0 < -(F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) := neg_pos.2 c227
            rcases lt_or_gt_of_ne n6 with c228 | c228
            · have c228p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c228
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c229 | c229
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c230 | c230 | c230
                · 
                  exact Frame20.om1n F hx hα hβ (by linarith only [c227p]) (by linarith only [c229]) (by linarith only [(neg_pos.2 c230)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n7 ⟨c230, hl⟩) with c231 | c231
                  · 
                    exact Frame20.om1z2 F hx hα hβ (by linarith only [c227p]) (by linarith only [c229]) (by linarith only [c230, (neg_pos.2 c231)]) (by linarith only [c230, (neg_pos.2 c231)]) (by linarith only [c230, (neg_pos.2 c231)]) hH
                  · 
                    exact Frame20.om1z1 F hx hα hβ (by linarith only [c227p]) (by linarith only [c229]) (by linarith only [c230, c231]) (by linarith only [c230, c231]) (by linarith only [c230, c231]) hH
                · 
                  exact Frame20.om1p F hx hα hβ (by linarith only [c227p]) (by linarith only [c229]) (by linarith only [c230]) hH
              · have c229p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c229]
                rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c232 | c232
                · 
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c233 | c233 | c233
                  · 
                    exact Frame20.om1n_R F hx hα hβ (by linarith only [c228p]) (by linarith only [c232]) (by linarith only [(neg_pos.2 c233)]) hHR
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n8 ⟨c233, hl⟩) with c234 | c234
                    · 
                      exact Frame20.om1z2_R F hx hα hβ (by linarith only [c228p]) (by linarith only [c232]) (by linarith only [c233, (neg_pos.2 c234)]) (by linarith only [c233, (neg_pos.2 c234)]) (by linarith only [c233, (neg_pos.2 c234)]) hHR
                    · 
                      exact Frame20.om1z1_R F hx hα hβ (by linarith only [c228p]) (by linarith only [c232]) (by linarith only [c233, c234]) (by linarith only [c233, c234]) (by linarith only [c233, c234]) hHR
                  · 
                    exact Frame20.om1p_R F hx hα hβ (by linarith only [c228p]) (by linarith only [c232]) (by linarith only [c233]) hHR
                · have c232p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c232]
                  rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c235 | c235 | c235
                  · 
                    exact Frame20.om3n F hx hα hβ (by linarith only [c227p]) (by linarith only [(mul_pos F.S.tm_pos c1), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [(neg_pos.2 c235)]) hH
                  · 
                    rcases lt_or_gt_of_ne (fun hl => n22 ⟨c235, hl⟩) with c236 | c236
                    · 
                      exact Frame20.om3z2 F hx hα hβ (by linarith only [c227p]) (by linarith only [(mul_pos F.S.tm_pos c1), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c235, (neg_pos.2 c236)]) (by linarith only [c235, (neg_pos.2 c236)]) (by linarith only [c235, (neg_pos.2 c236)]) hH
                    · 
                      exact Frame20.om3z1 F hx hα hβ (by linarith only [c227p]) (by linarith only [(mul_pos F.S.tm_pos c1), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c235, c236]) (by linarith only [c235, c236]) (by linarith only [c235, c236]) hH
                  · 
                    exact Frame20.om3p F hx hα hβ (by linarith only [c227p]) (by linarith only [(mul_pos F.S.tm_pos c1), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c235]) hH
            · 
              rcases le_or_gt 0 (F.S.tm - F.S.tp) with c237 | c237
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c238 | c238 | c238
                · 
                  exact Frame20.om1n F hx hα hβ (by linarith only [c227p]) (by linarith only [c237]) (by linarith only [(neg_pos.2 c238)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n7 ⟨c238, hl⟩) with c239 | c239
                  · 
                    exact Frame20.om1z2 F hx hα hβ (by linarith only [c227p]) (by linarith only [c237]) (by linarith only [c238, (neg_pos.2 c239)]) (by linarith only [c238, (neg_pos.2 c239)]) (by linarith only [c238, (neg_pos.2 c239)]) hH
                  · 
                    exact Frame20.om1z1 F hx hα hβ (by linarith only [c227p]) (by linarith only [c237]) (by linarith only [c238, c239]) (by linarith only [c238, c239]) (by linarith only [c238, c239]) hH
                · 
                  exact Frame20.om1p F hx hα hβ (by linarith only [c227p]) (by linarith only [c237]) (by linarith only [c238]) hH
              · have c237p : 0 < -(F.S.tm - F.S.tp) := by linarith only [c237]
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c240 | c240 | c240
                · 
                  exact Frame20.om3n F hx hα hβ (by linarith only [c227p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [(neg_pos.2 c240)]) hH
                · 
                  rcases lt_or_gt_of_ne (fun hl => n22 ⟨c240, hl⟩) with c241 | c241
                  · 
                    exact Frame20.om3z2 F hx hα hβ (by linarith only [c227p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c240, (neg_pos.2 c241)]) (by linarith only [c240, (neg_pos.2 c241)]) (by linarith only [c240, (neg_pos.2 c241)]) hH
                  · 
                    exact Frame20.om3z1 F hx hα hβ (by linarith only [c227p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c240, c241]) (by linarith only [c240, c241]) (by linarith only [c240, c241]) hH
                · 
                  exact Frame20.om3p F hx hα hβ (by linarith only [c227p]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) (by linarith only [c240]) hH
          · 
            rcases lt_or_gt_of_ne n6 with c242 | c242
            · have c242p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c242
              rcases le_or_gt 0 (-F.S.sm + F.S.sp) with c243 | c243
              · 
                rcases lt_trichotomy ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg) 0 with c244 | c244 | c244
                · 
                  exact Frame20.om1n_R F hx hα hβ (by linarith only [c242p]) (by linarith only [c243]) (by linarith only [(neg_pos.2 c244)]) hHR
                · 
                  rcases lt_or_gt_of_ne (fun hl => n8 ⟨c244, hl⟩) with c245 | c245
                  · 
                    exact Frame20.om1z2_R F hx hα hβ (by linarith only [c242p]) (by linarith only [c243]) (by linarith only [c244, (neg_pos.2 c245)]) (by linarith only [c244, (neg_pos.2 c245)]) (by linarith only [c244, (neg_pos.2 c245)]) hHR
                  · 
                    exact Frame20.om1z1_R F hx hα hβ (by linarith only [c242p]) (by linarith only [c243]) (by linarith only [c244, c245]) (by linarith only [c244, c245]) (by linarith only [c244, c245]) hHR
                · 
                  exact Frame20.om1p_R F hx hα hβ (by linarith only [c242p]) (by linarith only [c243]) (by linarith only [c244]) hHR
              · have c243p : 0 < -(-F.S.sm + F.S.sp) := by linarith only [c243]
                exact Frame20.om2a F hx hα hβ (by linarith only [c227]) (by linarith only [c1, c185p]) (by linarith only [c185p]) (by linarith only [c1]) hH
            · 
              exact Frame20.om2a F hx hα hβ (by linarith only [c227]) (by linarith only [(mul_pos F.S.tm_pos c1), (mul_pos (mul_pos F.S.tp_pos hsp1) F.S.hm_pos)]) (by linarith only [c185p]) (by linarith only [c1]) hH
        · 
          rcases lt_or_gt_of_ne n17 with c246 | c246
          · have c246p : 0 < -(-F.S.hm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm - F.S.km*F.S.tm*F.S.tp + F.S.km*F.S.tm + F.S.km*F.S.tp - F.S.km) := neg_pos.2 c246
            exact rupert_of_r (F.rFrame.vTri (by simp only [rFrame_S, Shape20.swap]; exact (by linarith only [c186])) (by simp only [rFrame_S, Shape20.swap]; exact (by linarith only [c226])) (by simp only [rFrame_S, Shape20.swap]; exact (by linarith only [c246p])))
          · 
            rcases lt_or_gt_of_ne n6 with c247 | c247
            · have c247p : 0 < -(F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp) := neg_pos.2 c247
              rcases lt_or_gt_of_ne n18 with c248 | c248
              · have c248p : 0 < -(-F.S.hp*F.S.sm + F.S.hp - F.S.km*F.S.tp) := neg_pos.2 c248
                rcases lt_or_gt_of_ne n19 with c249 | c249
                · have c249p : 0 < -(F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm*F.S.tp + F.S.kp) := neg_pos.2 c249
                  exact Frame20.ra4_X_R F hx hα hβ (by linarith only [c186]) (by linarith only [c226]) (by linarith only [c246]) (by linarith only [c247p]) (by linarith only [c248p]) (by linarith only [c249p])
                · 
                  exact Frame20.ra4_Y_R F hx hα hβ (by linarith only [c186]) (by linarith only [c226]) (by linarith only [c246]) (by linarith only [c247p]) (by linarith only [c248p]) (by linarith only [c249])
              · 
                exact Frame20.ra4_tBR_R F hx hα hβ (by linarith only [c247p]) (by linarith only [c248])
            · 
              exact Frame20.ra4_A_R F hx hα hβ (by linarith only [c186]) (by linarith only [c226]) (by linarith only [c246]) (by linarith only [c247])
    · 
      rcases lt_or_gt_of_ne n23 with c250 | c250
      · have c250p : 0 < -(-F.S.hp*F.S.sm*F.S.sp + F.S.hp*F.S.sm + F.S.hp*F.S.sp - F.S.hp - F.S.km*F.S.sp*F.S.tp + F.S.km*F.S.tp - F.S.kp*F.S.sm + F.S.kp) := neg_pos.2 c250
        exact F.vTri (by linarith only [c1]) (by linarith only [c185]) (by linarith only [c250p])
      · 
        rcases lt_or_gt_of_ne n5 with c251 | c251
        · have c251p : 0 < -(F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) := neg_pos.2 c251
          rcases lt_or_gt_of_ne n24 with c252 | c252
          · have c252p : 0 < -(-F.S.hp*F.S.sm - F.S.km*F.S.tp + F.S.km) := neg_pos.2 c252
            rcases lt_or_gt_of_ne n25 with c253 | c253
            · have c253p : 0 < -(-F.S.hm*F.S.sm*F.S.tp + F.S.hm - F.S.hp*F.S.sm*F.S.tm + F.S.hp*F.S.sm + F.S.km*F.S.tm - F.S.km) := neg_pos.2 c253
              exact Frame20.ra4_X F hx hα hβ (by linarith only [c1]) (by linarith only [c185]) (by linarith only [c250]) (by linarith only [c251p]) (by linarith only [c252p]) (by linarith only [c253p])
            · 
              exact Frame20.ra4_Y F hx hα hβ (by linarith only [c1]) (by linarith only [c185]) (by linarith only [c250]) (by linarith only [c251p]) (by linarith only [c252p]) (by linarith only [c253])
          · 
            exact Frame20.ra4_tBR F hx hα hβ (by linarith only [c251p]) (by linarith only [c252])
        · 
          exact Frame20.ra4_A F hx hα hβ (by linarith only [c1]) (by linarith only [c185]) (by linarith only [c250]) (by linarith only [c251])

end Minimality.CaseC20

end
