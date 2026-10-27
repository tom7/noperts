module

public import Minimality.CaseC18Vertex
public import Minimality.CaseC20R

@[expose] public section

/-!
# Type 20, acute case (c): the `Frame7` of a type-20 frame

The generic bridges of `CaseC18Bridge` (`rupert_crossing`, `rupert_rim4`, ..., and
`CaseC18Vertex`'s `rupert_vertex`) for the frame coordinates of type 20:
`x 5 = 0`, `x 1 = (1,0,0)`, `x 6 = (0,1,0)`, `x 0 = (t+,0,h+)`, `x 3 = (t-,0,-h-)`,
`x 2 = (0,s+,k+)`, `x 4 = (0,s-,-k-)`.
-/

namespace Minimality.CaseC20

open Finset Filter Minimality.CaseC09 Minimality.CaseC18
open scoped RealInnerProductSpace Topology

namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- The frame coordinates of the seven points of type 20. -/
noncomputable def pt (S : Shape20) : Fin 7 → C3 := ![⟨S.tp, 0, S.hp⟩, ⟨1, 0, 0⟩, ⟨0, S.sp, S.kp⟩,
  ⟨S.tm, 0, -S.hm⟩, ⟨0, S.sm, -S.km⟩, ⟨0, 0, 0⟩, ⟨0, 1, 0⟩]

/-- The `Frame7` of a type-20 frame. -/
noncomputable def toFrame7 : Frame7 x where
  base := x 5
  u1 := x 1 - x 5
  u2 := x 6 - x 5
  e := F.e
  indep := F.indep
  inner_u1_e := F.inner_u1_e
  inner_u2_e := F.inner_u2_e
  ptC := pt F.S
  x_eq := by
    intro j
    fin_cases j
    · show x 0 = x 5 + F.S.tp • (x 1 - x 5) + 0 • (x 6 - x 5) + F.S.hp • F.e
      rw [F.x0_eq]; simp
    · show x 1 = x 5 + (1:ℝ) • (x 1 - x 5) + 0 • (x 6 - x 5) + 0 • F.e
      simp
    · show x 2 = x 5 + 0 • (x 1 - x 5) + F.S.sp • (x 6 - x 5) + F.S.kp • F.e
      rw [F.x2_eq]; simp
    · show x 3 = x 5 + F.S.tm • (x 1 - x 5) + 0 • (x 6 - x 5) + (-F.S.hm) • F.e
      rw [F.x3_eq]; simp [sub_eq_add_neg]
    · show x 4 = x 5 + 0 • (x 1 - x 5) + F.S.sm • (x 6 - x 5) + (-F.S.km) • F.e
      rw [F.x4_eq]; simp [sub_eq_add_neg]
    · show x 5 = x 5 + 0 • (x 1 - x 5) + 0 • (x 6 - x 5) + 0 • F.e
      simp
    · show x 6 = x 5 + 0 • (x 1 - x 5) + (1:ℝ) • (x 6 - x 5) + 0 • F.e
      simp

lemma ptC_0 : F.toFrame7.ptC 0 = ⟨F.S.tp, 0, F.S.hp⟩ := by simp [toFrame7, pt]
lemma ptC_1 : F.toFrame7.ptC 1 = ⟨1, 0, 0⟩ := by simp [toFrame7, pt]
lemma ptC_2 : F.toFrame7.ptC 2 = ⟨0, F.S.sp, F.S.kp⟩ := by simp [toFrame7, pt]
lemma ptC_3 : F.toFrame7.ptC 3 = ⟨F.S.tm, 0, -F.S.hm⟩ := by simp [toFrame7, pt]
lemma ptC_4 : F.toFrame7.ptC 4 = ⟨0, F.S.sm, -F.S.km⟩ := by simp [toFrame7, pt]
lemma ptC_5 : F.toFrame7.ptC 5 = ⟨0, 0, 0⟩ := by simp [toFrame7, pt]
lemma ptC_6 : F.toFrame7.ptC 6 = ⟨0, 1, 0⟩ := by simp [toFrame7, pt]

/-- The entries of the depth form. -/
noncomputable def a11 (_F : Frame20 x) : ℝ := ⟪x 1 - x 5, x 1 - x 5⟫
noncomputable def a12 (_F : Frame20 x) : ℝ := ⟪x 1 - x 5, x 6 - x 5⟫
noncomputable def a22 (_F : Frame20 x) : ℝ := ⟪x 6 - x 5, x 6 - x 5⟫
noncomputable def gg : ℝ := ⟪F.e, F.e⟫

lemma g_pos : 0 < F.gg := real_inner_self_pos.mpr F.e_ne

lemma A11_pos : 0 < F.a11 := lt_of_lt_of_le F.A12_pos F.A12_le_A11
lemma A22_pos : 0 < F.a22 := lt_of_lt_of_le F.A12_pos F.A12_le_A22

/-- The depth of the point `j` along the view `u`. -/
noncomputable def dep (u : C3) (j : Fin 7) : ℝ := F.toFrame7.GG (F.toFrame7.ptC j) u

lemma GG_eq (a b : C3) : F.toFrame7.GG a b =
    F.a11 * (a.x * b.x) + F.a12 * (a.x * b.y + b.x * a.y) + F.a22 * (a.y * b.y) +
      F.gg * (a.z * b.z) := rfl

end Frame20

section RImage

lemma rperm_0 : rperm 0 = 4 := rfl
lemma rperm_1 : rperm 1 = 6 := rfl
lemma rperm_2 : rperm 2 = 3 := rfl
lemma rperm_3 : rperm 3 = 2 := rfl
lemma rperm_4 : rperm 4 = 0 := rfl
lemma rperm_5 : rperm 5 = 5 := rfl
lemma rperm_6 : rperm 6 = 1 := rfl

variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- The `R`-image coordinates of a vector: `(p, q, r) ↦ (q, p, -r)`. -/
def C3.rimg (u : C3) : C3 := ⟨u.y, u.x, -u.z⟩

lemma rFrame_S : F.rFrame.S = F.S.swap := rfl

lemma rFrame_ptC (j : Fin 7) :
    F.rFrame.toFrame7.ptC j = C3.rimg (F.toFrame7.ptC (rperm j)) := by
  fin_cases j <;>
    simp [Frame20.toFrame7, Frame20.pt, Frame20.rFrame, Shape20.swap, rperm, C3.rimg]

lemma rFrame_GG (a b : C3) :
    F.rFrame.toFrame7.GG a b = F.toFrame7.GG (C3.rimg a) (C3.rimg b) := by
  have h11 : F.rFrame.a11 = F.a22 := rfl
  have h22 : F.rFrame.a22 = F.a11 := rfl
  have h12 : F.rFrame.a12 = F.a12 := by
    show ⟪x (rperm 1) - x (rperm 5), x (rperm 6) - x (rperm 5)⟫ = _
    show ⟪x 6 - x 5, x 1 - x 5⟫ = _
    exact real_inner_comm _ _
  have hg : F.rFrame.gg = F.gg := by
    show ⟪-F.e, -F.e⟫ = ⟪F.e, F.e⟫
    simp
  simp only [Frame20.GG_eq, h11, h22, h12, hg, C3.rimg]
  ring

lemma rFrame_dep (u : C3) (j : Fin 7) :
    F.rFrame.dep u j = F.dep (C3.rimg u) (rperm j) := by
  simp only [Frame20.dep, rFrame_ptC, rFrame_GG]
  congr 1
  simp [C3.rimg]

end RImage

end Minimality.CaseC20

end
