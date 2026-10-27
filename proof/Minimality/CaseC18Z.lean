module

public import Minimality.CaseC18Frame

@[expose] public section

/-!
# Type 18: the symmetry `Z` (`z ↦ -z`, `m1+ ↔ m1-`, `m2+ ↔ m2-`)

Type 18's face set is invariant under the relabelling `zperm = (0 6)(1 2)`.  A frame of `x` gives a
frame of `x ∘ zperm` (`e ↦ -e`, the shape with `t+ ↔ t-`, `s+ ↔ s-`, `h+ ↔ h-`, `k+ ↔ k-`), with the
same Gram matrix, and the point set is the same, so every test proved for a frame transfers to its
`Z`-image.
-/

namespace Minimality.CaseC18

open Finset
open scoped RealInnerProductSpace

/-- The relabelling `Z`: `m1+ ↔ m1-` (`0 ↔ 6`), `m2+ ↔ m2-` (`1 ↔ 2`). -/
def zperm : Fin 7 → Fin 7 := ![6, 2, 1, 3, 4, 5, 0]

lemma zperm_bijective : Function.Bijective zperm := by decide

lemma image_zperm (x : Fin 7 → ℝ³) :
    Finset.univ.image (x ∘ zperm) = Finset.univ.image x := by
  ext p
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨j, rfl⟩ := zperm_bijective.2 i
    exact ⟨j, rfl⟩

/-- The `Z`-image of a shape. -/
def Shape18.swap (S : Shape18) : Shape18 where
  tp := S.tm
  tm := S.tp
  sp := S.sm
  sm := S.sp
  hp := S.hm
  hm := S.hp
  kp := S.km
  km := S.kp
  tp_pos := S.tm_pos
  tp_lt := S.tm_lt
  tm_pos := S.tp_pos
  tm_lt := S.tp_lt
  sp_pos := S.sm_pos
  sp_lt := S.sm_lt
  sm_pos := S.sp_pos
  sm_lt := S.sp_lt
  hp_pos := S.hm_pos
  hm_pos := S.hp_pos
  kp_pos := S.km_pos
  km_pos := S.kp_pos
  roof_p := S.roof_m
  roof_m := S.roof_p

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-- **The `Z`-image of a frame**: a frame of `x ∘ zperm`. -/
noncomputable def zFrame : Frame18 (x ∘ zperm) where
  e := -F.e
  S := F.S.swap
  e_ne := neg_ne_zero.2 F.e_ne
  indep := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h := Fintype.linearIndependent_iff.mp F.indep ![g 0, g 1, -g 2] (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_smul] at hg ⊢
      simpa [Function.comp, zperm, sub_eq_add_neg, neg_smul, add_assoc] using hg)
    intro i
    fin_cases i
    · simpa using h 0
    · simpa using h 1
    · simpa using h 2
  x0_eq := by
    show x 6 = x 5 + F.S.tm • (x 3 - x 5) + F.S.hm • -F.e
    rw [F.x6_eq]; simp [sub_eq_add_neg]
  x6_eq := by
    show x 0 = x 5 + F.S.tp • (x 3 - x 5) - F.S.hp • -F.e
    rw [F.x0_eq]; simp [sub_eq_add_neg]
  x1_eq := by
    show x 2 = x 5 + F.S.sm • (x 4 - x 5) + F.S.km • -F.e
    rw [F.x2_eq]; simp [sub_eq_add_neg]
  x2_eq := by
    show x 1 = x 5 + F.S.sp • (x 4 - x 5) - F.S.kp • -F.e
    rw [F.x1_eq]; simp [sub_eq_add_neg]
  inner_u1_e := by
    show ⟪x 3 - x 5, -F.e⟫ = 0
    rw [inner_neg_right, F.inner_u1_e, neg_zero]
  inner_u2_e := by
    show ⟪x 4 - x 5, -F.e⟫ = 0
    rw [inner_neg_right, F.inner_u2_e, neg_zero]
  A12_pos := F.A12_pos
  A12_le_A11 := F.A12_le_A11
  A12_le_A22 := F.A12_le_A22

end Frame18

/-- A set Rupert for the `Z`-image of the labelling is Rupert. -/
theorem rupert_of_z {x : Fin 7 → ℝ³} (h : IsRupert (Finset.univ.image (x ∘ zperm))) :
    IsRupert (Finset.univ.image x) := by
  rwa [image_zperm] at h

end Minimality.CaseC18

end
