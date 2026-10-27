module

public import Minimality.CaseC20Frame

@[expose] public section

/-!
# Type 20: the symmetry `R` (`x ↔ y`, `z ↦ -z`)

Type 20's face set is invariant under the relabelling `rperm = (0 4)(1 6)(2 3)`
(`m1+ ↔ m2-`, `xa ↔ xb`, `m1- ↔ m2+`, `v` fixed; `0135 ↔ 2456`, `016 ↔ 146`, `025 ↔ 345`,
`026 ↔ 134`).  A frame of `x` gives a frame of `x ∘ rperm` (`e ↦ -e`, `u₁ ↔ u₂`, the shape
`t+ ↔ s-`, `t- ↔ s+`, `h+ ↔ k-`, `h- ↔ k+`), with the Gram matrix `A11 ↔ A22`, `A12`, `g` fixed, and
the point set is the same, so every test proved for a frame transfers to its `R`-image.
-/

namespace Minimality.CaseC20

open Finset
open scoped RealInnerProductSpace

/-- The relabelling `R`. -/
def rperm : Fin 7 → Fin 7 := ![4, 6, 3, 2, 0, 5, 1]

lemma rperm_bijective : Function.Bijective rperm := by decide

lemma image_rperm (x : Fin 7 → ℝ³) :
    Finset.univ.image (x ∘ rperm) = Finset.univ.image x := by
  ext p
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨j, rfl⟩ := rperm_bijective.2 i
    exact ⟨j, rfl⟩

/-- The `R`-image of a shape. -/
def Shape20.swap (S : Shape20) : Shape20 where
  tp := S.sm
  tm := S.sp
  sp := S.tm
  sm := S.tp
  hp := S.km
  hm := S.kp
  kp := S.hm
  km := S.hp
  tp_pos := S.sm_pos
  tp_lt := S.sm_lt
  tm_pos := S.sp_pos
  tm_lt := S.sp_lt
  sp_pos := S.tm_pos
  sp_lt := S.tm_lt
  sm_pos := S.tp_pos
  sm_lt := S.tp_lt
  hp_pos := S.km_pos
  hm_pos := S.kp_pos
  kp_pos := S.hm_pos
  km_pos := S.hp_pos
  roof_p := S.roof_m
  roof_m := S.roof_p

namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- **The `R`-image of a frame**: a frame of `x ∘ rperm`. -/
noncomputable def rFrame : Frame20 (x ∘ rperm) where
  e := -F.e
  S := F.S.swap
  e_ne := neg_ne_zero.2 F.e_ne
  indep := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • (x 6 - x 5) + g 1 • (x 1 - x 5) + g 2 • (-F.e) = 0 := by
      simpa [Fin.sum_univ_three, Function.comp, rperm] using hg
    have h := Fintype.linearIndependent_iff.mp F.indep ![g 1, g 0, -g 2] (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [← hg']; module)
    intro i
    fin_cases i
    · simpa using h 1
    · simpa using h 0
    · simpa using h 2
  x0_eq := by
    show x 4 = x 5 + F.S.sm • (x 6 - x 5) + F.S.km • -F.e
    rw [F.x4_eq]; simp [sub_eq_add_neg]
  x3_eq := by
    show x 2 = x 5 + F.S.sp • (x 6 - x 5) - F.S.kp • -F.e
    rw [F.x2_eq]; simp [sub_eq_add_neg]
  x2_eq := by
    show x 3 = x 5 + F.S.tm • (x 1 - x 5) + F.S.hm • -F.e
    rw [F.x3_eq]; simp [sub_eq_add_neg]
  x4_eq := by
    show x 0 = x 5 + F.S.tp • (x 1 - x 5) - F.S.hp • -F.e
    rw [F.x0_eq]; simp [sub_eq_add_neg]
  inner_u1_e := by
    show ⟪x 6 - x 5, -F.e⟫ = 0
    rw [inner_neg_right, F.inner_u2_e, neg_zero]
  inner_u2_e := by
    show ⟪x 1 - x 5, -F.e⟫ = 0
    rw [inner_neg_right, F.inner_u1_e, neg_zero]
  A12_pos := by
    show 0 < ⟪x 6 - x 5, x 1 - x 5⟫
    rw [real_inner_comm]; exact F.A12_pos
  A12_le_A11 := by
    show ⟪x 6 - x 5, x 1 - x 5⟫ ≤ ⟪x 6 - x 5, x 6 - x 5⟫
    rw [real_inner_comm]; exact F.A12_le_A22
  A12_le_A22 := by
    show ⟪x 6 - x 5, x 1 - x 5⟫ ≤ ⟪x 1 - x 5, x 1 - x 5⟫
    rw [real_inner_comm]; exact F.A12_le_A11

end Frame20

/-- A set Rupert for the `R`-image of the labelling is Rupert. -/
theorem rupert_of_r {x : Fin 7 → ℝ³} (h : IsRupert (Finset.univ.image (x ∘ rperm))) :
    IsRupert (Finset.univ.image x) := by
  rwa [image_rperm] at h

end Minimality.CaseC20

end
