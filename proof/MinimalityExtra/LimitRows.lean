module

public import Mathlib
public import MinimalityExtra

/-!
# Limit rows can undercount

Proof of `MinimalityExtra.ExistsLimitRowsUndercount`.  Tetrahedron `UX` with vertices
`(-1,0,-1), (-1,-1,1), (1,-1,-1), (0,0,1)`; the face `1,2,3` is parallel to `UU = (0,1,1)`; tilt
`UD = (0,0,1)`.  The rim of `UU + ε UD` is the triangle `1, 2, 0` (vertex 3 hidden) for `0 < ε < 1/4`.
Farkas weights on the six limit rows at `UU`: `1` on the `next` row at vertex `1`, on the `prev` row
at vertex `2`, `2` on both rows at vertex `0` (positions `0, 1, 2` of `Ulab = ![1, 2, 0]`).  The
motion `ω = (-6, 4, -2) + ε (1, 2, 2)`, `τ = (4, 8, 0) + ε (3, 0, 2)` is free for the tilted views,
`ε < 1/4`: the leading term is a limit motion with all rows `≥ 0` (zero on the four rows with
positive weight), the order `ε` term makes those four rows positive.  Found by `side4/*.py`.
-/

@[expose] public section

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace MinimalityExtra
open scoped RealInnerProductSpace
open Finset

noncomputable def UX : Fin 4 → ℝ³ := ![!₂[-1, 0, -1], !₂[-1, -1, 1], !₂[1, -1, -1], !₂[0, 0, 1]]
noncomputable def UU : ℝ³ := !₂[0, 1, 1]
noncomputable def UD : ℝ³ := !₂[0, 0, 1]
def Ulab : ZMod 3 → Fin 4 := ![1, 2, 0]

theorem sum3 (f : ZMod 3 → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 := Fin.sum_univ_three f
theorem z3a : (0 : ZMod 3) + 1 = 1 := rfl
theorem z3b : (1 : ZMod 3) + 1 = 2 := rfl
theorem z3c : (2 : ZMod 3) + 1 = 0 := rfl
theorem z3d : (0 : ZMod 3) - 1 = 2 := rfl
theorem z3e : (1 : ZMod 3) - 1 = 0 := rfl
theorem z3f : (2 : ZMod 3) - 1 = 1 := rfl

theorem ux_noncoplanar : det3 (UX 1 - UX 0) (UX 2 - UX 0) (UX 3 - UX 0) ≠ 0 := by
  norm_num [det3, UX]

theorem ulab_inj : Function.Injective Ulab := by decide

theorem u_rigid : LimitRowsRigid (fun i => UX (Ulab i)) UU := by
  refine ⟨![1, 0, 2], ![0, 1, 2], ?_, ⟨0, Or.inl (by norm_num)⟩, ?_⟩
  · intro i; fin_cases i <;> norm_num
  · intro ω τ
    rw [sum3]
    simp only [cornerRowNext, cornerRowPrev, z3a, z3b, z3c, z3d, z3e, z3f, Ulab, UX, UU, det3, cross]
    norm_num
    ring

theorem all3 (i : ZMod 3) : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide
theorem all4' (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide

theorem u_rim (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 4) : StrictRimN UX (UU + ε • UD) Ulab := by
  intro m i hm1 hm2
  rcases all3 i with rfl | rfl | rfl <;> rcases all4' m with rfl | rfl | rfl | rfl <;>
    simp [Ulab, z3b, z3c, UX, UU, UD, det3] at hm1 hm2 ⊢ <;> nlinarith

theorem u_hidden (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 4) : HiddenInTriangles UX (UU + ε • UD) Ulab := by
  intro m hm
  have : m = 3 := by
    rcases all4' m with rfl | rfl | rfl | rfl
    · exact absurd rfl (hm 2)
    · exact absurd rfl (hm 0)
    · exact absurd rfl (hm 1)
    · rfl
  subst this
  refine ⟨UX 1, Finset.mem_image_of_mem _ (Finset.mem_univ _), UX 2, Finset.mem_image_of_mem _ (Finset.mem_univ _),
    UX 0, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_, ?_, ?_, ?_⟩ <;>
    simp [UX, UU, UD, det3] <;> nlinarith

theorem u_free (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 4) : FreeAt (univ.image UX) (UU + ε • UD) := by
  refine ⟨!₂[-6 + ε, 4 + 2 * ε, -2 + 2 * ε], !₂[4 + 3 * ε, 8, 2 * ε], ?_⟩
  intro y hy
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
  obtain ⟨i, rfl⟩ := hy
  have m : ∀ i, UX i ∈ univ.image UX := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  rcases all4' i with rfl | rfl | rfl | rfl
  · left
    exact ⟨UX 2, m _, UX 1, m _, by simp [UX, UU, UD, det3, cross]; nlinarith,
      by simp [UX, UU, UD, det3, cross]; nlinarith, by simp [UX, UU, UD, det3, cross]; nlinarith⟩
  · left
    exact ⟨UX 0, m _, UX 2, m _, by simp [UX, UU, UD, det3, cross]; nlinarith,
      by simp [UX, UU, UD, det3, cross]; nlinarith, by simp [UX, UU, UD, det3, cross]; nlinarith⟩
  · left
    exact ⟨UX 1, m _, UX 0, m _, by simp [UX, UU, UD, det3, cross]; nlinarith,
      by simp [UX, UU, UD, det3, cross]; nlinarith, by simp [UX, UU, UD, det3, cross]; nlinarith⟩
  · right
    exact ⟨UX 1, m _, UX 2, m _, UX 0, m _, by simp [UX, UU, UD, det3]; nlinarith,
      by simp [UX, UU, UD, det3]; nlinarith, by simp [UX, UU, UD, det3]; nlinarith,
      by simp [UX, UU, UD, det3]; nlinarith⟩

theorem existsLimitRowsUndercount : ExistsLimitRowsUndercount :=
  ⟨UX, Ulab, UU, UD, 1 / 4, by norm_num, ux_noncoplanar, ulab_inj,
    ⟨1, 2, 3, by decide, by decide, by decide, by norm_num [det3, UX, UU, UD], by norm_num [det3, UX, UU, UD]⟩,
    u_rigid, fun ε h0 h1 => ⟨u_rim ε h0 h1, u_hidden ε h0 h1, u_free ε h0 h1⟩⟩


end MinimalityExtra
