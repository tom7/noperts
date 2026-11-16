import Mathlib
import Minimality.CornerEQCert

/-!
# A concrete type 24 shape closed by an EQ certificate (pipeline test)

Shape 253 of the type 24 OOO census (`nopert229/out/bottleneck/p4/sat/stratsat`, T-EQ1; seed 777):
`Y = {X0, ..., X6}` with `X0 = (1,0,0)`, `X1 = 0`, `X2 = (0,1,0)`, `X6 = (0,0,1)` and
`X3, X4, X5` rational (denominators `2^24`, `2^10`, `2^12`).  The certificate has two EQ leaves,
both on the rim `(2 6 4 3 5)` (indices into `Y`, counterclockwise as in `cellSet`):
* leaf 0: `ρ`, `σ` extreme rays of the closed cell and of the closed cone `Conv(R)`,
  key `26435|034,035,046,345|C:256,346`;
* leaf 1: key `26435|025,034,035,345|C:235,256`.
The C++ literal is `c.G > 0 ⟺ ρᵀ G σ < 0`, `S = ∑ λ_i c_i`; Lean `certMatrix` is
`S_ab = -∑ λ_i (σ_a ρ_b + σ_b ρ_a)/2` (so the C++ off-diagonal coefficient is `2 S_ab`).  The data
(`ρ`, `σ` scaled to integer rays, `λ`, an interior point `q₀` of the open cell) come from
`teq1_export.exe 253`, which re-verifies them in exact rational arithmetic.

`CornerEQShape.rupert`: for this `Y`, every `E` with `det E > 0` and obtuse Gram matrix `Eᵀ E`
(off-diagonal entries `≤ 0`) makes `E Y` Rupert.
-/

set_option autoImplicit false

namespace Minimality.CornerEQShape

open Finset Matrix Minimality.RimCell Minimality.CornerEQ

theorem forall_zmod5 {P : ZMod 5 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) :
    ∀ i, P i := by
  intro i; fin_cases i
  exacts [h0, h1, h2, h3, h4]

theorem z5b : (1 : ZMod 5) + 1 = 2 := by decide
theorem z5c : (2 : ZMod 5) + 1 = 3 := by decide
theorem z5d : (3 : ZMod 5) + 1 = 4 := by decide
theorem z5e : (4 : ZMod 5) + 1 = 0 := by decide
theorem z5g : (1 : ZMod 5) + 2 = 3 := by decide
theorem z5h : (2 : ZMod 5) + 2 = 4 := by decide
theorem z5i : (3 : ZMod 5) + 2 = 0 := by decide
theorem z5j : (4 : ZMod 5) + 2 = 1 := by decide

/-- The seven vertices `X0, ..., X6`. -/
noncomputable def Vf : Fin 7 → Fin 3 → ℝ :=
  ![![1, 0, 0], ![0, 0, 0], ![0, 1, 0],
    ![35379181/16777216, 65846065/16777216, 51229357/16777216],
    ![2231/1024, 3185/4096, 20451/4096], ![6133/4096, 16525/4096, 817/4096], ![0, 0, 1]]

noncomputable def Yc : Finset (Fin 3 → ℝ) := Finset.univ.image Vf

/-- The rim `(2 6 4 3 5)`. -/
def rimIdx : ZMod 5 → Fin 7 := ![2, 6, 4, 3, 5]

noncomputable def yr : ZMod 5 → Fin 3 → ℝ := fun i => Vf (rimIdx i)

set_option linter.unusedTactic false in
theorem Vf_injective : Function.Injective Vf := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; simp [Vf] at h0 h1 h2 <;> norm_num at h0)

theorem yr_injective : Function.Injective yr := by
  have : Function.Injective rimIdx := by decide
  exact Vf_injective.comp this

theorem yr_mem : ∀ j, yr j ∈ Yc := fun _ => Finset.mem_image_of_mem _ (Finset.mem_univ _)

set_option hygiene false in
/-- Shared proof for the cell rows (strict or nonstrict). -/
macro "cellrows" : tactic =>
  `(tactic| (intro i v hv h1 h2
             obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hv
             revert i
             refine forall_zmod5 ?_ ?_ ?_ ?_ ?_ <;> intro h1 h2 <;> fin_cases j <;>
               first | exact absurd rfl h1 | exact absurd rfl h2 |
               norm_num [yr, Vf, rimIdx, Matrix.det_fin_three, z5b, z5c, z5d, z5e]))

macro "convrows" : tactic =>
  `(tactic| (refine forall_zmod5 ?_ ?_ ?_ ?_ ?_ <;>
               norm_num [omega, yr, Vf, rimIdx, Matrix.det_fin_three, z5b, z5c, z5d, z5e,
                 z5g, z5h, z5i, z5j]))

section Leaf0

/-- `ρ₀`, `σ₀`, `q₀` of leaf 0. -/
def ρ0 : Fin 3 → ℝ := ![4828, 3185, 20451]
def σ0 : Fin 3 → ℝ := ![-312402744193333, -89790424554445, -584934302265201]
def q0 : Fin 3 → ℝ := ![3351988002909578, 39940292014435900, 20349035345362473]

theorem q0_mem : q0 ∈ cellSet Yc yr := by
  show ∀ i : ZMod 5, ∀ v ∈ Yc, v ≠ yr i → v ≠ yr (i + 1) →
    0 < (Matrix.of ![yr (i + 1) - yr i, v - yr i, q0]).det
  simp only [q0]; cellrows

theorem ρ0_ok : ∀ i : ZMod 5, ∀ v ∈ Yc, v ≠ yr i → v ≠ yr (i + 1) →
    0 ≤ (Matrix.of ![yr (i + 1) - yr i, v - yr i, ρ0]).det := by
  simp only [ρ0]; cellrows

theorem σ0_ok : ∀ i : ZMod 5, 0 ≤ omega σ0 (yr (i + 1) - yr i) (yr (i + 2) - yr i) := by
  simp only [σ0]; convrows

end Leaf0

section Leaf1

def ρ1 : Fin 3 → ℝ := ![2037, 16525, 817]
def σ1 : Fin 3 → ℝ := ![-6133, -12429, -817]
def q1 : Fin 3 → ℝ := ![13310389021500556, 95917420292557400, 87748987830068421]

theorem q1_mem : q1 ∈ cellSet Yc yr := by
  show ∀ i : ZMod 5, ∀ v ∈ Yc, v ≠ yr i → v ≠ yr (i + 1) →
    0 < (Matrix.of ![yr (i + 1) - yr i, v - yr i, q1]).det
  simp only [q1]; cellrows

theorem ρ1_ok : ∀ i : ZMod 5, ∀ v ∈ Yc, v ≠ yr i → v ≠ yr (i + 1) →
    0 ≤ (Matrix.of ![yr (i + 1) - yr i, v - yr i, ρ1]).det := by
  simp only [ρ1]; cellrows

theorem σ1_ok : ∀ i : ZMod 5, 0 ≤ omega σ1 (yr (i + 1) - yr i) (yr (i + 2) - yr i) := by
  simp only [σ1]; convrows

end Leaf1

/-- The two EQ leaves, with `λ₀ = 1/11962491415625625651`, `λ₁ = 1/205389225`. -/
noncomputable def leaf0 : EQLeaf Yc :=
  EQLeaf.ofNonstrict (by norm_num) yr yr_injective yr_mem q0 q0_mem ρ0 σ0 ρ0_ok σ0_ok
    (1 / 11962491415625625651) (by norm_num)

noncomputable def leaf1 : EQLeaf Yc :=
  EQLeaf.ofNonstrict (by norm_num) yr yr_injective yr_mem q1 q1_mem ρ1 σ1 ρ1_ok σ1_ok
    (1 / 205389225) (by norm_num)

noncomputable def L : Fin 2 → EQLeaf Yc := ![leaf0, leaf1]

theorem S_diag : ∀ a, 0 < certMatrix L a a := by
  intro a
  fin_cases a <;>
    norm_num [certMatrix, L, leaf0, leaf1, EQLeaf.ofNonstrict, ρ0, σ0, ρ1, σ1, Fin.sum_univ_two]

theorem S_off : ∀ a b, a ≠ b → certMatrix L a b ≤ 0 ∨
    certMatrix L a b ^ 2 < certMatrix L a a * certMatrix L b b := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> try exact absurd rfl hab
  all_goals
    right
    norm_num [certMatrix, L, leaf0, leaf1, EQLeaf.ofNonstrict, ρ0, σ0, ρ1, σ1, Fin.sum_univ_two]

/-- **The test theorem.**  For the type 24 shape 253, every `E` with `det E > 0` and obtuse Gram
matrix makes `E Y` Rupert. -/
theorem rupert (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (hGo : ∀ a b, a ≠ b → (Eᵀ * E) a b ≤ 0) : IsRupert (Yc.image (emb E)) :=
  isRupert_of_eq_cert_sqfree L S_diag S_off E hE hGo

end Minimality.CornerEQShape
