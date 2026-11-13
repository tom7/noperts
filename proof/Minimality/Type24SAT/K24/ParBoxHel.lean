module

public import Mathlib
public import Minimality.HiddenEnd

@[expose] public section

/-!
# Type 24 box corner `R₄'`: the engine

`boxCfg` (box coordinates of the seven vertices) and `box_hel`: `hel_rupert` at the corner `4`
(`K = 0`, `J = 3`, `M = 6`, `γ = δ = 0`, `u₀ = (-L,0,0)`, `v₁ = (0,-r,-1)`) with row lemmas `cone_cert`, `tri_cert`
reducing a certificate to `LP` (lexicographic positivity of two polynomials).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
namespace Minimality.T24.Par
open Minimality.Split Minimality.Split.HEL
open Minimality (cross)

/-- The box corner in box coordinates: `x 0 = 0`, `x 4 = (L,0,0)`, `x 5 = (0,0,c)`, `x 3 = (L,0,c)`,
`x 2 = (0,y2,c)`, `x 6 = (L,y6,0)`, `x 1 = (xi L, b, ze c)`. -/
noncomputable def boxCfg (L c y2 y6 xi ze b : ℝ) : Fin 7 → ℝ³ :=
  ![!₂[0, 0, 0], !₂[xi * L, b, ze * c], !₂[0, y2, c], !₂[L, 0, c], !₂[L, 0, 0], !₂[0, 0, c], !₂[L, y6, 0]]

/-- `(A, B)` lexicographically positive (`LexPos3 A B 0`). -/
def LP (A B : ℝ) : Prop := 0 < A ∨ (A = 0 ∧ 0 < B)

/-- The view `u₀ = (-L,0,0)` and tilt `v₁ = (0,-r,-1)`: a `LexDet` is a `LP` of explicit polynomials. -/
theorem lexDet_box (L r : ℝ) (a b : ℝ³)
    (h : LP (-L * (a 1 * b 2 - a 2 * b 1)) (-r * (a 2 * b 0 - a 0 * b 2) - (a 0 * b 1 - a 1 * b 0))) :
    LexDet a b !₂[-L, 0, 0] !₂[0, -r, -1] 0 := by
  have eA : Split.det3 a b !₂[-L, 0, 0] = -L * (a 1 * b 2 - a 2 * b 1) := by
    simp only [Minimality.Split.det3]; simp; ring
  have eB : Split.det3 a b !₂[0, -r, -1] = -r * (a 2 * b 0 - a 0 * b 2) - (a 0 * b 1 - a 1 * b 0) := by
    simp only [Minimality.Split.det3]; simp; ring
  have eC : Split.det3 a b (0 : ℝ³) = 0 := by simp only [Minimality.Split.det3]; simp
  unfold LexDet LexPos3 LexPos2
  rw [eA, eB, eC]
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, Or.inl h2⟩

/-- The certificate for a cone `(y₀, y₁)` at `x`. -/
theorem cone_cert (L r : ℝ) (V : Finset ℝ³) (ω τ x y0 y1 : ℝ³) (h0 : y0 ∈ V) (h1 : y1 ∈ V)
    (d1 : LP (-L * ((y1 - x) 1 * (y0 - x) 2 - (y1 - x) 2 * (y0 - x) 1))
      (-r * ((y1 - x) 2 * (y0 - x) 0 - (y1 - x) 0 * (y0 - x) 2) - ((y1 - x) 0 * (y0 - x) 1 - (y1 - x) 1 * (y0 - x) 0)))
    (d2 : LP (-L * ((y1 - x) 1 * (cross ω x + τ) 2 - (y1 - x) 2 * (cross ω x + τ) 1))
      (-r * ((y1 - x) 2 * (cross ω x + τ) 0 - (y1 - x) 0 * (cross ω x + τ) 2) -
        ((y1 - x) 0 * (cross ω x + τ) 1 - (y1 - x) 1 * (cross ω x + τ) 0)))
    (d3 : LP (-L * ((x - y0) 1 * (cross ω x + τ) 2 - (x - y0) 2 * (cross ω x + τ) 1))
      (-r * ((x - y0) 2 * (cross ω x + τ) 0 - (x - y0) 0 * (cross ω x + τ) 2) -
        ((x - y0) 0 * (cross ω x + τ) 1 - (x - y0) 1 * (cross ω x + τ) 0))) :
    LexTiltCert V !₂[-L, 0, 0] !₂[0, -r, -1] 0 ω τ x :=
  Or.inl ⟨y0, h0, y1, h1, lexDet_box L r _ _ d1, lexDet_box L r _ _ d2, lexDet_box L r _ _ d3⟩

/-- The certificate for a triangle `(a, b, c)` containing `x`. -/
theorem tri_cert (L r : ℝ) (V : Finset ℝ³) (ω τ x a b c : ℝ³) (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V)
    (d1 : LP (-L * ((b - a) 1 * (c - a) 2 - (b - a) 2 * (c - a) 1))
      (-r * ((b - a) 2 * (c - a) 0 - (b - a) 0 * (c - a) 2) - ((b - a) 0 * (c - a) 1 - (b - a) 1 * (c - a) 0)))
    (d2 : LP (-L * ((b - a) 1 * (x - a) 2 - (b - a) 2 * (x - a) 1))
      (-r * ((b - a) 2 * (x - a) 0 - (b - a) 0 * (x - a) 2) - ((b - a) 0 * (x - a) 1 - (b - a) 1 * (x - a) 0)))
    (d3 : LP (-L * ((c - b) 1 * (x - b) 2 - (c - b) 2 * (x - b) 1))
      (-r * ((c - b) 2 * (x - b) 0 - (c - b) 0 * (x - b) 2) - ((c - b) 0 * (x - b) 1 - (c - b) 1 * (x - b) 0)))
    (d4 : LP (-L * ((a - c) 1 * (x - c) 2 - (a - c) 2 * (x - c) 1))
      (-r * ((a - c) 2 * (x - c) 0 - (a - c) 0 * (x - c) 2) - ((a - c) 0 * (x - c) 1 - (a - c) 1 * (x - c) 0))) :
    LexTiltCert V !₂[-L, 0, 0] !₂[0, -r, -1] 0 ω τ x :=
  Or.inr ⟨a, ha, b, hb, c, hc, lexDet_box L r _ _ d1, lexDet_box L r _ _ d2, lexDet_box L r _ _ d3,
    lexDet_box L r _ _ d4⟩

/-- **The engine at the box corner**: `hel_rupert` with corner `4`, `K = 0`, `J = 3`, `M = 6`, `γ = δ = 0`,
view `u₀ = (-L,0,0)`, tilt `v₁ = (0,-r,-1)`; a motion `(ω, τ)` with a lexicographic certificate at the six
points `1..6`. -/
theorem box_hel {L c y2 y6 xi ze b r : ℝ} (hL : 0 < L) (hc : 0 < c) (hy6 : 0 < y6) (hr : 0 < r)
    (ω τ : ℝ³)
    (h : ∀ i : Fin 7, i ≠ 0 →
      LexTiltCert (univ.image (boxCfg L c y2 y6 xi ze b)) !₂[-L, 0, 0] !₂[0, -r, -1] 0 ω τ
        (boxCfg L c y2 y6 xi ze b i)) :
    IsRupert (univ.image (boxCfg L c y2 y6 xi ze b)) := by
  have hD : 0 < hD (boxCfg L c y2 y6 xi ze b) 4 0 3 6 := by
    simp only [hD, Minimality.Split.det3, boxCfg]
    simp
    nlinarith [mul_pos (mul_pos hc hy6) hL]
  have e1 : hk (boxCfg L c y2 y6 xi ze b) 4 0 = !₂[-L, 0, 0] := by
    ext i; fin_cases i <;> simp [hk, boxCfg]
  have e2 : hv₁ (boxCfg L c y2 y6 xi ze b) 4 3 6 (1 / c) (r / y6) = !₂[0, -r, -1] := by
    ext i; fin_cases i <;> simp [hv₁, boxCfg] <;> field_simp
  have e3 : hv₂ (boxCfg L c y2 y6 xi ze b) 4 3 6 0 0 = 0 := by
    ext i; fin_cases i <;> simp [hv₂, boxCfg]
  refine hel_rupert (boxCfg L c y2 y6 xi ze b) 4 0 3 6 (1 / c) (r / y6) 0 0 ω τ hD
    (Or.inl (by positivity)) (Or.inl (by positivity)) ?_
  intro i hi
  rw [e1, e2, e3]
  exact h i hi

end Minimality.T24.Par
