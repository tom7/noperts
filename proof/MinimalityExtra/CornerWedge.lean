module

public import Mathlib
public import MinimalityExtra
public import Minimality.Type02X

/-!
# Theorem 02.W: the corner wedge is Rupert

Reduction to `Minimality.CaseC18.Frame7.wedge_rupert` (Type02X.lean): the frame is
`base = 0`, `u1 = (A,0,0)`, `u2 = (0,H1+H6,0)`, `e = (0,0,B)`, and the vertices have frame
coordinates `wpts ρ` with `ρ = H1/(H1+H6)`.
-/

@[expose] public section

open scoped Classical


namespace MinimalityExtra

open Minimality.CaseC18

theorem cornerWedgeRupert : CornerWedgeRupert := by
  intro A B H1 H6 hA hB h1 h6
  have hH : 0 < H1 + H6 := by linarith
  set H := H1 + H6 with hHdef
  set ρ := H1 / H with hρdef
  have hρ : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := by rw [hρdef, div_lt_one hH]; linarith
  have hρH : ρ * H = H1 := by rw [hρdef]; field_simp
  have hind : LinearIndependent ℝ ![(!₂[A, 0, 0] : ℝ³), !₂[0, H, 0], !₂[0, 0, B]] := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero ?_ ?_
    · intro i
      fin_cases i
      · intro h; have := congrArg (fun v : ℝ³ => v 0) h; simp at this; exact hA.ne' this
      · intro h; have := congrArg (fun v : ℝ³ => v 1) h; simp at this; exact hH.ne' this
      · intro h; have := congrArg (fun v : ℝ³ => v 2) h; simp at this; exact hB.ne' this
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
        simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  let G : Frame7 (cornerWedgeVertices A B H1 H6) :=
    { base := 0, u1 := !₂[A, 0, 0], u2 := !₂[0, H, 0], e := !₂[0, 0, B], indep := hind
      inner_u1_e := by simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
      inner_u2_e := by simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
      ptC := wpts ρ
      x_eq := by
        intro j
        fin_cases j <;>
        · simp only [cornerWedgeVertices, wpts]
          ext i
          fin_cases i <;> simp [hρH] <;> nlinarith [hρH] }
  exact G.wedge_rupert ρ hρ hρ1
    (by simp [Frame7.a12, G, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]) rfl

end MinimalityExtra
