module

public import Basic
public import Pipeline.KCapChart

@[expose] public section

/-!
# M12

The 7-vertex solid M12: permutations of (-11, 7, 7), (12, 3, 3), (-5, -5, -5) over 16
(`search/h12/h12-model.txt`), with the 3-fold axis (1, 1, 1).
-/

namespace M12
open Noperts

/-- The seven vertices of M12 (the model's rational vertices, denominator 16). -/
def vertexQ : Fin 7 → Fin 3 → ℚ := ![
  ![(-11 / 16 : ℚ), (7 / 16 : ℚ), (7 / 16 : ℚ)],
  ![(7 / 16 : ℚ), (-11 / 16 : ℚ), (7 / 16 : ℚ)],
  ![(7 / 16 : ℚ), (7 / 16 : ℚ), (-11 / 16 : ℚ)],
  ![(3 / 4 : ℚ), (3 / 16 : ℚ), (3 / 16 : ℚ)],
  ![(3 / 16 : ℚ), (3 / 4 : ℚ), (3 / 16 : ℚ)],
  ![(3 / 16 : ℚ), (3 / 16 : ℚ), (3 / 4 : ℚ)],
  ![(-5 / 16 : ℚ), (-5 / 16 : ℚ), (-5 / 16 : ℚ)]]

/-- Blend of the certificates (`capcert-m12` adds it to every chart): v₄'s image on the segment
v₀ v₅ at t*, (9/14) v₀ + (5/14) v₅. -/
def arcBlends : List (ℕ × ℕ × ℚ) := [(0, 5, 5 / 14)]

noncomputable def poly : Polyhedron (Fin 7) ℝ³ := ⟨fun i => toR3 (vertexQ i)⟩

/-- The solid. -/
def solid : Set ℝ³ := poly.hull

end M12

end
