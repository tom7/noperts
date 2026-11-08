module

public import Basic
public import Pipeline.KCapChart

@[expose] public section

/-!
# Septopert

The 7-vertex solid Septopert: permutations of (-27, 15, 15), (27, 6, 6), (-13, -13, -13) over 64
(`search/m7/m7-model.txt`), with the 3-fold axis (1, 1, 1).
-/

namespace Septopert
open Noperts

/-- The seven vertices of Septopert (the model's rational vertices, denominator 64). -/
def vertexQ : Fin 7 → Fin 3 → ℚ := ![
  ![(-27 / 64 : ℚ), (15 / 64 : ℚ), (15 / 64 : ℚ)],
  ![(15 / 64 : ℚ), (-27 / 64 : ℚ), (15 / 64 : ℚ)],
  ![(15 / 64 : ℚ), (15 / 64 : ℚ), (-27 / 64 : ℚ)],
  ![(27 / 64 : ℚ), (3 / 32 : ℚ), (3 / 32 : ℚ)],
  ![(3 / 32 : ℚ), (27 / 64 : ℚ), (3 / 32 : ℚ)],
  ![(3 / 32 : ℚ), (3 / 32 : ℚ), (27 / 64 : ℚ)],
  ![(-13 / 64 : ℚ), (-13 / 64 : ℚ), (-13 / 64 : ℚ)]]

/-- Blend of the certificates (`capcert-m7` adds it to every chart): v₄'s image on the segment
v₀ v₅ at t*, (7/11) v₀ + (4/11) v₅. -/
def arcBlends : List (ℕ × ℕ × ℚ) := [(0, 5, 4 / 11)]

noncomputable def poly : Polyhedron (Fin 7) ℝ³ := ⟨fun i => toR3 (vertexQ i)⟩

/-- The solid. -/
def solid : Set ℝ³ := poly.hull

end Septopert

end
