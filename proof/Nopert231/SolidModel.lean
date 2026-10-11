module

public import Pipeline.FivefoldModel
public import Nopert231.Vertices

@[expose] public section

/-!
# Nopert #231 as a fivefold solid model

Candidate #231's twenty vertices rotate four seeds about z in steps of 2π/5
(vertex `4k + s` is seed `s` rotated by `2πk/5`, up to rounding). The data
(`rationalVertices`, `seedVertex`) is in `Nopert231.Vertices`, which imports
only Mathlib.

`fivefoldSolid` (a scoped instance: in effect inside `namespace Nopert231`
only) makes this data a `FivefoldSolid`, hence a `SolidModel` for the
certificate pipeline (`Pipeline/`): C5 about z, rational Taylor symmetry
matrices within `κ/2`, model error `6 · 10⁻¹⁶`, C++ vertex `n` is slot `n`.
The facts it needs are checked by the kernel below.

`C5Model` is the pipeline's `CyclicModel` for this solid: every polyhedron
whose 20 vertices are four real seeds rotated *exactly* by `2πk/5` about z,
each within `modelErrorQ = 6 · 10⁻¹⁶` of the corresponding rational vertex
(`C5Model.ofRzL` and `C5Model.vertex_eq_RzL` state this with `RzL`). Until
2026-10-10 Nopert231 had its own definition of `C5Model`, with the same
fields; the pipeline's generic `CyclicModel` was called `C5Model` too.
-/

namespace Nopert231

open Noperts Noperts.Pipeline

theorem seedVertex_xy_sq_le_one :
    ∀ t : Fin 4, (Nopert231.seedVertex t 0) ^ 2 + (Nopert231.seedVertex t 1) ^ 2 ≤ 1 := by
  decide +kernel

/-- The rational vertices agree with the tight rational rotations of the
seeds (`tightVertex`) to `4 · 10⁻¹⁶`. Kernel checked. -/
theorem rationalVertices_tight_sq_close : ∀ i : Fin (5 * 4),
    (rationalVertices i 0 - tightVertex Nopert231.seedVertex i 0) ^ 2 +
    (rationalVertices i 1 - tightVertex Nopert231.seedVertex i 1) ^ 2 +
    (rationalVertices i 2 - tightVertex Nopert231.seedVertex i 2) ^ 2 ≤
      (4 / 10^16 : ℚ) ^ 2 := by
  decide +kernel

/-- Every rational vertex has norm in `[1/10, 1 - 10⁻¹²]`. -/
theorem rationalVertices_sq_norm_bounds : ∀ i : Fin (5 * 4),
    (1 / 100 : ℚ) ≤ rationalVertices i 0 ^ 2 + rationalVertices i 1 ^ 2 +
        rationalVertices i 2 ^ 2 ∧
      rationalVertices i 0 ^ 2 + rationalVertices i 1 ^ 2 + rationalVertices i 2 ^ 2 ≤
        (1 - 1 / 10^12) ^ 2 := by
  decide +kernel

/-- Candidate #231's model for the certificate pipeline. -/
scoped instance fivefoldSolid : FivefoldSolid where
  seedCount := 4
  seedCount_pos := by norm_num
  rationalVertices := rationalVertices
  seedVertex := Nopert231.seedVertex
  seed_xy_sq_le_one := seedVertex_xy_sq_le_one
  tight_sq_close := rationalVertices_tight_sq_close
  rationalVertex_sq_norm_bounds := rationalVertices_sq_norm_bounds

/-- A polyhedron with exact fivefold symmetry about z near the rational
model: vertex `i` is seed `seedIndex i` rotated by `2π · orbitIndex i / 5`,
and each vertex is within `modelErrorQ` (`6 · 10⁻¹⁶`) of `rationalVertex i`.
This is the pipeline's `CyclicModel` for candidate #231. -/
abbrev C5Model : Type := CyclicModel

/-- Vertex `4k + s` of a `C5Model` is seed `s` rotated by `2πk/5` about z. -/
theorem C5Model.vertex_eq (P : C5Model) {i : VertexIndex} (k : Fin 5) (s : Fin 4)
    (hi : i.val = 4 * k.val + s.val) :
    P.vertex i = RzL (2 * Real.pi * (k : ℝ) / 5) (P.seed s) := by
  rw [CyclicModel.vertex_eq_RzL]
  have hk : orbitIndex i = k := by
    apply Fin.ext
    change i.val / 4 = k.val
    omega
  have hs : seedIndex i = s := by
    apply Fin.ext
    change i.val % 4 = s.val
    omega
  rw [hk, hs]

/-- Coordinate `j` of seed `s` rotated by `2πk/5` is within `6 · 10⁻¹⁶` of
rational vertex `4k + s`. -/
theorem C5Model.seed_apply_close (P : C5Model) (k : Fin 5) (s : Fin 4) (i : Fin 20)
    (hi : i.val = 4 * k.val + s.val) (j : Fin 3) :
    |RzL (2 * Real.pi * (k : ℝ) / 5) (P.seed s) j - (rationalVertices i j : ℝ)| ≤
      ((6 / 10 ^ 16 : ℚ) : ℝ) := by
  have h := (PiLp.norm_apply_le (P.vertex i - toR3 (rationalVertex i)) j).trans
    (P.vertex_close_model i)
  rw [P.vertex_eq k s hi] at h
  simp only [toR3, PiLp.sub_apply, Real.norm_eq_abs] at h
  exact h

/-- A `C5Model` from four seeds and the closeness of their exact rotations
(by `RzL (2πk/5)`) to the rational vertices. -/
noncomputable def C5Model.ofRzL (seed : Fin 4 → ℝ³)
    (close : ∀ i : Fin 20,
      ‖RzL (2 * Real.pi * ((i.val / 4 : ℕ) : ℝ) / 5) (seed ⟨i.val % 4, by omega⟩) -
        toR3 (rationalVertices i)‖ ≤ ((6 / 10^16 : ℚ) : ℝ)) : C5Model where
  seed := seed
  close i := by
    rw [symmetryMatrix_apply_eq_RzL]
    exact close i

/-- The model error of candidate #231: `6 · 10⁻¹⁶`. -/
theorem modelErrorQ_value : modelErrorQ = 6 / 10 ^ 16 := rfl

end Nopert231

end
