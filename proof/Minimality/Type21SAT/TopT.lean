module

public import Minimality.Type21SAT.Top
public import Minimality.Type21SilF

@[expose] public section

/-!
# L3, part 23: core A for a `Facets21` shape, and the geometric form of `D not parallel to H`

`caseA_of_unsat_T` states the top theorem for a shape with `Facets21 x` (the realization of the faces of type 21 as the
repository states it) of the chirality of `S0`.  `offDH_of_nonpar` turns "the normals of `D` and `H` are not proportional"
into the two-atom form the case clause uses.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H21.SAT

variable {x : Fin 7 → ℝ³}

/-- The facet sets of `S21` are those of the repository (`h21S`). -/
theorem S21_eq : S21 = h21S := by
  funext a; fin_cases a <;> rfl

/-- The eight facets of `Facets21` as an `S0xFac 8 S21 x`. -/
noncomputable def toS0xFac (T : Facets21 x) : S0xFac 8 S21 x where
  f := (fac8 T).f
  N := (fac8 T).N
  hN := (fac8 T).hN
  zero := fun t i hi => (fac8 T).zero t i (by rwa [S21_eq] at hi)
  neg := fun t i hi => (fac8 T).neg t i (by rwa [S21_eq] at hi)

/-- **Not parallel `D`, `H`, geometrically**: if the normals of the facets `D` (3) and `H` (7) are not proportional, then
`<N_D, x2 - x3>` and `<N_D, x2 - x5>` are not both zero. -/
theorem offDH_of_nonpar (F : S0xFac 8 S21 x) (h : ¬ ∃ r : ℝ, F.N 3 = r • F.N 7) :
    ¬ (⟪F.N 3, x 2 - x 3⟫ = 0 ∧ ⟪F.N 3, x 2 - x 5⟫ = 0) := by
  rintro ⟨h1, h2⟩
  have hx := inj_of_fac F
  have z : ∀ (t : Fin 8) (i j : Fin 7), i ∈ S21 t → j ∈ S21 t → ⟪F.N t, x i - x j⟫ = 0 := by
    intro t i j hi hj
    rw [F.inner_sub, F.zero t i hi, F.zero t j hj, sub_self]
  have hu : x 2 - x 3 ≠ 0 := fun h0 => by
    have := hx (sub_eq_zero.mp h0); exact absurd (congrArg Fin.val this) (by decide)
  have hN7 : F.N 7 ≠ 0 := by
    intro h0
    have := F.neg 7 0 (by decide +kernel)
    have h3 := F.zero 7 2 (by decide +kernel)
    have h4 := F.hN 7 (x 0) (x 2)
    rw [h0, h3] at h4
    simp at h4
    linarith
  have h7a := z 7 2 3 (by decide +kernel) (by decide +kernel)
  have h7b := z 7 2 5 (by decide +kernel) (by decide +kernel)
  have h6a := z 6 2 3 (by decide +kernel) (by decide +kernel)
  have h6b : ⟪F.N 6, x 2 - x 5⟫ ≠ 0 := by
    rw [F.inner_sub, F.zero 6 2 (by decide +kernel)]
    have := F.neg 6 5 (by decide +kernel)
    linarith
  apply h
  exact parallel_of_perp (x 2 - x 3) (x 2 - x 5) (F.N 7) (F.N 3) (F.N 6) hu hN7
    h7a h7b
    h1 h2
    h6a h6b

/-- **Top theorem for core A, for `Facets21`.**  If the numbered clauses of core A are unsatisfiable, every shape with
`Facets21 x` of the chirality of `S0` and facets `D`, `H` not parallel is Rupert. -/
theorem caseA_of_unsat_T (hA : CoreUnsatA) (T : Facets21 x)
    (hchir : 0 < det3 (x 0 - x 2) (x 3 - x 2) (x 6 - x 2))
    (hDH : ¬ ∃ r : ℝ, T.f046.N = r • T.f235.N) : IsRupert (univ.image x) :=
  caseA_of_unsat hA (toS0xFac T) hchir (offDH_of_nonpar (toS0xFac T) hDH)

end Minimality.H21.SAT

