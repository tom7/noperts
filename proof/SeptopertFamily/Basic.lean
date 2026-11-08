module

public import EuclideanSpaceNotation
public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Rat.Cast.Order

/-!
# The Septopert family

The *Septopert family* is the family of 7-point solids with the symmetry of a
cube corner (the group C₃ᵥ: the coordinate permutations), given by five
integers `x = (x₀, x₁, x₂, x₃, x₄)`:

* `(x₀, x₁, x₁)`, `(x₁, x₀, x₁)`, `(x₁, x₁, x₀)`,
* `(x₂, x₃, x₃)`, `(x₃, x₂, x₃)`, `(x₃, x₃, x₂)`,
* `(x₄, x₄, x₄)`.

The *height* of `x` is `⌈(max x − min x) / 2⌉`. The Septoperts (M7, M18, ...)
are members of this family.
-/

@[expose] public section

namespace SeptopertFamily

/-- The 7 points of the Septopert family with integer parameters `x`. -/
noncomputable def familyVerts (x : Fin 5 → ℤ) : Finset ℝ³ :=
  {!₂[(x 0 : ℝ), x 1, x 1], !₂[(x 1 : ℝ), x 0, x 1], !₂[(x 1 : ℝ), x 1, x 0],
   !₂[(x 2 : ℝ), x 3, x 3], !₂[(x 3 : ℝ), x 2, x 3], !₂[(x 3 : ℝ), x 3, x 2],
   !₂[(x 4 : ℝ), x 4, x 4]}

/-- The height `⌈(max x − min x) / 2⌉` of the parameters `x`. -/
def familyHeight (x : Fin 5 → ℤ) : ℤ :=
  ⌈((Finset.univ.sup' Finset.univ_nonempty x - Finset.univ.inf' Finset.univ_nonempty x : ℤ) : ℚ) / 2⌉

/-- Height below 7 means that all parameters lie within 12 of each other. -/
theorem sub_le_twelve_of_familyHeight_lt_seven {x : Fin 5 → ℤ} (h : familyHeight x < 7)
    (i j : Fin 5) : x i - x j ≤ 12 := by
  have hi := Finset.le_sup' x (Finset.mem_univ i)
  have hj := Finset.inf'_le x (Finset.mem_univ j)
  have h6 : familyHeight x ≤ 6 := by omega
  unfold familyHeight at h6
  rw [Int.ceil_le] at h6
  have h12 : ((Finset.univ.sup' Finset.univ_nonempty x - Finset.univ.inf' Finset.univ_nonempty x : ℤ) : ℚ) ≤ 12 := by
    push_cast at h6 ⊢; linarith
  have h12' : Finset.univ.sup' Finset.univ_nonempty x - Finset.univ.inf' Finset.univ_nonempty x ≤ 12 := by
    exact_mod_cast h12
  omega

end SeptopertFamily

end
