module

public import SeptopertFamily.Check

/-!
# No Septopert-family nopert of height below 7

The Septopert family (`SeptopertFamily.familyVerts`): for integers
`x = (x₀, …, x₄)` the 7 points `(x₀, x₁, x₁)`, `(x₁, x₀, x₁)`, `(x₁, x₁, x₀)`,
`(x₂, x₃, x₃)`, `(x₃, x₂, x₃)`, `(x₃, x₃, x₂)`, `(x₄, x₄, x₄)`, of height
`⌈(max x − min x) / 2⌉` (`SeptopertFamily.familyHeight`).

**Theorem** (`SeptopertFamily.not_isNopert_of_familyHeight_lt_seven`): no
member of height below 7 is a nopert, given the certificate check
`LeastHeightValid`. With M7, a Septopert of height 7, this makes height 7 the
least height of an integer nopert of the family.

Every tuple is reduced to one with minimum 0 by a translation along `(1, 1, 1)`,
then to a primitive tuple by a scaling and, possibly, to its reflection
`max − x` (all similarities, which preserve being a nopert). Each of the 55,651
remaining tuples has a certificate: its points are coplanar (161 tuples), one point
lies in the hull of the others, so at most 6 points span the solid, and every
solid with at most 6 points is Rupert (25,932), or an explicit rational Rupert
passage (29,558). See `SeptopertFamily/Check.lean` for the check and
`checkSeptopertFamily.lean` for the native executable that runs it on
`SeptopertFamily/data/leastheight.txt`.

All results depend only on the three standard axioms `propext`,
`Classical.choice` and `Quot.sound`, plus `LeastHeightValid` as a hypothesis.
-/

@[expose] public section

namespace SeptopertFamily

/-- The certificate data is valid: some certificate table passes `checkAll`.
(Established by running `checkSeptopertFamily` on the data.) -/
def LeastHeightValid : Prop := ∃ tbl : Table, checkAll tbl = true

/-- **No nopert in the family with parameters within 12 of each other.** -/
theorem not_isNopert_of_sub_le_twelve (hvalid : LeastHeightValid) (x : Fin 5 → ℤ)
    (hx : ∀ i j, x i - x j ≤ 12) : ¬ IsNopert (familyVerts x) := by
  obtain ⟨tbl, h⟩ := hvalid
  exact checkAll_sound h x hx

/-- **No nopert in the family of height below 7.** -/
theorem not_isNopert_of_familyHeight_lt_seven (hvalid : LeastHeightValid) (x : Fin 5 → ℤ)
    (hx : familyHeight x < 7) : ¬ IsNopert (familyVerts x) :=
  not_isNopert_of_sub_le_twelve hvalid x (sub_le_twelve_of_familyHeight_lt_seven hx)

end SeptopertFamily

end
