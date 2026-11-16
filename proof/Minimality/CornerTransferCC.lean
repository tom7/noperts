module

public import Mathlib
public import Minimality.CornerTransfer
public import Minimality.RimCellClosed

/-!
# Closed-cell adapter: a closed-cell vertex leaf is a corner leaf at its own apex

Source: `notes/LIFT-TRANSFER-DESIGN.md`, build step 5.  The rim-exposing lex-cell constructions
`h21b_core_pos_rim` (`Type21Sl2C`), `s0x_sil_cell_lexUni_rim`, `s0x_sil_cell_lex_rim` (`SilS0XB`), of which
`h21b_core_pos`, `s0x_sil_cell_lexUni`, `s0x_sil_cell_lex` are corollaries, and the adapter
`cornerLeaf_of_closedCell`.
* `lexCell_of_closedCell`: closed cell + `RobUni` gives `u₀ ≠ 0` and a lex cell of `univ.image x` with such a rim.
* `cornerLeaf_of_closedCell`: if the cycle avoids the vertex `i₀` (`c i ≠ i₀`), this is a `CornerLeaf` of
  `(univ.erase i₀).image x` at the apex `x i₀`, ready for `cornerLeaf_lift`.
-/

@[expose] public section

set_option autoImplicit false

namespace Minimality.H21

open Finset
open scoped RealInnerProductSpace

variable {n m k : ℕ} [NeZero k] {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³} {c : ZMod k → Fin n} {u₀ v : ℝ³}

/-- **Closed cell as a lex cell with exposed rim.**  Same hypotheses as `isRupert_of_closedCell`. -/
theorem lexCell_of_closedCell (hk : 4 ≤ k) (F : S0xFac m S x)
    (hx : Function.Injective x) (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {a : ℝ³} (ha : CellAt F U Dn a)
    (hu : CellLe F U Dn u₀) (hR : RobUni (fun i => ⟪x (c i), u₀⟫)) :
    u₀ ≠ 0 ∧ ∃ (v' : ℝ³) (y : ZMod k → ℝ³), (∀ i, ∃ j, y i = x (c j)) ∧
      LexCell (univ.image x) u₀ v' y := by
  obtain ⟨D⟩ := silL_of_cell F hcyc hu ha
  refine ⟨?_, s0x_sil_cell_lex_rim (by omega) hx hc D hR⟩
  intro h0
  rw [h0] at hR
  exact not_robUni_const hk 0 (by simpa using hR)

/-- **Closed-cell corner leaf.**  If the cycle avoids the vertex `i₀` (this is what the leaf must record),
the closed-cell leaf is a `CornerLeaf` of `O = x '' (univ \ {i₀})` at the apex `x i₀`. -/
theorem cornerLeaf_of_closedCell (hk : 4 ≤ k) (F : S0xFac m S x)
    (hx : Function.Injective x) (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {a : ℝ³} (ha : CellAt F U Dn a)
    (hu : CellLe F U Dn u₀) (hR : RobUni (fun i => ⟪x (c i), u₀⟫)) (i₀ : Fin n)
    (hci : ∀ i, c i ≠ i₀) (z : Fin 3 → ℝ³) :
    Minimality.CornerEQ.CornerLeaf ((univ.erase i₀).image x) z (x i₀) := by
  obtain ⟨hu0, v', y, hy, hlex⟩ := lexCell_of_closedCell hk F hx hc hcyc ha hu hR
  left
  have hI : insert (x i₀) ((univ.erase i₀).image x) = univ.image x := by
    ext w
    simp only [mem_insert, mem_image, mem_erase, mem_univ, and_true]
    constructor
    · rintro (rfl | ⟨j, -, rfl⟩)
      · exact ⟨i₀, trivial, rfl⟩
      · exact ⟨j, trivial, rfl⟩
    · rintro ⟨j, -, rfl⟩
      by_cases h : j = i₀
      · exact Or.inl (by rw [h])
      · exact Or.inr ⟨j, h, rfl⟩
  refine ⟨u₀, v', k, inferInstance, y, hu0, fun i => ?_, fun i => ?_, by rw [hI]; exact hlex⟩
  · obtain ⟨j, hj⟩ := hy i
    rw [hj]
    exact mem_image.2 ⟨c j, mem_erase.2 ⟨hci j, mem_univ _⟩, rfl⟩
  · obtain ⟨j, hj⟩ := hy i
    rw [hj]
    exact fun h => hci j (hx h)

end Minimality.H21
