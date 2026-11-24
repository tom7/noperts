module

public import Minimality.GenericLeaves
public import Minimality.RimCellClosed
public import Minimality.SlideDS
public import Minimality.Type24SAT.Facets24
public import Minimality.Sym24Transport

/-! Q4 leaf (LEAFPLUS, 2026-11-24): a stronger generic leaf for the type-24 hole (design note: nopert229
tools/genleaves/LEAFPLUS.md).

* `Q4Any`: Lemma Q4 on a closed rim cone (existing proof `isRupert_of_closedCell_q4`, RimCellClosed.lean:224).
  Not limit form: a cell-level (two-view) leaf.  Proved here (wrapper, no sorry).
* (`SepAny`, Theorem 8.10 at an open-cell view, was tested and is never the only closer on the 3219 events: dropped.)
* Type-24 use: `hole24_q4` (an IsRupert conclusion for the type-24 facets); `Hole24` carries `¬ Q4Any F`
  (Type24HoleReduce.lean).  `q4Any_sym`: the leaf transports along the `(2 6)(4 5)` symmetry `sym24`. -/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset

@[expose] public section

namespace Minimality.GenPlus

open Minimality Minimality.H21

/-- **Q4 on a closed rim cone.**  A 4-cycle silhouette `c` of the up facets `U` and down facets `Dn` (only the facets of
the rim edges need be listed, so the cone is the whole region where `c` is the silhouette), a strict cone point `a`,
and closure points `g`, `g'` where some diagonal form is negative resp. positive. -/
def Q4Any {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³} (F : S0xFac m S x) : Prop :=
  ∃ (c : ZMod 4 → Fin n) (U Dn : Finset (Fin m)) (a g g' : ℝ³),
    Function.Injective c ∧ S0xCycUD S c U Dn ∧ CellAt F U Dn a ∧ CellLe F U Dn g ∧ CellLe F U Dn g' ∧
    (∃ p ∈ RimCell.diagPairs, ⟪x (c p.1) - x (c p.2), g⟫ < 0) ∧
    (∃ p ∈ RimCell.diagPairs, 0 < ⟪x (c p.1) - x (c p.2), g'⟫)

theorem q4Any_isRupert {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (hx : Function.Injective x) (h : Q4Any F) : IsRupert (univ.image x) := by
  rcases h with ⟨c, U, Dn, a, g, g', hc, hcyc, ha, hg, hg', hn, hp⟩
  exact isRupert_of_closedCell_q4 F hx hc hcyc ha hg hg' hn hp

/-- Type-24 instance (`Hole24` carries `¬ Q4Any F`, closed by this in `type24_rupert_or_hole`). -/
theorem hole24_q4 {x : Fin 7 → ℝ³} (F : S0xFac 9 Minimality.T24.SAT.s0x_S24 x) (hx : Function.Injective x) (h : Q4Any F) :
    IsRupert (univ.image x) :=
  q4Any_isRupert F hx h

open Minimality.T24.SAT Minimality.T24.Sym in
/-- `Q4Any` transfers along the `(2 6)(4 5)` symmetry `sym24` (cycle `π ∘ c`, facet sets mapped by `σ`; the views
`a`, `g`, `g'` are unchanged), as `Sym.lexAny_sym`. -/
theorem q4Any_sym {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : Q4Any (sym24 F)) : Q4Any F := by
  rcases h with ⟨c, U, Dn, a, g, g', hc, hcyc, ha, hg, hg', hn, hp⟩
  have hcell : ∀ (P : ℝ → Prop) {W : Finset (Fin 9)} {v : ℝ³}, (∀ t ∈ W, P ⟪(sym24 F).N t, v⟫) →
      ∀ t ∈ W.map sig24.toEmbedding, P ⟪F.N t, v⟫ := by
    intro P W v hW t' ht'
    rcases mem_map.mp ht' with ⟨t, ht, rfl⟩
    exact hW t ht
  refine ⟨pi24 ∘ c, U.map sig24.toEmbedding, Dn.map sig24.toEmbedding, a, g, g',
    pi24.injective.comp hc, ?_, ⟨hcell (0 < ·) ha.1, hcell (· < 0) ha.2⟩,
    ⟨hcell (0 ≤ ·) hg.1, hcell (· ≤ 0) hg.2⟩, ⟨hcell (0 ≤ ·) hg'.1, hcell (· ≤ 0) hg'.2⟩, hn, hp⟩
  intro i
  obtain ⟨ea, hea, eb, heb, h1, h2, h3, h4, h5⟩ := hcyc i
  refine ⟨sig24 ea, mem_map_of_mem _ hea, sig24 eb, mem_map_of_mem _ heb,
    (s24_sym ea (c i)).1 h1, (s24_sym eb (c i)).1 h2,
    (s24_sym ea (c (i + 1))).1 h3, (s24_sym eb (c (i + 1))).1 h4, ?_⟩
  intro q hqi hqi1
  obtain ⟨q', rfl⟩ := pi24.surjective q
  rcases h5 q' (fun h => hqi (by simp [h])) (fun h => hqi1 (by simp [h])) with hq | hq
  · exact Or.inl (fun h => hq ((s24_sym ea q').2 h))
  · exact Or.inr (fun h => hq ((s24_sym eb q').2 h))

end Minimality.GenPlus
