module

public import Minimality.Type16Arc3B
public import Minimality.SilS0XC

@[expose] public section

/-!
# H16G: the generic all-views route for type 16, and the combined arc residual

Copy of `Type29GA` for type 16 (8 facets `fIdx`, 13 edges).  `h16g_seg i j pat` (view `x j - x i`) and
`h16g_lin X Y pat` (view `N_X x N_Y`) are the generic leaves; `H16GenResid T` = no generic leaf applies;
`H16ArcGenResid T = H16ArcResid3 T ∧ H16GenResid T`.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H16A
open Minimality.H21 Minimality.H16U Minimality.V2

/-- The 13 edges of type 16 with their two facets. -/
def h16g_E : List (Fin 7 × Fin 7 × Fin 8 × Fin 8) :=
  [(0, 2, 0, 2), (0, 3, 0, 3), (0, 4, 2, 4), (0, 6, 3, 4), (1, 4, 5, 6), (1, 5, 1, 5), (1, 6, 1, 6),
    (2, 4, 2, 7), (2, 5, 0, 7), (3, 5, 0, 1), (3, 6, 1, 3), (4, 5, 5, 7), (4, 6, 4, 6)]

def h16g_nb (pat : Fin 8 → Bool) (v : Fin 7) : List (Fin 7) :=
  h16g_E.filterMap fun e =>
    if pat e.2.2.1 != pat e.2.2.2 then
      (if e.1 = v then some e.2.1 else if e.2.1 = v then some e.1 else none)
    else none

def h16g_walk (pat : Fin 8 → Bool) (s : Fin 7) : ℕ → Fin 7 → Fin 7 → List (Fin 7)
  | 0, _, _ => []
  | n + 1, p, c =>
    if c = s then [] else c :: h16g_walk pat s n c (((h16g_nb pat c).filter (· ≠ p)).headD c)

def h16g_cyc (pat : Fin 8 → Bool) : List (Fin 7) :=
  match (List.finRange 7).find? (fun v => !(h16g_nb pat v).isEmpty) with
  | none => []
  | some s => s :: h16g_walk pat s 7 s ((h16g_nb pat s).headD s)

def h16g_k (pat : Fin 8 → Bool) : ℕ := (h16g_cyc pat).length - 3 + 3

instance (pat : Fin 8 → Bool) : NeZero (h16g_k pat) := ⟨by unfold h16g_k; omega⟩

def h16g_c (pat : Fin 8 → Bool) (a : ZMod (h16g_k pat)) : Fin 7 := (h16g_cyc pat).getD a.val 0

def h16g_seg (i j : Fin 7) (pat : Fin 8 → Bool) : S0xSeg 7 8 (h16g_k pat) :=
  ⟨i, j, pat, h16g_c pat⟩

def h16g_lin (X Y : Fin 8) (pat : Fin 8 → Bool) : S0xLin 7 8 (h16g_k pat) :=
  ⟨X, Y, pat, h16g_c pat⟩

variable {x : Fin 7 → ℝ³}

/-- The type-16 facets as a type-free facet family. -/
noncomputable def h16g_fac (T : Type16 x) : S0xFac 8 fIdx x where
  f := T.ff
  N := T.fN
  hN := ff_hN T
  zero t i h := ff_zero T t i h
  neg t i h := ff_neg T t i h

def H16GSegLeaf (T : Type16 x) (i j : Fin 7) (pat : Fin 8 → Bool) : Prop :=
  (h16g_seg i j pat).Good fIdx ∧ (h16g_seg i j pat).Cond (h16g_fac T)

def H16GLinLeaf (T : Type16 x) (X Y : Fin 8) (pat : Fin 8 → Bool) : Prop :=
  (h16g_lin X Y pat).Good fIdx ∧ (h16g_lin X Y pat).Cond (h16g_fac T)

/-- **The residual**: no generic silhouette cell applies, at any segment or facet-pair line view. -/
def H16GenResid (T : Type16 x) : Prop :=
  (∀ i j pat, ¬ H16GSegLeaf T i j pat) ∧ (∀ X Y pat, ¬ H16GLinLeaf T X Y pat)

theorem h16g_seg_isRupert (T : Type16 x) {i j : Fin 7} {pat : Fin 8 → Bool}
    (h : H16GSegLeaf T i j pat) : IsRupert (univ.image x) :=
  s0x_seg_rupert (h16g_fac T) T.inj _ h.1 h.2

theorem h16g_lin_isRupert (T : Type16 x) {X Y : Fin 8} {pat : Fin 8 → Bool}
    (h : H16GLinLeaf T X Y pat) : IsRupert (univ.image x) :=
  s0x_lin_rupert (h16g_fac T) T.inj _ h.1 h.2

theorem h16g_rule_isRupert (T : Type16 x) (h : ¬ H16GenResid T) : IsRupert (univ.image x) := by
  unfold H16GenResid at h
  by_cases hs : ∀ i j pat, ¬ H16GSegLeaf T i j pat
  · have hl : ¬ ∀ X Y pat, ¬ H16GLinLeaf T X Y pat := fun hl => h ⟨hs, hl⟩
    push_neg at hl
    obtain ⟨X, Y, pat, hl⟩ := hl
    exact h16g_lin_isRupert T hl
  · push_neg at hs
    obtain ⟨i, j, pat, hs⟩ := hs
    exact h16g_seg_isRupert T hs

/-- **Type 16 generic silhouette rule**. -/
theorem h16g_rule_false (hN : IsNopert (Finset.univ.image x)) (T : Type16 x)
    (h : ¬ H16GenResid T) : False :=
  hN.2 (h16g_rule_isRupert T h)

/-- The combined residual: no arc leaf (`H16ArcResid3`) and no generic silhouette cell. -/
def H16ArcGenResid (T : Type16 x) : Prop := H16ArcResid3 T ∧ H16GenResid T

theorem h16g_arcgen_isRupert (T : Type16 x) (h : ¬ H16ArcGenResid T) : IsRupert (univ.image x) := by
  by_cases h3 : H16ArcResid3 T
  · exact h16g_rule_isRupert T (fun hg => h ⟨h3, hg⟩)
  · exact h16a3_rule_isRupert T h3

theorem h16g_arcgen_rule_false (hN : IsNopert (Finset.univ.image x)) (T : Type16 x)
    (h : ¬ H16ArcGenResid T) : False :=
  hN.2 (h16g_arcgen_isRupert T h)

theorem h16g_arcgen_imp_arc (T : Type16 x) (h : H16ArcGenResid T) : H16ArcResid3 T := h.1
theorem h16g_arcgen_imp_gen (T : Type16 x) (h : H16ArcGenResid T) : H16GenResid T := h.2

end H16A
end Minimality
