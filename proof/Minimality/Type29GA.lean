module

public import Minimality.Type29SilE

@[expose] public section

/-!
# H29G: the generic all-views route for type 29, and the residual

Copy of `Type20SilC` for type 29 (9 facets `s0x_S29`, 14 edges).  `h29g_cyc pat` computes the silhouette
cycle from the facing pattern; `h29g_seg i j pat` (view `x j - x i`) and `h29g_lin X Y pat` (view
`N_X x N_Y`) are the generic leaves; `H29GenResid T` = no generic leaf applies; `h29g_rule_false`.
The 25 edge-view leaves of `Type29SilE` are instances (`h29g_gen_imp_E`); the 12 older W leaves use `Uni`
(not `RobUni`) and are not.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H29S
open Minimality.H21

/-- The 14 edges of type 29 with their two facets. -/
def h29g_E : List (Fin 7 × Fin 7 × Fin 9 × Fin 9) :=
  [(0, 1, 0, 1), (0, 2, 0, 2), (0, 3, 2, 3), (0, 5, 1, 3), (1, 2, 0, 4), (1, 4, 4, 5),
    (1, 5, 1, 5), (2, 3, 2, 6), (2, 4, 4, 6), (3, 4, 6, 7), (3, 5, 3, 8), (3, 6, 7, 8),
    (4, 6, 5, 7), (5, 6, 5, 8)]

/-- Silhouette neighbours of `v` under `pat` (increasing for the smallest vertex of the cycle). -/
def h29g_nb (pat : Fin 9 → Bool) (v : Fin 7) : List (Fin 7) :=
  h29g_E.filterMap fun e =>
    if pat e.2.2.1 != pat e.2.2.2 then
      (if e.1 = v then some e.2.1 else if e.2.1 = v then some e.1 else none)
    else none

/-- Walk the silhouette from `c` (coming from `p`) until the start `s`. -/
def h29g_walk (pat : Fin 9 → Bool) (s : Fin 7) : ℕ → Fin 7 → Fin 7 → List (Fin 7)
  | 0, _, _ => []
  | n + 1, p, c =>
    if c = s then [] else c :: h29g_walk pat s n c (((h29g_nb pat c).filter (· ≠ p)).headD c)

/-- The silhouette cycle of `pat`, canonical (from the smallest vertex, smaller neighbour first). -/
def h29g_cyc (pat : Fin 9 → Bool) : List (Fin 7) :=
  match (List.finRange 7).find? (fun v => !(h29g_nb pat v).isEmpty) with
  | none => []
  | some s => s :: h29g_walk pat s 7 s ((h29g_nb pat s).headD s)

/-- Cycle length (at least 3, so `ZMod` is finite; shorter lists fail `Good` by injectivity). -/
def h29g_k (pat : Fin 9 → Bool) : ℕ := (h29g_cyc pat).length - 3 + 3

instance (pat : Fin 9 → Bool) : NeZero (h29g_k pat) := ⟨by unfold h29g_k; omega⟩

/-- The computed cycle as a map `ZMod k → Fin 7`. -/
def h29g_c (pat : Fin 9 → Bool) (a : ZMod (h29g_k pat)) : Fin 7 := (h29g_cyc pat).getD a.val 0

/-- Generic segment leaf: view `x j - x i`, pattern `pat`, computed cycle. -/
def h29g_seg (i j : Fin 7) (pat : Fin 9 → Bool) : S0xSeg 7 9 (h29g_k pat) :=
  ⟨i, j, pat, h29g_c pat⟩

/-- Generic line leaf: view `N_X × N_Y`, pattern `pat`, computed cycle. -/
def h29g_lin (X Y : Fin 9) (pat : Fin 9 → Bool) : S0xLin 7 9 (h29g_k pat) :=
  ⟨X, Y, pat, h29g_c pat⟩

variable {x : Fin 7 → ℝ³}

/-- A segment-view cell applies. -/
def H29GSegLeaf (T : Facets29 x) (i j : Fin 7) (pat : Fin 9 → Bool) : Prop :=
  (h29g_seg i j pat).Good s0x_S29 ∧ (h29g_seg i j pat).Cond (s0x_fac29 T)

/-- A line-view cell applies. -/
def H29GLinLeaf (T : Facets29 x) (X Y : Fin 9) (pat : Fin 9 → Bool) : Prop :=
  (h29g_lin X Y pat).Good s0x_S29 ∧ (h29g_lin X Y pat).Cond (s0x_fac29 T)

/-- **The residual**: no generic silhouette cell applies, at any segment or facet-pair line view. -/
def H29GenResid (T : Facets29 x) : Prop :=
  (∀ i j pat, ¬ H29GSegLeaf T i j pat) ∧ (∀ X Y pat, ¬ H29GLinLeaf T X Y pat)

theorem h29g_seg_isRupert (T : Facets29 x) {i j : Fin 7} {pat : Fin 9 → Bool}
    (h : H29GSegLeaf T i j pat) : IsRupert (univ.image x) :=
  s0x_seg_rupert (s0x_fac29 T) T.inj _ h.1 h.2

theorem h29g_lin_isRupert (T : Facets29 x) {X Y : Fin 9} {pat : Fin 9 → Bool}
    (h : H29GLinLeaf T X Y pat) : IsRupert (univ.image x) :=
  s0x_lin_rupert (s0x_fac29 T) T.inj _ h.1 h.2

theorem h29g_rule_isRupert (T : Facets29 x) (h : ¬ H29GenResid T) : IsRupert (univ.image x) := by
  unfold H29GenResid at h
  by_cases hs : ∀ i j pat, ¬ H29GSegLeaf T i j pat
  · have hl : ¬ ∀ X Y pat, ¬ H29GLinLeaf T X Y pat := fun hl => h ⟨hs, hl⟩
    push_neg at hl
    obtain ⟨X, Y, pat, hl⟩ := hl
    exact h29g_lin_isRupert T hl
  · push_neg at hs
    obtain ⟨i, j, pat, hs⟩ := hs
    exact h29g_seg_isRupert T hs

/-- **Type 29 generic silhouette rule**: a nopert realizing type 29 lies in the residual. -/
theorem h29g_rule_false (hN : IsNopert (Finset.univ.image x)) (T : Facets29 x)
    (h : ¬ H29GenResid T) : False :=
  hN.2 (h29g_rule_isRupert T h)

/-- Transport of `RobUni` from an explicit cycle to the computed one. -/
theorem h29g_robUni_tr (pat : Fin 9 → Bool) {k : ℕ} (hk : h29g_k pat = k) (c : ZMod k → Fin 7)
    (hc : ∀ a : ZMod k, c a = (h29g_cyc pat).getD a.val 0) (u : ℝ³)
    (h : RobUni (fun a : ZMod k => ⟪x (c a), u⟫)) :
    RobUni (fun a : ZMod (h29g_k pat) => ⟪x (h29g_c pat a), u⟫) := by
  subst hk
  have : c = h29g_c pat := funext hc
  subst this
  exact h

end H29S
end Minimality
