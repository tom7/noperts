module

public import Minimality.Type20SilB

@[expose] public section


/-!
# H20S-C: the generic all-views route and the residual

One leaf for any view and facing pattern, with the silhouette cycle computed from the pattern:
* `h20s_cyc pat`: the silhouette edges of `pat` (polytope edges between an up and a down facet),
  walked from the smallest vertex towards its smaller neighbour (`sil.h`'s `canonCyc`).
* `h20s_seg i j pat` (view `x j - x i`) and `h20s_lin X Y pat` (view `N_X × N_Y`): the leaf specs.
* `H20SegLeaf F i j pat` / `H20LinLeaf F X Y pat`: `Good` (decidable) and `Cond` (literals, `RobUni`).
* `H20SilResid F`: no generic leaf applies, at any segment view, any facet-pair line view, any pattern.
* `h20s_rule_false`: a nopert realizing type 20 is in `H20SilResid (h20s_fac hR)`.
The metric cells of H20SB are instances (`h20s_notResid_*`).
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H20S
open Minimality.H21

/-- The 13 edges of type 20 with their two facets. -/
def h20s_E : List (Fin 7 × Fin 7 × Fin 8 × Fin 8) :=
  [(0, 1, 2, 4), (0, 2, 1, 5), (0, 5, 1, 2), (0, 6, 4, 5), (1, 3, 0, 2), (1, 4, 0, 6),
    (1, 6, 4, 6), (2, 5, 1, 7), (2, 6, 5, 7), (3, 4, 0, 3), (3, 5, 2, 3), (4, 5, 3, 7),
    (4, 6, 6, 7)]

/-- Silhouette neighbours of `v` under `pat` (increasing for the smallest vertex of the cycle). -/
def h20s_nb (pat : Fin 8 → Bool) (v : Fin 7) : List (Fin 7) :=
  h20s_E.filterMap fun e =>
    if pat e.2.2.1 != pat e.2.2.2 then
      (if e.1 = v then some e.2.1 else if e.2.1 = v then some e.1 else none)
    else none

/-- Walk the silhouette from `c` (coming from `p`) until the start `s`. -/
def h20s_walk (pat : Fin 8 → Bool) (s : Fin 7) : ℕ → Fin 7 → Fin 7 → List (Fin 7)
  | 0, _, _ => []
  | n + 1, p, c =>
    if c = s then [] else c :: h20s_walk pat s n c (((h20s_nb pat c).filter (· ≠ p)).headD c)

/-- The silhouette cycle of `pat`, canonical (from the smallest vertex, smaller neighbour first). -/
def h20s_cyc (pat : Fin 8 → Bool) : List (Fin 7) :=
  match (List.finRange 7).find? (fun v => !(h20s_nb pat v).isEmpty) with
  | none => []
  | some s => s :: h20s_walk pat s 7 s ((h20s_nb pat s).headD s)

/-- Cycle length (at least 3, so `ZMod` is finite; shorter lists fail `Good` by injectivity). -/
def h20s_k (pat : Fin 8 → Bool) : ℕ := (h20s_cyc pat).length - 3 + 3

instance (pat : Fin 8 → Bool) : NeZero (h20s_k pat) := ⟨by unfold h20s_k; omega⟩

/-- The computed cycle as a map `ZMod k → Fin 7`. -/
def h20s_c (pat : Fin 8 → Bool) (a : ZMod (h20s_k pat)) : Fin 7 := (h20s_cyc pat).getD a.val 0

/-- Generic segment leaf: view `x j - x i`, pattern `pat`, computed cycle. -/
def h20s_seg (i j : Fin 7) (pat : Fin 8 → Bool) : S0xSeg 7 8 (h20s_k pat) :=
  ⟨i, j, pat, h20s_c pat⟩

/-- Generic line leaf: view `N_X × N_Y`, pattern `pat`, computed cycle. -/
def h20s_lin (X Y : Fin 8) (pat : Fin 8 → Bool) : S0xLin 7 8 (h20s_k pat) :=
  ⟨X, Y, pat, h20s_c pat⟩

variable {x : Fin 7 → ℝ³}

/-- A segment-view cell applies. -/
def H20SegLeaf (F : S0xFac 8 h20s_S x) (i j : Fin 7) (pat : Fin 8 → Bool) : Prop :=
  (h20s_seg i j pat).Good h20s_S ∧ (h20s_seg i j pat).Cond F

/-- A line-view cell applies. -/
def H20LinLeaf (F : S0xFac 8 h20s_S x) (X Y : Fin 8) (pat : Fin 8 → Bool) : Prop :=
  (h20s_lin X Y pat).Good h20s_S ∧ (h20s_lin X Y pat).Cond F

/-- **The residual**: no silhouette cell applies, at any segment or facet-pair line view. -/
def H20SilResid (F : S0xFac 8 h20s_S x) : Prop :=
  (∀ i j pat, ¬ H20SegLeaf F i j pat) ∧ (∀ X Y pat, ¬ H20LinLeaf F X Y pat)

theorem h20s_seg_isRupert (F : S0xFac 8 h20s_S x) (hx : Function.Injective x) {i j : Fin 7}
    {pat : Fin 8 → Bool} (h : H20SegLeaf F i j pat) : IsRupert (univ.image x) :=
  s0x_seg_rupert F hx _ h.1 h.2

theorem h20s_lin_isRupert (F : S0xFac 8 h20s_S x) (hx : Function.Injective x) {X Y : Fin 8}
    {pat : Fin 8 → Bool} (h : H20LinLeaf F X Y pat) : IsRupert (univ.image x) :=
  s0x_lin_rupert F hx _ h.1 h.2

theorem h20s_rule_isRupert (F : S0xFac 8 h20s_S x) (hx : Function.Injective x)
    (h : ¬ H20SilResid F) : IsRupert (univ.image x) := by
  unfold H20SilResid at h
  by_cases hs : ∀ i j pat, ¬ H20SegLeaf F i j pat
  · have hl : ¬ ∀ X Y pat, ¬ H20LinLeaf F X Y pat := fun hl => h ⟨hs, hl⟩
    push_neg at hl
    obtain ⟨X, Y, pat, hl⟩ := hl
    exact h20s_lin_isRupert F hx hl
  · push_neg at hs
    obtain ⟨i, j, pat, hs⟩ := hs
    exact h20s_seg_isRupert F hx hs

/-- **Type 20 silhouette rule**: a nopert realizing type 20 lies in the residual. -/
theorem h20s_rule_false (hN : IsNopert (univ.image x)) (hx : Function.Injective x)
    (hR : RealizesFaces x (sevenTypeFaces 19)) (h : ¬ H20SilResid (h20s_fac hR)) : False :=
  hN.2 (h20s_rule_isRupert _ hx h)

/-! ### The metric cells (H20SB) are generic leaves -/

/-- Transport of `RobUni` from an explicit cycle to the computed one. -/
theorem h20s_robUni_tr (pat : Fin 8 → Bool) {k : ℕ} (hk : h20s_k pat = k) (c : ZMod k → Fin 7)
    (hc : ∀ a : ZMod k, c a = (h20s_cyc pat).getD a.val 0) (u : ℝ³)
    (h : RobUni (fun a : ZMod k => ⟪x (c a), u⟫)) :
    RobUni (fun a : ZMod (h20s_k pat) => ⟪x (h20s_c pat a), u⟫) := by
  subst hk
  have : c = h20s_c pat := funext hc
  subst this
  exact h

theorem h20s_notResid_LCG (F : S0xFac 8 h20s_S x) (hC : h20s_LCG.Cond F) : ¬ H20SilResid F :=
  fun h => h.2 2 6 h20s_LCG.pat
    ⟨by decide, hC.1, h20s_robUni_tr _ (by decide) h20s_LCG.c (by decide) _ hC.2⟩

theorem h20s_notResid_LCG' (F : S0xFac 8 h20s_S x) (hC : h20s_LCG'.Cond F) : ¬ H20SilResid F :=
  fun h => h.2 2 6 h20s_LCG'.pat
    ⟨by decide, hC.1, h20s_robUni_tr _ (by decide) h20s_LCG'.c (by decide) _ hC.2⟩

theorem h20s_notResid_s05 (F : S0xFac 8 h20s_S x) (hC : h20s_s05.Cond F) : ¬ H20SilResid F :=
  fun h => h.1 0 5 h20s_s05.pat
    ⟨by decide, hC.1, h20s_robUni_tr _ (by decide) h20s_s05.c (by decide) _ hC.2⟩

theorem h20s_notResid_s01 (F : S0xFac 8 h20s_S x) (hC : h20s_s01.Cond F) : ¬ H20SilResid F :=
  fun h => h.1 0 1 h20s_s01.pat
    ⟨by decide, hC.1, h20s_robUni_tr _ (by decide) h20s_s01.c (by decide) _ hC.2⟩

theorem h20s_notResid_s35 (F : S0xFac 8 h20s_S x) (hC : h20s_s35.Cond F) : ¬ H20SilResid F :=
  fun h => h.1 3 5 h20s_s35.pat
    ⟨by decide, hC.1, h20s_robUni_tr _ (by decide) h20s_s35.c (by decide) _ hC.2⟩

theorem h20s_notResid_LCF (F : S0xFac 8 h20s_S x) (hC : h20s_LCF.Cond F) : ¬ H20SilResid F :=
  fun h => h.2 2 5 h20s_LCF.pat
    ⟨by decide, hC.1, h20s_robUni_tr _ (by decide) h20s_LCF.c (by decide) _ hC.2⟩

theorem h20s_notResid_LCF' (F : S0xFac 8 h20s_S x) (hC : h20s_LCF'.Cond F) : ¬ H20SilResid F :=
  fun h => h.2 2 5 h20s_LCF'.pat
    ⟨by decide, hC.1, h20s_robUni_tr _ (by decide) h20s_LCF'.c (by decide) _ hC.2⟩

theorem h20s_notResid_LBD (F : S0xFac 8 h20s_S x) (hC : h20s_LBD.Cond F) : ¬ H20SilResid F :=
  fun h => h.2 1 3 h20s_LBD.pat
    ⟨by decide, hC.1, h20s_robUni_tr _ (by decide) h20s_LBD.c (by decide) _ hC.2⟩

theorem h20s_notResid_LBD' (F : S0xFac 8 h20s_S x) (hC : h20s_LBD'.Cond F) : ¬ H20SilResid F :=
  fun h => h.2 1 3 h20s_LBD'.pat
    ⟨by decide, hC.1, h20s_robUni_tr _ (by decide) h20s_LBD'.c (by decide) _ hC.2⟩

theorem h20s_notResid_LAF (F : S0xFac 8 h20s_S x) (hC : h20s_LAF.Cond F) : ¬ H20SilResid F :=
  fun h => h.2 0 5 h20s_LAF.pat
    ⟨by decide, hC.1, h20s_robUni_tr _ (by decide) h20s_LAF.c (by decide) _ hC.2⟩

theorem h20s_notResid_LAF' (F : S0xFac 8 h20s_S x) (hC : h20s_LAF'.Cond F) : ¬ H20SilResid F :=
  fun h => h.2 0 5 h20s_LAF'.pat
    ⟨by decide, hC.1, h20s_robUni_tr _ (by decide) h20s_LAF'.c (by decide) _ hC.2⟩

end H20S
end Minimality
