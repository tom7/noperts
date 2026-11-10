module

public import Minimality.Type16SAT.TriDataX
public import Minimality.Type16SAT.TriSound

@[expose] public section

/-!
# The extra routes of the triple table are sound (generated)
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped RealInnerProductSpace
open Classical
open Minimality.H29.SAT

namespace Minimality.H16.SAT

/-- **Every extra route gives the three valued sign of its determinant.** -/
theorem triRoutesX_sound {g : Geo} (hF : FacOK g) (hO : OriOK g) :
    ∀ k ∈ triRoutesX, Sg3 (rho g) k.2.ent (det3 (g.dv k.1.1) (g.dv k.1.2.1) (g.dv k.1.2.2)) := by
  unfold triRoutesX
  simp (config := {maxSteps := 100000000}) only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact b4_key3 hF hO _ _ _ 5 1 4 5 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by ent_ring)  -- B4
  · exact at_key3 _ _ _ (V.lv 0 1 5 3 6) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact at_key3 _ _ _ (V.lv 0 1 6 3 5) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact b4_key3 hF hO _ _ _ 0 0 2 5 1 (-1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by ent_ring)  -- B4
  · exact fac_key3 hF hO _ _ _ 0 2 4 12 2 _ (by decide)  -- FAC
  · exact at_key3 _ _ _ (V.lv 0 3 4 1 5) (-1) (by simp [rho]) (by ent_ring)  -- AT
  · exact at_key3 _ _ _ (V.mv 3 13 17) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact fac_key3 hF hO _ _ _ 1 9 17 4 0 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 1 10 20 4 0 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 7 12 18 4 0 _ (by decide)  -- FAC
  · exact at_key3 _ _ _ (V.lv 1 2 5 0 6) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact at_key3 _ _ _ (V.lv 1 2 5 0 6) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact entry_zero (rho_proper g) (by ent_ring)  -- ZC
  · exact fac_key3 hF hO _ _ _ 1 9 17 6 0 _ (by decide)  -- FAC
  · exact entry_zero (rho_proper g) (by ent_ring)  -- ZC
  · exact at_key3 _ _ _ (V.lv 1 2 5 3 6) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact at_key3 _ _ _ (V.lv 1 2 6 3 5) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact fac_key3 hF hO _ _ _ 1 9 10 14 2 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 1 9 17 11 1 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 1 9 17 12 1 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 1 9 17 13 1 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 5 9 18 15 1 _ (by decide)  -- FAC
  · exact at_key3 _ _ _ (V.lv 3 4 6 1 5) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact fac_key3 hF hO _ _ _ 1 9 20 15 1 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 1 9 17 18 2 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 1 9 17 19 2 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 1 10 20 13 1 _ (by decide)  -- FAC
  · exact at_key3 _ _ _ (V.lv 3 4 5 1 6) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact fac_key3 hF hO _ _ _ 1 10 20 15 1 _ (by decide)  -- FAC

end Minimality.H16.SAT
