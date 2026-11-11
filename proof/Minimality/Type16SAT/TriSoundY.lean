module

public import Minimality.Type16SAT.TriDataY
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
theorem triRoutesY_sound {g : Geo} (hF : FacOK g) (hO : OriOK g) :
    ∀ k ∈ triRoutesY, Sg3 (rho g) k.2.ent (det3 (g.dv k.1.1) (g.dv k.1.2.1) (g.dv k.1.2.2)) := by
  unfold triRoutesY
  simp (config := {maxSteps := 100000000}) only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact entry_zero (rho_proper g) (by ent_ring)  -- ZC
  · exact at_key3 _ _ _ (V.br 0 1 2 6) (-1) (by simp [rho]) (by ent_ring)  -- AT
  · exact b4_key3 hF hO _ _ _ 1 1 5 6 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by ent_ring)  -- B4
  · exact b4_key3 hF hO _ _ _ 0 0 2 5 1 (-1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by ent_ring)  -- B4
  · exact at_key3 _ _ _ (V.lv 0 1 2 3 5) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact at_key3 _ _ _ (V.lv 0 1 3 2 5) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact at_key3 _ _ _ (V.mv 0 14 16) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact at_key3 _ _ _ (V.lv 0 1 2 3 6) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact at_key3 _ _ _ (V.lv 1 3 4 0 2) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact at_key3 _ _ _ (V.lv 1 3 4 0 2) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact fac_key3 hF hO _ _ _ 0 1 11 19 2 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 1 17 20 1 0 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 0 2 4 10 2 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 0 2 13 6 1 _ (by decide)  -- FAC
  · exact at_key3 _ _ _ (V.mv 2 9 12) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact at_key3 _ _ _ (V.lv 2 5 6 0 3) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact fac_key3 hF hO _ _ _ 1 17 20 2 0 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 0 4 11 3 0 _ (by decide)  -- FAC
  · exact at_key3 _ _ _ (V.lv 1 2 3 0 4) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact at_key3 _ _ _ (V.lv 1 2 3 0 4) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact at_key3 _ _ _ (V.mv 3 7 13) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact at_key3 _ _ _ (V.lv 0 3 4 1 5) (-1) (by simp [rho]) (by ent_ring)  -- AT
  · exact at_key3 _ _ _ (V.lv 0 5 6 1 4) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact fac_key3 hF hO _ _ _ 4 5 19 4 0 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 6 8 19 4 0 _ (by decide)  -- FAC
  · exact at_key3 _ _ _ (V.lv 0 1 5 4 6) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact fac_key3 hF hO _ _ _ 6 10 19 4 0 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 0 4 11 12 2 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 0 4 11 18 2 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 0 4 16 15 1 _ (by decide)  -- FAC
  · exact b4_key3 hF hO _ _ _ 0 0 3 5 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by ent_ring)  -- B4
  · exact b4_key3 hF hO _ _ _ 4 0 4 6 5 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by ent_ring)  -- B4
  · exact b4_key3 hF hO _ _ _ 4 0 4 6 5 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by ent_ring)  -- B4
  · exact at_key3 _ _ _ (V.lv 1 2 5 0 6) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact at_key3 _ _ _ (V.lv 0 1 6 2 5) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact at_key3 _ _ _ (V.br 1 2 3 4) (-1) (by simp [rho]) (by ent_ring)  -- AT
  · exact at_key3 _ _ _ (V.lv 1 2 4 3 6) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact at_key3 _ _ _ (V.lv 3 4 5 1 2) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact at_key3 _ _ _ (V.lv 3 4 5 1 2) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact at_key3 _ _ _ (V.lv 2 5 6 1 3) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact fac_key3 hF hO _ _ _ 0 13 16 7 0 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 7 13 18 7 0 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 1 7 17 14 1 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 1 7 17 18 2 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 1 7 20 18 1 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 0 11 13 9 0 _ (by decide)  -- FAC
  · exact at_key3 _ _ _ (V.lv 2 3 4 1 5) 1 (by simp [rho]) (by ent_ring)  -- AT
  · exact zq_key3 hF _ _ _ 1 (by decide) (by decide)  -- ZQ
  · exact fac_key3 hF hO _ _ _ 1 9 20 19 1 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 0 11 16 10 0 _ (by decide)  -- FAC
  · exact fac_key3 hF hO _ _ _ 1 10 20 11 1 _ (by decide)  -- FAC
  · exact b4_key3 hF hO _ _ _ 0 2 3 5 6 (-1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by ent_ring)  -- B4
  · exact fac_key3 hF hO _ _ _ 0 11 16 19 2 _ (by decide)  -- FAC
  · exact at_key3 _ _ _ (V.lv 2 4 6 3 5) (-1) (by simp [rho]) (by ent_ring)  -- AT
  · exact b4_key3 hF hO _ _ _ 7 2 4 5 6 (-1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by ent_ring)  -- B4

end Minimality.H16.SAT
