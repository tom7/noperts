module

public import Minimality.Type16SAT.TabX
public import Minimality.Type16SAT.TriSoundY

@[expose] public section

/-!
# The triple table with two lists of extra routes: `tab3Y`

`triRoutesY` (`TriDataY`) lists routes for triples that `triRoutes` and `triRoutesX` lack (the keys of the cores off `Z` and
off its `sigma16` image).  `tab3Y` looks a key up in `triRoutes`, then `triRoutesX`, then `triRoutesY`.  Nothing existing
changes.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Classical
open Minimality.H29.SAT

namespace Minimality.H16.SAT

/-- The triple table with both lists of extra routes (zero off the keys). -/
def triOfY (a b c : Nat) : S3 :=
  match triRoutes.find? fun r => r.1 == (a, b, c) with
  | some r => r.2.ent
  | none =>
    match triRoutesX.find? fun r => r.1 == (a, b, c) with
    | some r => r.2.ent
    | none => ((triRoutesY.find? fun r => r.1 == (a, b, c)).map fun r => r.2.ent).getD zeroS

/-- The tables of the encoder with both lists of extra routes. -/
def tab3Y : Tab := ⟨triOfY, nlOf, fup3⟩

/-- The key `(a, b, c)` is in `triRoutes`, `triRoutesX` or `triRoutesY`. -/
def hasKeyY (a b c : Nat) : Bool :=
  hasKey3 triRoutes a b c || hasKey3 triRoutesX a b c || hasKey3 triRoutesY a b c

/-- **The tables with both extensions tell the truth** on the keys of the three lists. -/
theorem entOK_tab3Y {g : Geo} (hF : FacOK g) (hO : OriOK g) :
    EntOK tab3Y g (fun a b c => hasKeyY a b c = true) (fun a b c => hasKey3 nlRoutes a b c = true)
      (fun _t p q => p < 7 ∧ q < 7) where
  ent a b c h := by
    unfold hasKeyY hasKey3 at h
    cases hf : triRoutes.find? fun r => r.1 == (a, b, c) with
    | some r =>
      have hk : r.1 = (a, b, c) := by simpa using List.find?_some hf
      have S := triRoutes_sound hF hO r (List.mem_of_find?_eq_some hf)
      rw [hk] at S
      show Sg3 _ (triOfY a b c) _
      simpa [triOfY, hf] using S
    | none =>
      cases hf2 : triRoutesX.find? fun r => r.1 == (a, b, c) with
      | some r =>
        have hk : r.1 = (a, b, c) := by simpa using List.find?_some hf2
        have S := triRoutesX_sound hF hO r (List.mem_of_find?_eq_some hf2)
        rw [hk] at S
        show Sg3 _ (triOfY a b c) _
        simpa [triOfY, hf, hf2] using S
      | none =>
        cases hf3 : triRoutesY.find? fun r => r.1 == (a, b, c) with
        | none => simp [hf, hf2, hf3] at h
        | some r =>
          have hk : r.1 = (a, b, c) := by simpa using List.find?_some hf3
          have S := triRoutesY_sound hF hO r (List.mem_of_find?_eq_some hf3)
          rw [hk] at S
          show Sg3 _ (triOfY a b c) _
          simpa [triOfY, hf, hf2, hf3] using S
  nl a b c h := (entOK_tab3 hF hO).nl a b c h
  fup _t p q h := (entOK_tab3 hF hO).fup _t p q h

end Minimality.H16.SAT
