module

public import Minimality.Type16SAT.TriSoundX
public import Minimality.Type16SAT.Tabs

@[expose] public section

/-!
# The triple table with the extra routes: `tab3X`, and `EntOK` on the keys of both route lists

`triRoutesX` (`TriDataX`) lists routes for triples that `triRoutes` lacks.  The table `tab3X` looks a key up in `triRoutes`
first, then in `triRoutesX`.  It serves the family 13 rows (`row4OKX`) of cores that need more triple keys than the first
twelve cores; the existing table and its soundness are untouched.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Classical
open Minimality.H29.SAT

namespace Minimality.H16.SAT

/-- The triple table with the extra routes (zero off the keys). -/
def triOfX (a b c : Nat) : S3 :=
  match triRoutes.find? fun r => r.1 == (a, b, c) with
  | some r => r.2.ent
  | none => ((triRoutesX.find? fun r => r.1 == (a, b, c)).map fun r => r.2.ent).getD zeroS

/-- The tables of the encoder with the extra routes. -/
def tab3X : Tab := ⟨triOfX, nlOf, fup3⟩

/-- The key `(a, b, c)` is in `triRoutes` or in `triRoutesX`. -/
def hasKeyX (a b c : Nat) : Bool := hasKey3 triRoutes a b c || hasKey3 triRoutesX a b c

/-- **The extended tables tell the truth** on the keys of both lists. -/
theorem entOK_tab3X {g : Geo} (hF : FacOK g) (hO : OriOK g) :
    EntOK tab3X g (fun a b c => hasKeyX a b c = true) (fun a b c => hasKey3 nlRoutes a b c = true)
      (fun t p q => p < 7 ∧ q < 7) where
  ent a b c h := by
    unfold hasKeyX hasKey3 at h
    cases hf : triRoutes.find? fun r => r.1 == (a, b, c) with
    | some r =>
      have hk : r.1 = (a, b, c) := by simpa using List.find?_some hf
      have S := triRoutes_sound hF hO r (List.mem_of_find?_eq_some hf)
      rw [hk] at S
      show Sg3 _ (triOfX a b c) _
      simpa [triOfX, hf] using S
    | none =>
      cases hf2 : triRoutesX.find? fun r => r.1 == (a, b, c) with
      | none => simp [hf, hf2] at h
      | some r =>
        have hk : r.1 = (a, b, c) := by simpa using List.find?_some hf2
        have S := triRoutesX_sound hF hO r (List.mem_of_find?_eq_some hf2)
        rw [hk] at S
        show Sg3 _ (triOfX a b c) _
        simpa [triOfX, hf, hf2] using S
  nl a b c h := (entOK_tab3 hF hO).nl a b c h
  fup _t p q h := (entOK_tab3 hF hO).fup _t p q h

end Minimality.H16.SAT
