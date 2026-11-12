module

public import Minimality.Type24SAT.Geo.TriSound
public import Minimality.Type24SAT.Geo.NlSound

@[expose] public section

/-!
# Type 24 stack: the tables of the encoder, three valued, and `EntOK`

`tab3` has `tri`, `nl` looked up from the routes and `fup = fup3`.  It tells the truth on the keys of the lists
(`triRoutes`: all 1330 triples of edges; `nlRoutes`: all 84 triples of facets) and on every pair of points of the shape.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Classical
open Minimality.H29.SAT

namespace Minimality.H24.SAT

/-- The key `(a, b, c)` is in a table. -/
def hasKey3 {α : Type} (L : List ((Nat × Nat × Nat) × α)) (a b c : Nat) : Bool :=
  (L.find? fun r => r.1 == (a, b, c)).isSome

/-- The triple table: the entry of the route with this key (zero off the keys). -/
def triOf (a b c : Nat) : S3 :=
  ((triRoutes.find? fun r => r.1 == (a, b, c)).map fun r => r.2.ent).getD zeroS

/-- The normal table. -/
def nlOf (a b c : Nat) : S3 :=
  ((nlRoutes.find? fun r => r.1 == (a, b, c)).map fun r => r.2.ent r.1).getD zeroS

/-- The tables of the encoder. -/
def tab3 : Tab := ⟨triOf, nlOf, fup3⟩

/-- **The tables tell the truth** for a shape with `FacOK` and `OriOK`, on the keys of the lists. -/
theorem entOK_tab3 {g : Geo} (hF : FacOK g) (hO : OriOK g) :
    EntOK tab3 g (fun a b c => hasKey3 triRoutes a b c = true) (fun a b c => hasKey3 nlRoutes a b c = true)
      (fun t p q => p < 7 ∧ q < 7) where
  ent a b c h := by
    unfold hasKey3 at h
    cases hf : triRoutes.find? fun r => r.1 == (a, b, c) with
    | none => simp [hf] at h
    | some r =>
      have hk : r.1 = (a, b, c) := by simpa using List.find?_some hf
      have S := triRoutes_sound hF hO r (List.mem_of_find?_eq_some hf)
      rw [hk] at S
      show Sg3 _ (triOf a b c) _
      simpa [triOf, hf] using S
  nl a b c h := by
    unfold hasKey3 at h
    cases hf : nlRoutes.find? fun r => r.1 == (a, b, c) with
    | none => simp [hf] at h
    | some r =>
      have hk : r.1 = (a, b, c) := by simpa using List.find?_some hf
      have S := nlRoutes_sound hF hO r (List.mem_of_find?_eq_some hf)
      rw [hk] at S
      show Sg3 _ (nlOf a b c) _
      simp only [nlOf, hf, Option.map_some, Option.getD_some]
      rw [hk]; exact S
  fup t p q h := fup3_sound hF t p q h.1 h.2

end Minimality.H24.SAT
