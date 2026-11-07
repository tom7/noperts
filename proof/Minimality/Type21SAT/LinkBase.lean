module

public import Minimality.Type21SAT.Checker
public import Minimality.Type21SAT.RowA

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# Link, shared part: comparing the decoded rows with the checker's CNF chunk by chunk

`cnfOfRows rows` is the checker's view of the packed rows.  `chkAt rows c o` says the decoded rows, chunk by chunk,
are consecutive slices of `c` starting at offset `o`; one `decide +kernel` per chunk keeps the kernel's cache small.
-/

namespace Minimality.H21.SAT.K3

open Minimality.H21.SAT

/-- The CNF of a core as the checker sees it: the decoded rows, in order. -/
def cnfOfRows (rows : List (List Nat)) : List Cl := rows.flatMap fun ch => ch.map fun n => (decRow n).2.2

/-- The chunks `rows` decode to consecutive slices of `c` from offset `o` on, and nothing is left. -/
def chkAt : List (List Nat) → List Cl → Nat → Prop
  | [], c, o => c.drop o = []
  | r :: rs, c, o => (c.drop o).take r.length = cnfOfRows [r] ∧ chkAt rs c (o + r.length)

theorem cnfOfRows_of_chkAt : ∀ (rs : List (List Nat)) (c : List Cl) (o : Nat), chkAt rs c o →
    cnfOfRows rs = c.drop o
  | [], c, o, h => by simpa [cnfOfRows] using h.symm
  | r :: rs, c, o, ⟨h1, h2⟩ => by
    have ih := cnfOfRows_of_chkAt rs c (o + r.length) h2
    have e : cnfOfRows (r :: rs) = cnfOfRows [r] ++ cnfOfRows rs := by simp [cnfOfRows]
    rw [e, ih, ← h1, show List.drop (o + r.length) c = (List.drop o c).drop r.length from (List.drop_drop ..).symm]
    exact List.take_append_drop _ _

end Minimality.H21.SAT.K3
