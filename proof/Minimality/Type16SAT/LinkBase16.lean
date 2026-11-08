module

public import Minimality.Type29SAT.Checker
public import Minimality.Type16SAT.Dec

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# Type 16, link, shared part (J8): comparing the decoded rows with the checker's CNF chunk by chunk

Copy of `Type29SAT/LinkBase` over the type 16 decoder `Minimality.H16.SAT.decRow` (`digs 128`, so it is no longer the
type 29 `decRow`).  `cnfOfRows16 rows` is the checker's view of the packed rows.  `chkAt16 rows c o` says the decoded rows,
chunk by chunk, are consecutive slices of `c` starting at offset `o`; one `decide +kernel` per chunk keeps the kernel's cache small.
-/

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

/-- The CNF of a core as the checker sees it: the decoded rows (type 16 decoder), in order. -/
def cnfOfRows16 (rows : List (List Nat)) : List Cl :=
  rows.flatMap fun ch => ch.map fun n => (Minimality.H16.SAT.decRow n).2.2

/-- The chunks `rows` decode to consecutive slices of `c` from offset `o` on, and nothing is left. -/
def chkAt16 : List (List Nat) → List Cl → Nat → Prop
  | [], c, o => c.drop o = []
  | r :: rs, c, o => (c.drop o).take r.length = cnfOfRows16 [r] ∧ chkAt16 rs c (o + r.length)

theorem cnfOfRows16_of_chkAt : ∀ (rs : List (List Nat)) (c : List Cl) (o : Nat), chkAt16 rs c o →
    cnfOfRows16 rs = c.drop o
  | [], c, o, h => by simpa [cnfOfRows16] using h.symm
  | r :: rs, c, o, ⟨h1, h2⟩ => by
    have ih := cnfOfRows16_of_chkAt rs c (o + r.length) h2
    have e : cnfOfRows16 (r :: rs) = cnfOfRows16 [r] ++ cnfOfRows16 rs := by simp [cnfOfRows16]
    rw [e, ih, ← h1, show List.drop (o + r.length) c = (List.drop o c).drop r.length from (List.drop_drop ..).symm]
    exact List.take_append_drop _ _

end Minimality.H16K.SAT
