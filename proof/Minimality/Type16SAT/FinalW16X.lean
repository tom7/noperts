module

public import Minimality.Type16SAT.FinalW16
public import Minimality.Type16SAT.LinkPZMMU
public import Minimality.Type16SAT.LinkPZMMZ
public import Minimality.Type16SAT.LinkMZMMU
public import Minimality.Type16SAT.LinkMZMMZ

@[expose] public section

/-!
# Type 16: the one-zero vectors next to the open classes with the zero at `[0134]` or `[2346]`

* `+0+-`, `-0+-` and their `sigma16` images `--+0`, `+-+0`: not Rupert-closed by a core: they do not occur (`not_cls16Dead`, `GPDead16`).
* `+0--`, `-0--` and their images `---0`, `+--0`: as the walls of `FinalW16` (`r = 1` on `Z`), two case cores each
  (`PZMMU`/`PZMMZ`, `MZMMU`/`MZMMZ`) and the Slide Lemma at `r = 1`, off the residue `⟪x 0 - x 3, x 6 - x 3⟫ = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H16.SAT

open Minimality.H16K.SAT

/-- The eight vectors of this module. -/
def Cls16WallX (x : Fin 7 → ℝ³) : Prop :=
  Vec16 1 0 1 (-1) x ∨ Vec16 (-1) (-1) 1 0 x ∨ Vec16 (-1) 0 1 (-1) x ∨ Vec16 1 (-1) 1 0 x ∨
  Vec16 1 0 (-1) (-1) x ∨ Vec16 (-1) (-1) (-1) 0 x ∨ Vec16 (-1) 0 (-1) (-1) x ∨ Vec16 1 (-1) (-1) 0 x

end Minimality.H16.SAT
