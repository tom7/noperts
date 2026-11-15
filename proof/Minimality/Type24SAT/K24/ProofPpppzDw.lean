module

public import Minimality.Type24SAT.K24.LratPpppzDw

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.K24
def PpppzDwC0 : List Step := PpppzDwS0 ++ PpppzDwS1 ++ PpppzDwS2 ++ PpppzDwS3
def PpppzDwC1 : List Step := PpppzDwS4 ++ PpppzDwS5 ++ PpppzDwS6 ++ PpppzDwS7
def PpppzDwC2 : List Step := PpppzDwS8 ++ PpppzDwS9 ++ PpppzDwS10 ++ PpppzDwS11
theorem PpppzDwok0 : chkChunk 15 PpppzDwCnf ([]) PpppzDwC0 = true := by decide +kernel
theorem PpppzDwok1 : chkChunk 15 PpppzDwCnf (PpppzDwC0) PpppzDwC1 = true := by decide +kernel
theorem PpppzDwok2 : chkChunk 15 PpppzDwCnf (PpppzDwC0 ++ PpppzDwC1) PpppzDwC2 = true := by decide +kernel
theorem PpppzDwfinal : OKs 15 PpppzDwCnf [] [PpppzDwC0,PpppzDwC1,PpppzDwC2] :=
  ⟨PpppzDwok0, ⟨PpppzDwok1, ⟨PpppzDwok2, trivial⟩⟩⟩
theorem PpppzDwempty : [PpppzDwC0,PpppzDwC1,PpppzDwC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PpppzDwunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PpppzDwCnf, SatCl ρ c := chunks_sound 15 PpppzDwCnf _ PpppzDwfinal PpppzDwempty
end Minimality.H24.SAT.K24
