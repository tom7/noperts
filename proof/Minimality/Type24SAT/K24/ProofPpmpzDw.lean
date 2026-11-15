module

public import Minimality.Type24SAT.K24.LratPpmpzDw

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.K24
def PpmpzDwC0 : List Step := PpmpzDwS0 ++ PpmpzDwS1 ++ PpmpzDwS2 ++ PpmpzDwS3
def PpmpzDwC1 : List Step := PpmpzDwS4 ++ PpmpzDwS5 ++ PpmpzDwS6 ++ PpmpzDwS7
def PpmpzDwC2 : List Step := PpmpzDwS8 ++ PpmpzDwS9 ++ PpmpzDwS10
theorem PpmpzDwok0 : chkChunk 15 PpmpzDwCnf ([]) PpmpzDwC0 = true := by decide +kernel
theorem PpmpzDwok1 : chkChunk 15 PpmpzDwCnf (PpmpzDwC0) PpmpzDwC1 = true := by decide +kernel
theorem PpmpzDwok2 : chkChunk 15 PpmpzDwCnf (PpmpzDwC0 ++ PpmpzDwC1) PpmpzDwC2 = true := by decide +kernel
theorem PpmpzDwfinal : OKs 15 PpmpzDwCnf [] [PpmpzDwC0,PpmpzDwC1,PpmpzDwC2] :=
  ⟨PpmpzDwok0, ⟨PpmpzDwok1, ⟨PpmpzDwok2, trivial⟩⟩⟩
theorem PpmpzDwempty : [PpmpzDwC0,PpmpzDwC1,PpmpzDwC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PpmpzDwunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PpmpzDwCnf, SatCl ρ c := chunks_sound 15 PpmpzDwCnf _ PpmpzDwfinal PpmpzDwempty
end Minimality.H24.SAT.K24
