module

public import Minimality.Type24SAT.K24.LratPpzpm

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT.K29
namespace Minimality.H24.SAT.K24
def PpzpmC0 : List Step := PpzpmS0 ++ PpzpmS1 ++ PpzpmS2 ++ PpzpmS3
def PpzpmC1 : List Step := PpzpmS4 ++ PpzpmS5 ++ PpzpmS6 ++ PpzpmS7
def PpzpmC2 : List Step := PpzpmS8 ++ PpzpmS9 ++ PpzpmS10 ++ PpzpmS11
theorem Ppzpmok0 : chkChunk 15 PpzpmCnf ([]) PpzpmC0 = true := by decide +kernel
theorem Ppzpmok1 : chkChunk 15 PpzpmCnf (PpzpmC0) PpzpmC1 = true := by decide +kernel
theorem Ppzpmok2 : chkChunk 15 PpzpmCnf (PpzpmC0 ++ PpzpmC1) PpzpmC2 = true := by decide +kernel
theorem Ppzpmfinal : OKs 15 PpzpmCnf [] [PpzpmC0,PpzpmC1,PpzpmC2] :=
  ⟨Ppzpmok0, ⟨Ppzpmok1, ⟨Ppzpmok2, trivial⟩⟩⟩
theorem Ppzpmempty : [PpzpmC0,PpzpmC1,PpzpmC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Ppzpmunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PpzpmCnf, SatCl ρ c := chunks_sound 15 PpzpmCnf _ Ppzpmfinal Ppzpmempty
end Minimality.H24.SAT.K24
