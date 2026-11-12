module

public import Minimality.Type24SAT.K24.LratPpmpm

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT.K29
namespace Minimality.H24.SAT.K24
def PpmpmC0 : List Step := PpmpmS0 ++ PpmpmS1 ++ PpmpmS2 ++ PpmpmS3
def PpmpmC1 : List Step := PpmpmS4 ++ PpmpmS5 ++ PpmpmS6 ++ PpmpmS7
def PpmpmC2 : List Step := PpmpmS8
theorem Ppmpmok0 : chkChunk 15 PpmpmCnf ([]) PpmpmC0 = true := by decide +kernel
theorem Ppmpmok1 : chkChunk 15 PpmpmCnf (PpmpmC0) PpmpmC1 = true := by decide +kernel
theorem Ppmpmok2 : chkChunk 15 PpmpmCnf (PpmpmC0 ++ PpmpmC1) PpmpmC2 = true := by decide +kernel
theorem Ppmpmfinal : OKs 15 PpmpmCnf [] [PpmpmC0,PpmpmC1,PpmpmC2] :=
  ⟨Ppmpmok0, ⟨Ppmpmok1, ⟨Ppmpmok2, trivial⟩⟩⟩
theorem Ppmpmempty : [PpmpmC0,PpmpmC1,PpmpmC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Ppmpmunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PpmpmCnf, SatCl ρ c := chunks_sound 15 PpmpmCnf _ Ppmpmfinal Ppmpmempty
end Minimality.H24.SAT.K24
