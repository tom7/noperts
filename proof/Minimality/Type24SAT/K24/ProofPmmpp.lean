module

public import Minimality.Type24SAT.K24.LratPmmpp

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT.K29
namespace Minimality.H24.SAT.K24
def PmmppC0 : List Step := PmmppS0 ++ PmmppS1 ++ PmmppS2 ++ PmmppS3
def PmmppC1 : List Step := PmmppS4 ++ PmmppS5 ++ PmmppS6 ++ PmmppS7
def PmmppC2 : List Step := PmmppS8 ++ PmmppS9
theorem Pmmppok0 : chkChunk 15 PmmppCnf ([]) PmmppC0 = true := by decide +kernel
theorem Pmmppok1 : chkChunk 15 PmmppCnf (PmmppC0) PmmppC1 = true := by decide +kernel
theorem Pmmppok2 : chkChunk 15 PmmppCnf (PmmppC0 ++ PmmppC1) PmmppC2 = true := by decide +kernel
theorem Pmmppfinal : OKs 15 PmmppCnf [] [PmmppC0,PmmppC1,PmmppC2] :=
  ⟨Pmmppok0, ⟨Pmmppok1, ⟨Pmmppok2, trivial⟩⟩⟩
theorem Pmmppempty : [PmmppC0,PmmppC1,PmmppC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Pmmppunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PmmppCnf, SatCl ρ c := chunks_sound 15 PmmppCnf _ Pmmppfinal Pmmppempty
end Minimality.H24.SAT.K24
