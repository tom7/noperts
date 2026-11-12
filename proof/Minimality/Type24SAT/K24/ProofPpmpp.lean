module

public import Minimality.Type24SAT.K24.LratPpmpp

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT.K29
namespace Minimality.H24.SAT.K24
def PpmppC0 : List Step := PpmppS0 ++ PpmppS1 ++ PpmppS2 ++ PpmppS3
def PpmppC1 : List Step := PpmppS4 ++ PpmppS5 ++ PpmppS6 ++ PpmppS7
def PpmppC2 : List Step := PpmppS8 ++ PpmppS9 ++ PpmppS10 ++ PpmppS11
def PpmppC3 : List Step := PpmppS12
theorem Ppmppok0 : chkChunk 15 PpmppCnf ([]) PpmppC0 = true := by decide +kernel
theorem Ppmppok1 : chkChunk 15 PpmppCnf (PpmppC0) PpmppC1 = true := by decide +kernel
theorem Ppmppok2 : chkChunk 15 PpmppCnf (PpmppC0 ++ PpmppC1) PpmppC2 = true := by decide +kernel
theorem Ppmppok3 : chkChunk 15 PpmppCnf (PpmppC0 ++ PpmppC1 ++ PpmppC2) PpmppC3 = true := by decide +kernel
theorem Ppmppfinal : OKs 15 PpmppCnf [] [PpmppC0,PpmppC1,PpmppC2,PpmppC3] :=
  ⟨Ppmppok0, ⟨Ppmppok1, ⟨Ppmppok2, ⟨Ppmppok3, trivial⟩⟩⟩⟩
theorem Ppmppempty : [PpmppC0,PpmppC1,PpmppC2,PpmppC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Ppmppunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PpmppCnf, SatCl ρ c := chunks_sound 15 PpmppCnf _ Ppmppfinal Ppmppempty
end Minimality.H24.SAT.K24
