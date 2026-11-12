module

public import Minimality.Type24SAT.K24.LratPpppm

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT.K29
namespace Minimality.H24.SAT.K24
def PpppmC0 : List Step := PpppmS0 ++ PpppmS1 ++ PpppmS2 ++ PpppmS3
def PpppmC1 : List Step := PpppmS4 ++ PpppmS5 ++ PpppmS6 ++ PpppmS7
def PpppmC2 : List Step := PpppmS8 ++ PpppmS9
theorem Ppppmok0 : chkChunk 15 PpppmCnf ([]) PpppmC0 = true := by decide +kernel
theorem Ppppmok1 : chkChunk 15 PpppmCnf (PpppmC0) PpppmC1 = true := by decide +kernel
theorem Ppppmok2 : chkChunk 15 PpppmCnf (PpppmC0 ++ PpppmC1) PpppmC2 = true := by decide +kernel
theorem Ppppmfinal : OKs 15 PpppmCnf [] [PpppmC0,PpppmC1,PpppmC2] :=
  ⟨Ppppmok0, ⟨Ppppmok1, ⟨Ppppmok2, trivial⟩⟩⟩
theorem Ppppmempty : [PpppmC0,PpppmC1,PpppmC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Ppppmunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PpppmCnf, SatCl ρ c := chunks_sound 15 PpppmCnf _ Ppppmfinal Ppppmempty
end Minimality.H24.SAT.K24
