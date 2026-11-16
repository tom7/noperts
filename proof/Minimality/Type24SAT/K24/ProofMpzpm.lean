module

public import Minimality.Type24SAT.K24.LratMpzpm

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.Lrat
def MpzpmC0 : List Step := MpzpmS0 ++ MpzpmS1 ++ MpzpmS2 ++ MpzpmS3
def MpzpmC1 : List Step := MpzpmS4 ++ MpzpmS5 ++ MpzpmS6 ++ MpzpmS7
def MpzpmC2 : List Step := MpzpmS8 ++ MpzpmS9 ++ MpzpmS10
theorem Mpzpmok0 : chkChunk 15 MpzpmCnf ([]) MpzpmC0 = true := by decide +kernel
theorem Mpzpmok1 : chkChunk 15 MpzpmCnf (MpzpmC0) MpzpmC1 = true := by decide +kernel
theorem Mpzpmok2 : chkChunk 15 MpzpmCnf (MpzpmC0 ++ MpzpmC1) MpzpmC2 = true := by decide +kernel
theorem Mpzpmfinal : OKs 15 MpzpmCnf [] [MpzpmC0,MpzpmC1,MpzpmC2] :=
  ⟨Mpzpmok0, ⟨Mpzpmok1, ⟨Mpzpmok2, trivial⟩⟩⟩
theorem Mpzpmempty : [MpzpmC0,MpzpmC1,MpzpmC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Mpzpmunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ MpzpmCnf, SatCl ρ c := chunks_sound 15 MpzpmCnf _ Mpzpmfinal Mpzpmempty
end Minimality.H24.SAT.Lrat
