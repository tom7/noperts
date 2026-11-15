module

public import Minimality.Type24SAT.K24.LratMpzpp

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT.K29
namespace Minimality.H24.SAT.K24
def MpzppC0 : List Step := MpzppS0 ++ MpzppS1 ++ MpzppS2 ++ MpzppS3
def MpzppC1 : List Step := MpzppS4 ++ MpzppS5 ++ MpzppS6 ++ MpzppS7
def MpzppC2 : List Step := MpzppS8 ++ MpzppS9 ++ MpzppS10 ++ MpzppS11
theorem Mpzppok0 : chkChunk 15 MpzppCnf ([]) MpzppC0 = true := by decide +kernel
theorem Mpzppok1 : chkChunk 15 MpzppCnf (MpzppC0) MpzppC1 = true := by decide +kernel
theorem Mpzppok2 : chkChunk 15 MpzppCnf (MpzppC0 ++ MpzppC1) MpzppC2 = true := by decide +kernel
theorem Mpzppfinal : OKs 15 MpzppCnf [] [MpzppC0,MpzppC1,MpzppC2] :=
  ⟨Mpzppok0, ⟨Mpzppok1, ⟨Mpzppok2, trivial⟩⟩⟩
theorem Mpzppempty : [MpzppC0,MpzppC1,MpzppC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Mpzppunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ MpzppCnf, SatCl ρ c := chunks_sound 15 MpzppCnf _ Mpzppfinal Mpzppempty
end Minimality.H24.SAT.K24
