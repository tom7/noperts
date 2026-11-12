module

public import Minimality.Type24SAT.K24.LratMpmpp

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT.K29
namespace Minimality.H24.SAT.K24
def MpmppC0 : List Step := MpmppS0 ++ MpmppS1 ++ MpmppS2 ++ MpmppS3
def MpmppC1 : List Step := MpmppS4 ++ MpmppS5 ++ MpmppS6 ++ MpmppS7
def MpmppC2 : List Step := MpmppS8 ++ MpmppS9 ++ MpmppS10 ++ MpmppS11
def MpmppC3 : List Step := MpmppS12
theorem Mpmppok0 : chkChunk 15 MpmppCnf ([]) MpmppC0 = true := by decide +kernel
theorem Mpmppok1 : chkChunk 15 MpmppCnf (MpmppC0) MpmppC1 = true := by decide +kernel
theorem Mpmppok2 : chkChunk 15 MpmppCnf (MpmppC0 ++ MpmppC1) MpmppC2 = true := by decide +kernel
theorem Mpmppok3 : chkChunk 15 MpmppCnf (MpmppC0 ++ MpmppC1 ++ MpmppC2) MpmppC3 = true := by decide +kernel
theorem Mpmppfinal : OKs 15 MpmppCnf [] [MpmppC0,MpmppC1,MpmppC2,MpmppC3] :=
  ⟨Mpmppok0, ⟨Mpmppok1, ⟨Mpmppok2, ⟨Mpmppok3, trivial⟩⟩⟩⟩
theorem Mpmppempty : [MpmppC0,MpmppC1,MpmppC2,MpmppC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Mpmppunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ MpmppCnf, SatCl ρ c := chunks_sound 15 MpmppCnf _ Mpmppfinal Mpmppempty
end Minimality.H24.SAT.K24
