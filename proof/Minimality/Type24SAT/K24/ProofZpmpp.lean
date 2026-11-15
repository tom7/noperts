module

public import Minimality.Type24SAT.K24.LratZpmpp

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT.K29
namespace Minimality.H24.SAT.K24
def ZpmppC0 : List Step := ZpmppS0 ++ ZpmppS1 ++ ZpmppS2 ++ ZpmppS3
def ZpmppC1 : List Step := ZpmppS4 ++ ZpmppS5 ++ ZpmppS6 ++ ZpmppS7
def ZpmppC2 : List Step := ZpmppS8 ++ ZpmppS9 ++ ZpmppS10 ++ ZpmppS11
def ZpmppC3 : List Step := ZpmppS12 ++ ZpmppS13 ++ ZpmppS14
theorem Zpmppok0 : chkChunk 15 ZpmppCnf ([]) ZpmppC0 = true := by decide +kernel
theorem Zpmppok1 : chkChunk 15 ZpmppCnf (ZpmppC0) ZpmppC1 = true := by decide +kernel
theorem Zpmppok2 : chkChunk 15 ZpmppCnf (ZpmppC0 ++ ZpmppC1) ZpmppC2 = true := by decide +kernel
theorem Zpmppok3 : chkChunk 15 ZpmppCnf (ZpmppC0 ++ ZpmppC1 ++ ZpmppC2) ZpmppC3 = true := by decide +kernel
theorem Zpmppfinal : OKs 15 ZpmppCnf [] [ZpmppC0,ZpmppC1,ZpmppC2,ZpmppC3] :=
  ⟨Zpmppok0, ⟨Zpmppok1, ⟨Zpmppok2, ⟨Zpmppok3, trivial⟩⟩⟩⟩
theorem Zpmppempty : [ZpmppC0,ZpmppC1,ZpmppC2,ZpmppC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Zpmppunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZpmppCnf, SatCl ρ c := chunks_sound 15 ZpmppCnf _ Zpmppfinal Zpmppempty
end Minimality.H24.SAT.K24
