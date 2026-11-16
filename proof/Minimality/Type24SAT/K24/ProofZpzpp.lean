module

public import Minimality.Type24SAT.K24.LratZpzpp

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.Lrat
def ZpzppC0 : List Step := ZpzppS0 ++ ZpzppS1 ++ ZpzppS2 ++ ZpzppS3
def ZpzppC1 : List Step := ZpzppS4 ++ ZpzppS5
theorem Zpzppok0 : chkChunk 15 ZpzppCnf ([]) ZpzppC0 = true := by decide +kernel
theorem Zpzppok1 : chkChunk 15 ZpzppCnf (ZpzppC0) ZpzppC1 = true := by decide +kernel
theorem Zpzppfinal : OKs 15 ZpzppCnf [] [ZpzppC0,ZpzppC1] :=
  ⟨Zpzppok0, ⟨Zpzppok1, trivial⟩⟩
theorem Zpzppempty : [ZpzppC0,ZpzppC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Zpzppunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZpzppCnf, SatCl ρ c := chunks_sound 15 ZpzppCnf _ Zpzppfinal Zpzppempty
end Minimality.H24.SAT.Lrat
