module

public import Minimality.Type24SAT.K24.LratZpzpm

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.Lrat
def ZpzpmC0 : List Step := ZpzpmS0 ++ ZpzpmS1 ++ ZpzpmS2 ++ ZpzpmS3
def ZpzpmC1 : List Step := ZpzpmS4
theorem Zpzpmok0 : chkChunk 15 ZpzpmCnf ([]) ZpzpmC0 = true := by decide +kernel
theorem Zpzpmok1 : chkChunk 15 ZpzpmCnf (ZpzpmC0) ZpzpmC1 = true := by decide +kernel
theorem Zpzpmfinal : OKs 15 ZpzpmCnf [] [ZpzpmC0,ZpzpmC1] :=
  ⟨Zpzpmok0, ⟨Zpzpmok1, trivial⟩⟩
theorem Zpzpmempty : [ZpzpmC0,ZpzpmC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Zpzpmunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZpzpmCnf, SatCl ρ c := chunks_sound 15 ZpzpmCnf _ Zpzpmfinal Zpzpmempty
end Minimality.H24.SAT.Lrat
