module

public import Minimality.Type24SAT.K24.LratZpmpm

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.K24
def ZpmpmC0 : List Step := ZpmpmS0 ++ ZpmpmS1 ++ ZpmpmS2 ++ ZpmpmS3
def ZpmpmC1 : List Step := ZpmpmS4 ++ ZpmpmS5 ++ ZpmpmS6 ++ ZpmpmS7
def ZpmpmC2 : List Step := ZpmpmS8 ++ ZpmpmS9 ++ ZpmpmS10
theorem Zpmpmok0 : chkChunk 15 ZpmpmCnf ([]) ZpmpmC0 = true := by decide +kernel
theorem Zpmpmok1 : chkChunk 15 ZpmpmCnf (ZpmpmC0) ZpmpmC1 = true := by decide +kernel
theorem Zpmpmok2 : chkChunk 15 ZpmpmCnf (ZpmpmC0 ++ ZpmpmC1) ZpmpmC2 = true := by decide +kernel
theorem Zpmpmfinal : OKs 15 ZpmpmCnf [] [ZpmpmC0,ZpmpmC1,ZpmpmC2] :=
  ⟨Zpmpmok0, ⟨Zpmpmok1, ⟨Zpmpmok2, trivial⟩⟩⟩
theorem Zpmpmempty : [ZpmpmC0,ZpmpmC1,ZpmpmC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Zpmpmunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZpmpmCnf, SatCl ρ c := chunks_sound 15 ZpmpmCnf _ Zpmpmfinal Zpmpmempty
end Minimality.H24.SAT.K24
