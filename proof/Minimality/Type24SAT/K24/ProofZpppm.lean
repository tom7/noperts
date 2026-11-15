module

public import Minimality.Type24SAT.K24.LratZpppm

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT.K29
namespace Minimality.H24.SAT.K24
def ZpppmC0 : List Step := ZpppmS0 ++ ZpppmS1 ++ ZpppmS2 ++ ZpppmS3
def ZpppmC1 : List Step := ZpppmS4 ++ ZpppmS5 ++ ZpppmS6 ++ ZpppmS7
theorem Zpppmok0 : chkChunk 15 ZpppmCnf ([]) ZpppmC0 = true := by decide +kernel
theorem Zpppmok1 : chkChunk 15 ZpppmCnf (ZpppmC0) ZpppmC1 = true := by decide +kernel
theorem Zpppmfinal : OKs 15 ZpppmCnf [] [ZpppmC0,ZpppmC1] :=
  ⟨Zpppmok0, ⟨Zpppmok1, trivial⟩⟩
theorem Zpppmempty : [ZpppmC0,ZpppmC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Zpppmunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZpppmCnf, SatCl ρ c := chunks_sound 15 ZpppmCnf _ Zpppmfinal Zpppmempty
end Minimality.H24.SAT.K24
