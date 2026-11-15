module

public import Minimality.Type24SAT.K24.LratZpppzPq

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.K24
def ZpppzPqC0 : List Step := ZpppzPqS0 ++ ZpppzPqS1 ++ ZpppzPqS2 ++ ZpppzPqS3
def ZpppzPqC1 : List Step := ZpppzPqS4 ++ ZpppzPqS5 ++ ZpppzPqS6 ++ ZpppzPqS7
theorem ZpppzPqok0 : chkChunk 15 ZpppzPqCnf ([]) ZpppzPqC0 = true := by decide +kernel
theorem ZpppzPqok1 : chkChunk 15 ZpppzPqCnf (ZpppzPqC0) ZpppzPqC1 = true := by decide +kernel
theorem ZpppzPqfinal : OKs 15 ZpppzPqCnf [] [ZpppzPqC0,ZpppzPqC1] :=
  ⟨ZpppzPqok0, ⟨ZpppzPqok1, trivial⟩⟩
theorem ZpppzPqempty : [ZpppzPqC0,ZpppzPqC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZpppzPqunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZpppzPqCnf, SatCl ρ c := chunks_sound 15 ZpppzPqCnf _ ZpppzPqfinal ZpppzPqempty
end Minimality.H24.SAT.K24
