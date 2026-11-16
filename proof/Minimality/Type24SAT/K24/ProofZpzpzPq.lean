module

public import Minimality.Type24SAT.K24.LratZpzpzPq

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.Lrat
def ZpzpzPqC0 : List Step := ZpzpzPqS0 ++ ZpzpzPqS1 ++ ZpzpzPqS2 ++ ZpzpzPqS3
def ZpzpzPqC1 : List Step := ZpzpzPqS4 ++ ZpzpzPqS5
theorem ZpzpzPqok0 : chkChunk 15 ZpzpzPqCnf ([]) ZpzpzPqC0 = true := by decide +kernel
theorem ZpzpzPqok1 : chkChunk 15 ZpzpzPqCnf (ZpzpzPqC0) ZpzpzPqC1 = true := by decide +kernel
theorem ZpzpzPqfinal : OKs 15 ZpzpzPqCnf [] [ZpzpzPqC0,ZpzpzPqC1] :=
  ⟨ZpzpzPqok0, ⟨ZpzpzPqok1, trivial⟩⟩
theorem ZpzpzPqempty : [ZpzpzPqC0,ZpzpzPqC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZpzpzPqunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZpzpzPqCnf, SatCl ρ c := chunks_sound 15 ZpzpzPqCnf _ ZpzpzPqfinal ZpzpzPqempty
end Minimality.H24.SAT.Lrat
