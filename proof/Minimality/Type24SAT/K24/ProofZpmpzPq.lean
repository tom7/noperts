module

public import Minimality.Type24SAT.K24.LratZpmpzPq

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.Lrat
def ZpmpzPqC0 : List Step := ZpmpzPqS0 ++ ZpmpzPqS1 ++ ZpmpzPqS2 ++ ZpmpzPqS3
def ZpmpzPqC1 : List Step := ZpmpzPqS4 ++ ZpmpzPqS5 ++ ZpmpzPqS6 ++ ZpmpzPqS7
theorem ZpmpzPqok0 : chkChunk 15 ZpmpzPqCnf ([]) ZpmpzPqC0 = true := by decide +kernel
theorem ZpmpzPqok1 : chkChunk 15 ZpmpzPqCnf (ZpmpzPqC0) ZpmpzPqC1 = true := by decide +kernel
theorem ZpmpzPqfinal : OKs 15 ZpmpzPqCnf [] [ZpmpzPqC0,ZpmpzPqC1] :=
  ⟨ZpmpzPqok0, ⟨ZpmpzPqok1, trivial⟩⟩
theorem ZpmpzPqempty : [ZpmpzPqC0,ZpmpzPqC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZpmpzPqunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZpmpzPqCnf, SatCl ρ c := chunks_sound 15 ZpmpzPqCnf _ ZpmpzPqfinal ZpmpzPqempty
end Minimality.H24.SAT.Lrat
