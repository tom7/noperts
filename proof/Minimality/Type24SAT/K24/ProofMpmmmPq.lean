module

public import Minimality.Type24SAT.K24.LratMpmmmPq

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT.K29
namespace Minimality.H24.SAT.K24
def MpmmmPqC0 : List Step := MpmmmPqS0 ++ MpmmmPqS1 ++ MpmmmPqS2 ++ MpmmmPqS3
def MpmmmPqC1 : List Step := MpmmmPqS4 ++ MpmmmPqS5 ++ MpmmmPqS6
theorem MpmmmPqok0 : chkChunk 15 MpmmmPqCnf ([]) MpmmmPqC0 = true := by decide +kernel
theorem MpmmmPqok1 : chkChunk 15 MpmmmPqCnf (MpmmmPqC0) MpmmmPqC1 = true := by decide +kernel
theorem MpmmmPqfinal : OKs 15 MpmmmPqCnf [] [MpmmmPqC0,MpmmmPqC1] :=
  ⟨MpmmmPqok0, ⟨MpmmmPqok1, trivial⟩⟩
theorem MpmmmPqempty : [MpmmmPqC0,MpmmmPqC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem MpmmmPqunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ MpmmmPqCnf, SatCl ρ c := chunks_sound 15 MpmmmPqCnf _ MpmmmPqfinal MpmmmPqempty
end Minimality.H24.SAT.K24
