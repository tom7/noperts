module

public import Minimality.Type24SAT.K24.LratMpmzmPq

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.Lrat
def MpmzmPqC0 : List Step := MpmzmPqS0 ++ MpmzmPqS1 ++ MpmzmPqS2 ++ MpmzmPqS3
def MpmzmPqC1 : List Step := MpmzmPqS4 ++ MpmzmPqS5
theorem MpmzmPqok0 : chkChunk 15 MpmzmPqCnf ([]) MpmzmPqC0 = true := by decide +kernel
theorem MpmzmPqok1 : chkChunk 15 MpmzmPqCnf (MpmzmPqC0) MpmzmPqC1 = true := by decide +kernel
theorem MpmzmPqfinal : OKs 15 MpmzmPqCnf [] [MpmzmPqC0,MpmzmPqC1] :=
  ⟨MpmzmPqok0, ⟨MpmzmPqok1, trivial⟩⟩
theorem MpmzmPqempty : [MpmzmPqC0,MpmzmPqC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem MpmzmPqunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ MpmzmPqCnf, SatCl ρ c := chunks_sound 15 MpmzmPqCnf _ MpmzmPqfinal MpmzmPqempty
end Minimality.H24.SAT.Lrat
