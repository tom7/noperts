module

public import Minimality.Type24SAT.K24.LratMpmpmPq

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT.K29
namespace Minimality.H24.SAT.K24
def MpmpmPqC0 : List Step := MpmpmPqS0 ++ MpmpmPqS1 ++ MpmpmPqS2 ++ MpmpmPqS3
def MpmpmPqC1 : List Step := MpmpmPqS4 ++ MpmpmPqS5 ++ MpmpmPqS6 ++ MpmpmPqS7
def MpmpmPqC2 : List Step := MpmpmPqS8
theorem MpmpmPqok0 : chkChunk 15 MpmpmPqCnf ([]) MpmpmPqC0 = true := by decide +kernel
theorem MpmpmPqok1 : chkChunk 15 MpmpmPqCnf (MpmpmPqC0) MpmpmPqC1 = true := by decide +kernel
theorem MpmpmPqok2 : chkChunk 15 MpmpmPqCnf (MpmpmPqC0 ++ MpmpmPqC1) MpmpmPqC2 = true := by decide +kernel
theorem MpmpmPqfinal : OKs 15 MpmpmPqCnf [] [MpmpmPqC0,MpmpmPqC1,MpmpmPqC2] :=
  ⟨MpmpmPqok0, ⟨MpmpmPqok1, ⟨MpmpmPqok2, trivial⟩⟩⟩
theorem MpmpmPqempty : [MpmpmPqC0,MpmpmPqC1,MpmpmPqC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem MpmpmPqunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ MpmpmPqCnf, SatCl ρ c := chunks_sound 15 MpmpmPqCnf _ MpmpmPqfinal MpmpmPqempty
end Minimality.H24.SAT.K24
