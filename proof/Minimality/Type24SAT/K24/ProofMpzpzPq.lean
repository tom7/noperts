module

public import Minimality.Type24SAT.K24.LratMpzpzPq

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.K24
def MpzpzPqC0 : List Step := MpzpzPqS0 ++ MpzpzPqS1 ++ MpzpzPqS2 ++ MpzpzPqS3
def MpzpzPqC1 : List Step := MpzpzPqS4 ++ MpzpzPqS5 ++ MpzpzPqS6 ++ MpzpzPqS7
theorem MpzpzPqok0 : chkChunk 15 MpzpzPqCnf ([]) MpzpzPqC0 = true := by decide +kernel
theorem MpzpzPqok1 : chkChunk 15 MpzpzPqCnf (MpzpzPqC0) MpzpzPqC1 = true := by decide +kernel
theorem MpzpzPqfinal : OKs 15 MpzpzPqCnf [] [MpzpzPqC0,MpzpzPqC1] :=
  ⟨MpzpzPqok0, ⟨MpzpzPqok1, trivial⟩⟩
theorem MpzpzPqempty : [MpzpzPqC0,MpzpzPqC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem MpzpzPqunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ MpzpzPqCnf, SatCl ρ c := chunks_sound 15 MpzpzPqCnf _ MpzpzPqfinal MpzpzPqempty
end Minimality.H24.SAT.K24
