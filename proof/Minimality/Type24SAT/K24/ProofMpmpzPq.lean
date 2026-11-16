module

public import Minimality.Type24SAT.K24.LratMpmpzPq

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.Lrat
def MpmpzPqC0 : List Step := MpmpzPqS0 ++ MpmpzPqS1 ++ MpmpzPqS2 ++ MpmpzPqS3
def MpmpzPqC1 : List Step := MpmpzPqS4 ++ MpmpzPqS5 ++ MpmpzPqS6 ++ MpmpzPqS7
theorem MpmpzPqok0 : chkChunk 15 MpmpzPqCnf ([]) MpmpzPqC0 = true := by decide +kernel
theorem MpmpzPqok1 : chkChunk 15 MpmpzPqCnf (MpmpzPqC0) MpmpzPqC1 = true := by decide +kernel
theorem MpmpzPqfinal : OKs 15 MpmpzPqCnf [] [MpmpzPqC0,MpmpzPqC1] :=
  ⟨MpmpzPqok0, ⟨MpmpzPqok1, trivial⟩⟩
theorem MpmpzPqempty : [MpmpzPqC0,MpmpzPqC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem MpmpzPqunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ MpmpzPqCnf, SatCl ρ c := chunks_sound 15 MpmpzPqCnf _ MpmpzPqfinal MpmpzPqempty
end Minimality.H24.SAT.Lrat
