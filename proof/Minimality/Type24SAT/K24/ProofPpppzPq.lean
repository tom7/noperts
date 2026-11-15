module

public import Minimality.Type24SAT.K24.LratPpppzPq

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.K24
def PpppzPqC0 : List Step := PpppzPqS0 ++ PpppzPqS1 ++ PpppzPqS2 ++ PpppzPqS3
def PpppzPqC1 : List Step := PpppzPqS4 ++ PpppzPqS5 ++ PpppzPqS6 ++ PpppzPqS7
theorem PpppzPqok0 : chkChunk 15 PpppzPqCnf ([]) PpppzPqC0 = true := by decide +kernel
theorem PpppzPqok1 : chkChunk 15 PpppzPqCnf (PpppzPqC0) PpppzPqC1 = true := by decide +kernel
theorem PpppzPqfinal : OKs 15 PpppzPqCnf [] [PpppzPqC0,PpppzPqC1] :=
  ⟨PpppzPqok0, ⟨PpppzPqok1, trivial⟩⟩
theorem PpppzPqempty : [PpppzPqC0,PpppzPqC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PpppzPqunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PpppzPqCnf, SatCl ρ c := chunks_sound 15 PpppzPqCnf _ PpppzPqfinal PpppzPqempty
end Minimality.H24.SAT.K24
