module

public import Minimality.Type24SAT.K24.LratPzpppPq

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.Lrat
def PzpppPqC0 : List Step := PzpppPqS0 ++ PzpppPqS1 ++ PzpppPqS2 ++ PzpppPqS3
def PzpppPqC1 : List Step := PzpppPqS4 ++ PzpppPqS5 ++ PzpppPqS6 ++ PzpppPqS7
theorem PzpppPqok0 : chkChunk 15 PzpppPqCnf ([]) PzpppPqC0 = true := by decide +kernel
theorem PzpppPqok1 : chkChunk 15 PzpppPqCnf (PzpppPqC0) PzpppPqC1 = true := by decide +kernel
theorem PzpppPqfinal : OKs 15 PzpppPqCnf [] [PzpppPqC0,PzpppPqC1] :=
  ⟨PzpppPqok0, ⟨PzpppPqok1, trivial⟩⟩
theorem PzpppPqempty : [PzpppPqC0,PzpppPqC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PzpppPqunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PzpppPqCnf, SatCl ρ c := chunks_sound 15 PzpppPqCnf _ PzpppPqfinal PzpppPqempty
end Minimality.H24.SAT.Lrat
