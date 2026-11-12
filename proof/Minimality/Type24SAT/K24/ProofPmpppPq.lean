module

public import Minimality.Type24SAT.K24.LratPmpppPq

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT.K29
namespace Minimality.H24.SAT.K24
def PmpppPqC0 : List Step := PmpppPqS0 ++ PmpppPqS1 ++ PmpppPqS2 ++ PmpppPqS3
def PmpppPqC1 : List Step := PmpppPqS4 ++ PmpppPqS5 ++ PmpppPqS6 ++ PmpppPqS7
def PmpppPqC2 : List Step := PmpppPqS8
theorem PmpppPqok0 : chkChunk 15 PmpppPqCnf ([]) PmpppPqC0 = true := by decide +kernel
theorem PmpppPqok1 : chkChunk 15 PmpppPqCnf (PmpppPqC0) PmpppPqC1 = true := by decide +kernel
theorem PmpppPqok2 : chkChunk 15 PmpppPqCnf (PmpppPqC0 ++ PmpppPqC1) PmpppPqC2 = true := by decide +kernel
theorem PmpppPqfinal : OKs 15 PmpppPqCnf [] [PmpppPqC0,PmpppPqC1,PmpppPqC2] :=
  ⟨PmpppPqok0, ⟨PmpppPqok1, ⟨PmpppPqok2, trivial⟩⟩⟩
theorem PmpppPqempty : [PmpppPqC0,PmpppPqC1,PmpppPqC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PmpppPqunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PmpppPqCnf, SatCl ρ c := chunks_sound 15 PmpppPqCnf _ PmpppPqfinal PmpppPqempty
end Minimality.H24.SAT.K24
