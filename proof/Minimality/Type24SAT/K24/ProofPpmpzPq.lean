module

public import Minimality.Type24SAT.K24.LratPpmpzPq

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.Lrat
def PpmpzPqC0 : List Step := PpmpzPqS0 ++ PpmpzPqS1 ++ PpmpzPqS2 ++ PpmpzPqS3
def PpmpzPqC1 : List Step := PpmpzPqS4 ++ PpmpzPqS5 ++ PpmpzPqS6 ++ PpmpzPqS7
theorem PpmpzPqok0 : chkChunk 15 PpmpzPqCnf ([]) PpmpzPqC0 = true := by decide +kernel
theorem PpmpzPqok1 : chkChunk 15 PpmpzPqCnf (PpmpzPqC0) PpmpzPqC1 = true := by decide +kernel
theorem PpmpzPqfinal : OKs 15 PpmpzPqCnf [] [PpmpzPqC0,PpmpzPqC1] :=
  ⟨PpmpzPqok0, ⟨PpmpzPqok1, trivial⟩⟩
theorem PpmpzPqempty : [PpmpzPqC0,PpmpzPqC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PpmpzPqunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PpmpzPqCnf, SatCl ρ c := chunks_sound 15 PpmpzPqCnf _ PpmpzPqfinal PpmpzPqempty
end Minimality.H24.SAT.Lrat
