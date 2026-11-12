module

public import Minimality.Type24SAT.K24.LratPpmmm

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT.K29
namespace Minimality.H24.SAT.K24
def PpmmmC0 : List Step := PpmmmS0 ++ PpmmmS1 ++ PpmmmS2 ++ PpmmmS3
def PpmmmC1 : List Step := PpmmmS4 ++ PpmmmS5 ++ PpmmmS6 ++ PpmmmS7
def PpmmmC2 : List Step := PpmmmS8
theorem Ppmmmok0 : chkChunk 15 PpmmmCnf ([]) PpmmmC0 = true := by decide +kernel
theorem Ppmmmok1 : chkChunk 15 PpmmmCnf (PpmmmC0) PpmmmC1 = true := by decide +kernel
theorem Ppmmmok2 : chkChunk 15 PpmmmCnf (PpmmmC0 ++ PpmmmC1) PpmmmC2 = true := by decide +kernel
theorem Ppmmmfinal : OKs 15 PpmmmCnf [] [PpmmmC0,PpmmmC1,PpmmmC2] :=
  ⟨Ppmmmok0, ⟨Ppmmmok1, ⟨Ppmmmok2, trivial⟩⟩⟩
theorem Ppmmmempty : [PpmmmC0,PpmmmC1,PpmmmC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Ppmmmunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PpmmmCnf, SatCl ρ c := chunks_sound 15 PpmmmCnf _ Ppmmmfinal Ppmmmempty
end Minimality.H24.SAT.K24
