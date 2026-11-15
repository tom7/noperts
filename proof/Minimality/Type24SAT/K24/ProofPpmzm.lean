module

public import Minimality.Type24SAT.K24.LratPpmzm

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT.K29
namespace Minimality.H24.SAT.K24
def PpmzmC0 : List Step := PpmzmS0 ++ PpmzmS1 ++ PpmzmS2 ++ PpmzmS3
def PpmzmC1 : List Step := PpmzmS4 ++ PpmzmS5 ++ PpmzmS6 ++ PpmzmS7
def PpmzmC2 : List Step := PpmzmS8 ++ PpmzmS9 ++ PpmzmS10 ++ PpmzmS11
def PpmzmC3 : List Step := PpmzmS12 ++ PpmzmS13 ++ PpmzmS14 ++ PpmzmS15
def PpmzmC4 : List Step := PpmzmS16 ++ PpmzmS17
theorem Ppmzmok0 : chkChunk 15 PpmzmCnf ([]) PpmzmC0 = true := by decide +kernel
theorem Ppmzmok1 : chkChunk 15 PpmzmCnf (PpmzmC0) PpmzmC1 = true := by decide +kernel
theorem Ppmzmok2 : chkChunk 15 PpmzmCnf (PpmzmC0 ++ PpmzmC1) PpmzmC2 = true := by decide +kernel
theorem Ppmzmok3 : chkChunk 15 PpmzmCnf (PpmzmC0 ++ PpmzmC1 ++ PpmzmC2) PpmzmC3 = true := by decide +kernel
theorem Ppmzmok4 : chkChunk 15 PpmzmCnf (PpmzmC0 ++ PpmzmC1 ++ PpmzmC2 ++ PpmzmC3) PpmzmC4 = true := by decide +kernel
theorem Ppmzmfinal : OKs 15 PpmzmCnf [] [PpmzmC0,PpmzmC1,PpmzmC2,PpmzmC3,PpmzmC4] :=
  ⟨Ppmzmok0, ⟨Ppmzmok1, ⟨Ppmzmok2, ⟨Ppmzmok3, ⟨Ppmzmok4, trivial⟩⟩⟩⟩⟩
theorem Ppmzmempty : [PpmzmC0,PpmzmC1,PpmzmC2,PpmzmC3,PpmzmC4].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Ppmzmunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PpmzmCnf, SatCl ρ c := chunks_sound 15 PpmzmCnf _ Ppmzmfinal Ppmzmempty
end Minimality.H24.SAT.K24
