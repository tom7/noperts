module

public import Minimality.Type16SAT.LratPPMM

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PPMMC0 : List Step := PPMMS0 ++ PPMMS1 ++ PPMMS2 ++ PPMMS3
def PPMMC1 : List Step := PPMMS4 ++ PPMMS5 ++ PPMMS6 ++ PPMMS7
def PPMMC2 : List Step := PPMMS8 ++ PPMMS9 ++ PPMMS10 ++ PPMMS11
theorem PPMMok0 : chkChunk 15 PPMMCnf ([]) PPMMC0 = true := by decide +kernel
theorem PPMMok1 : chkChunk 15 PPMMCnf (PPMMC0) PPMMC1 = true := by decide +kernel
theorem PPMMok2 : chkChunk 15 PPMMCnf (PPMMC0 ++ PPMMC1) PPMMC2 = true := by decide +kernel
theorem PPMMfinal : OKs 15 PPMMCnf [] [PPMMC0,PPMMC1,PPMMC2] :=
  ⟨PPMMok0, ⟨PPMMok1, ⟨PPMMok2, trivial⟩⟩⟩
theorem PPMMempty : [PPMMC0,PPMMC1,PPMMC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PPMMunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PPMMCnf, SatCl ρ c := chunks_sound 15 PPMMCnf _ PPMMfinal PPMMempty
end Minimality.H29.SAT.K29
