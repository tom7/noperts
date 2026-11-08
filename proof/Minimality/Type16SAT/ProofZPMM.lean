module

public import Minimality.Type16SAT.LratZPMM

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def ZPMMC0 : List Step := ZPMMS0 ++ ZPMMS1 ++ ZPMMS2 ++ ZPMMS3
def ZPMMC1 : List Step := ZPMMS4 ++ ZPMMS5 ++ ZPMMS6 ++ ZPMMS7
def ZPMMC2 : List Step := ZPMMS8 ++ ZPMMS9 ++ ZPMMS10 ++ ZPMMS11
theorem ZPMMok0 : chkChunk 15 ZPMMCnf ([]) ZPMMC0 = true := by decide +kernel
theorem ZPMMok1 : chkChunk 15 ZPMMCnf (ZPMMC0) ZPMMC1 = true := by decide +kernel
theorem ZPMMok2 : chkChunk 15 ZPMMCnf (ZPMMC0 ++ ZPMMC1) ZPMMC2 = true := by decide +kernel
theorem ZPMMfinal : OKs 15 ZPMMCnf [] [ZPMMC0,ZPMMC1,ZPMMC2] :=
  ⟨ZPMMok0, ⟨ZPMMok1, ⟨ZPMMok2, trivial⟩⟩⟩
theorem ZPMMempty : [ZPMMC0,ZPMMC1,ZPMMC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZPMMunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZPMMCnf, SatCl ρ c := chunks_sound 15 ZPMMCnf _ ZPMMfinal ZPMMempty
end Minimality.H29.SAT.K29
