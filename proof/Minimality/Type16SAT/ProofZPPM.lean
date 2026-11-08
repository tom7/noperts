module

public import Minimality.Type16SAT.LratZPPM

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def ZPPMC0 : List Step := ZPPMS0 ++ ZPPMS1 ++ ZPPMS2 ++ ZPPMS3
def ZPPMC1 : List Step := ZPPMS4
theorem ZPPMok0 : chkChunk 15 ZPPMCnf ([]) ZPPMC0 = true := by decide +kernel
theorem ZPPMok1 : chkChunk 15 ZPPMCnf (ZPPMC0) ZPPMC1 = true := by decide +kernel
theorem ZPPMfinal : OKs 15 ZPPMCnf [] [ZPPMC0,ZPPMC1] :=
  ⟨ZPPMok0, ⟨ZPPMok1, trivial⟩⟩
theorem ZPPMempty : [ZPPMC0,ZPPMC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZPPMunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZPPMCnf, SatCl ρ c := chunks_sound 15 ZPPMCnf _ ZPPMfinal ZPPMempty
end Minimality.H29.SAT.K29
