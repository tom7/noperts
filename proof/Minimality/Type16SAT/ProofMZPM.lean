module

public import Minimality.Type16SAT.LratMZPM

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def MZPMC0 : List Step := MZPMS0 ++ MZPMS1 ++ MZPMS2 ++ MZPMS3
def MZPMC1 : List Step := MZPMS4
theorem MZPMok0 : chkChunk 15 MZPMCnf ([]) MZPMC0 = true := by decide +kernel
theorem MZPMok1 : chkChunk 15 MZPMCnf (MZPMC0) MZPMC1 = true := by decide +kernel
theorem MZPMfinal : OKs 15 MZPMCnf [] [MZPMC0,MZPMC1] :=
  ⟨MZPMok0, ⟨MZPMok1, trivial⟩⟩
theorem MZPMempty : [MZPMC0,MZPMC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem MZPMunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ MZPMCnf, SatCl ρ c := chunks_sound 15 MZPMCnf _ MZPMfinal MZPMempty
end Minimality.H29.SAT.K29
