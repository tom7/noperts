module

public import Minimality.Type16SAT.LratPZPM

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PZPMC0 : List Step := PZPMS0 ++ PZPMS1 ++ PZPMS2 ++ PZPMS3
theorem PZPMok0 : chkChunk 15 PZPMCnf ([]) PZPMC0 = true := by decide +kernel
theorem PZPMfinal : OKs 15 PZPMCnf [] [PZPMC0] :=
  ⟨PZPMok0, trivial⟩
theorem PZPMempty : [PZPMC0].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PZPMunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PZPMCnf, SatCl ρ c := chunks_sound 15 PZPMCnf _ PZPMfinal PZPMempty
end Minimality.H29.SAT.K29
