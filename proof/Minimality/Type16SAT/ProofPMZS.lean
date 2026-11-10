module

public import Minimality.Type16SAT.LratPMZS

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PMZSC0 : List Step := PMZSS0 ++ PMZSS1 ++ PMZSS2 ++ PMZSS3
def PMZSC1 : List Step := PMZSS4 ++ PMZSS5 ++ PMZSS6 ++ PMZSS7
def PMZSC2 : List Step := PMZSS8 ++ PMZSS9 ++ PMZSS10 ++ PMZSS11
theorem PMZSok0 : chkChunk 15 PMZSCnf ([]) PMZSC0 = true := by decide +kernel
theorem PMZSok1 : chkChunk 15 PMZSCnf (PMZSC0) PMZSC1 = true := by decide +kernel
theorem PMZSok2 : chkChunk 15 PMZSCnf (PMZSC0 ++ PMZSC1) PMZSC2 = true := by decide +kernel
theorem PMZSfinal : OKs 15 PMZSCnf [] [PMZSC0,PMZSC1,PMZSC2] :=
  ⟨PMZSok0, ⟨PMZSok1, ⟨PMZSok2, trivial⟩⟩⟩
theorem PMZSempty : [PMZSC0,PMZSC1,PMZSC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PMZSunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PMZSCnf, SatCl ρ c := chunks_sound 15 PMZSCnf _ PMZSfinal PMZSempty
end Minimality.H29.SAT.K29
