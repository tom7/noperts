module

public import Minimality.Type16SAT.LratPMPMZ

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PMPMZC0 : List Step := PMPMZS0 ++ PMPMZS1 ++ PMPMZS2 ++ PMPMZS3
def PMPMZC1 : List Step := PMPMZS4 ++ PMPMZS5 ++ PMPMZS6 ++ PMPMZS7
def PMPMZC2 : List Step := PMPMZS8 ++ PMPMZS9 ++ PMPMZS10
theorem PMPMZok0 : chkChunk 15 PMPMZCnf ([]) PMPMZC0 = true := by decide +kernel
theorem PMPMZok1 : chkChunk 15 PMPMZCnf (PMPMZC0) PMPMZC1 = true := by decide +kernel
theorem PMPMZok2 : chkChunk 15 PMPMZCnf (PMPMZC0 ++ PMPMZC1) PMPMZC2 = true := by decide +kernel
theorem PMPMZfinal : OKs 15 PMPMZCnf [] [PMPMZC0,PMPMZC1,PMPMZC2] :=
  ⟨PMPMZok0, ⟨PMPMZok1, ⟨PMPMZok2, trivial⟩⟩⟩
theorem PMPMZempty : [PMPMZC0,PMPMZC1,PMPMZC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PMPMZunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PMPMZCnf, SatCl ρ c := chunks_sound 15 PMPMZCnf _ PMPMZfinal PMPMZempty
end Minimality.H29.SAT.K29
