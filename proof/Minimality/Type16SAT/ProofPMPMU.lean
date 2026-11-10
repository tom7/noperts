module

public import Minimality.Type16SAT.LratPMPMU

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PMPMUC0 : List Step := PMPMUS0 ++ PMPMUS1 ++ PMPMUS2 ++ PMPMUS3
def PMPMUC1 : List Step := PMPMUS4 ++ PMPMUS5 ++ PMPMUS6 ++ PMPMUS7
def PMPMUC2 : List Step := PMPMUS8 ++ PMPMUS9 ++ PMPMUS10 ++ PMPMUS11
theorem PMPMUok0 : chkChunk 15 PMPMUCnf ([]) PMPMUC0 = true := by decide +kernel
theorem PMPMUok1 : chkChunk 15 PMPMUCnf (PMPMUC0) PMPMUC1 = true := by decide +kernel
theorem PMPMUok2 : chkChunk 15 PMPMUCnf (PMPMUC0 ++ PMPMUC1) PMPMUC2 = true := by decide +kernel
theorem PMPMUfinal : OKs 15 PMPMUCnf [] [PMPMUC0,PMPMUC1,PMPMUC2] :=
  ⟨PMPMUok0, ⟨PMPMUok1, ⟨PMPMUok2, trivial⟩⟩⟩
theorem PMPMUempty : [PMPMUC0,PMPMUC1,PMPMUC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PMPMUunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PMPMUCnf, SatCl ρ c := chunks_sound 15 PMPMUCnf _ PMPMUfinal PMPMUempty
end Minimality.H29.SAT.K29
