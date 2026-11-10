module

public import Minimality.Type16SAT.LratPMZMU

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PMZMUC0 : List Step := PMZMUS0 ++ PMZMUS1 ++ PMZMUS2 ++ PMZMUS3
def PMZMUC1 : List Step := PMZMUS4 ++ PMZMUS5 ++ PMZMUS6 ++ PMZMUS7
def PMZMUC2 : List Step := PMZMUS8 ++ PMZMUS9 ++ PMZMUS10 ++ PMZMUS11
def PMZMUC3 : List Step := PMZMUS12 ++ PMZMUS13
theorem PMZMUok0 : chkChunk 15 PMZMUCnf ([]) PMZMUC0 = true := by decide +kernel
theorem PMZMUok1 : chkChunk 15 PMZMUCnf (PMZMUC0) PMZMUC1 = true := by decide +kernel
theorem PMZMUok2 : chkChunk 15 PMZMUCnf (PMZMUC0 ++ PMZMUC1) PMZMUC2 = true := by decide +kernel
theorem PMZMUok3 : chkChunk 15 PMZMUCnf (PMZMUC0 ++ PMZMUC1 ++ PMZMUC2) PMZMUC3 = true := by decide +kernel
theorem PMZMUfinal : OKs 15 PMZMUCnf [] [PMZMUC0,PMZMUC1,PMZMUC2,PMZMUC3] :=
  ⟨PMZMUok0, ⟨PMZMUok1, ⟨PMZMUok2, ⟨PMZMUok3, trivial⟩⟩⟩⟩
theorem PMZMUempty : [PMZMUC0,PMZMUC1,PMZMUC2,PMZMUC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PMZMUunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PMZMUCnf, SatCl ρ c := chunks_sound 15 PMZMUCnf _ PMZMUfinal PMZMUempty
end Minimality.H29.SAT.K29
