module

public import Minimality.Type16SAT.LratPMZMZ

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PMZMZC0 : List Step := PMZMZS0 ++ PMZMZS1 ++ PMZMZS2 ++ PMZMZS3
def PMZMZC1 : List Step := PMZMZS4 ++ PMZMZS5 ++ PMZMZS6 ++ PMZMZS7
def PMZMZC2 : List Step := PMZMZS8 ++ PMZMZS9 ++ PMZMZS10 ++ PMZMZS11
def PMZMZC3 : List Step := PMZMZS12
theorem PMZMZok0 : chkChunk 15 PMZMZCnf ([]) PMZMZC0 = true := by decide +kernel
theorem PMZMZok1 : chkChunk 15 PMZMZCnf (PMZMZC0) PMZMZC1 = true := by decide +kernel
theorem PMZMZok2 : chkChunk 15 PMZMZCnf (PMZMZC0 ++ PMZMZC1) PMZMZC2 = true := by decide +kernel
theorem PMZMZok3 : chkChunk 15 PMZMZCnf (PMZMZC0 ++ PMZMZC1 ++ PMZMZC2) PMZMZC3 = true := by decide +kernel
theorem PMZMZfinal : OKs 15 PMZMZCnf [] [PMZMZC0,PMZMZC1,PMZMZC2,PMZMZC3] :=
  ⟨PMZMZok0, ⟨PMZMZok1, ⟨PMZMZok2, ⟨PMZMZok3, trivial⟩⟩⟩⟩
theorem PMZMZempty : [PMZMZC0,PMZMZC1,PMZMZC2,PMZMZC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PMZMZunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PMZMZCnf, SatCl ρ c := chunks_sound 15 PMZMZCnf _ PMZMZfinal PMZMZempty
end Minimality.H29.SAT.K29
