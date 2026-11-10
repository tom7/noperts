module

public import Minimality.Type16SAT.LratMZMMZ

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def MZMMZC0 : List Step := MZMMZS0 ++ MZMMZS1 ++ MZMMZS2 ++ MZMMZS3
def MZMMZC1 : List Step := MZMMZS4 ++ MZMMZS5 ++ MZMMZS6 ++ MZMMZS7
def MZMMZC2 : List Step := MZMMZS8 ++ MZMMZS9
theorem MZMMZok0 : chkChunk 15 MZMMZCnf ([]) MZMMZC0 = true := by decide +kernel
theorem MZMMZok1 : chkChunk 15 MZMMZCnf (MZMMZC0) MZMMZC1 = true := by decide +kernel
theorem MZMMZok2 : chkChunk 15 MZMMZCnf (MZMMZC0 ++ MZMMZC1) MZMMZC2 = true := by decide +kernel
theorem MZMMZfinal : OKs 15 MZMMZCnf [] [MZMMZC0,MZMMZC1,MZMMZC2] :=
  ⟨MZMMZok0, ⟨MZMMZok1, ⟨MZMMZok2, trivial⟩⟩⟩
theorem MZMMZempty : [MZMMZC0,MZMMZC1,MZMMZC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem MZMMZunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ MZMMZCnf, SatCl ρ c := chunks_sound 15 MZMMZCnf _ MZMMZfinal MZMMZempty
end Minimality.H29.SAT.K29
