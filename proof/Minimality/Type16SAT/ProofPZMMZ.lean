module

public import Minimality.Type16SAT.LratPZMMZ

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PZMMZC0 : List Step := PZMMZS0 ++ PZMMZS1 ++ PZMMZS2 ++ PZMMZS3
def PZMMZC1 : List Step := PZMMZS4 ++ PZMMZS5 ++ PZMMZS6 ++ PZMMZS7
def PZMMZC2 : List Step := PZMMZS8 ++ PZMMZS9 ++ PZMMZS10 ++ PZMMZS11
def PZMMZC3 : List Step := PZMMZS12
theorem PZMMZok0 : chkChunk 15 PZMMZCnf ([]) PZMMZC0 = true := by decide +kernel
theorem PZMMZok1 : chkChunk 15 PZMMZCnf (PZMMZC0) PZMMZC1 = true := by decide +kernel
theorem PZMMZok2 : chkChunk 15 PZMMZCnf (PZMMZC0 ++ PZMMZC1) PZMMZC2 = true := by decide +kernel
theorem PZMMZok3 : chkChunk 15 PZMMZCnf (PZMMZC0 ++ PZMMZC1 ++ PZMMZC2) PZMMZC3 = true := by decide +kernel
theorem PZMMZfinal : OKs 15 PZMMZCnf [] [PZMMZC0,PZMMZC1,PZMMZC2,PZMMZC3] :=
  ⟨PZMMZok0, ⟨PZMMZok1, ⟨PZMMZok2, ⟨PZMMZok3, trivial⟩⟩⟩⟩
theorem PZMMZempty : [PZMMZC0,PZMMZC1,PZMMZC2,PZMMZC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PZMMZunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PZMMZCnf, SatCl ρ c := chunks_sound 15 PZMMZCnf _ PZMMZfinal PZMMZempty
end Minimality.H29.SAT.K29
