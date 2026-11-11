module

public import Minimality.Type16SAT.LratZZMMZ

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def ZZMMZC0 : List Step := ZZMMZS0 ++ ZZMMZS1 ++ ZZMMZS2 ++ ZZMMZS3
def ZZMMZC1 : List Step := ZZMMZS4 ++ ZZMMZS5 ++ ZZMMZS6 ++ ZZMMZS7
def ZZMMZC2 : List Step := ZZMMZS8 ++ ZZMMZS9 ++ ZZMMZS10 ++ ZZMMZS11
def ZZMMZC3 : List Step := ZZMMZS12
theorem ZZMMZok0 : chkChunk 15 ZZMMZCnf ([]) ZZMMZC0 = true := by decide +kernel
theorem ZZMMZok1 : chkChunk 15 ZZMMZCnf (ZZMMZC0) ZZMMZC1 = true := by decide +kernel
theorem ZZMMZok2 : chkChunk 15 ZZMMZCnf (ZZMMZC0 ++ ZZMMZC1) ZZMMZC2 = true := by decide +kernel
theorem ZZMMZok3 : chkChunk 15 ZZMMZCnf (ZZMMZC0 ++ ZZMMZC1 ++ ZZMMZC2) ZZMMZC3 = true := by decide +kernel
theorem ZZMMZfinal : OKs 15 ZZMMZCnf [] [ZZMMZC0,ZZMMZC1,ZZMMZC2,ZZMMZC3] :=
  ⟨ZZMMZok0, ⟨ZZMMZok1, ⟨ZZMMZok2, ⟨ZZMMZok3, trivial⟩⟩⟩⟩
theorem ZZMMZempty : [ZZMMZC0,ZZMMZC1,ZZMMZC2,ZZMMZC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZZMMZunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZZMMZCnf, SatCl ρ c := chunks_sound 15 ZZMMZCnf _ ZZMMZfinal ZZMMZempty
end Minimality.H29.SAT.K29
