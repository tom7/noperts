module

public import Minimality.Type16SAT.LratZZMPZ

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def ZZMPZC0 : List Step := ZZMPZS0 ++ ZZMPZS1 ++ ZZMPZS2 ++ ZZMPZS3
def ZZMPZC1 : List Step := ZZMPZS4 ++ ZZMPZS5 ++ ZZMPZS6 ++ ZZMPZS7
def ZZMPZC2 : List Step := ZZMPZS8 ++ ZZMPZS9 ++ ZZMPZS10
theorem ZZMPZok0 : chkChunk 15 ZZMPZCnf ([]) ZZMPZC0 = true := by decide +kernel
theorem ZZMPZok1 : chkChunk 15 ZZMPZCnf (ZZMPZC0) ZZMPZC1 = true := by decide +kernel
theorem ZZMPZok2 : chkChunk 15 ZZMPZCnf (ZZMPZC0 ++ ZZMPZC1) ZZMPZC2 = true := by decide +kernel
theorem ZZMPZfinal : OKs 15 ZZMPZCnf [] [ZZMPZC0,ZZMPZC1,ZZMPZC2] :=
  ⟨ZZMPZok0, ⟨ZZMPZok1, ⟨ZZMPZok2, trivial⟩⟩⟩
theorem ZZMPZempty : [ZZMPZC0,ZZMPZC1,ZZMPZC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZZMPZunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZZMPZCnf, SatCl ρ c := chunks_sound 15 ZZMPZCnf _ ZZMPZfinal ZZMPZempty
end Minimality.H29.SAT.K29
