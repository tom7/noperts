module

public import Minimality.Type16SAT.LratZZMZZZ

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def ZZMZZZC0 : List Step := ZZMZZZS0 ++ ZZMZZZS1 ++ ZZMZZZS2 ++ ZZMZZZS3
def ZZMZZZC1 : List Step := ZZMZZZS4 ++ ZZMZZZS5 ++ ZZMZZZS6 ++ ZZMZZZS7
def ZZMZZZC2 : List Step := ZZMZZZS8 ++ ZZMZZZS9 ++ ZZMZZZS10 ++ ZZMZZZS11
def ZZMZZZC3 : List Step := ZZMZZZS12
theorem ZZMZZZok0 : chkChunk 15 ZZMZZZCnf ([]) ZZMZZZC0 = true := by decide +kernel
theorem ZZMZZZok1 : chkChunk 15 ZZMZZZCnf (ZZMZZZC0) ZZMZZZC1 = true := by decide +kernel
theorem ZZMZZZok2 : chkChunk 15 ZZMZZZCnf (ZZMZZZC0 ++ ZZMZZZC1) ZZMZZZC2 = true := by decide +kernel
theorem ZZMZZZok3 : chkChunk 15 ZZMZZZCnf (ZZMZZZC0 ++ ZZMZZZC1 ++ ZZMZZZC2) ZZMZZZC3 = true := by decide +kernel
theorem ZZMZZZfinal : OKs 15 ZZMZZZCnf [] [ZZMZZZC0,ZZMZZZC1,ZZMZZZC2,ZZMZZZC3] :=
  ⟨ZZMZZZok0, ⟨ZZMZZZok1, ⟨ZZMZZZok2, ⟨ZZMZZZok3, trivial⟩⟩⟩⟩
theorem ZZMZZZempty : [ZZMZZZC0,ZZMZZZC1,ZZMZZZC2,ZZMZZZC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZZMZZZunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZZMZZZCnf, SatCl ρ c := chunks_sound 15 ZZMZZZCnf _ ZZMZZZfinal ZZMZZZempty
end Minimality.H29.SAT.K29
