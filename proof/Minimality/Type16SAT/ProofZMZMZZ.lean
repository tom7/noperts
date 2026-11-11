module

public import Minimality.Type16SAT.LratZMZMZZ

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def ZMZMZZC0 : List Step := ZMZMZZS0 ++ ZMZMZZS1 ++ ZMZMZZS2 ++ ZMZMZZS3
def ZMZMZZC1 : List Step := ZMZMZZS4 ++ ZMZMZZS5 ++ ZMZMZZS6 ++ ZMZMZZS7
def ZMZMZZC2 : List Step := ZMZMZZS8 ++ ZMZMZZS9 ++ ZMZMZZS10
theorem ZMZMZZok0 : chkChunk 15 ZMZMZZCnf ([]) ZMZMZZC0 = true := by decide +kernel
theorem ZMZMZZok1 : chkChunk 15 ZMZMZZCnf (ZMZMZZC0) ZMZMZZC1 = true := by decide +kernel
theorem ZMZMZZok2 : chkChunk 15 ZMZMZZCnf (ZMZMZZC0 ++ ZMZMZZC1) ZMZMZZC2 = true := by decide +kernel
theorem ZMZMZZfinal : OKs 15 ZMZMZZCnf [] [ZMZMZZC0,ZMZMZZC1,ZMZMZZC2] :=
  ⟨ZMZMZZok0, ⟨ZMZMZZok1, ⟨ZMZMZZok2, trivial⟩⟩⟩
theorem ZMZMZZempty : [ZMZMZZC0,ZMZMZZC1,ZMZMZZC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZMZMZZunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZMZMZZCnf, SatCl ρ c := chunks_sound 15 ZMZMZZCnf _ ZMZMZZfinal ZMZMZZempty
end Minimality.H29.SAT.K29
