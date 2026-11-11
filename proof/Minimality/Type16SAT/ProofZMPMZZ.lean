module

public import Minimality.Type16SAT.LratZMPMZZ

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def ZMPMZZC0 : List Step := ZMPMZZS0 ++ ZMPMZZS1 ++ ZMPMZZS2 ++ ZMPMZZS3
def ZMPMZZC1 : List Step := ZMPMZZS4 ++ ZMPMZZS5 ++ ZMPMZZS6 ++ ZMPMZZS7
def ZMPMZZC2 : List Step := ZMPMZZS8 ++ ZMPMZZS9
theorem ZMPMZZok0 : chkChunk 15 ZMPMZZCnf ([]) ZMPMZZC0 = true := by decide +kernel
theorem ZMPMZZok1 : chkChunk 15 ZMPMZZCnf (ZMPMZZC0) ZMPMZZC1 = true := by decide +kernel
theorem ZMPMZZok2 : chkChunk 15 ZMPMZZCnf (ZMPMZZC0 ++ ZMPMZZC1) ZMPMZZC2 = true := by decide +kernel
theorem ZMPMZZfinal : OKs 15 ZMPMZZCnf [] [ZMPMZZC0,ZMPMZZC1,ZMPMZZC2] :=
  ⟨ZMPMZZok0, ⟨ZMPMZZok1, ⟨ZMPMZZok2, trivial⟩⟩⟩
theorem ZMPMZZempty : [ZMPMZZC0,ZMPMZZC1,ZMPMZZC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZMPMZZunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZMPMZZCnf, SatCl ρ c := chunks_sound 15 ZMPMZZCnf _ ZMPMZZfinal ZMPMZZempty
end Minimality.H29.SAT.K29
