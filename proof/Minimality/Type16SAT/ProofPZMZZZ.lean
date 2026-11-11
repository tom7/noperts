module

public import Minimality.Type16SAT.LratPZMZZZ

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PZMZZZC0 : List Step := PZMZZZS0 ++ PZMZZZS1 ++ PZMZZZS2 ++ PZMZZZS3
def PZMZZZC1 : List Step := PZMZZZS4 ++ PZMZZZS5 ++ PZMZZZS6 ++ PZMZZZS7
def PZMZZZC2 : List Step := PZMZZZS8 ++ PZMZZZS9
theorem PZMZZZok0 : chkChunk 15 PZMZZZCnf ([]) PZMZZZC0 = true := by decide +kernel
theorem PZMZZZok1 : chkChunk 15 PZMZZZCnf (PZMZZZC0) PZMZZZC1 = true := by decide +kernel
theorem PZMZZZok2 : chkChunk 15 PZMZZZCnf (PZMZZZC0 ++ PZMZZZC1) PZMZZZC2 = true := by decide +kernel
theorem PZMZZZfinal : OKs 15 PZMZZZCnf [] [PZMZZZC0,PZMZZZC1,PZMZZZC2] :=
  ⟨PZMZZZok0, ⟨PZMZZZok1, ⟨PZMZZZok2, trivial⟩⟩⟩
theorem PZMZZZempty : [PZMZZZC0,PZMZZZC1,PZMZZZC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PZMZZZunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PZMZZZCnf, SatCl ρ c := chunks_sound 15 PZMZZZCnf _ PZMZZZfinal PZMZZZempty
end Minimality.H29.SAT.K29
