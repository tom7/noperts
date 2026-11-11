module

public import Minimality.Type16SAT.LratMZMZT

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def MZMZTC0 : List Step := MZMZTS0 ++ MZMZTS1 ++ MZMZTS2 ++ MZMZTS3
def MZMZTC1 : List Step := MZMZTS4
theorem MZMZTok0 : chkChunk 15 MZMZTCnf ([]) MZMZTC0 = true := by decide +kernel
theorem MZMZTok1 : chkChunk 15 MZMZTCnf (MZMZTC0) MZMZTC1 = true := by decide +kernel
theorem MZMZTfinal : OKs 15 MZMZTCnf [] [MZMZTC0,MZMZTC1] :=
  ⟨MZMZTok0, ⟨MZMZTok1, trivial⟩⟩
theorem MZMZTempty : [MZMZTC0,MZMZTC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem MZMZTunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ MZMZTCnf, SatCl ρ c := chunks_sound 15 MZMZTCnf _ MZMZTfinal MZMZTempty
end Minimality.H29.SAT.K29
