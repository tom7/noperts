module

public import Minimality.Type16SAT.LratPZMZT

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PZMZTC0 : List Step := PZMZTS0 ++ PZMZTS1 ++ PZMZTS2
theorem PZMZTok0 : chkChunk 15 PZMZTCnf ([]) PZMZTC0 = true := by decide +kernel
theorem PZMZTfinal : OKs 15 PZMZTCnf [] [PZMZTC0] :=
  ⟨PZMZTok0, trivial⟩
theorem PZMZTempty : [PZMZTC0].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PZMZTunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PZMZTCnf, SatCl ρ c := chunks_sound 15 PZMZTCnf _ PZMZTfinal PZMZTempty
end Minimality.H29.SAT.K29
