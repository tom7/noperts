module

public import Minimality.Type16SAT.LratPPPZ

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PPPZC0 : List Step := PPPZS0 ++ PPPZS1 ++ PPPZS2 ++ PPPZS3
theorem PPPZok0 : chkChunk 15 PPPZCnf ([]) PPPZC0 = true := by decide +kernel
theorem PPPZfinal : OKs 15 PPPZCnf [] [PPPZC0] :=
  ⟨PPPZok0, trivial⟩
theorem PPPZempty : [PPPZC0].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PPPZunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PPPZCnf, SatCl ρ c := chunks_sound 15 PPPZCnf _ PPPZfinal PPPZempty
end Minimality.H29.SAT.K29
