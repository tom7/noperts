module

public import Minimality.Type29KSAT.LratZB

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def ZBC0 : List Step := ZBS0 ++ ZBS1 ++ ZBS2 ++ ZBS3
theorem ZBok0 : chkChunk 15 ZBCnf ([]) ZBC0 = true := by decide +kernel
theorem ZBfinal : OKs 15 ZBCnf [] [ZBC0] :=
  ⟨ZBok0, trivial⟩
theorem ZBempty : [ZBC0].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZBunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZBCnf, SatCl ρ c := chunks_sound 15 ZBCnf _ ZBfinal ZBempty
end Minimality.H29.SAT.K29
