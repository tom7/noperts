module

public import Minimality.Type29KSAT.LratZA

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def ZAC0 : List Step := ZAS0 ++ ZAS1 ++ ZAS2 ++ ZAS3
def ZAC1 : List Step := ZAS4 ++ ZAS5
theorem ZAok0 : chkChunk 15 ZACnf ([]) ZAC0 = true := by decide +kernel
theorem ZAok1 : chkChunk 15 ZACnf (ZAC0) ZAC1 = true := by decide +kernel
theorem ZAfinal : OKs 15 ZACnf [] [ZAC0,ZAC1] :=
  ⟨ZAok0, ⟨ZAok1, trivial⟩⟩
theorem ZAempty : [ZAC0,ZAC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZAunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZACnf, SatCl ρ c := chunks_sound 15 ZACnf _ ZAfinal ZAempty
end Minimality.H29.SAT.K29
