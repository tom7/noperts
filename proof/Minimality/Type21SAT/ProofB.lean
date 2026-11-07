module

public import Minimality.Type21SAT.LratB

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H21.SAT.K3
def BC0 : List Step := BS0 ++ BS1 ++ BS2
def BC1 : List Step := BS3 ++ BS4 ++ BS5
def BC2 : List Step := BS6 ++ BS7 ++ BS8
def BC3 : List Step := BS9 ++ BS10 ++ BS11
theorem Bok0 : chkChunk 15 BCnf ([]) BC0 = true := by decide +kernel
theorem Bok1 : chkChunk 15 BCnf (BC0) BC1 = true := by decide +kernel
theorem Bok2 : chkChunk 15 BCnf (BC0 ++ BC1) BC2 = true := by decide +kernel
theorem Bok3 : chkChunk 15 BCnf (BC0 ++ BC1 ++ BC2) BC3 = true := by decide +kernel
theorem Bfinal : OKs 15 BCnf [] [BC0,BC1,BC2,BC3] :=
  ⟨Bok0, ⟨Bok1, ⟨Bok2, ⟨Bok3, trivial⟩⟩⟩⟩
theorem Bempty : [BC0,BC1,BC2,BC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Bunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ BCnf, SatCl ρ c := chunks_sound 15 BCnf _ Bfinal Bempty
end Minimality.H21.SAT.K3
