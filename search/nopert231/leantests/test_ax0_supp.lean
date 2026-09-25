import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Noperthedron.Nopert229

theorem ax0_supp_zero : ∀ i k, box.supportUpper 0 i k ≤ 0 := by decide +kernel
