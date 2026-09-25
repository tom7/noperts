import Noperthedron.test_box_delta200
import Noperthedron.test_flock_lean

open Noperthedron Noperthedron.Nopert229

def b235 : Box := { box200 with δ := 235 / 1000000 }

#eval decide (b235.decomposedBarycentricValid (25 / 1000))
#eval decide (∀ m : Fin 4, (b235.withCoreAxis (flock m) (25 / 1000000) (35 / 10000)).variationRadiusSum 0 + 3 * variationError ≤ (flock m).B * b235.δ)
