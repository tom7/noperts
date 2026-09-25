import test_flock_lean

open Noperthedron Noperthedron.Nopert229

def b235 : Box := { box260 with δ := 235 / 1000000 }
def b240 : Box := { box260 with δ := 240 / 1000000 }
def b250 : Box := { box260 with δ := 250 / 1000000 }

def main : IO Unit := do
  IO.println s!"b235 bary: {decide (b235.decomposedBarycentricValid (25 / 1000))}"
  IO.println s!"b235 flock: {decide (∀ m : Fin 4, (b235.withCoreAxis (flock m) (25 / 1000000) (35 / 10000)).variationRadiusSum 0 + 3 * variationError ≤ (flock m).B * b235.δ)}"
  IO.println s!"b240 bary: {decide (b240.decomposedBarycentricValid (25 / 1000))}"
  IO.println s!"b240 flock: {decide (∀ m : Fin 4, (b240.withCoreAxis (flock m) (25 / 1000000) (35 / 10000)).variationRadiusSum 0 + 3 * variationError ≤ (flock m).B * b240.δ)}"
  IO.println s!"b250 bary: {decide (b250.decomposedBarycentricValid (25 / 1000))}"
  IO.println s!"b250 flock: {decide (∀ m : Fin 4, (b250.withCoreAxis (flock m) (25 / 1000000) (35 / 10000)).variationRadiusSum 0 + 3 * variationError ≤ (flock m).B * b250.δ)}"
