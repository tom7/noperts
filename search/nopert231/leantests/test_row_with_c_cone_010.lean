import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

-- Complement axes from triple (64, 77, 266):
def ax1_64 : AxisCertificate := {
  edgeStart := fun | 0 => 18 | 1 => 9 | 2 => 10
  edgeFinish := fun | 0 => 1 | 1 => 10 | 2 => 15
  edgeStart₂ := fun | 0 => 1 | 1 => 10 | 2 => 15
  edgeFinish₂ := fun | 0 => 5 | 1 => 15 | 2 => 19
  mix := fun | 0 => ⟨200, by decide⟩ | 1 => ⟨270, by decide⟩ | 2 => ⟨200, by decide⟩
  index := fun | 0 => 1 | 1 => 10 | 2 => 15
  nonzeroWitness := fun | 0 => 15 | 1 => 1 | 2 => 4
  B := 888108627 / 1000000000
}

def ax2_77 : AxisCertificate := {
  edgeStart := fun | 0 => 15 | 1 => 5 | 2 => 15
  edgeFinish := fun | 0 => 19 | 1 => 8 | 2 => 19
  edgeStart₂ := fun | 0 => 19 | 1 => 8 | 2 => 19
  edgeFinish₂ := fun | 0 => 3 | 1 => 9 | 2 => 3
  mix := fun | 0 => ⟨290, by decide⟩ | 1 => ⟨600, by decide⟩ | 2 => ⟨600, by decide⟩
  index := fun | 0 => 19 | 1 => 8 | 2 => 19
  nonzeroWitness := fun | 0 => 8 | 1 => 19 | 2 => 4
  B := 13977267 / 100000000
}

def ax3_266 : AxisCertificate := {
  edgeStart := fun | 0 => 3 | 1 => 2 | 2 => 14
  edgeFinish := fun | 0 => 2 | 1 => 1 | 2 => 15
  edgeStart₂ := fun | 0 => 2 | 1 => 1 | 2 => 15
  edgeFinish₂ := fun | 0 => 1 | 1 => 5 | 2 => 19
  mix := fun | 0 => ⟨130, by decide⟩ | 1 => ⟨420, by decide⟩ | 2 => ⟨800, by decide⟩
  index := fun | 0 => 2 | 1 => 1 | 2 => 15
  nonzeroWitness := fun | 0 => 9 | 1 => 15 | 2 => 1
  B := 232020949 / 500000000
}

def main : IO Unit := do
  let packed ← IO.FS.readFile "local-view0.pack"
  let table := PackedLocalViewTree.decodePackedTable 0 packed
  let row := table.get 3253
  match row with
  | .decomposed _ box _ _ D0 r_min _ _ _ _ =>
      let newBox : Box := { box with
        certificate := fun
          | 0 => box.certificate 0
          | 1 => ax1_64
          | 2 => ax2_77
          | 3 => ax3_266
        c := 1 / 10000000  -- 1e-7
      }
      IO.println s!"box.triangle: {repr box.triangle}"
      let cc : ℚ := 8 / 1000
      IO.println s!"Testing cc = {cc}:"
      IO.println s!"bary: {decide (newBox.decomposedBarycentricValid cc)}"
      let B0 := (newBox.certificate 0).B
      let r := newBox.r
      let delta := newBox.δ
      let lhs := ((1/2 : ℚ) * r ^ 2 * B0 + D0) ^ 2
      let rhs := r_min ^ 2 * (1 - (1/4 : ℚ) * r ^ 2) * ((cc - delta) ^ 2 * B0 ^ 2)
      IO.println s!"annular dominance: {decide (lhs ≤ rhs)}"
      IO.println s!"lhs = {lhs}"
      IO.println s!"rhs = {rhs}"
  | _ => IO.println "Not decomposed!"
