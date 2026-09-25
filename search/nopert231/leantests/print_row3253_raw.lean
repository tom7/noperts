import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

def main : IO Unit := do
  let packed ← IO.FS.readFile "local-view0.pack"
  let table := PackedLocalViewTree.decodePackedTable 0 packed
  let row := table.get 3253
  match row with
  | .decomposed id box coreAxis defect0 D0 r_min c_cone c_core lam w =>
      IO.println s!"id: {id}"
      let p0 := box.triangle 0
      let p1 := box.triangle 1
      let p2 := box.triangle 2
      IO.println s!"box.triangle: corners = ({p0 0}, {p0 1}, {p0 2}), ({p1 0}, {p1 1}, {p1 2}), ({p2 0}, {p2 1}, {p2 2})"
      IO.println s!"box.r: {box.r}"
      IO.println s!"box.c: {box.c}"
      IO.println s!"box.δ: {box.δ}"
      IO.println s!"D0: {D0}"
      IO.println s!"r_min: {r_min}"
      IO.println s!"c_cone: {c_cone}"
      IO.println s!"c_core: {c_core}"
      IO.println s!"lam: {lam}"
      IO.println s!"w: ({w 0}, {w 1}, {w 2})"
      for j in ([⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩] : List (Fin 4)) do
        let cert := box.certificate j
        IO.println s!"axis {j}: B = {cert.B}, nonzeroWitness = ({cert.nonzeroWitness 0}, {cert.nonzeroWitness 1}, {cert.nonzeroWitness 2})"
      IO.println s!"coreAxis: B = {coreAxis.B}"
  | _ => IO.println "Not decomposed"

