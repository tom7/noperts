import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

def compAxis1 : AxisCertificate := {
  edgeStart := ![2, 10, 3]
  edgeFinish := ![1, 15, 2]
  edgeStart₂ := ![1, 15, 2]
  edgeFinish₂ := ![4, 19, 1]
  mix := ![⟨500, by decide⟩, ⟨666, by decide⟩, ⟨0, by decide⟩]
  index := ![1, 15, 2]
  nonzeroWitness := ![15, 1, 10]
  B := 384025501/1000000000
}

def compAxis2 : AxisCertificate := {
  edgeStart := ![3, 8, 3]
  edgeFinish := ![2, 9, 2]
  edgeStart₂ := ![2, 9, 2]
  edgeFinish₂ := ![1, 10, 1]
  mix := ![⟨500, by decide⟩, ⟨200, by decide⟩, ⟨666, by decide⟩]
  index := ![2, 9, 2]
  nonzeroWitness := ![9, 2, 9]
  B := 3000813/100000000
}

def compAxis3 : AxisCertificate := {
  edgeStart := ![2, 1, 10]
  edgeFinish := ![1, 4, 15]
  edgeStart₂ := ![1, 4, 15]
  edgeFinish₂ := ![4, 8, 19]
  mix := ![⟨333, by decide⟩, ⟨800, by decide⟩, ⟨200, by decide⟩]
  index := ![1, 4, 15]
  nonzeroWitness := ![15, 15, 4]
  B := 31818461/125000000
}

def main : IO Unit := do
  let packed ← IO.FS.readFile "local-view0.pack"
  let table := PackedLocalViewTree.decodePackedTable 0 packed
  let row := table.get 3253
  match row with
  | .decomposed _ box _ _ _ _ _ _ _ _ =>
      let newCerts : Fin 4 → AxisCertificate := fun j =>
        match j with
        | 0 => box.certificate 0
        | 1 => compAxis1
        | 2 => compAxis2
        | 3 => compAxis3
      let testBox : Box := { box with certificate := newCerts, c := 1/10000, δ := 4/10000000 }
      let c_cone_val : ℚ := 1/100
      IO.println s!"det = {LocalCertificate.tetraDetQ (testBox.decomposedCenter c_cone_val)}"
      for k in ([⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩] : List (Fin 6)) do
        let b := testBox.decomposedBarycentric c_cone_val k
        IO.println s!"Target {k}: b = ({b 0}, {b 1}, {b 2}, {b 3})"
  | _ => IO.println "Not decomposed"

