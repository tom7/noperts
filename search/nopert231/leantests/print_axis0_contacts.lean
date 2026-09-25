import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

open Noperthedron.Nopert229

def main : IO Unit := do
  let packed ← IO.FS.readFile "local-view0.pack"
  let table := PackedLocalViewTree.decodePackedTable 0 packed
  let row := table.get 3253
  match row with
  | .decomposed _ box _ _ _ _ _ _ _ _ =>
      let ax0 := box.certificate 0
      IO.println "Axis 0 contacts:"
      let fs : List (Fin 3) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]
      for f in fs do
        IO.println s!"  contact {f.val}: e1=({ax0.edgeStart f}->{ax0.edgeFinish f}), e2=({ax0.edgeStart₂ f}->{ax0.edgeFinish₂ f}), mix={ax0.mix f}, v={ax0.index f}"
  | _ => pure ()

