import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
open Noperthedron.SnubCube

#eval (List.range 24).foldl (fun acc k =>
  let v : SnubCube.VertexIndex := VertexIndex.ofFin24 ⟨k, by omega⟩
  max acc (box.supportUpper 0 2 v)) 0

