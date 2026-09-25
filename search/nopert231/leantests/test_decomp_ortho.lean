import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

def candidate2CoreAxis : AxisCertificate := {
  edgeStart := fun | 0 => 3 | 1 => 1 | 2 => 10
  edgeFinish := fun | 0 => 2 | 1 => 4 | 2 => 15
  edgeStart₂ := fun | 0 => 2 | 1 => 4 | 2 => 15
  edgeFinish₂ := fun | 0 => 1 | 1 => 8 | 2 => 19
  mix := fun | 0 => ⟨800, by decide⟩ | 1 => ⟨800, by decide⟩ | 2 => ⟨500, by decide⟩
  index := fun | 0 => 2 | 1 => 4 | 2 => 15
  nonzeroWitness := fun | 0 => 9 | 1 => 15 | 2 => 1
  B := 78237223/50000000
}

def dot3 (a b : Fin 3 → ℚ) : ℚ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2

def main : IO Unit := do
  let packed ← IO.FS.readFile "local-view0.pack"
  let table := PackedLocalViewTree.decodePackedTable 0 packed
  let row := table.get 3253
  match row with
  | .decomposed _ box _ _ _ _ _ _ _ _ =>
      let d26_delta : ℚ := 38/1000000000
      let c_val : ℚ := 1/10000
      let c_cone_val : ℚ := 3/200 -- 0.015
      let testBox : Box := { box with c := c_val, δ := d26_delta }

      let c_core_val : ℚ := 1/10000
      let r_min_val : ℚ := 1/8000
      let coreBox := testBox.withCoreAxis candidate2CoreAxis c_core_val r_min_val

      let u := testBox.approxNormalizedCenter 0
      let v := coreBox.approxNormalizedCenter 0

      let u_dot_u := dot3 u u
      let v_dot_u := dot3 v u
      let lam := v_dot_u / u_dot_u
      let w : Fin 3 → ℚ := fun i => v i - lam * u i
      let w_dot_w := dot3 w w

      IO.println s!"u_dot_u = {u_dot_u}"
      IO.println s!"v_dot_u = {v_dot_u}"
      IO.println s!"lam = {lam}"
      IO.println s!"w_dot_u = {dot3 w u}"
      IO.println s!"w_dot_w = {w_dot_w}"

      let hortho := (dot3 u w == 0)
      IO.println s!"hortho: {hortho}"

      let hdecomp := (v 0 == lam * u 0 + w 0) && (v 1 == lam * u 1 + w 1) && (v 2 == lam * u 2 + w 2)
      IO.println s!"hdecomp: {hdecomp}"

      let hmargin := decide (0 ≤ lam * c_cone_val - c_core_val)
      IO.println s!"hmargin: {hmargin} (val = {lam * c_cone_val - c_core_val})"

      let lhs := w_dot_w * (u_dot_u - c_cone_val^2)
      let rhs := u_dot_u * (lam * c_cone_val - c_core_val)^2
      let hineq := decide (lhs ≤ rhs)
      IO.println s!"hineq: {hineq}"
      IO.println s!"  lhs = {lhs}"
      IO.println s!"  rhs = {rhs}"

  | _ => IO.println "Not decomposed"

