module

public import Noperthedron.Nopert7.Caps
public import Noperthedron.ParallelBool

@[expose] public section

/-!
# Native checking of the 7-vertex solid's cap certificate

`capCheckPar` is `CapCert.check` with the chart trees checked as parallel
native tasks (`ParallelBool.allParB`); `check_of_par` recovers the sequential
check, so a native run proves `certOk` (`certOk_of_par`) and hence the cap
(`capHolds_of_cert`, `cap_not_rupert`).

`decodeCert` reads a `capcert7 --export` file. Nothing in the decoding is
trusted: the decoded certificate is checked before it is used (its chart list
against Lean's `chartList`, its frame, μ₀, vertices and half-turn element
against `certOk`'s constants, every tree with Lean's own Bernstein bounds).
-/

namespace Noperthedron.Nopert7

open Noperthedron.PentagonalHexecontahedron
open Noperthedron.PentagonalHexecontahedron.Cap

def chartPred (c : CapCert) (i : ℕ) : Bool :=
  match c.charts[i]? with
  | some e => chartCheck c e.1 e.2
  | none => true

/-- `CapCert.check` with the chart trees checked in parallel. -/
def capCheckPar (c : CapCert) : Bool :=
  decide (0 < c.verts.size) && c.zList.all (fun e => decide (0 < e.2)) && Cap.frameCheck c.st &&
    (c.charts.map (·.1) == chartList c.st c.pr c.zOf) &&
    ParallelBool.allParB (chartPred c) c.charts.length c.charts.length && c.tieCheck

theorem check_of_par (c : CapCert) (h : capCheckPar c = true) : c.check = true := by
  simp only [capCheckPar, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hV, hz⟩, hF⟩, hlist⟩, hpar⟩, htc⟩ := h
  have hall := ParallelBool.all_of_parB hpar
  simp only [CapCert.check, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨hV, hz⟩, hF⟩, hlist⟩, ?_⟩, htc⟩
  rw [List.all_eq_true]
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  have := hall i hi
  simpa [chartPred, List.getElem?_eq_getElem hi] using this

/-- `certOk` with the parallel check. -/
def certOkPar (c : CapCert) : Bool :=
  capCheckPar c && decide (c.st.strongScale = 2) && decide (1 ≤ c.st.mcm) && decide (c.st.x = capX) &&
    decide (c.st.e1 = capE1) && decide (c.st.e2 = capE2) && decide (c.pr.mu0 = capMu0) &&
    decide (c.verts = solidVerts) && c.usePrune && decide (c.Gcol = capGcol)

theorem certOk_of_par (c : CapCert) (h : certOkPar c = true) : certOk c = true := by
  unfold certOkPar at h
  unfold certOk
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hc, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨check_of_par c hc, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩

/-! ### Untrusted decoding -/

instance : Inhabited IcoQ := ⟨IcoQ.zero⟩
instance : Inhabited Kind := ⟨.fe⟩

def parseQ (s : String) : ℚ :=
  match s.splitOn "/" with
  | [n] => (n.toInt?.getD 0 : ℚ)
  | [n, d] => (n.toInt?.getD 0 : ℚ) / (d.toNat?.getD 1 : ℚ)
  | _ => 0

def parseK (t : Array String) (i : ℕ) : IcoQ := ⟨parseQ t[i]!, parseQ t[i+1]!, parseQ t[i+2]!, parseQ t[i+3]!⟩
def parseKV (t : Array String) (i : ℕ) : KVec := ![parseK t i, parseK t (i+4), parseK t (i+8)]

def tokens (l : String) : Array String := ((l.splitOn " ").filter (· ≠ "")).toArray

/-- A preorder certificate tree: `S<axis>` split, `L<w>,` witness leaf, `P` prune, `X` cone, `F` fail. -/
partial def parseTree (s : Array Char) (i : ℕ) : CTree × ℕ :=
  match s[i]! with
  | 'S' => let a := s[i+1]!.toNat - '0'.toNat
           let (l, j) := parseTree s (i+2)
           let (r, k) := parseTree s j
           (.split ⟨a % 5, Nat.mod_lt _ (by norm_num)⟩ l r, k)
  | 'L' => Id.run do
           let mut j := i + 1
           let mut n := 0
           while s[j]! != ',' do
             n := n * 10 + (s[j]!.toNat - '0'.toNat)
             j := j + 1
           return (.leaf n, j + 1)
  | 'P' => (.prune, i + 1)
  | 'X' => (.cone, i + 1)
  | _ => (.fail, i + 1)

def kindOf (s : String) : Kind := match s with | "Fe" => .fe | "cone" => .cone | "Mcone" => .mcone | _ => .face

/-- Decodes a `capcert7 --export` file (`witness i k k' c`). Without ratio blow-ups capcert7 exports
z = 0, which no polynomial or box uses (ratio 0); it is read as 1 (`CapCert.check` wants z > 0). -/
def decodeCert (lines : Array String) : CapCert := Id.run do
  let mut V : Array KVec := #[]
  let mut W : Array (ℕ × ℕ × KVec) := #[]
  let mut x : KVec := fun _ => IcoQ.zero
  let mut e1 := x
  let mut e2 := x
  let mut aniso := false
  let mut halfTurn := false
  let mut tie := false
  let mut ratioOn := false
  let mut mu0 : ℚ := 0
  let mut sscale := 2
  let mut t0 : ℚ := 1/4
  let mut t0m : ℚ := 1/4
  let mut mcm : ℕ := 1
  let mut charts : Array (ChartId × CTree) := #[]
  let mut zl : List ((Kind × ℕ × ℕ × Bool) × ℕ) := []
  let mut tieCharts : List ((Kind × ℕ × ℕ × Bool) × (ℕ × ℕ × ℕ)) := []
  let mut pending : Option ChartId := none
  for l in lines do
    let t := tokens l
    if t.size == 0 then continue
    match t[0]! with
    | "cap" => aniso := t[3]! == "1"; halfTurn := t[5]! == "1"; tie := t[7]! == "1"; mu0 := parseQ t[9]!
               sscale := t[11]!.toNat!; t0 := parseQ t[13]!
               ratioOn := t[15]!.toNat! > 0 || t[17]!.toNat! > 0
               if t.size > 19 then t0m := parseQ t[19]!; mcm := t[21]!.toNat!
    | "frame" => x := parseKV t 1; e1 := parseKV t 13; e2 := parseKV t 25
    | "tie_chart" =>
      tieCharts := tieCharts ++ [((kindOf t[1]!, t[2]!.toNat!, t[3]!.toNat!, t[4]! == "1"),
        (t[5]!.toNat!, t[6]!.toNat!, t[7]!.toNat!))]
    | "vertex" => V := V.push (parseKV t 2)
    | "witness" => W := W.push (t[2]!.toNat!, t[3]!.toNat!, parseKV t 4)
    | "chart" =>
      let id : ChartId := ⟨kindOf t[1]!, t[2]!.toNat!, t[3]!.toNat!, t[4]! == "1", t[5]!.toNat!, t[6]!.toNat!,
        t[7]! == "1", max 1 t[9]!.toNat!⟩
      pending := some id
      let b := (id.kind, id.side, id.axis, id.sign)
      if !(zl.any (fun e => e.1 == b)) then zl := zl ++ [(b, id.z)]
    | "tree" => match pending with
      | some id => charts := charts.push (id, (parseTree t[1]!.toList.toArray 0).1); pending := none
      | none => pure ()
    | _ => pure ()
  return { st := { aniso, halfTurn, strongScale := sscale, mcm, x, e1, e2, tieCharts },
           pr := ⟨mu0, t0, t0m, tie, ratioOn⟩, zList := zl, verts := V, wits := W, usePrune := halfTurn,
           Gcol := capGcol, charts := charts.toList }

end Noperthedron.Nopert7
