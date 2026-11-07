import SeptopertFamily

/-!
Native executable that checks the certificate data of the Septopert family of
height below 7 and, if it is valid, instantiates
`SeptopertFamily.not_isNopert_of_familyHeight_lt_seven`: no integer member
of the family with height below 7 is a nopert.

Usage:
  checkSeptopertFamily [SeptopertFamily/data/leastheight.txt]

The data is untrusted: each line is one certificate (`SeptopertFamily.Cert`)
for a tuple, decoded into a hash table, and `SeptopertFamily.checkAll` is
evaluated natively on it. On success it prints
  instantiated: ∀ x : Fin 5 → ℤ, familyHeight x < 7 → ¬ IsNopert (familyVerts x)
How to regenerate the data: nopert229/out/bottleneck/famcensus/lean/REPORT.md.
-/

open SeptopertFamily

def parseInt (s : String) : IO ℤ :=
  match s.toInt? with
  | some n => pure n
  | none => throw (IO.userError s!"not an integer: {s}")

def parseLine (line : String) : IO (Option (List ℤ × Cert)) := do
  let fs := (line.splitOn " ").filter (· ≠ "")
  if fs.isEmpty || line.startsWith "#" then return none
  let ints (l : List String) : IO (List ℤ) := l.mapM parseInt
  let y ← ints (fs.take 5)
  let rest := fs.drop 6
  match fs[5]? with
  | some "C" =>
      let n ← ints rest
      return some (y, .coplanar (n.getD 0 0) (n.getD 1 0) (n.getD 2 0))
  | some "E" =>
      let v ← ints rest
      return some (y, .hull (v.getD 0 0).toNat (v.getD 1 0) (v.drop 2).toArray)
  | some "R" =>
      let v ← ints (rest.take 11)
      let tri := (rest.getD 11 "").toList.map fun c => c.toNat - '0'.toNat
      return some (y, .passage (v.take 4).toArray ((v.drop 4).take 4).toArray
        (v.getD 8 0) (v.getD 9 0) (v.getD 10 0) tri.toArray)
  | _ => throw (IO.userError s!"bad line: {line}")

def main (args : List String) : IO Unit := do
  let path := args.headD "SeptopertFamily/data/leastheight.txt"
  let t0 ← IO.monoMsNow
  let mut tbl : Table := {}
  for line in ← IO.FS.lines path do
    if let some (y, c) ← parseLine line then
      tbl := tbl.insert y c
  let t1 ← IO.monoMsNow
  IO.println s!"{tbl.size} certificates read in {t1 - t0} ms"
  if h : checkAll tbl = true then
    let t2 ← IO.monoMsNow
    IO.println s!"all tuples in [0, 12]^5 checked in {t2 - t1} ms"
    let _thm : ∀ x : Fin 5 → ℤ, familyHeight x < 7 → ¬ IsNopert (familyVerts x) :=
      not_isNopert_of_familyHeight_lt_seven ⟨tbl, h⟩
    IO.println "instantiated: ∀ x : Fin 5 → ℤ, familyHeight x < 7 → ¬ IsNopert (familyVerts x) (no Septopert-family nopert of height below 7)"
  else
    throw (IO.userError "the certificate check failed")
