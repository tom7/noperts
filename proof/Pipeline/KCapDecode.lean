module

public import Pipeline.KCapTree
public import Pipeline.TribQ
public import ParallelBool

@[expose] public section

/-!
# Decoding balanced cap certificates over ℚ(t) (untrusted)

`decodeKCert` reads a `search/sc/sccapcert.cc --export` file into a
`KCert TribQ`. Nothing here is trusted: the decoded certificate is checked
(`KCert.check`, or `KCert.checkPar` with the charts as native tasks) before
its claims are used.
-/

namespace Noperts.Pipeline

namespace KCap

/-! ### Parallel check -/

variable {K : Type} [ExactScalarOps K]

/-- The subtrees at depth d (or the leaves above it), with their boxes. -/
def KTree.frontier : ℕ → KTree → Box → List (KTree × Box)
  | d + 1, .split a l r, box => l.frontier d (half box a false) ++ r.frontier d (half box a true)
  | _, t, box => [(t, box)]

theorem KTree.check_of_frontier (leafOk : Leaf → Box → Bool) (coneOk : Box → Bool) :
    ∀ (d : ℕ) (t : KTree) (box : Box), (∀ e ∈ t.frontier d box, e.1.check leafOk coneOk e.2 = true) →
      t.check leafOk coneOk box = true
  | 0, t, box, h => h (t, box) (by cases t <;> simp [KTree.frontier])
  | d + 1, .split a l r, box, h => by
    simp only [KTree.frontier, List.mem_append] at h
    simp only [KTree.check, Bool.and_eq_true]
    exact ⟨KTree.check_of_frontier leafOk coneOk d l _ (fun e he => h e (Or.inl he)),
      KTree.check_of_frontier leafOk coneOk d r _ (fun e he => h e (Or.inr he))⟩
  | _ + 1, .leaf w, box, h => h (.leaf w, box) (by simp [KTree.frontier])
  | _ + 1, .cone, box, h => h (.cone, box) (by simp [KTree.frontier])
  | _ + 1, .fail, box, h => h (.fail, box) (by simp [KTree.frontier])

/-- The chart entry for `id` (the first). -/
def KCert.entry (c : KCert K) (id : ChartId) : Option KTree :=
  (c.charts.find? fun e => decide (e.1 = id)).map (·.2)

/-- The work items: per required chart, the frontier of its tree at depth 16. -/
def KCert.items (c : KCert K) : Array (ChartId × KTree × Box) :=
  (requiredCharts.flatMap fun id =>
    match c.entry id with
    | some t => (t.frontier 16 (rootBox c id)).map fun e => (id, e.1, e.2)
    | none => []).toArray

def KCert.itemPred (c : KCert K) (i : ℕ) : Bool :=
  match c.items[i]? with
  | some (id, t, box) =>
    t.check (fun l b => l.check c.V (chartData c.fr c.pr id c.V) id b) (coneOk c id) box
  | none => true

/-- `KCert.check` with the trees' frontier subtrees checked as native tasks. -/
def KCert.checkPar (c : KCert K) : Bool :=
  c.paramsOk && c.frameOk && requiredCharts.all (fun id => (c.entry id).isSome) &&
    ParallelBool.allParB c.itemPred c.items.size 256

theorem KCert.check_of_par (c : KCert K) (h : c.checkPar = true) : c.check = true := by
  simp only [KCert.checkPar, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hp, hf⟩, hsome⟩, hpar⟩ := h
  have hall := ParallelBool.all_of_parB hpar
  simp only [KCert.check, Bool.and_eq_true, hp, hf, true_and, List.all_eq_true]
  intro id hid
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hsome id hid)
  -- The entry: a chart of the certificate with this id.
  have hent : ∃ e ∈ c.charts, e.1 = id ∧ e.2 = t := by
    unfold KCert.entry at ht
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp ht
    exact ⟨e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he, rfl⟩
  obtain ⟨e, hemem, he1, he2⟩ := hent
  unfold KCert.hasChart
  rw [List.any_eq_true]
  refine ⟨e, hemem, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨he1, ?_⟩
  rw [he1, he2]
  unfold KCert.chartCheck
  apply KTree.check_of_frontier _ _ 16
  intro f hf
  -- f is an item of c.items.
  have hmem : (id, f.1, f.2) ∈ c.items.toList := by
    simp only [KCert.items, List.mem_flatMap]
    exact ⟨id, hid, by rw [ht]; exact List.mem_map.mpr ⟨f, hf, rfl⟩⟩
  obtain ⟨i, hi, hfi⟩ := List.getElem_of_mem hmem
  have hi' : i < c.items.size := by simpa using hi
  have := hall i hi'
  unfold KCert.itemPred at this
  have hget : c.items[i]? = some (id, f.1, f.2) := by
    rw [Array.getElem?_eq_getElem hi', ← hfi]
    simp
  rw [hget] at this
  exact this

/-! ### Untrusted decoding -/

def parseQ (s : String) : ℚ :=
  match s.splitOn "/" with
  | [n] => (n.toInt?.getD 0 : ℚ)
  | [n, d] => (n.toInt?.getD 0 : ℚ) / (d.toNat?.getD 1 : ℚ)
  | _ => 0

def tokens (l : String) : Array String := ((l.splitOn " ").filter (· ≠ "")).toArray

def parseT (t : Array String) (i : ℕ) : TribQ := ⟨parseQ t[i]!, parseQ t[i+1]!, parseQ t[i+2]!⟩

def parseTV (t : Array String) (i : ℕ) : KVec TribQ := ![parseT t i, parseT t (i+3), parseT t (i+6)]

instance : Inhabited TribQ := ⟨TribQ.zero⟩

/-- A leaf line: `l K s` then per contact `a b n S_1 … S_n`, then the tuple count and the
inner choices (K per tuple). -/
def parseLeaf (t : Array String) : Leaf := Id.run do
  let K := t[1]!.toNat!
  let s := parseQ t[2]!
  let mut i := 3
  let mut edges : Array (ℕ × ℕ) := #[]
  let mut outer : Array (List ℕ) := #[]
  for _ in [0:K] do
    let a := t[i]!.toNat!
    let b := t[i+1]!.toNat!
    let n := t[i+2]!.toNat!
    edges := edges.push (a, b)
    outer := outer.push ((List.range n).map fun j => t[i+3+j]!.toNat!)
    i := i + 3 + n
  let nt := t[i]!.toNat!
  i := i + 1
  let mut inner : Array (List ℕ) := #[]
  for _ in [0:nt] do
    inner := inner.push ((List.range K).map fun k => t[i+k]!.toNat!)
    i := i + K
  return ⟨s, edges.toList, outer.toList, inner.toList⟩

/-- A preorder tree, one node per line from `i`: `s <axis>`, `l …`, `c` (cone), `f` (fail). -/
partial def parseTree (lines : Array (Array String)) (i : ℕ) : KTree × ℕ :=
  let t := lines[i]!
  match t[0]! with
  | "s" =>
    let a := t[1]!.toNat!
    let (l, j) := parseTree lines (i + 1)
    let (r, k) := parseTree lines j
    (.split ⟨a % 5, Nat.mod_lt _ (by norm_num)⟩ l r, k)
  | "l" => (.leaf (parseLeaf t), i + 1)
  | "c" => (.cone, i + 1)
  | _ => (.fail, i + 1)

def kindOfNat : ℕ → Kind
  | 0 => .fe
  | 1 => .face
  | 2 => .cone
  | _ => .tcone

/-- Decodes a `sccapcert --export` file. -/
def decodeKCert (lines : Array String) : KCert TribQ := Id.run do
  let toks := lines.map tokens
  let mut V : Array (KVec TribQ) := #[]
  let zero : KVec TribQ := fun _ => TribQ.zero
  let mut fx := zero
  let mut fe1 := zero
  let mut fe2 := zero
  let mut fZ := zero
  let mut fE1 := zero
  let mut fX := zero
  let mut pr : Params := ⟨0, 0, 0, 0, 0⟩
  let mut mu0 : ℚ := 0
  let mut tieMu0 : ℚ := 0
  let mut charts : Array (ChartId × KTree) := #[]
  let mut i := 0
  while i < toks.size do
    let t := toks[i]!
    if t.size == 0 then
      i := i + 1
      continue
    match t[0]! with
    | "v" => V := V.push (parseTV t 1); i := i + 1
    | "frame" =>
      let v := parseTV t 2
      match t[1]! with
      | "x" => fx := v
      | "e1" => fe1 := v
      | "e2" => fe2 := v
      | "Z" => fZ := v
      | "E1" => fE1 := v
      | _ => fX := v
      i := i + 1
    | "param" =>
      mu0 := parseQ t[1]!
      pr := ⟨parseQ t[2]!, parseQ t[3]!, t[4]!.toNat!, parseQ t[5]!, parseQ t[6]!⟩
      tieMu0 := parseQ t[7]!
      i := i + 1
    | "chart" =>
      let id : ChartId := ⟨kindOfNat t[1]!.toNat!, t[2]!.toNat!, t[3]!.toNat!, t[4]! == "1"⟩
      let (tree, j) := parseTree toks (i + 1)
      charts := charts.push (id, tree)
      i := j
    | _ => i := i + 1
  return { V, fr := ⟨fx, fe1, fe2, fZ, fE1, fX⟩, pr, mu0, tieMu0, charts := charts.toList }

end KCap

end Noperts.Pipeline

end
