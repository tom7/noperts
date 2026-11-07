module

public import Pipeline.ArcCapClaim
public import Pipeline.KCapDecode

@[expose] public section

/-!
# Arc cap certificates: decoding and the parallel check (untrusted decoding)

`decodeCert` reads the charts of `capcert-neo --export` (`exportall.sh` concatenates
the pieces): per chart a line `chart u <side> <kind> <axis> <sign>` or
`chart w <piece> <kind> <a> <b> <c>`, then the tree in preorder as for
`KCap.parseTree`. Nothing here is trusted: `certCheckPar` is `certCheck` with the
frontier subtrees of every chart as native tasks (`certCheck_of_par`).
-/

namespace Noperts.Pipeline

namespace ArcCap

open Noperts.Pipeline.KCap

variable {K : Type} [ExactScalarOps K]

/-- The chart entry for `id` (the first). -/
def entry (c : Cert) (id : ChartId) : Option KTree :=
  (c.find? fun e => decide (e.1 = id)).map (·.2)

/-- The work items: per required chart its data, computed once, and the frontier of its tree. -/
def items (req : List ChartId) (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (c : Cert) :
    Array (ChartId × ChartData K × KTree × Box) :=
  (req.flatMap fun id =>
    match entry c id with
    | some t =>
      let cd := chartCd V fr pr id
      (t.frontier 12 (rootBox pr id)).map fun e => (id, cd, e.1, e.2)
    | none => []).toArray

def itemOk (V : Array (KCap.KVec K)) (pr : Params) (it : ChartId × ChartData K × KTree × Box) : Bool :=
  it.2.2.1.check (fun l b => l.checkBy V (red it.1) it.2.1 b) (coneOk pr it.1) it.2.2.2

def certCheckParOn (req : List ChartId) (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (c : Cert) : Bool :=
  let its := items req V fr pr c
  req.all (fun id => (entry c id).isSome) &&
    ParallelBool.allParB (fun i => match its[i]? with
      | some it => itemOk V pr it
      | none => true) its.size 512

def certCheckPar (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (c : Cert) : Bool :=
  certCheckParOn requiredCharts V fr pr c

theorem certCheckOn_of_par (req : List ChartId) (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (c : Cert)
    (h : certCheckParOn req V fr pr c = true) : certCheckOn req V fr pr c = true := by
  simp only [certCheckParOn, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hsome, hpar⟩ := h
  have hall := ParallelBool.all_of_parB hpar
  simp only [certCheckOn, List.all_eq_true]
  intro id hid
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hsome id hid)
  have hent : ∃ e ∈ c, e.1 = id ∧ e.2 = t := by
    unfold entry at ht
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp ht
    exact ⟨e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he, rfl⟩
  obtain ⟨e, hemem, he1, he2⟩ := hent
  rw [List.any_eq_true]
  refine ⟨e, hemem, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨he1, ?_⟩
  rw [he2]
  unfold chartCheck
  apply KTree.check_of_frontier _ _ 12
  intro f hf
  have hmem : (id, chartCd V fr pr id, f.1, f.2) ∈ (items req V fr pr c).toList := by
    simp only [items, List.toList_toArray, List.mem_flatMap]
    exact ⟨id, hid, by rw [ht]; exact List.mem_map.mpr ⟨f, hf, rfl⟩⟩
  obtain ⟨i, hi, hfi⟩ := List.getElem_of_mem hmem
  have hi' : i < (items req V fr pr c).size := by simpa using hi
  have := hall i hi'
  have hget : (items req V fr pr c)[i]? = some (id, chartCd V fr pr id, f.1, f.2) := by
    rw [Array.getElem?_eq_getElem hi', ← hfi]
    simp
  rw [hget] at this
  exact this

theorem certCheck_of_par (V : Array (KCap.KVec K)) (fr : Frame K) (pr : Params) (c : Cert)
    (h : certCheckPar V fr pr c = true) : certCheck V fr pr c = true :=
  certCheckOn_of_par _ V fr pr c h

/-! ### Untrusted decoding -/

/-- Adds the blends to every leaf of a tree. -/
def withBlends (bl : List (ℕ × ℕ × ℚ)) : KTree → KTree
  | .split a l r => .split a (withBlends bl l) (withBlends bl r)
  | .leaf w => .leaf { w with blends := bl }
  | t => t

def s1OfNat : ℕ → S1
  | 0 => .i
  | 1 => .p
  | _ => .m

def pieceOfNat : ℕ → Piece
  | 0 => .w0
  | 1 => .wm
  | 2 => .w1
  | _ => .w2

def parseId (t : Array String) : ChartId :=
  let n : ℕ → ℕ := fun i => t[i]!.toNat!
  let b : ℕ → Bool := fun i => n i == 1
  if t[1]! == "u" then
    -- the side: 1 and 0 are the sides 0 and 3 of `capcert-neo`, 2 and 3 the sides 1 and 2
    .u (match n 2 with | 1 => 0 | 0 => 3 | 2 => 1 | _ => 2) (match n 3 with
      | 0 => .fe
      | 1 => .face (n 4) (b 5)
      | _ => .cone (n 4) (b 5))
  else
    .w (pieceOfNat (n 2)) (match n 3 with
      | 0 => .fe (b 4) (b 5)
      | 1 => .cone (b 4) (n 5) (b 6)
      | 2 => .face0 (b 4)
      | 3 => .face1 (s1OfNat (n 5)) (b 4)
      | _ => .face2 (s1OfNat (n 5)) (b 4))

/-- Decodes the concatenated `--export` files. -/
def decodeCert (bl : List (ℕ × ℕ × ℚ)) (lines : Array String) : Cert := Id.run do
  let toks := lines.map tokens
  let mut charts : Array (ChartId × KTree) := #[]
  let mut i := 0
  while i < toks.size do
    let t := toks[i]!
    if t.size == 0 then
      i := i + 1
      continue
    if t[0]! == "chart" then
      let (tree, j) := parseTree toks (i + 1)
      charts := charts.push (parseId t, withBlends bl tree)
      i := j
    else
      i := i + 1
  return charts.toList

end ArcCap

end Noperts.Pipeline

end
