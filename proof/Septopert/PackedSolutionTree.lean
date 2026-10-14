module

public import Septopert.SolutionTree
public import Pipeline.PackedLocalViewTree

@[expose] public section

/-!
# Packed chart tables for the 7-vertex solid

The `PackedSolutionTree` decoder of the icosahedral solids, for the
Septopert's packs (written by `pack5d`): the layout is unchanged; every
region's `root, triangleIndex` pair carries the job's projective root (0 or
1); tag 13 is the C3 prune (neighbor n ∈ {0,1}: c3Mat (n+1)), tag 14 the
mirror prune (element g: mirrorQMat g), tag 16 a cap leaf; tags 0 (viewRoot),
8 (fundamentalPrune) and 15 (tieLeaf) are not part of the Septopert's trees
and decode to `radiusPrune` rows (which the checker rejects unless the box is outside the
Cayley ball). Per-code packs (`pack5d --per_code`) are concatenated behind a
`codeRoot` row over `AtlasPose.rootInterval` (all four charts).

The decoder is untrusted plumbing: every decoded row is checked by
`SolutionTree.Table.Valid`.
-/

namespace Septopert.PackedSolutionTree
open Noperts

open Noperts.Pipeline
open SolutionTree AtlasProjectiveView
open AtlasProjectiveEdgeCertificate AtlasProjectiveGlobalCertificate
open AtlasProjectiveLocalCertificate
open PackedLocalViewTree
open Noperts.Atlas.ProjectiveView

abbrev Decoder := PackedLocalViewTree.Decoder

def relativeInterval (center radius : Fin 3 → ℚ) : SolutionTree.Interval :=
  AtlasInterval.mk
    { θ := 0, φ := 0,
      x := center 0 - |radius 0|,
      y := center 1 - |radius 1|,
      z := center 2 - |radius 2| }
    { θ := 8 / 5, φ := 4,
      x := center 0 + |radius 0|,
      y := center 1 + |radius 1|,
      z := center 2 + |radius 2| }
    (by
      rw [AtlasPose.le_iff]
      exact ⟨by norm_num, by norm_num,
        by linarith [abs_nonneg (radius 0)],
        by linarith [abs_nonneg (radius 1)],
        by linarith [abs_nonneg (radius 2)]⟩)

def readInterval : Decoder SolutionTree.Interval := do
  let cx ← readRat
  let cy ← readRat
  let cz ← readRat
  let wx ← readRat
  let wy ← readRat
  let wz ← readRat
  pure (relativeInterval ![cx, cy, cz] ![wx, wy, wz])

def readTriangle : Decoder SolutionTree.Triangle := do
  let a0 ← readRat
  let a1 ← readRat
  let a2 ← readRat
  let b0 ← readRat
  let b1 ← readRat
  let b2 ← readRat
  let c0 ← readRat
  let c1 ← readRat
  let c2 ← readRat
  pure ![![a0, a1, a2], ![b0, b1, b2], ![c0, c1, c2]]

def readMany {α : Type} (readOne : Decoder α) : Nat → Array α → Decoder (Array α)
  | 0, values => pure values
  | count + 1, values => do
      let value ← readOne
      readMany readOne count (values.push value)

def readNats : Nat → Array Nat → Decoder (Array Nat)
  | 0, values => pure values
  | count + 1, values => do
      let value ← readNat
      readNats count (values.push value)

def intervalAt (intervals : Array SolutionTree.Interval) (index : Nat) : SolutionTree.Interval :=
  (intervals[index]?).getD (AtlasPose.rootInterval ℚ)

def triangleAt (triangles : Array SolutionTree.Triangle) (index : Nat) : SolutionTree.Triangle :=
  (triangles[index]?).getD (rootTriangle 0)

def vertexAt (values : Array Nat) (index : Nat) : Pipeline.VertexIndex :=
  vertexSlot ((values[index]?).getD 0)

def readRegion (triangles : Array SolutionTree.Triangle) : Decoder Region := do
  let root ← readNat
  let triangleIndex ← readNat
  pure (.triangle (fin8 root) (triangleAt triangles triangleIndex))

def readEdgeRow (chart : CayleyAtlas.ChartIndex) (triangles : Array SolutionTree.Triangle)
    (id : Nat) (interval : SolutionTree.Interval) : Decoder Row := do
  let root ← readNat
  let triangleIndex ← readNat
  let edgePred ← readNat
  let count := edgePred + 1
  let outer ← readNats count #[]
  let inner ← readNats count #[]
  let witnesses ← readNats count #[]
  let m0 ← readRat
  let m1 ← readRat
  let m2 ← readRat
  pure (.projective id {
    interval
    root := fin8 root
    triangle := triangleAt triangles triangleIndex
    chart
    edgePred
    outerIndex := fun i => vertexAt outer i
    innerIndex := fun i => vertexAt inner i
    nonzeroWitness := fun i => vertexAt witnesses i
    ballMultiplier := ![m0, m1, m2] })

def readGlobalRow (chart : CayleyAtlas.ChartIndex) (triangles : Array SolutionTree.Triangle)
    (id : Nat) (interval : SolutionTree.Interval) : Decoder Row := do
  let root ← readNat
  let triangleIndex ← readNat
  let certificate ← readAxis
  let innerIndex ← readVertices
  let ballMultiplier ← readRat
  pure (.projectiveGlobal id {
    interval
    root := fin8 root
    triangle := triangleAt triangles triangleIndex
    chart
    certificate
    innerIndex
    ballMultiplier })

/-- Blended inner points (tags 17, 18): per contact the other vertex, then per
contact t (the inner point (1 − t) v_inner + t v_other). -/
def readBlend : Decoder ((Fin 3 → VertexIndex) × (Fin 3 → ℚ)) := do
  let other ← readVertices
  let t0 ← readRat
  let t1 ← readRat
  let t2 ← readRat
  pure (other, ![t0, t1, t2])

def readGlobalRowBlended (chart : CayleyAtlas.ChartIndex) (triangles : Array SolutionTree.Triangle)
    (id : Nat) (interval : SolutionTree.Interval) : Decoder Row := do
  let root ← readNat
  let triangleIndex ← readNat
  let certificate ← readAxis
  let innerIndex ← readVertices
  let ballMultiplier ← readRat
  let (innerOther, innerT) ← readBlend
  pure (.projectiveGlobal id {
    interval
    root := fin8 root
    triangle := triangleAt triangles triangleIndex
    chart
    certificate
    innerIndex
    ballMultiplier
    innerOther
    innerT })

def readMixedComponent : Decoder AtlasProjectiveMixedGlobalCertificate.Component := do
  let certificate ← readAxis
  let innerIndex ← readVertices
  let ballMultiplier ← readRat
  pure { certificate, innerIndex, ballMultiplier }

def readMixedComponentBlended : Decoder AtlasProjectiveMixedGlobalCertificate.Component := do
  let certificate ← readAxis
  let innerIndex ← readVertices
  let ballMultiplier ← readRat
  let (innerOther, innerT) ← readBlend
  pure { certificate, innerIndex, ballMultiplier, innerOther, innerT }

def readMixedGlobalRow (chart : CayleyAtlas.ChartIndex)
    (triangles : Array SolutionTree.Triangle)
    (id : Nat) (interval : SolutionTree.Interval) (blended : Bool := false) : Decoder Row := do
  let root ← readNat
  let triangleIndex ← readNat
  let w0 ← readRat
  let w1 ← readRat
  let w2 ← readRat
  let w3 ← readRat
  let comp := if blended then readMixedComponentBlended else readMixedComponent
  let c0 ← comp
  let c1 ← comp
  let c2 ← comp
  let c3 ← comp
  pure (.projectiveMixedGlobal id {
    interval
    root := fin8 root
    triangle := triangleAt triangles triangleIndex
    chart
    component := ![c0, c1, c2, c3]
    weight := ![w0, w1, w2, w3] })

def readLocalRow (chart : CayleyAtlas.ChartIndex) (triangles : Array SolutionTree.Triangle)
    (id : Nat) (interval : SolutionTree.Interval) : Decoder Row := do
  let root ← readNat
  let triangleIndex ← readNat
  let symmetryIndex ← readNat
  let certificate ← readCertificate
  let c ← readRat
  let δ ← readRat
  let r ← readRat
  pure (.projectiveLocal id {
    interval
    root := fin8 root
    triangle := triangleAt triangles triangleIndex
    chart
    symmetryIndex := finMod symmetryIndex
    certificate
    c
    δ
    r })

def readPath : Nat → Decoder (List (Fin 4))
  | 0 => pure []
  | length + 1 => do
      let child ← readNat
      let rest ← readPath length
      pure (fin4 child :: rest)

/-- Decode one row; `intervalOf` resolves the pack's interval indices. -/
def readRow (chart : CayleyAtlas.ChartIndex) (intervalOf : Nat → SolutionTree.Interval)
    (triangles : Array SolutionTree.Triangle) : Decoder Row := do
  let tag ← readNat
  let id ← readNat
  let intervalIndex ← readNat
  let interval := intervalOf intervalIndex
  if tag = 0 then
    -- viewRoot (DH only): not a Septopert row.
    let _child ← readNat
    pure (.radiusPrune id interval .sphere)
  else if tag = 1 then
    let lowerChild ← readNat
    let upperChild ← readNat
    let coordinate ← readNat
    let region ← readRegion triangles
    pure (.cayleySplit id lowerChild upperChild (fin5 coordinate) interval region)
  else if tag = 2 then
    let a ← readNat
    let b ← readNat
    let c ← readNat
    let d ← readNat
    let root ← readNat
    let triangleIndex ← readNat
    pure (.viewSplit id ![a, b, c, d] interval (fin8 root) (triangleAt triangles triangleIndex))
  else if tag = 3 then
    readEdgeRow chart triangles id interval
  else if tag = 4 then
    readGlobalRow chart triangles id interval
  else if tag = 5 then
    readLocalRow chart triangles id interval
  else if tag = 6 then
    let symmetryIndex ← readNat
    let r ← readRat
    let sharedIndex ← readNat
    let pathLength ← readNat
    let path ← readPath pathLength
    let region ← readRegion triangles
    pure (.symmetryTube id { interval, chart, symmetryIndex := finMod symmetryIndex, r }
      sharedIndex path region)
  else if tag = 7 then
    let region ← readRegion triangles
    pure (.radiusPrune id interval region)
  else if tag = 8 then
    -- fundamentalPrune (DH only): not a Septopert row.
    let _direction ← readNat
    let region ← readRegion triangles
    pure (.radiusPrune id interval region)
  else if tag = 13 then
    let neighbor ← readNat
    let region ← readRegion triangles
    pure (.c3Prune id { interval, chart, neighbor := finMod neighbor } region)
  else if tag = 14 then
    let element ← readNat
    let region ← readRegion triangles
    match region with
    | .triangle root triangle =>
        pure (.mirrorPrune id { interval, chart, triangle, element := finMod element } root)
    | .sphere => pure (.radiusPrune id interval region)
  else if tag = 15 then
    -- tieLeaf (DH only): not a Septopert row.
    let _normal ← readNat
    let _rho ← readRat
    let _node ← readNat
    let region ← readRegion triangles
    pure (.radiusPrune id interval region)
  else if tag = 16 then
    let cap ← readNat
    let region ← readRegion triangles
    match region with
    | .triangle root triangle => pure (.capLeaf id interval root triangle cap)
    | .sphere => pure (.radiusPrune id interval region)
  else if tag = 10 then
    let count ← readNat
    let children ← readNats count #[]
    pure (.codeRoot id children interval)
  else if tag = 12 then
    let lowerChild ← readNat
    let upperChild ← readNat
    let coordinate ← readNat
    let cut ← readRat
    let region ← readRegion triangles
    pure (.cayleySplitAt id lowerChild upperChild (fin5 coordinate) cut interval region)
  else if tag = 11 then
    let child ← readNat
    let root ← readNat
    let triangleIndex ← readNat
    let outerIndex ← readNat
    pure (.regionRelax id child interval (fin8 root)
      (triangleAt triangles triangleIndex) (triangleAt triangles outerIndex))
  else if tag = 17 then
    readGlobalRowBlended chart triangles id interval
  else if tag = 18 then
    readMixedGlobalRow chart triangles id interval (blended := true)
  else
    readMixedGlobalRow chart triangles id interval

def readRows (chart : CayleyAtlas.ChartIndex) (intervals : Array SolutionTree.Interval)
    (triangles : Array SolutionTree.Triangle) : Nat → Array Row → Decoder (Array Row)
  | 0, rows => pure rows
  | count + 1, rows => do
      let row ← readRow chart (intervalAt intervals) triangles
      readRows chart intervals triangles count (rows.push row)

structure Decoded where
  count : Nat
  rows : Array Row

def readDecoded (chart : CayleyAtlas.ChartIndex) : Decoder Decoded := do
  let count ← readNat
  let intervalCount ← readNat
  let intervals ← readMany readInterval intervalCount #[]
  let triangleCount ← readNat
  let triangles ← readMany readTriangle triangleCount #[]
  let rows ← readRows chart intervals triangles count #[]
  pure { count, rows }

/-- Decode one chart pack (`pack5d --chart C --all`, or a single job). -/
def decodeTable (chart : CayleyAtlas.ChartIndex) (shared : SharedLocalTables)
    (packed : String) : Table :=
  let decoded := (readDecoded chart { data := packed.toUTF8 }).1
  { chart, get := fun i => decoded.rows[i]!, size := decoded.count, sharedLocal := shared }

/-- Add `k` to a row's id and to its children's ids. -/
def shiftRow (k : Nat) : Row → Row
  | .cayleySplit id l u c iv r => .cayleySplit (id + k) (l + k) (u + k) c iv r
  | .viewSplit id ch iv root tri => .viewSplit (id + k) (fun i => ch i + k) iv root tri
  | .projective id b => .projective (id + k) b
  | .projectiveGlobal id b => .projectiveGlobal (id + k) b
  | .projectiveMixedGlobal id b => .projectiveMixedGlobal (id + k) b
  | .symmetryLocal id b r => .symmetryLocal (id + k) b r
  | .projectiveLocal id b => .projectiveLocal (id + k) b
  | .symmetryTube id tube s path r => .symmetryTube (id + k) tube s path r
  | .codeRoot id ch iv => .codeRoot (id + k) (ch.map (· + k)) iv
  | .radiusPrune id iv r => .radiusPrune (id + k) iv r
  | .c3Prune id b r => .c3Prune (id + k) b r
  | .mirrorPrune id b root => .mirrorPrune (id + k) b root
  | .capLeaf id iv root tri cap => .capLeaf (id + k) iv root tri cap
  | .regionRelax id ch iv root tri outer => .regionRelax (id + k) (ch + k) iv root tri outer
  | .cayleySplitAt id l u c cut iv r => .cayleySplitAt (id + k) (l + k) (u + k) c cut iv r

/-- Decode a chart table from per-code packs (`pack5d --per_code`, one per code
triangle in `ViewCover.codeTriangles` order, each with its job's root as row
0): row 0 is a `codeRoot` over `AtlasPose.rootInterval`, followed by each
code's rows with their ids shifted. -/
def decodeCodeTables (chart : CayleyAtlas.ChartIndex) (shared : SharedLocalTables)
    (packs : Array String) : Table :=
  let decoded := packs.map fun packed => (readDecoded chart { data := packed.toUTF8 }).1
  let (offsets, size) := decoded.foldl
    (fun (acc : Array Nat × Nat) d => (acc.1.push acc.2, acc.2 + d.count)) (#[], 1)
  let root : Row := .codeRoot 0 offsets (AtlasPose.rootInterval ℚ)
  let rows := (decoded.zip offsets).foldl
    (fun (rows : Array Row) (d, offset) => rows ++ d.rows.map (shiftRow offset)) #[root]
  { chart, get := fun i => rows[i]!, size, sharedLocal := shared }

/-! ## Lazy decoding

A chart pack is kept as its bytes plus the byte offset of every interval and
row; `get i` decodes row `i` on demand (and its interval). The decoded table
is checked exactly as an eagerly decoded one (`Table.get` is any function), so
the decoder stays untrusted plumbing, but no pack's rows are ever all
materialized. -/

/-- Skip `count` comma-terminated numbers from byte `pos`. -/
def skipNumbers (data : ByteArray) (pos count : Nat) : Nat := Id.run do
  let mut pos := pos
  let mut left := count
  let size := data.size
  while h : pos < size ∧ 0 < left do
    if data[pos]'h.1 = 44 then
      left := left - 1
    pos := pos + 1
  pos

/-- One chart pack: its bytes, the byte offsets of its intervals and rows, and
its (few) triangles. -/
structure LazyPack where
  data : ByteArray
  count : Nat
  intervalStarts : Array Nat
  triangles : Array SolutionTree.Triangle
  rowStarts : Array Nat

/-- Index a chart pack (one decoding pass to find the row boundaries; each
row is dropped right after it is read). -/
def LazyPack.index (chart : CayleyAtlas.ChartIndex) (data : ByteArray) : LazyPack := Id.run do
  let (count, cursor) := (readNat : Decoder Nat) { data }
  let (intervalCount, cursor) := (readNat : Decoder Nat) cursor
  let mut pos := cursor.pos
  let mut intervalStarts : Array Nat := Array.mkEmpty intervalCount
  for _ in [0:intervalCount] do
    intervalStarts := intervalStarts.push pos
    pos := skipNumbers data pos 12
  let (triangleCount, cursor) := (readNat : Decoder Nat) { data, pos }
  let (triangles, cursor) := readMany readTriangle triangleCount #[] cursor
  let mut cursor := cursor
  let mut rowStarts : Array Nat := Array.mkEmpty count
  for _ in [0:count] do
    rowStarts := rowStarts.push cursor.pos
    cursor := (readRow chart (fun _ => AtlasPose.rootInterval ℚ) triangles cursor).2
  pure { data, count, intervalStarts, triangles, rowStarts }

def LazyPack.interval (pack : LazyPack) (k : Nat) : SolutionTree.Interval :=
  match pack.intervalStarts[k]? with
  | some pos => (readInterval { data := pack.data, pos }).1
  | none => AtlasPose.rootInterval ℚ

/-- Row `i` of the pack (a placeholder past the end; the checker never reads
past `size`). -/
def LazyPack.row (chart : CayleyAtlas.ChartIndex) (pack : LazyPack) (i : Nat) : Row :=
  match pack.rowStarts[i]? with
  | some pos => (readRow chart pack.interval pack.triangles { data := pack.data, pos }).1
  | none => .radiusPrune i (AtlasPose.rootInterval ℚ) .sphere

/-- Lazily decode one chart pack (`pack5d --chart C --all`, or a single job). -/
def decodeTableLazy (chart : CayleyAtlas.ChartIndex) (shared : SharedLocalTables)
    (data : ByteArray) : Table :=
  let pack := LazyPack.index chart data
  { chart, get := pack.row chart, size := pack.count, sharedLocal := shared }

/-- Per-code packs behind a `codeRoot` row, decoded on demand: the rows of
`decodeCodeTables` (row 0 the `codeRoot`, then each code's rows shifted by its
offset). -/
structure LazyCodeTables where
  packs : Array LazyPack
  /-- The global id of each pack's row 0. -/
  offsets : Array Nat
  size : Nat

def LazyCodeTables.ofPacks (packs : Array LazyPack) : LazyCodeTables :=
  let (offsets, size) := packs.foldl
    (fun (acc : Array Nat × Nat) p => (acc.1.push acc.2, acc.2 + p.count)) (#[], 1)
  { packs, offsets, size }

/-- The pack holding global row `i ≥ 1` (the last one starting at or before it). -/
def LazyCodeTables.packOf (tables : LazyCodeTables) (i : Nat) : Nat := Id.run do
  let mut found := 0
  for k in [0:tables.offsets.size] do
    if tables.offsets[k]! ≤ i then found := k
  found

def LazyCodeTables.get (chart : CayleyAtlas.ChartIndex) (tables : LazyCodeTables)
    (i : Nat) : Row :=
  if i = 0 then .codeRoot 0 tables.offsets (AtlasPose.rootInterval ℚ)
  else
    let k := tables.packOf i
    let offset := tables.offsets[k]!
    match tables.packs[k]? with
    | some pack => shiftRow offset (pack.row chart (i - offset))
    | none => .radiusPrune i (AtlasPose.rootInterval ℚ) .sphere

/-- Lazily decode a chart table from its per-code packs (`decodeCodeTables`'s
layout, from the packs' bytes). -/
def decodeCodeTablesLazy (chart : CayleyAtlas.ChartIndex) (shared : SharedLocalTables)
    (packs : Array LazyPack) : Table :=
  let tables := LazyCodeTables.ofPacks packs
  { chart, get := tables.get chart, size := tables.size, sharedLocal := shared }

end Septopert.PackedSolutionTree
