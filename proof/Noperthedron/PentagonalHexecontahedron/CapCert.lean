module

public import Noperthedron.PentagonalHexecontahedron.CapCheck

@[expose] public section

/-!
# Cap certificates

`CapCert`: a cap (frame, parameters, the exact vertices, the witnesses) and
per chart of Lean's `chartList` its certificate tree. `CapCert.check` checks
(natively) that the charts are exactly `chartList`, that the cap is isotropic
with an orthogonal frame, and every tree (width witnesses (k, k', c)); `CapCert.check_sound` gives `ChartGood` at every
point of every chart, hence (`cap_pose_not_rupert`) the cap theorem.
-/

namespace Noperthedron.PentagonalHexecontahedron.Cap

open NPoly PVec

structure CapCert where
  st : Setup
  pr : Params
  zList : List ((Kind × ℕ × ℕ × Bool) × ℕ)
  verts : Array KVec
  /-- Width witnesses (k, k', c). -/
  wits : Array (ℕ × ℕ × KVec)
  usePrune : Bool
  Gcol : Fin 3 → KVec
  charts : List (ChartId × CTree)

def CapCert.zOf (c : CapCert) (b : Kind × ℕ × ℕ × Bool) : ℕ :=
  match c.zList.find? (fun e => decide (e.1 = b)) with
  | some e => e.2
  | none => 1

/-- Per used witness: the vertices, the direction, the screened polynomials and the d ≠ 0 check
on the root box. -/
structure WitData where
  vk : KVec
  vk' : KVec
  c : KVec
  Q : Array (NPoly 5)
  dok : Bool

def witData (c : CapCert) (id : ChartId) (wi : ℕ) : Option WitData :=
  match c.wits[wi]? with
  | some (k, k', cv) =>
    match c.verts[k]?, c.verts[k']? with
    | some vk, some vk' => some ⟨vk, vk', cv,
        screened (witnessPolys (makeChart c.st id) id (pairDiffs c.verts) (ksub vk vk') cv) (rootBox c.st c.pr id),
        dOk c.st c.pr id cv⟩
    | _, _ => none
  | none => none

def leafCheck (c : CapCert) (id : ChartId) (cache : Array (Option WitData)) (wi : ℕ) (box : Box) : Bool :=
  match cache[wi]? with
  | some (some d) => (d.dok || dOkBox c.st id d.c box) && boxOk d.Q box
  | _ => false

def CTree.leafIds : CTree → List ℕ
  | .split _ l r => l.leafIds ++ r.leafIds
  | .leaf w => [w]
  | _ => []

def chartCheck (c : CapCert) (id : ChartId) (t : CTree) : Bool :=
  let root := rootBox c.st c.pr id
  let used := t.leafIds
  let cache : Array (Option WitData) :=
    (Array.range c.wits.size).map fun wi => if used.contains wi then witData c id wi else none
  decide (∀ i : Fin 5, 0 ≤ (root i).2) && decide (id.axis < 3) && decide (id.side < 4) &&
    t.check (leafCheck c id cache) (fun box => c.usePrune && pruneOk c.st id c.Gcol box) (coneOk c.st c.pr id) root

/-- An isotropic cap with an orthogonal frame (|f|² > 0 by the rational lower enclosure). -/
def frameCheck (st : Setup) : Bool :=
  !st.aniso && decide (0 < IcoQ.lo (kdot st.e1 st.e1)) && decide (0 < IcoQ.lo (kdot st.e2 st.e2)) &&
  decide (0 < IcoQ.lo (kdot st.x st.x)) &&
  decide (kdot st.e1 st.e2 = IcoQ.zero) && decide (kdot st.e1 st.x = IcoQ.zero) && decide (kdot st.e2 st.x = IcoQ.zero)

/-- The tie scheme's parameters are admissible (`TieOK`). -/
def CapCert.tieCheck (c : CapCert) : Bool :=
  c.st.tieCharts.all fun e => (e.1.1 != .face) ||
    (decide (e.1.2.2.1 ≠ 0) && decide (c.zOf e.1 + e.2.1 ≤ e.2.2.1) && decide (e.2.2.1 < e.2.2.2) &&
      c.pr.ratioOn && c.st.strong e.1.2.2.1)

def CapCert.check (c : CapCert) : Bool :=
  decide (0 < c.verts.size) && c.zList.all (fun e => decide (0 < e.2)) && frameCheck c.st &&
    (c.charts.map (·.1) == chartList c.st c.pr c.zOf) && c.charts.all (fun e => chartCheck c e.1 e.2) &&
    c.tieCheck

theorem CapCert.tieOK (c : CapCert) (h : c.tieCheck = true) : TieOK c.st c.pr c.zOf := by
  intro b p hp hface
  unfold Setup.tieOf at hp
  obtain ⟨e, hfind, rfl⟩ := Option.map_eq_some_iff.mp hp
  have hmem := List.mem_of_find?_eq_some hfind
  have heq : e.1 = b := by simpa using List.find?_some hfind
  have he := List.all_eq_true.mp h e hmem
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, decide_eq_true_eq] at he
  rcases he with he | he
  · exact absurd (heq ▸ hface) he
  · rw [← heq]
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := he
    exact ⟨h1, h2, h3, h4, h5⟩

theorem frameCheck_sound (st : Setup) (h : frameCheck st = true) : FrameOK st := by
  simp only [frameCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨⟨⟨⟨⟨han, h11⟩, h22⟩, hxx⟩, h12⟩, h1x⟩, h2x⟩ := h
  have hv : ∀ a b : KVec, ∀ q : IcoQ, kdot a b = q → rdot (kv a) (kv b) = q.val := by
    intro a b q hq; rw [← val_kdot, hq]
  have hpos : ∀ a b : KVec, 0 < IcoQ.lo (kdot a b) → 0 < rdot (kv a) (kv b) := by
    intro a b hl
    rw [← val_kdot]
    exact lt_of_lt_of_le (by exact_mod_cast hl) (IcoQ.lo_le_val _)
  refine ⟨han, hpos _ _ h11, hpos _ _ h22, hpos _ _ hxx, ?_, ?_, ?_⟩
  · rw [hv _ _ _ h12]; simp [IcoQ.val, IcoQ.zero]
  · rw [hv _ _ _ h1x]; simp [IcoQ.val, IcoQ.zero]
  · rw [hv _ _ _ h2x]; simp [IcoQ.val, IcoQ.zero]

theorem CapCert.zOf_pos (c : CapCert) (h : c.zList.all (fun e => decide (0 < e.2)) = true) (b) : 0 < c.zOf b := by
  unfold CapCert.zOf
  split
  · next e he =>
    have hmem := List.mem_of_find?_eq_some he
    have := List.all_eq_true.mp h e hmem
    simpa using this
  · norm_num

theorem cache_spec (c : CapCert) (id : ChartId) (used : List ℕ) (wi : ℕ) (d : WitData)
    (h : ((Array.range c.wits.size).map fun wi => if used.contains wi then witData c id wi else none)[wi]? =
      some (some d)) : witData c id wi = some d := by
  rw [Array.getElem?_map, Array.getElem?_range] at h
  split_ifs at h with hwi
  · simp only [Option.map_some, Option.some.injEq] at h
    split_ifs at h with hu
    · exact h
  · simp at h

theorem witData_spec (c : CapCert) (id : ChartId) (wi : ℕ) (d : WitData) (h : witData c id wi = some d) :
    ∃ vk ∈ c.verts, ∃ vk' ∈ c.verts, ∃ cv : KVec, d = ⟨vk, vk', cv,
      screened (witnessPolys (makeChart c.st id) id (pairDiffs c.verts) (ksub vk vk') cv) (rootBox c.st c.pr id),
      dOk c.st c.pr id cv⟩ := by
  rcases hw : c.wits[wi]? with _ | ⟨k, k', cv⟩
  · simp only [witData, hw] at h; cases h
  · rcases hv : c.verts[k]? with _ | vk
    · simp only [witData, hw, hv] at h; cases h
    · rcases hv' : c.verts[k']? with _ | vk'
      · simp only [witData, hw, hv, hv'] at h; cases h
      · simp only [witData, hw, hv, hv', Option.some.injEq] at h
        exact ⟨vk, Array.mem_of_getElem? hv, vk', Array.mem_of_getElem? hv', cv, h.symm⟩

set_option maxHeartbeats 1000000 in
/-- **Certificate soundness**: a checked cap certificate makes every chart point good. -/
theorem CapCert.check_sound (c : CapCert) (h : c.check = true) :
    FrameOK c.st ∧ (∀ b, 0 < c.zOf b) ∧ TieOK c.st c.pr c.zOf ∧
      ∀ id ∈ chartList c.st c.pr c.zOf, ∀ y, InBoxR (rootBox c.st c.pr id) y →
        ChartGood c.st c.pr (c.verts.toList.map kv) c.usePrune (gMat c.Gcol) id y := by
  simp only [CapCert.check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hV, hz⟩, hF⟩, hlist⟩, hall⟩, htc⟩ := h
  have hF' := frameCheck_sound c.st hF
  refine ⟨hF', c.zOf_pos hz, c.tieOK htc, ?_⟩
  intro id hid y hy
  rw [← hlist] at hid
  obtain ⟨⟨id', t⟩, hmem, rfl⟩ := List.mem_map.mp hid
  have hc := List.all_eq_true.mp hall _ hmem
  simp only [chartCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hw, hax⟩, hside⟩, htree⟩ := hc
  have hVne : c.verts.toList.map kv ≠ [] := by
    intro h0
    have : c.verts.toList = [] := List.map_eq_nil_iff.mp h0
    have : c.verts.size = 0 := by rw [← Array.length_toList, this]; rfl
    omega
  have hu := rChartU_ne_zero c.st hF' id' hside
  refine CTree.check_sound _ _ _ (fun y => InBoxR (rootBox c.st c.pr id') y →
      ChartGood c.st c.pr (c.verts.toList.map kv) c.usePrune (gMat c.Gcol) id' y)
    ?_ ?_ ?_ t (rootBox c.st c.pr id') hw htree y hy hy
  · -- Witness leaves.
    intro wi box hbw hleaf y hyb hyr
    unfold leafCheck at hleaf
    split at hleaf
    · next d hd =>
      obtain ⟨vk, hvk, vk', hvk', cv, rfl⟩ := witData_spec c id' wi d (cache_spec c id' _ wi _ hd)
      have hok : witnessLeafOk c.st c.pr id' c.verts vk vk' cv box = true := by
        unfold witnessLeafOk; simpa only using hleaf
      obtain ⟨hdn, hval⟩ := witnessLeafOk_sound c.st c.pr id' hax c.verts vk vk' cv box hok hw hbw y hyb hyr
      right; right
      refine ⟨kv vk, List.mem_map.mpr ⟨vk, Array.mem_toList_iff.mpr hvk, rfl⟩,
        kv vk', List.mem_map.mpr ⟨vk', Array.mem_toList_iff.mpr hvk', rfl⟩, kv cv, hdn, ?_⟩
      intro vj₁ hvj₁ vj₂ hvj₂
      obtain ⟨vj, hvj, rfl⟩ := List.mem_map.mp hvj₁
      obtain ⟨vj', hvj', rfl⟩ := List.mem_map.mp hvj₂
      exact hval vj (Array.mem_toList_iff.mp hvj) vj' (Array.mem_toList_iff.mp hvj')
    · exact absurd hleaf (by simp)
  · -- Half-turn prune leaves.
    intro box hbw hprune y hyb hyr
    simp only [Bool.and_eq_true] at hprune
    obtain ⟨hpr, hok⟩ := hprune
    have hμ0 := y0_nonneg_of_root c.st c.pr id' y hyr
    rcases eq_or_lt_of_le hμ0 with h0 | hpos
    · exact chartGood_of_w_zero _ _ _ hVne _ _ _ _ (hu y) (rChartW_mu_zero c.st id' y h0.symm)
    · have hnm : id'.kind ≠ .mcone := by
        simp only [pruneOk, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1
      by_cases hcone : isCone id' = true
      · have hk : id'.kind = .cone := by
          unfold isCone at hcone; simp at hcone
          rcases hcone with h | h
          · exact h
          · exact absurd h hnm
        have h2 := y2_nonneg_of_root_cone c.st c.pr id' hcone hax y hyr
        rcases eq_or_lt_of_le h2 with h20 | h2pos
        · exact chartGood_of_w_zero _ _ _ hVne _ _ _ _ (hu y) (rChartW_cone_tip c.st id' hk y h20.symm)
        · right; left
          exact ⟨hpr, pruneOk_sound c.st id' c.Gcol box hok hbw y hyb hpos (fun _ => h2pos)
            (rdot_self_ne_zero_of_ne (hu y))⟩
      · right; left
        exact ⟨hpr, pruneOk_sound c.st id' c.Gcol box hok hbw y hyb hpos (fun h => absurd h hcone)
          (rdot_self_ne_zero_of_ne (hu y))⟩
  · -- Cone-region leaves.
    intro box hbw hcone y hyb hyr
    left
    exact coneOk_sound c.st c.pr id' box hcone y hyb

open scoped Matrix in
/-- **The cap theorem from a checked certificate.** -/
theorem CapCert.not_rupert (c : CapCert) (hc : c.check = true) (hS : 2 ≤ c.st.strongScale)
    (hmcm : 1 ≤ c.st.mcm) (S : Set ℝ³) (hSdef : S = convexHull ℝ {v | ∃ vj ∈ c.verts.toList.map kv, v = toEuc vj})
    (p : MatrixPose)
    (hx : 0 < frameCoord c.st p.view 2)
    (he1 : |frameCoord c.st p.view 0| ≤ c.pr.mu0 * frameCoord c.st p.view 2)
    (he2 : |frameCoord c.st p.view 1| ≤ c.pr.mu0 * frameCoord c.st p.view 2)
    (w : Fin 3 → ℝ) (hR : p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2))
    (hw : ∀ i, |frameCoord c.st w i| ≤ (c.st.range i : ℝ) * (c.pr.mu0 : ℝ) ^ isoWt i)
    (hcell : c.usePrune = true →
      Matrix.trace (halfTurnMat p.view * p.relativeRotation * gMat c.Gcol) ≤ Matrix.trace p.relativeRotation) :
    ¬ RupertPose p S := by
  obtain ⟨hF, hz, htie, hgood⟩ := c.check_sound hc
  exact cap_pose_not_rupert c.st c.pr c.zOf hz htie hF hS hmcm _ c.usePrune (gMat c.Gcol) hgood S
    hSdef p hx he1 he2 w hR hw hcell

end Noperthedron.PentagonalHexecontahedron.Cap
