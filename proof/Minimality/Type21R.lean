module

public import Minimality.Type21F2

@[expose] public section

/-!
# Type 21: the tier R (`FEWER-FACES-PROOFS.md` Lemma 16.5)

* **A ridge view** (`isRupert_ridge`): an edge `v w` of `K` lying on two faces `f_A`, `f_B`
  that are both vertical at the view `u = w − v` (they contain `u`).  The shadow is the angle at
  `q = P v = P w` between the projections of the two faces, cut by the far ends `A`, `B`
  (the other vertex of each face, `m_A`, `m_B`, a middle, `EdgeMid`) and the last point `C`
  (strictly beneath both faces).  If `C` is hidden (strictly on `q`'s side of the line
  `P(A) P(B)`), the rims are the triangles `(v, A, B)`, `(w, A, B)` and `K_v` is unimodal
  (`isRupert_edgeTri_robust`); if `C` is a corner and `v`, `w` lie weakly on opposite sides of
  the plane `A C B` (Lemma E), one of the closings `(v, A, C, B)`, `(w, A, C, B)` is robustly
  unimodal (`isRupert_edgePair_robust`).  Either orientation of the screen; depth ties allowed
  except three equal depths on a rim.
* **Lemma 16.5 (R)** — `isRupert_type21_R`: the ridge `26` of type 21 (faces `0256`, `2346`,
  view `u = 2 − 6`).  With `2 = 0 + α (5 − 0) + β (6 − 0)` and `2 = 4 + α' (3 − 4) + β' (6 − 4)`
  (`β = r' = δ_015(2)/δ_015(6)`, `β' = r = δ_134(2)/δ_134(6)`): the far end of `0256` is `5` if
  `β > 1` (then `0` is a middle) and `0` if `β < 1`; the far end of `2346` is `3` if `β' > 1`
  and `4` if `β' < 1`.  The tier R (`Type21R`): `1` hidden, or the far ends are `(5, 4)` and
  `2`, `6` lie on opposite sides of the plane `145`, or `(0, 3)` and the plane `013`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

theorem EdgeMid.swap_ab {v w a b m : ℝ³} (h : EdgeMid v w a b m) : EdgeMid v w b a m := by
  obtain ⟨s, δ, hs0, hs1, hδ, h | h | h | h⟩ := h
  · exact ⟨1 - s, δ, by linarith, by linarith, hδ, Or.inr (Or.inl (by rw [h]; module))⟩
  · exact ⟨1 - s, δ, by linarith, by linarith, hδ, Or.inl (by rw [h]; module)⟩
  · exact ⟨1 - s, δ, by linarith, by linarith, hδ, Or.inr (Or.inr (Or.inr (by rw [h]; module)))⟩
  · exact ⟨1 - s, δ, by linarith, by linarith, hδ, Or.inr (Or.inr (Or.inl (by rw [h]; module)))⟩

/-- **A ridge view.**  `v w` lies on two faces `f_A` (through `v, w, A`) and `f_B` (through
`v, w, B`), both containing the view `u = w − v`; `C` is strictly beneath both, `A` beneath
`f_B` and `B` beneath `f_A`; every point of `K` is `v, w, A, B, C` or a middle (`EdgeMid`).
If `C` is hidden (`hid`: `C` and `v` on one side of the vertical plane through `A B`), or a
corner with `v`, `w` weakly on opposite sides of the plane `A C B` (Lemma E), then, with ties
allowed (`v, A, B` and `A, C, B` not each at one depth: Lemma E with ties,
`isRupert_edgePair_robust`, and `isRupert_edgeTri_robust`) and no horizontal double normals at
`u`, `K` is Rupert. -/
theorem isRupert_ridge (K : Finset ℝ³) {v w A B C : ℝ³} {fA fB : ℝ³ → ℝ} {NA NB : ℝ³}
    (hfA : ∀ y z, fA y - fA z = ⟪NA, y - z⟫) (hfB : ∀ y z, fB y - fB z = ⟪NB, y - z⟫)
    (hAv : fA v = 0) (hAw : fA w = 0) (hAA : fA A = 0) (hAB : fA B < 0) (hAC : fA C < 0)
    (hBv : fB v = 0) (hBw : fB w = 0) (hBB : fB B = 0) (hBA : fB A < 0) (hBC : fB C < 0)
    (hT : det3 (A - v) (B - v) (w - v) ≠ 0)
    (hvK : v ∈ K) (hwK : w ∈ K) (hAK : A ∈ K) (hBK : B ∈ K) (hCK : C ∈ K)
    (hK : ∀ z ∈ K, z = v ∨ z = w ∨ z = A ∨ z = B ∨ z = C ∨ EdgeMid v w A B z)
    (hcase : 0 < det3 (B - A) (C - A) (w - v) * det3 (B - A) (v - A) (w - v) ∨
      (det3 (B - A) (C - A) (w - v) * det3 (B - A) (v - A) (w - v) < 0 ∧
        det3 (B - A) (C - A) (v - A) * det3 (B - A) (C - A) (w - A) ≤ 0))
    (htri : ¬ (⟪v, w - v⟫ = ⟪A, w - v⟫ ∧ ⟪A, w - v⟫ = ⟪B, w - v⟫))
    (h3 : ¬ (⟪A, w - v⟫ = ⟪C, w - v⟫ ∧ ⟪C, w - v⟫ = ⟪B, w - v⟫))
    (hnd₁ : NoHDNAt (K.erase w) (w - v)) (hnd₂ : NoHDNAt (K.erase v) (w - v)) :
    IsRupert K := by
  set u := w - v with hu
  set T := det3 (A - v) (B - v) u with hT_def
  have hNAu : ⟪NA, u⟫ = 0 := by rw [hu, ← hfA, hAw, hAv, sub_self]
  have hNBu : ⟪NB, u⟫ = 0 := by rw [hu, ← hfB, hBw, hBv, sub_self]
  have hNAe : ⟪NA, A - v⟫ = 0 := by rw [← hfA, hAA, hAv, sub_self]
  have hNBe : ⟪NB, B - v⟫ = 0 := by rw [← hfB, hBB, hBv, sub_self]
  -- the screen coordinates of `C`: `det(A − v, C − v) = p_B T`, `det(C − v, B − v) = p_A T`
  have k1 : det3 (A - v) (C - v) u * fA B = T * fA C := by
    have := det3_mul_inner_eq (N := NA) (e := A - v) (u := u) (w := C - v) (w' := B - v) hNAe hNAu
    rw [← hfA, ← hfA, hAv, sub_zero, sub_zero] at this; linarith
  have k2 : det3 (C - v) (B - v) u * fB A = T * fB C := by
    have := det3_mul_inner_eq (N := NB) (e := B - v) (u := u) (w := C - v) (w' := A - v) hNBe hNBu
    rw [← hfB, ← hfB, hBv, sub_zero, sub_zero] at this
    have e1 : det3 (B - v) (C - v) u = -det3 (C - v) (B - v) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have e2 : det3 (B - v) (A - v) u = -T := by
      simp only [hT_def, det3_expand, PiLp.sub_apply]; ring
    rw [e1, e2] at this; linarith
  set ℓ := det3 (B - A) (C - A) u with hℓ
  have eT : det3 (B - A) (v - A) u = T := by
    simp only [hT_def, det3_expand, PiLp.sub_apply]; ring
  rw [eT] at hcase
  have hu0 : u ≠ 0 := by
    intro h0; apply hT; simp only [hT_def, h0, det3, inner_zero_right]
  have hmid : ∀ z ∈ K, z = v ∨ z = w ∨ z = A ∨ z = B ∨ z = C ∨ EdgeMid v w B A z := by
    intro z hz
    rcases hK z hz with h | h | h | h | h | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)),
      Or.inr (Or.inr (Or.inr (Or.inl h))), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h.swap_ab))))]
  -- the orientation-free facts
  have rA : 0 < fA C / fA B := div_pos_of_neg_of_neg hAC hAB
  have rB : 0 < fB C / fB A := div_pos_of_neg_of_neg hBC hBA
  have d1 : det3 (A - v) (C - v) u = fA C / fA B * T := by
    rw [div_mul_eq_mul_div, eq_div_iff hAB.ne]; linarith [k1]
  have d2 : det3 (C - v) (B - v) u = fB C / fB A * T := by
    rw [div_mul_eq_mul_div, eq_div_iff hBA.ne]; linarith [k2]
  rcases lt_or_gt_of_ne hT with hTn | hTp
  · -- clockwise: use `(v, B, A)`
    rcases hcase with hh | ⟨hc, hE⟩
    · have hℓn : ℓ < 0 := neg_of_mul_pos_left hh hTn.le
      refine isRupert_edgeTri_robust K hvK hwK hBK hAK ?_
        (fun h => htri ⟨h.1.trans h.2, h.2.symm⟩) (fun z hz => ?_) hnd₁
      · have : det3 (B - v) (A - v) u = -T := by
          simp only [hT_def, det3_expand, PiLp.sub_apply]; ring
        rw [this]; linarith
      · rcases hmid z hz with h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inl h))
        · subst h
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))))
          · have : det3 (B - v) (z - v) u = -det3 (z - v) (B - v) u := by
              simp only [det3_expand, PiLp.sub_apply]; ring
            rw [this, d2]; nlinarith
          · have : det3 (A - B) (z - B) u = -ℓ := by
              simp only [hℓ, det3_expand, PiLp.sub_apply]; ring
            rw [this]; linarith
          · have : det3 (v - A) (z - A) u = -det3 (A - v) (z - v) u := by
              simp only [det3_expand, PiLp.sub_apply]; ring
            rw [this, d1]; nlinarith
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · have hℓp : 0 < ℓ := pos_of_mul_neg_left hc hTn.le
      refine isRupert_edgePair_robust (v := v) (w := w) (a := B) (b := A) (c := C) K hvK hwK
        hBK hAK hCK ?_ ?_ ?_ ?_ ?_ (fun h => h3 ⟨h.2.symm, h.1.symm⟩) (fun z hz => ?_) hnd₁ hnd₂
      · have : det3 (B - v) (C - v) u = -det3 (C - v) (B - v) u := by
          simp only [det3_expand, PiLp.sub_apply]; ring
        rw [this, d2]; nlinarith
      · have : det3 (C - B) (A - B) u = ℓ := by
          simp only [hℓ, det3_expand, PiLp.sub_apply]; ring
        rw [this]; exact hℓp
      · have : det3 (A - C) (v - C) u = -det3 (A - v) (C - v) u := by
          simp only [det3_expand, PiLp.sub_apply]; ring
        rw [this, d1]; nlinarith
      · have : det3 (v - A) (B - A) u = -T := by
          simp only [hT_def, det3_expand, PiLp.sub_apply]; ring
        rw [this]; linarith
      · have e1 : det3 (A - B) (C - B) (v - B) = -det3 (B - A) (C - A) (v - A) := by
          simp only [det3_expand, PiLp.sub_apply]; ring
        have e2 : det3 (A - B) (C - B) (w - B) = -det3 (B - A) (C - A) (w - A) := by
          simp only [det3_expand, PiLp.sub_apply]; ring
        rw [e1, e2, neg_mul_neg]; exact hE
      · rcases hmid z hz with h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · -- counterclockwise: `(v, A, B)`
    rcases hcase with hh | ⟨hc, hE⟩
    · have hℓp : 0 < ℓ := pos_of_mul_pos_left hh hTp.le
      refine isRupert_edgeTri_robust K hvK hwK hAK hBK hTp htri (fun z hz => ?_) hnd₁
      rcases hK z hz with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · subst h
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, hℓp, ?_⟩))))
        · rw [d1]; exact mul_pos rA hTp
        · have : det3 (v - B) (z - B) u = det3 (z - v) (B - v) u := by
            simp only [det3_expand, PiLp.sub_apply]; ring
          rw [this, d2]; exact mul_pos rB hTp
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · have hℓn : ℓ < 0 := neg_of_mul_neg_left hc hTp.le
      refine isRupert_edgePair_robust (v := v) (w := w) (a := A) (b := B) (c := C) K hvK hwK
        hAK hBK hCK ?_ ?_ ?_ ?_ hE h3 (fun z hz => ?_) hnd₁ hnd₂
      · rw [d1]; exact mul_pos rA hTp
      · have : det3 (C - A) (B - A) u = -ℓ := by
          simp only [hℓ, det3_expand, PiLp.sub_apply]; ring
        rw [this]; linarith
      · have : det3 (B - C) (v - C) u = det3 (C - v) (B - v) u := by
          simp only [det3_expand, PiLp.sub_apply]; ring
        rw [this, d2]; exact mul_pos rB hTp
      · have : det3 (v - B) (A - B) u = T := by
          simp only [hT_def, det3_expand, PiLp.sub_apply]; ring
        rw [this]; exact hTp
      · rcases hK z hz with h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

/-! ### Lemma 16.5 for type 21 -/

/-- One quadrant of the ridge view of type 21: the far ends `A ∈ {0, 5}` of `0256` and
`B ∈ {3, 4}` of `2346`, the other vertices `m_A`, `m_B` middles. -/
theorem isRupert_type21_ridge_quad {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) {A mA B mB : ℝ³} (hA : (A = b' ∧ mA = a) ∨ (A = a ∧ mA = b'))
    (hB : (B = a' ∧ mB = b) ∨ (B = b ∧ mB = a'))
    (hmA : EdgeMid c' d A B mA) (hmB : EdgeMid c' d A B mB)
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hcase : 0 < det3 (B - A) (c - A) (d - c') * det3 (B - A) (c' - A) (d - c') ∨
      (det3 (B - A) (c - A) (d - c') * det3 (B - A) (c' - A) (d - c') < 0 ∧
        det3 (B - A) (c - A) (c' - A) * det3 (B - A) (c - A) (d - A) ≤ 0)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  set K := insert d ({a, a', b, b', c, c'} : Finset ℝ³) with hK
  have hAK : A ∈ K := by rcases hA with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [hK]
  have hBK : B ∈ K := by rcases hB with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [hK]
  -- the faces `0256` (`f_A`) and `2346` (`f_B`)
  have fAA : F.ab'c'.f A = 0 := by rcases hA with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [F.ab'c'.hQ, F.ab'c'.hP]
  have fBB : F.a'bc'.f B = 0 := by rcases hB with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [F.a'bc'.hP, F.a'bc'.hQ]
  have fAB : F.ab'c'.f B < 0 := by
    rcases hB with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [F.ab'c'.neg _ (by simp) (Ne.symm haa') ha'b' ha'c', F.ab'c'.neg _ (by simp)
      (Ne.symm hab) hbb' hbc']
  have fBA : F.a'bc'.f A < 0 := by
    rcases hA with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [F.a'bc'.neg _ (by simp) (Ne.symm ha'b') (Ne.symm hbb') hb'c', F.a'bc'.neg _
      (by simp) haa' hab hac']
  have fAC := F.ab'c'.neg c (by simp) (Ne.symm hac) (Ne.symm hb'c) hcc'
  have fBC := F.a'bc'.neg c (by simp) (Ne.symm ha'c) (Ne.symm hbc) hcc'
  -- `det(A − 6, B − 6, 2 − 6) ≠ 0`: else `B` would lie on the plane of `0256`
  have hT : det3 (A - c') (B - c') (d - c') ≠ 0 := by
    intro h0
    have hc : cross (A - c') (d - c') ≠ 0 := by
      rcases hA with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · refine cross_ne_zero_of_affine (g := fun x => -F.a'b'c'.f x) (N := -F.a'b'c'.N)
          (fun y z => by rw [inner_neg_left, ← F.a'b'c'.hN]; ring) (Ne.symm hb'c')
          (by simp [F.a'b'c'.hR]) (by simp [F.a'b'c'.hQ]) (by simp; exact hd.a'b'c')
      · exact cross_ne_zero_of_affine F.abc'.hN (Ne.symm hac') F.abc'.hR F.abc'.hP hd.abc'
    have := affine_zero_of_coplanar F.ab'c'.hN F.ab'c'.hR fAA hd.ab'c' hc (w := B) (by
      have e : det3 (A - c') (d - c') (B - c') = -det3 (A - c') (B - c') (d - c') := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [e, h0, neg_zero])
    linarith
  -- no three of the rim corners at one depth (`GenPosTie`, along the segment `6 2`)
  have hKc' : c' ∈ K := by simp [hK]
  have hKd : d ∈ K := by simp [hK]
  have hKc : c ∈ K := by simp [hK]
  have Ac' : A ≠ c' := by rcases hA with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [hb'c', hac']
  have Bc' : B ≠ c' := by rcases hB with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [ha'c', hbc']
  have Ac : A ≠ c := by rcases hA with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [hb'c, hac]
  have Bc : B ≠ c := by rcases hB with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [ha'c, hbc]
  have AB : A ≠ B := by
    rcases hA with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rcases hB with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [Ne.symm ha'b', Ne.symm hbb', haa', hab]
  have htri := hgen.noTriple hKc' hKd hKc' hAK hBK (Ne.symm hdc') (Ne.symm Ac') AB (Ne.symm Bc')
  have h3 := hgen.noTriple hKc' hKd hAK hKc hBK (Ne.symm hdc') Ac (Ne.symm Bc) AB
  obtain ⟨n1, n2⟩ := noHDN_pair hnd hKc' hKd (Ne.symm hdc')
  refine isRupert_ridge K F.ab'c'.hN F.a'bc'.hN F.ab'c'.hR hd.ab'c' fAA fAB fAC F.a'bc'.hR
    hd.a'bc' fBB fBA fBC hT hKc' hKd hAK hBK hKc (fun z hz => ?_) hcase htri h3 n2 n1
  simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · rcases hA with ⟨-, rfl⟩ | ⟨rfl, -⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hmA))))
    · exact Or.inr (Or.inr (Or.inl rfl))
  · rcases hB with ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hmB))))
  · rcases hB with ⟨-, rfl⟩ | ⟨rfl, -⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hmB))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · rcases hA with ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hmA))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inl rfl

/-- In the plane of a quadrilateral face `P Q d c'` with `d = P + α (Q − P) + β (c' − P)`
(`α, β > 0`, `α + β > 1`), seen along `d − c'`: if `β > 1`, `Q` is the far end and `P` a middle. -/
theorem ridge_mid_far {P Q c' d X : ℝ³} {α β : ℝ} (hco : d = P + α • (Q - P) + β • (c' - P))
    (hα : 0 < α) (h : 1 < β) : EdgeMid c' d Q X P := by
  refine ⟨α / (α + β - 1), 1 / (α + β - 1), div_pos hα (by linarith),
    (div_lt_one (by linarith)).mpr (by linarith), div_pos one_pos (by linarith), Or.inl ?_⟩
  rw [hco]
  have ht : α + β - 1 ≠ 0 := by linarith
  match_scalars <;> field_simp <;> ring

/-- As `ridge_mid_far`, with `β < 1`: `P` is the far end and `Q` a middle (on the side of `d`). -/
theorem ridge_mid_near {P Q c' d X : ℝ³} {α β : ℝ} (hco : d = P + α • (Q - P) + β • (c' - P))
    (hα : 0 < α) (hβ : 0 < β) (hαβ : 1 < α + β) (h : β < 1) : EdgeMid c' d P X Q := by
  refine ⟨(α + β - 1) / α, β / α, div_pos (by linarith) hα,
    (div_lt_one hα).mpr (by linarith), div_pos hβ hα, Or.inr (Or.inr (Or.inl ?_))⟩
  rw [hco]
  have ht : α ≠ 0 := hα.ne'
  match_scalars <;> field_simp <;> ring

/-- The ridge condition of one quadrant (far ends `A`, `B`): `1` hidden (on `6`'s side of the
vertical plane through `A B`), or `1` a corner and `6`, `2` weakly on opposite sides of the
plane `A 1 B` (Lemma E). -/
def RidgeOK (A B c c' d : ℝ³) : Prop :=
  0 < det3 (B - A) (c - A) (d - c') * det3 (B - A) (c' - A) (d - c') ∨
    (det3 (B - A) (c - A) (d - c') * det3 (B - A) (c' - A) (d - c') < 0 ∧
      det3 (B - A) (c - A) (c' - A) * det3 (B - A) (c - A) (d - A) ≤ 0)

/-- **The tier R of §16** (Lemma 16.5), for the ratios `β = δ_015(2)/δ_015(6)` (`> 1`: the far
end of `0256` along the ridge `26` is `5`; `< 1`: it is `0`) and `β' = δ_134(2)/δ_134(6)`
(`> 1`: the far end of `2346` is `3`; `< 1`: it is `4`): the ridge condition `RidgeOK` holds in
the corresponding quadrant. -/
def Type21RQ (β β' : ℝ) (a a' b b' c c' d : ℝ³) : Prop :=
  (1 < β ∧ 1 < β' ∧ RidgeOK b' a' c c' d) ∨ (1 < β ∧ β' < 1 ∧ RidgeOK b' b c c' d) ∨
  (β < 1 ∧ 1 < β' ∧ RidgeOK a a' c c' d) ∨ (β < 1 ∧ β' < 1 ∧ RidgeOK a b c c' d)

/-- The tier R for `K = O ∪ {d}` with `O`'s facet functions. -/
def Type21R {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') (d : ℝ³) : Prop :=
  Type21RQ (F.ab'c.f d / F.ab'c.f c') (F.a'bc.f d / F.a'bc.f c') a a' b b' c c' d

/-- **Lemma 16.5 (the tier R)**: at the view along the ridge `26` the faces `0256`, `2346` are
vertical; their far ends `f0 ∈ {0, 5}`, `f3 ∈ {3, 4}` and `1` are the corners of the shadow
(the other vertices are middles).  If `1` is hidden, or the closings `(6, f0, 1, f3)`,
`(2, f0, 1, f3)` satisfy Lemma E, `K` is Rupert (off `GenPosTie` and horizontal double normals at
the view along `26`). -/
theorem isRupert_type21_R {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d)
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hR : Type21R F d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨hα, hβ, hαβ, hco⟩ := hd.coords
  obtain ⟨hα', hβ', hαβ', hco'⟩ := hd.sigma1.coords
  change 0 < F.abc'.f d / F.abc'.f a' at hα'
  change 0 < F.a'bc.f d / F.a'bc.f c' at hβ'
  change 1 < F.abc'.f d / F.abc'.f a' + F.a'bc.f d / F.a'bc.f c' at hαβ'
  change d = b + (F.abc'.f d / F.abc'.f a') • (a' - b) + (F.a'bc.f d / F.a'bc.f c') • (c' - b)
    at hco'
  unfold Type21R Type21RQ at hR
  rcases hR with ⟨h1, h2, hok⟩ | ⟨h1, h2, hok⟩ | ⟨h1, h2, hok⟩ | ⟨h1, h2, hok⟩
  · exact isRupert_type21_ridge_quad F hd (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩)
      (ridge_mid_far hco hα h1) (ridge_mid_far hco' hα' h2).swap_ab hgen hnd hok
  · exact isRupert_type21_ridge_quad F hd (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩)
      (ridge_mid_far hco hα h1) (ridge_mid_near hco' hα' hβ' hαβ' h2).swap_ab hgen hnd hok
  · exact isRupert_type21_ridge_quad F hd (Or.inr ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩)
      (ridge_mid_near hco hα hβ hαβ h1) (ridge_mid_far hco' hα' h2).swap_ab hgen hnd hok
  · exact isRupert_type21_ridge_quad F hd (Or.inr ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩)
      (ridge_mid_near hco hα hβ hαβ h1) (ridge_mid_near hco' hα' hβ' hαβ' h2).swap_ab hgen hnd hok

end Minimality

end
