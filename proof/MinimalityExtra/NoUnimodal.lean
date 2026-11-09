module

public import MinimalityExtra
public import MinimalityExtra.NoUnimodalData

/-!
# The converse of the unimodal criterion fails

A 7-point set (the integer points `NoUni.ptl`, scaled by `10^9`) with a first-order passage
and no unimodal view.  The non-existence of a unimodal view is proved by a certified
computation: `NoUni.tree_ok` is checked by the kernel (`decide +kernel`, no extra axioms), and
`NoUni.tree_sound` turns it into a refutation of every configuration.  Here we reduce an
arbitrary `HasUnimodalView` to such a configuration (normalising the rotation of the cycle).
-/

@[expose] public section

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace NoUni

open scoped RealInnerProductSpace
open Finset

noncomputable def xN (n : ℕ) : ℝ³ := !₂[((pt n).1 : ℝ), ((pt n).2.1 : ℝ), ((pt n).2.2 : ℝ)]

/-- the seven points -/
noncomputable def vx (i : Fin 7) : ℝ³ := xN i.val

theorem det_ev (a b m : ℕ) (u : ℝ³) :
    MinimalityExtra.det3 (xN b - xN a) (xN m - xN a) u = ev (sideF a b m) (u 0) (u 1) (u 2) := by
  simp only [MinimalityExtra.det3, sideF, pcross, psub, ev, xN, PiLp.sub_apply]
  simp

theorem dep_true (a b : ℕ) (u : ℝ³) :
    ev (depF a b true) (u 0) (u 1) (u 2) = ⟪xN b, u⟫ - ⟪xN a, u⟫ := by
  simp only [depF, ite_true, psub, ev, xN, PiLp.inner_apply, Fin.sum_univ_three]
  simp
  ring

theorem dep_false (a b : ℕ) (u : ℝ³) :
    ev (depF a b false) (u 0) (u 1) (u 2) = ⟪xN a, u⟫ - ⟪xN b, u⟫ := by
  simp only [depF, Bool.false_eq_true, ite_false, psub, ev, xN, PiLp.inner_apply,
    Fin.sum_univ_three]
  simp
  ring

theorem len_filter_range (k : ℕ) (F : ℕ → Bool) :
    ((List.range k).filter F).length = ((Finset.range k).filter (fun j => F j = true)).card := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, Finset.range_add_one,
      Finset.filter_insert]
    by_cases h : F n = true
    · simp [h, ih, Finset.card_insert_of_notMem]
    · simp [h, ih]

theorem no_unimodal (u : ℝ³) (k : ℕ) [NeZero k] (lab : ZMod k → Fin 7) (h3 : 3 ≤ k)
    (hinj : Function.Injective lab) (hrim : MinimalityExtra.StrictRim vx u lab)
    (hz : MinimalityExtra.IsCyclicUnimodal (fun i => ⟪vx (lab i), u⟫)) : False := by
  obtain ⟨hzinj, hcount⟩ := hz
  have hk7 : k ≤ 7 := by
    have := Fintype.card_le_of_injective lab hinj
    simpa using this
  obtain ⟨r, hr⟩ : ∃ r : ZMod k, ∀ i, (lab r).val ≤ (lab i).val := by
    obtain ⟨r, -, hr⟩ := Finset.exists_min_image Finset.univ (fun i => (lab i).val)
      Finset.univ_nonempty
    exact ⟨r, fun i => hr i (Finset.mem_univ i)⟩
  set z : ZMod k → ℝ := fun i => ⟪vx (lab i), u⟫ with hzdef
  let c : ℕ → ℕ := fun j => (lab ((j : ZMod k) + r)).val
  let s : ℕ → Bool := fun j => decide (z ((j : ZMod k) + r) < z ((j : ZMod k) + r + 1))
  have hnxt : ∀ j, ((nxt k j : ℕ) : ZMod k) = (j : ZMod k) + 1 := by
    intro j; unfold nxt; rw [ZMod.natCast_mod]; push_cast; rfl
  have hprv : ∀ j : ℕ, (((j + k - 1) % k : ℕ) : ZMod k) = (j : ZMod k) - 1 := by
    intro j
    rw [ZMod.natCast_mod, Nat.cast_sub (by have := NeZero.pos k; omega)]
    push_cast
    simp
  have hne1 : ∀ t : ZMod k, t ≠ t + 1 := by
    intro t h
    have h1 : (1 : ZMod k) = 0 := by
      have := congrArg (fun y => y - t) h
      simpa using this.symm
    have : ((1 : ℕ) : ZMod k) = 0 := by simpa using h1
    have := (ZMod.natCast_eq_zero_iff 1 k).1 this
    have := Nat.le_of_dvd one_pos this
    omega
  have hzne : ∀ t : ZMod k, z t ≠ z (t + 1) := fun t h => hne1 t (hzinj h)
  have hR : HR (u 0) (u 1) (u 2) k c := by
    intro i hi m hm h1 h2
    have e : ((nxt k i : ℕ) : ZMod k) + r = ((i : ZMod k) + r) + 1 := by rw [hnxt]; ring
    have := hrim ⟨m, hm⟩ ((i : ZMod k) + r) (fun h => h1 (congrArg Fin.val h))
      (fun h => h2 (by rw [← e] at h; exact congrArg Fin.val h))
    rw [← e] at this
    rw [← det_ev]
    exact this
  have hD : HD (u 0) (u 1) (u 2) k c s := by
    intro i hi
    have e : ((nxt k i : ℕ) : ZMod k) + r = ((i : ZMod k) + r) + 1 := by rw [hnxt]; ring
    have hc1 : c (nxt k i) = (lab (((i : ZMod k) + r) + 1)).val := by
      simp only [c]; rw [e]
    cases hs : s i
    · have h' : ¬ z ((i : ZMod k) + r) < z ((i : ZMod k) + r + 1) := by
        simpa [s] using hs
      have hlt := lt_of_le_of_ne (not_lt.mp h') (hzne _).symm
      rw [dep_false]
      simp only [hc1, c]
      have : ⟪xN (lab ((i : ZMod k) + r)).val, u⟫ = z ((i : ZMod k) + r) := rfl
      have h2 : ⟪xN (lab ((i : ZMod k) + r + 1)).val, u⟫ = z ((i : ZMod k) + r + 1) := rfl
      rw [this, h2]; linarith
    · have h' : z ((i : ZMod k) + r) < z ((i : ZMod k) + r + 1) := by
        simpa [s] using hs
      rw [dep_true]
      simp only [hc1, c]
      have : ⟪xN (lab ((i : ZMod k) + r)).val, u⟫ = z ((i : ZMod k) + r) := rfl
      have h2 : ⟪xN (lab ((i : ZMod k) + r + 1)).val, u⟫ = z ((i : ZMod k) + r + 1) := rfl
      rw [this, h2]; linarith
  -- the count
  have hsprev : ∀ j : ℕ, s ((j + k - 1) % k) =
      decide (z ((j : ZMod k) + r - 1) < z ((j : ZMod k) + r)) := by
    intro j
    simp only [s, hprv]
    have e1 : (j : ZMod k) - 1 + r = (j : ZMod k) + r - 1 := by ring
    rw [e1, sub_add_cancel]
  have hF : ∀ j : ℕ, (s ((j + k - 1) % k) && !s j) = true ↔
      (z ((j : ZMod k) + r - 1) < z ((j : ZMod k) + r) ∧
        z ((j : ZMod k) + r + 1) < z ((j : ZMod k) + r)) := by
    intro j
    rw [hsprev]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', s, decide_eq_false_iff_not]
    refine and_congr Iff.rfl ?_
    constructor
    · intro h; exact lt_of_le_of_ne (not_lt.mp h) (hzne _).symm
    · intro h; exact not_lt.mpr h.le
  have hone : OneT k s := by
    unfold OneT
    rw [len_filter_range]
    refine Eq.trans ?_ hcount
    apply Finset.card_bij (fun (j : ℕ) _ => (j : ZMod k) + r)
    · intro j hj
      rw [Finset.mem_filter] at hj ⊢
      exact ⟨Finset.mem_univ _, (hF j).1 hj.2⟩
    · intro a ha b hb h
      have h' : (a : ZMod k) = (b : ZMod k) := add_right_cancel h
      have := (ZMod.natCast_eq_natCast_iff' a b k).1 h'
      rw [Finset.mem_filter, Finset.mem_range] at ha hb
      rwa [Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at this
    · intro t ht
      rw [Finset.mem_filter] at ht
      refine ⟨(t - r).val, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨ZMod.val_lt _, (hF _).2 ?_⟩
        rw [ZMod.natCast_zmod_val]
        simpa using ht.2
      · simp
  refine tree_sound tree tree_ok (u 0) (u 1) (u 2) k c s ⟨h3, hk7, ?_, ?_, ?_, hR, hone, hD⟩
  · intro i _; exact (lab _).is_lt
  · intro i hi j hj h
    have h1 : lab ((i : ZMod k) + r) = lab ((j : ZMod k) + r) := Fin.ext h
    have h2 := add_right_cancel (hinj h1)
    have := (ZMod.natCast_eq_natCast_iff' i j k).1 h2
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  · intro i _
    simp only [c, Nat.cast_zero, zero_add]
    exact hr _

noncomputable def vw : ℝ³ := !₂[6643, -7449, 623]
noncomputable def vω : ℝ³ := !₂[-2045, -6067, 10000]
noncomputable def vτ : ℝ³ := !₂[-388000000000, 0, 254000000000]

theorem exposed : ∀ i : Fin 7, ∃ c : ℝ³, ∀ j, j ≠ i → ⟪c, vx j⟫ < ⟪c, vx i⟫ := by
  intro i
  fin_cases i
  · refine ⟨!₂[-4, 6, 2], ?_⟩
    intro j hj; fin_cases j <;> simp_all [PiLp.inner_apply, Fin.sum_univ_three, vx, xN, pt, ptl] <;> norm_num
  · refine ⟨!₂[-6, -4, 4], ?_⟩
    intro j hj; fin_cases j <;> simp_all [PiLp.inner_apply, Fin.sum_univ_three, vx, xN, pt, ptl] <;> norm_num
  · refine ⟨!₂[-6, -6, 5], ?_⟩
    intro j hj; fin_cases j <;> simp_all [PiLp.inner_apply, Fin.sum_univ_three, vx, xN, pt, ptl] <;> norm_num
  · refine ⟨!₂[1, -2, 1], ?_⟩
    intro j hj; fin_cases j <;> simp_all [PiLp.inner_apply, Fin.sum_univ_three, vx, xN, pt, ptl] <;> norm_num
  · refine ⟨!₂[0, -1, -6], ?_⟩
    intro j hj; fin_cases j <;> simp_all [PiLp.inner_apply, Fin.sum_univ_three, vx, xN, pt, ptl] <;> norm_num
  · refine ⟨!₂[-6, 1, -6], ?_⟩
    intro j hj; fin_cases j <;> simp_all [PiLp.inner_apply, Fin.sum_univ_three, vx, xN, pt, ptl] <;> norm_num
  · refine ⟨!₂[-6, -6, -6], ?_⟩
    intro j hj; fin_cases j <;> simp_all [PiLp.inner_apply, Fin.sum_univ_three, vx, xN, pt, ptl] <;> norm_num

/-- vertices 0..3 lie on the plane z = 0 and 4..6 strictly below it -/
theorem face : ∃ n : ℝ³, ∃ h : ℝ, n ≠ 0 ∧
    (∀ i : Fin 7, i.val < 4 → ⟪n, vx i⟫ = h) ∧ (∀ i : Fin 7, 4 ≤ i.val → ⟪n, vx i⟫ < h) := by
  refine ⟨!₂[0, 0, 1], 0, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun v : ℝ³ => v 2) h
    norm_num at this
  · intro i hi
    fin_cases i <;> simp_all [PiLp.inner_apply, Fin.sum_univ_three, vx, xN, pt, ptl]
  · intro i hi
    fin_cases i <;> simp_all [PiLp.inner_apply, Fin.sum_univ_three, vx, xN, pt, ptl] 

theorem vw_ne_zero : vw ≠ 0 := by
  intro h
  have := congrArg (fun v : ℝ³ => v 0) h
  norm_num [vw] at this

/-- every vertex has a local tilt certificate for the view vw with motion (vω, vτ) -/
theorem tilt_all : ∀ y ∈ (Finset.univ.image vx), MinimalityExtra.TiltCert (Finset.univ.image vx) vw vω vτ y := by
  have m : ∀ i : Fin 7, vx i ∈ univ.image vx := fun i => mem_image_of_mem vx (mem_univ i)
  intro y hy
  obtain ⟨i, -, rfl⟩ := mem_image.mp hy
  fin_cases i
  · exact Or.inl ⟨vx 5, m 5, vx 1, m 1, by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ], by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ], by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ]⟩
  · exact Or.inl ⟨vx 0, m 0, vx 2, m 2, by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ], by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ], by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ]⟩
  · exact Or.inl ⟨vx 1, m 1, vx 6, m 6, by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ], by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ], by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ]⟩
  · exact Or.inr ⟨vx 0, m 0, vx 1, m 1, vx 4, m 4, by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ], by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ], by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ], by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ]⟩
  · exact Or.inl ⟨vx 6, m 6, vx 5, m 5, by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ], by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ], by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ]⟩
  · exact Or.inl ⟨vx 4, m 4, vx 0, m 0, by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ], by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ], by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ]⟩
  · exact Or.inl ⟨vx 2, m 2, vx 4, m 4, by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ], by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ], by norm_num [MinimalityExtra.det3, MinimalityExtra.cross, vx, xN, pt, ptl, vw, vω, vτ]⟩


end NoUni

namespace MinimalityExtra

/-- **The converse of the unimodal criterion fails.** -/
theorem existsFirstOrderPassageWithoutUnimodalView :
    ExistsFirstOrderPassageWithoutUnimodalView := by
  refine ⟨NoUni.vx, NoUni.exposed, NoUni.face, ⟨NoUni.vw, NoUni.vω, NoUni.vτ, NoUni.vw_ne_zero, NoUni.tilt_all⟩, ?_⟩
  rintro ⟨u, k, hk, lab, h3, hinj, hrim, hz⟩
  exact NoUni.no_unimodal u k lab h3 hinj hrim hz

end MinimalityExtra

#print axioms MinimalityExtra.existsFirstOrderPassageWithoutUnimodalView
