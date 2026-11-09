module

public import MinimalityExtra
public import MinimalityExtra.NoUnimodal
public import MinimalityExtra.NoUnimodalOpenNear

/-!
# An open set of point sets without a unimodal view

Every 7-point set `x` close enough to the integer points `x0` (those of
`existsFirstOrderPassageWithoutUnimodalView`) whose first four points stay coplanar has no unimodal
view.  The proof re-runs the certificate tree of `NoUnimodalOpenData`, which is valid near `x0`
(`NoUniO.tree_near`) with certificates whose weights are polynomials in the coordinates
(`NoUniO.certB_sound`).
-/

@[expose] public section

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace NoUniO

open scoped RealInnerProductSpace
open Finset Filter Topology MinimalityExtra

noncomputable def uv (u : ℝ³) : V ℝ := (u 0, u 1, u 2)

theorem PX_val (x : Fin 7 → ℝ³) (i : Fin 7) : PX x i.val = (x i 0, x i 1, x i 2) := by
  simp [PX]

theorem det_ev (x : Fin 7 → ℝ³) (a b m : Fin 7) (u : ℝ³) :
    MinimalityExtra.det3 (x b - x a) (x m - x a) u = vdot (sideF (PX x) a.val b.val m.val) (uv u) := by
  simp only [sideF, PX_val, MinimalityExtra.det3, vcross, vsub, vdot, uv, PiLp.sub_apply]

theorem dep_true (x : Fin 7 → ℝ³) (a b : Fin 7) (u : ℝ³) :
    vdot (depF (PX x) a.val b.val true) (uv u) = ⟪x b, u⟫ - ⟪x a, u⟫ := by
  simp only [depF, ite_true, PX_val, vsub, vdot, uv, PiLp.inner_apply, Fin.sum_univ_three]
  simp
  ring

theorem dep_false (x : Fin 7 → ℝ³) (a b : Fin 7) (u : ℝ³) :
    vdot (depF (PX x) a.val b.val false) (uv u) = ⟪x a, u⟫ - ⟪x b, u⟫ := by
  simp only [depF, Bool.false_eq_true, ite_false, PX_val, vsub, vdot, uv, PiLp.inner_apply,
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

theorem no_unimodal (x : Fin 7 → ℝ³) (hchk : chkT (certB (PX x)) [] tree = true)
    (hpl : Planar (PX x)) (u : ℝ³) (k : ℕ) [NeZero k] (lab : ZMod k → Fin 7) (h3 : 3 ≤ k)
    (hinj : Function.Injective lab) (hrim : MinimalityExtra.StrictRim x u lab)
    (hz : MinimalityExtra.IsCyclicUnimodal (fun i => ⟪x (lab i), u⟫)) : False := by
  obtain ⟨hzinj, hcount⟩ := hz
  have hk7 : k ≤ 7 := by
    have := Fintype.card_le_of_injective lab hinj
    simpa using this
  obtain ⟨r, hr⟩ : ∃ r : ZMod k, ∀ i, (lab r).val ≤ (lab i).val := by
    obtain ⟨r, -, hr⟩ := Finset.exists_min_image Finset.univ (fun i => (lab i).val)
      Finset.univ_nonempty
    exact ⟨r, fun i => hr i (Finset.mem_univ i)⟩
  set z : ZMod k → ℝ := fun i => ⟪x (lab i), u⟫ with hzdef
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
  have hR : HR (PX x) (uv u) k c := by
    intro i hi m hm h1 h2
    have e : ((nxt k i : ℕ) : ZMod k) + r = ((i : ZMod k) + r) + 1 := by rw [hnxt]; ring
    have := hrim ⟨m, hm⟩ ((i : ZMod k) + r) (fun h => h1 (congrArg Fin.val h))
      (fun h => h2 (by rw [← e] at h; exact congrArg Fin.val h))
    rw [← e] at this
    exact lt_of_lt_of_eq this (det_ev x _ _ ⟨m, hm⟩ u)
  have hD : HD (PX x) (uv u) k c s := by
    intro i hi
    have e : ((nxt k i : ℕ) : ZMod k) + r = ((i : ZMod k) + r) + 1 := by rw [hnxt]; ring
    have hc1 : c (nxt k i) = (lab (((i : ZMod k) + r) + 1)).val := by
      simp only [c]; rw [e]
    cases hs : s i
    · have h' : ¬ z ((i : ZMod k) + r) < z ((i : ZMod k) + r + 1) := by
        simpa [s] using hs
      have hlt := lt_of_le_of_ne (not_lt.mp h') (hzne _).symm
      rw [hc1]
      have : ⟪x (lab ((i : ZMod k) + r)), u⟫ = z ((i : ZMod k) + r) := rfl
      have h2 : ⟪x (lab ((i : ZMod k) + r + 1)), u⟫ = z ((i : ZMod k) + r + 1) := rfl
      exact lt_of_lt_of_eq (by rw [this, h2]; linarith)
        (dep_false x (lab ((i : ZMod k) + r)) (lab ((i : ZMod k) + r + 1)) u).symm
    · have h' : z ((i : ZMod k) + r) < z ((i : ZMod k) + r + 1) := by
        simpa [s] using hs
      rw [hc1]
      have : ⟪x (lab ((i : ZMod k) + r)), u⟫ = z ((i : ZMod k) + r) := rfl
      have h2 : ⟪x (lab ((i : ZMod k) + r + 1)), u⟫ = z ((i : ZMod k) + r + 1) := rfl
      exact lt_of_lt_of_eq (by rw [this, h2]; linarith)
        (dep_true x (lab ((i : ZMod k) + r)) (lab ((i : ZMod k) + r + 1)) u).symm
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
  refine tree_sound (certB (PX x)) tree hchk (PX x) (uv u)
    (fun ps ds c' h hS hD => certB_sound hpl hS hD h) k c s ⟨h3, hk7, ?_, ?_, ?_, hR, hone, hD⟩
  · intro i _; exact (lab _).is_lt
  · intro i hi j hj h
    have h1 : lab ((i : ZMod k) + r) = lab ((j : ZMod k) + r) := Fin.ext h
    have h2 := add_right_cancel (hinj h1)
    have := (ZMod.natCast_eq_natCast_iff' i j k).1 h2
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  · intro i _
    simp only [c, Nat.cast_zero, zero_add]
    exact hr _


theorem planar_of_face (x : Fin 7 → ℝ³) (n : ℝ³) (h : ℝ) (hn : n ≠ 0)
    (hx : ∀ i : Fin 7, i.val < 4 → ⟪n, x i⟫ = h) : Planar (PX x) := by
  refine ⟨uv n, h, ?_, ?_⟩
  · simp only [vdot, uv]
    by_contra hc
    have h0 : n 0 = 0 := by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1), sq_nonneg (n 2)]
    have h1 : n 1 = 0 := by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1), sq_nonneg (n 2)]
    have h2 : n 2 = 0 := by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1), sq_nonneg (n 2)]
    apply hn
    ext j; fin_cases j <;> simp [h0, h1, h2]
  · intro i hi
    have := hx ⟨i, by omega⟩ hi
    rw [← this]
    have e : PX x i = (x ⟨i, by omega⟩ 0, x ⟨i, by omega⟩ 1, x ⟨i, by omega⟩ 2) :=
      PX_val x ⟨i, by omega⟩
    rw [e]
    simp only [vdot, uv, PiLp.inner_apply, Fin.sum_univ_three]
    simp
    ring

attribute [fun_prop] cont_coord

theorem cont_det3_cross (w ω τ : ℝ³) (i j k : Fin 7) :
    Continuous fun x : Fin 7 → ℝ³ => det3 (x j - x i) (cross ω (x k) + τ) w := by
  simp only [det3, cross, PiLp.add_apply, PiLp.sub_apply]
  simp
  fun_prop

theorem cont_det3_pt (w : ℝ³) (a b c d : Fin 7) :
    Continuous fun x : Fin 7 → ℝ³ => det3 (x b - x a) (x d - x c) w := by
  simp only [det3, PiLp.sub_apply]
  fun_prop


theorem ev_pos {g : (Fin 7 → ℝ³) → ℝ} (hg : Continuous g) (h : 0 < g x0) :
    ∀ᶠ x in 𝓝 x0, 0 < g x :=
  continuousAt_const.eventually_lt hg.continuousAt h

theorem tilt_persist (w ω τ : ℝ³) (i : Fin 7)
    (h : TiltCert (univ.image x0) w ω τ (x0 i)) :
    ∀ᶠ x in 𝓝 x0, TiltCert (univ.image x) w ω τ (x i) := by
  rcases h with ⟨y0, hy0, y1, hy1, h1, h2, h3⟩ | ⟨a, ha, b, hb, c, hc, h1, h2, h3, h4⟩
  · obtain ⟨j0, -, rfl⟩ := mem_image.1 hy0
    obtain ⟨j1, -, rfl⟩ := mem_image.1 hy1
    filter_upwards [ev_pos (cont_det3_pt w i j1 i j0) h1, ev_pos (cont_det3_cross w ω τ i j1 i) h2,
      ev_pos (cont_det3_cross w ω τ j0 i i) h3] with x e1 e2 e3
    exact Or.inl ⟨x j0, mem_image_of_mem x (mem_univ _), x j1, mem_image_of_mem x (mem_univ _),
      e1, e2, e3⟩
  · obtain ⟨ja, -, rfl⟩ := mem_image.1 ha
    obtain ⟨jb, -, rfl⟩ := mem_image.1 hb
    obtain ⟨jc, -, rfl⟩ := mem_image.1 hc
    filter_upwards [ev_pos (cont_det3_pt w ja jb ja jc) h1, ev_pos (cont_det3_pt w ja jb ja i) h2,
      ev_pos (cont_det3_pt w jb jc jb i) h3, ev_pos (cont_det3_pt w jc ja jc i) h4] with x e1 e2 e3 e4
    exact Or.inr ⟨x ja, mem_image_of_mem x (mem_univ _), x jb, mem_image_of_mem x (mem_univ _),
      x jc, mem_image_of_mem x (mem_univ _), e1, e2, e3, e4⟩

theorem passage_ev : ∀ᶠ x in 𝓝 x0, HasFirstOrderPassage (univ.image x) := by
  have hall : ∀ᶠ x in 𝓝 x0, ∀ i : Fin 7,
      TiltCert (univ.image x) NoUni.vw NoUni.vω NoUni.vτ (x i) :=
    Filter.eventually_all.2 fun i =>
      tilt_persist _ _ _ i (NoUni.tilt_all _ (mem_image_of_mem NoUni.vx (mem_univ i)))
  filter_upwards [hall] with x hx
  exact ⟨NoUni.vw, NoUni.vω, NoUni.vτ, NoUni.vw_ne_zero, fun y hy => by
    obtain ⟨i, -, rfl⟩ := mem_image.1 hy; exact hx i⟩

theorem exposed_ev : ∀ᶠ x in 𝓝 x0, ∀ i : Fin 7, ∃ c : ℝ³, ∀ j, j ≠ i → ⟪c, x j⟫ < ⟪c, x i⟫ := by
  refine Filter.eventually_all.2 fun i => ?_
  obtain ⟨c, hc⟩ := NoUni.exposed i
  have : ∀ᶠ x in 𝓝 x0, ∀ j, j ≠ i → ⟪c, x j⟫ < ⟪c, x i⟫ := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases hj : j = i
    · exact Eventually.of_forall fun x h => absurd hj h
    · have hcj : Continuous fun x : Fin 7 → ℝ³ => ⟪c, x j⟫ :=
        continuous_const.inner (continuous_apply j)
      have hci : Continuous fun x : Fin 7 → ℝ³ => ⟪c, x i⟫ :=
        continuous_const.inner (continuous_apply i)
      filter_upwards [hcj.continuousAt.eventually_lt hci.continuousAt (hc j hj)] with x hx _ using hx
  filter_upwards [this] with x hx using ⟨c, hx⟩


/-- The core of the open-family theorem, with the statement spelled out. -/
theorem open_family : ∃ (x₀ : Fin 7 → ℝ³) (ε : ℝ), 0 < ε ∧
    (∃ (n : ℝ³) (h : ℝ), n ≠ 0 ∧ (∀ i : Fin 7, i.val < 4 → ⟪n, x₀ i⟫ = h) ∧
      (∀ i : Fin 7, 4 ≤ i.val → ⟪n, x₀ i⟫ < h)) ∧
    ∀ x : Fin 7 → ℝ³, (∀ i, dist (x i) (x₀ i) < ε) →
      (∃ (n : ℝ³) (h : ℝ), n ≠ 0 ∧ (∀ i : Fin 7, i.val < 4 → ⟪n, x i⟫ = h) ∧
        (∀ i : Fin 7, 4 ≤ i.val → ⟪n, x i⟫ < h)) →
      (∀ i, ∃ c : ℝ³, ∀ j, j ≠ i → ⟪c, x j⟫ < ⟪c, x i⟫) ∧
      HasFirstOrderPassage (univ.image x) ∧ ¬ HasUnimodalView x := by
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff.1
    (tree_near.and (passage_ev.and exposed_ev))
  refine ⟨x0, ε, hε, NoUni.face, ?_⟩
  intro x hx hq
  obtain ⟨n, h, hn, hf, -⟩ := hq
  have hd : dist x x0 < ε := (dist_pi_lt_iff hε).2 hx
  obtain ⟨hchk, hpass, hexp⟩ := hall hd
  refine ⟨hexp, hpass, ?_⟩
  rintro ⟨u, k, hk, lab, h3, hinj, hrim, hz⟩
  exact no_unimodal x hchk (planar_of_face x n h hn hf) u k lab h3 hinj hrim hz

end NoUniO

namespace MinimalityExtra

theorem existsOpenFamilyWithoutUnimodalView : ExistsOpenFamilyWithoutUnimodalView :=
  NoUniO.open_family

end MinimalityExtra
