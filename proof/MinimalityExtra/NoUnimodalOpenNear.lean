module

public import Mathlib
public import MinimalityExtra.NoUnimodalOpenCheck
public import MinimalityExtra.NoUnimodalOpenData

/-!
# Open neighbourhood of the no-unimodal-view point set: persistence of the certificates

The certificate tree of `NoUnimodalOpenData` is valid at the integer points (kernel check).  Here
we show that it is valid at every nearby real configuration: each certificate asks for finitely many
strict inequalities between polynomials in the coordinates.
-/

@[expose] public section

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace NoUniO

open Filter Topology

/-- the base configuration: the seven integer points -/
noncomputable def x0 : Fin 7 → ℝ³ := fun i =>
  !₂[((NoUni.pt i.val).1 : ℝ), ((NoUni.pt i.val).2.1 : ℝ), ((NoUni.pt i.val).2.2 : ℝ)]

/-- coordinates of the points of a configuration, indexed by `ℕ` (zero outside `Fin 7`) -/
noncomputable def PX (x : Fin 7 → ℝ³) (n : ℕ) : V ℝ :=
  if h : n < 7 then (x ⟨n, h⟩ 0, x ⟨n, h⟩ 1, x ⟨n, h⟩ 2) else (0, 0, 0)

def vmap {R S : Type*} (f : R → S) (a : V R) : V S := (f a.1, f a.2.1, f a.2.2)

section map
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

theorem vsub_map (a b : V R) : vmap f (vsub a b) = vsub (vmap f a) (vmap f b) := by
  simp [vmap, vsub]
theorem vcross_map (a b : V R) : vmap f (vcross a b) = vcross (vmap f a) (vmap f b) := by
  simp [vmap, vcross]
theorem vdot_map (a b : V R) : f (vdot a b) = vdot (vmap f a) (vmap f b) := by
  simp [vmap, vdot]
theorem vdet_map (a b c : V R) : f (vdet a b c) = vdet (vmap f a) (vmap f b) (vmap f c) := by
  simp [vdet, vdot_map, vcross_map]
theorem form_map (P : ℕ → V R) (r : Ref) :
    form (fun n => vmap f (P n)) r = vmap f (form P r) := by
  unfold form sideF depF
  split_ifs <;> simp [vsub_map, vcross_map]
theorem weights_map (P : ℕ → V R) (c : Cert) :
    weights (fun n => vmap f (P n)) c = (weights P c).map f := by
  cases c <;> simp [weights, form_map, vdet_map, vsub_map, vdot_map]

end map

theorem PX_x0 : PX x0 = fun n => vmap (Int.castRingHom ℝ) (NoUni.pt n) := by
  funext n
  by_cases h : n < 7
  · simp only [PX, h, dite_true, vmap, x0]
    simp
  · simp only [PX, h, dite_false, vmap, NoUni.pt]
    have : NoUni.ptl.getD n (0, 0, 0) = (0, 0, 0) := by
      rw [List.getD_eq_getElem?_getD]
      have : NoUni.ptl.length = 7 := rfl
      rw [List.getElem?_eq_none (by omega)]; rfl
    rw [this]; simp


/-! ### Continuity -/

theorem cont_coord (i : Fin 7) (j : Fin 3) : Continuous fun x : Fin 7 → ℝ³ => x i j :=
  (EuclideanSpace.proj j).continuous.comp (continuous_apply i)

theorem cont_PX (n : ℕ) : Continuous fun x : Fin 7 → ℝ³ => PX x n := by
  by_cases h : n < 7
  · simp only [PX, h, dite_true]
    exact (cont_coord _ 0).prodMk ((cont_coord _ 1).prodMk (cont_coord _ 2))
  · simp only [PX, h, dite_false]
    exact continuous_const

section cont
variable {X : Type*} [TopologicalSpace X] {f g h : X → V ℝ}

theorem cont_vsub (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => vsub (f x) (g x) := by
  unfold vsub
  have := hf.fst; have := hf.snd.fst; have := hf.snd.snd
  have := hg.fst; have := hg.snd.fst; have := hg.snd.snd
  fun_prop

theorem cont_vcross (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => vcross (f x) (g x) := by
  unfold vcross
  have := hf.fst; have := hf.snd.fst; have := hf.snd.snd
  have := hg.fst; have := hg.snd.fst; have := hg.snd.snd
  fun_prop

theorem cont_vdot (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => vdot (f x) (g x) := by
  unfold vdot
  have := hf.fst; have := hf.snd.fst; have := hf.snd.snd
  have := hg.fst; have := hg.snd.fst; have := hg.snd.snd
  fun_prop

theorem cont_vdet (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous fun x => vdet (f x) (g x) (h x) :=
  cont_vdot (cont_vcross hf hg) hh

end cont

theorem cont_form (r : Ref) : Continuous fun x : Fin 7 → ℝ³ => form (PX x) r := by
  unfold form sideF depF
  split_ifs
  · exact cont_vcross (cont_vsub (cont_PX _) (cont_PX _)) (cont_vsub (cont_PX _) (cont_PX _))
  · exact cont_vsub (cont_PX _) (cont_PX _)
  · exact cont_vsub (cont_PX _) (cont_PX _)


/-! ### Weights as functions of the configuration -/

noncomputable def wf : Cert → List ((Fin 7 → ℝ³) → ℝ)
  | .c4 r1 r2 r3 r4 =>
    [fun x => vdet (form (PX x) r2) (form (PX x) r3) (form (PX x) r4),
     fun x => -vdet (form (PX x) r1) (form (PX x) r3) (form (PX x) r4),
     fun x => vdet (form (PX x) r1) (form (PX x) r2) (form (PX x) r4),
     fun x => -vdet (form (PX x) r1) (form (PX x) r2) (form (PX x) r3)]
  | .c3 a b m1 m2 m3 =>
    [fun x => vdet (vsub (PX x b) (PX x a)) (vsub (PX x m2) (PX x a)) (vsub (PX x m3) (PX x a)),
     fun x => -vdet (vsub (PX x b) (PX x a)) (vsub (PX x m1) (PX x a)) (vsub (PX x m3) (PX x a)),
     fun x => vdet (vsub (PX x b) (PX x a)) (vsub (PX x m1) (PX x a)) (vsub (PX x m2) (PX x a))]
  | .c2 r1 r2 =>
    [fun x => -vdot (form (PX x) r1) (form (PX x) r2),
     fun x => vdot (form (PX x) r1) (form (PX x) r1)]

theorem weights_wf (c : Cert) (x : Fin 7 → ℝ³) :
    weights (PX x) c = (wf c).map (fun f => f x) := by
  cases c <;> rfl

theorem wf_cont (c : Cert) : ∀ f ∈ wf c, Continuous f := by
  intro f hf
  cases c with
  | c4 r1 r2 r3 r4 =>
    simp only [wf, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact cont_vdet (cont_form _) (cont_form _) (cont_form _)
    · exact (cont_vdet (cont_form _) (cont_form _) (cont_form _)).neg
    · exact cont_vdet (cont_form _) (cont_form _) (cont_form _)
    · exact (cont_vdet (cont_form _) (cont_form _) (cont_form _)).neg
  | c3 a b m1 m2 m3 =>
    simp only [wf, List.mem_cons, List.not_mem_nil, or_false] at hf
    have e : ∀ m, Continuous fun x : Fin 7 → ℝ³ => vsub (PX x m) (PX x a) :=
      fun m => cont_vsub (cont_PX _) (cont_PX _)
    rcases hf with rfl | rfl | rfl
    · exact cont_vdet (e b) (e m2) (e m3)
    · exact (cont_vdet (e b) (e m1) (e m3)).neg
    · exact cont_vdet (e b) (e m1) (e m2)
  | c2 r1 r2 =>
    simp only [wf, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact (cont_vdot (cont_form _) (cont_form _)).neg
    · exact cont_vdot (cont_form _) (cont_form _)

theorem ev_wsign (c : Cert) (h : wsignB (weights NoUni.pt c) = true) :
    ∀ᶠ x in 𝓝 x0, wsignB (weights (PX x) c) = true := by
  have hmap : (wf c).map (fun f => f x0) = (weights NoUni.pt c).map (Int.cast : ℤ → ℝ) := by
    rw [← weights_wf, PX_x0, weights_map]; rfl
  simp only [wsignB, Bool.or_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  have key : ∀ (q : ℝ → Prop), (∀ w ∈ weights NoUni.pt c, q (w : ℝ)) →
      ∀ f ∈ wf c, q (f x0) := by
    intro q hq f hf
    have : f x0 ∈ (wf c).map (fun f => f x0) := List.mem_map.2 ⟨f, hf, rfl⟩
    rw [hmap] at this
    obtain ⟨w, hw, e⟩ := List.mem_map.1 this
    rw [← e]; exact hq w hw
  rcases h with h | h
  · have h0 := key (fun r => 0 < r) (fun w hw => Int.cast_pos.2 (h w hw))
    have : ∀ᶠ x in 𝓝 x0, ∀ f ∈ {f | f ∈ wf c}, 0 < f x :=
      (eventually_all_finite (List.finite_toSet _)).2 fun f hf =>
        continuousAt_const.eventually_lt (wf_cont c f hf).continuousAt (h0 f hf)
    filter_upwards [this] with x hx
    simp only [wsignB, Bool.or_eq_true, List.all_eq_true, decide_eq_true_eq, weights_wf,
      List.mem_map]
    left
    rintro _ ⟨f, hf, rfl⟩
    exact hx f hf
  · have h0 := key (fun r => r < 0) (fun w hw => Int.cast_lt_zero.2 (h w hw))
    have : ∀ᶠ x in 𝓝 x0, ∀ f ∈ {f | f ∈ wf c}, f x < 0 :=
      (eventually_all_finite (List.finite_toSet _)).2 fun f hf =>
        (wf_cont c f hf).continuousAt.eventually_lt continuousAt_const (h0 f hf)
    filter_upwards [this] with x hx
    simp only [wsignB, Bool.or_eq_true, List.all_eq_true, decide_eq_true_eq, weights_wf,
      List.mem_map]
    right
    rintro _ ⟨f, hf, rfl⟩
    exact hx f hf

theorem ev_cert {ps ds c} (h : certB NoUni.pt ps ds c = true) :
    ∀ᶠ x in 𝓝 x0, certB (PX x) ps ds c = true := by
  unfold certB at h ⊢
  rw [Bool.and_eq_true] at h
  filter_upwards [ev_wsign c h.2] with x hx
  rw [Bool.and_eq_true]
  exact ⟨h.1, hx⟩


/-! ### Persistence of the whole tree check -/

section tree
variable {ι : Type*} (F : Filter ι) (ok0 : OkFn) (okX : ι → OkFn)
  (h : ∀ ps ds c, ok0 ps ds c = true → ∀ᶠ x in F, okX x ps ds c = true)

include h

theorem chkPats_ev (p : List ℕ) : ∀ (pats : List (List Bool)) (cs : List Cert),
    chkPats ok0 p pats cs = true → ∀ᶠ x in F, chkPats (okX x) p pats cs = true := by
  intro pats
  induction pats with
  | nil =>
    intro cs hc
    cases cs with
    | nil => exact Eventually.of_forall fun x => by simp [chkPats]
    | cons c cs => simp [chkPats] at hc
  | cons l ls ih =>
    intro cs hc
    cases cs with
    | nil => simp [chkPats] at hc
    | cons c cs =>
      simp only [chkPats, Bool.and_eq_true] at hc
      filter_upwards [h _ _ _ hc.1, ih cs hc.2] with x h1 h2
      simp only [chkPats, Bool.and_eq_true]
      exact ⟨h1, h2⟩

theorem chkC_ev (p : List ℕ) (cl : Closure) (hc : chkC ok0 p cl = true) :
    ∀ᶠ x in F, chkC (okX x) p cl = true := by
  cases cl with
  | none => exact Eventually.of_forall fun x => by simpa [chkC] using hc
  | rim c => exact h _ _ _ hc
  | pats cs => exact chkPats_ev F ok0 okX h p _ cs hc

mutual
theorem chkT_ev : ∀ (t : Tree) (p : List ℕ), chkT ok0 p t = true →
    ∀ᶠ x in F, chkT (okX x) p t = true
  | .kill c, p, hc => h _ _ _ hc
  | .br cl f, p, hc => by
    simp only [chkT, Bool.and_eq_true] at hc
    filter_upwards [chkC_ev F ok0 okX h p cl hc.1, chkF_ev f p (cands p) hc.2] with x h1 h2
    simp only [chkT, Bool.and_eq_true]
    exact ⟨h1, h2⟩
theorem chkF_ev : ∀ (f : Forest) (p ms : List ℕ), chkF ok0 p ms f = true →
    ∀ᶠ x in F, chkF (okX x) p ms f = true
  | .nil, p, [], hc => Eventually.of_forall fun x => by simp [chkF]
  | .nil, p, m :: ms, hc => by simp [chkF] at hc
  | .cons m' t f, p, [], hc => by simp [chkF] at hc
  | .cons m' t f, p, m :: ms, hc => by
    simp only [chkF, Bool.and_eq_true] at hc
    filter_upwards [chkT_ev t (p ++ [m]) hc.1.2, chkF_ev f p ms hc.2] with x h1 h2
    simp only [chkF, Bool.and_eq_true]
    exact ⟨⟨hc.1.1, h1⟩, h2⟩
end

end tree

theorem tree_near : ∀ᶠ x in 𝓝 x0, chkT (certB (PX x)) [] tree = true :=
  chkT_ev (𝓝 x0) (certB NoUni.pt) (fun x => certB (PX x)) (fun _ _ _ h => ev_cert h) tree []
    tree_ok

end NoUniO
