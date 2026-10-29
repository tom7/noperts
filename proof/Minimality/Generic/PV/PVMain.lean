module

public import Minimality.Generic.PV.PVChainCU
public import Minimality.Generic.PV.PVRim
public import Minimality.Generic.PV.PVCycle

@[expose] public section


/-! Lemma PV (general prismatoid with hidden set). -/

namespace Minimality
open scoped RealInnerProductSpace
open Finset

/-- The linear map `(x, y) ↦ (x, s y)`. -/
noncomputable def reflS (s : ℝ) : ℝ² →ₗ[ℝ] ℝ² where
  toFun x := !₂[x 0, s * x 1]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring

theorem convPos_chartS {s : ℝ} (hs : s = 1 ∨ s = -1) {n d : ℝ³} {F : Finset ℝ³}
    (h : ConvPos (F.image (planeChart n d))) : ConvPos (F.image (chartS s n d)) := by
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hinj : Function.Injective (reflS s) := by
    intro x y hxy
    have h0 := congrArg (fun z : ℝ² => z 0) hxy
    have h1 := congrArg (fun z : ℝ² => z 1) hxy
    simp [reflS] at h0 h1
    ext i; fin_cases i
    · exact h0
    · rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 hs0
  have := ConvPos.image_linear h (reflS s) hinj
  have e : (F.image (planeChart n d)).image (reflS s) = F.image (chartS s n d) := by
    rw [Finset.image_image]
    congr 1
  rwa [e] at this

section
variable {V F₁ F₂ H : Finset ℝ³} {n₁ n₂ : ℝ³} {h₁ h₂ : ℝ}

/-- **Lemma PV, core.**  The tilt signs `σ₁, σ₂` select the lower/upper chain of each face; `p₁, p₂`
are the corresponding extreme-depth vertices (the `eᵢ` of the skeleton).  If the skeleton is
cyclically unimodal, the pair is Rupert. -/
theorem lemmaPV_core (P : IsPrismPair V F₁ F₂ H n₁ n₂ h₁ h₂) (E : PVEnds F₁ F₂ n₁ n₂ h₁ h₂)
    (hinj : Set.InjOn (pvDepth n₁ n₂) V) (hH : ∀ p ∈ H, PVHidden E p)
    {σ₁ σ₂ : ℝ} (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1) {p₁ p₂ : ℝ³}
    (hp₁ : p₁ ∈ F₁) (hp₂ : p₂ ∈ F₂)
    (hp₁e : ∀ z ∈ F₁, σ₁ * pvDepth n₁ n₂ p₁ ≤ σ₁ * pvDepth n₁ n₂ z)
    (hp₂e : ∀ z ∈ F₂, σ₂ * pvDepth n₁ n₂ p₂ ≤ σ₂ * pvDepth n₁ n₂ z)
    (hCU : CU (skelList (pvDepth n₁ n₂ E.A₁) (pvDepth n₁ n₂ p₁) (pvDepth n₁ n₂ E.B₁)
      (pvDepth n₁ n₂ E.B₂) (pvDepth n₁ n₂ p₂) (pvDepth n₁ n₂ E.A₂))) : IsRupert V := by
  classical
  set d := cross n₁ n₂ with hdef
  have hd0 : d ≠ 0 := P.d_ne
  have hdd : 0 < ⟪d, d⟫ := real_inner_self_pos.mpr hd0
  have hpv : ∀ p, pvDepth n₁ n₂ p = ⟪d, p⟫ := fun _ => rfl
  have hF₁V : ∀ p ∈ F₁, p ∈ V := fun p hp => by rw [P.union]; simp [hp]
  have hF₂V : ∀ p ∈ F₂, p ∈ V := fun p hp => by rw [P.union]; simp [hp]
  have hdinj₁ : ∀ p ∈ F₁, ∀ q ∈ F₁, ⟪d, p⟫ = ⟪d, q⟫ → p = q := fun p hp q hq h =>
    hinj (hF₁V p hp) (hF₁V q hq) h
  have hdinj₂ : ∀ p ∈ F₂, ∀ q ∈ F₂, ⟪d, p⟫ = ⟪d, q⟫ → p = q := fun p hp q hq h =>
    hinj (hF₂V p hp) (hF₂V q hq) h
  have hAB₁ := P.A₁_ne_B₁ E
  have hAB₂ := P.A₂_ne_B₂ E
  -- the two chains
  obtain ⟨m₁, c₁, hc₁⟩ := faceChain hσ₁ P.n₁_ne hd0 (inner_d1 n₁ n₂) (F := F₁) (h := h₁) P.on₁
    (convPos_chartS hσ₁ P.conv₁) hdinj₁ E.A₁_mem E.B₁_mem hAB₁
    (fun y hy hne => face1_lt P.n₁_ne (P.on₁ y hy) (P.on₁ _ E.A₁_mem) (E.A₁_near y hy hne))
    (fun y hy hne => face1_lt P.n₁_ne (P.on₁ _ E.B₁_mem) (P.on₁ y hy) (E.B₁_far y hy hne))
  obtain ⟨m₂, c₂, hc₂⟩ := faceChain hσ₂ P.n₂_ne hd0 (inner_d2 n₁ n₂) (F := F₂) (h := h₂) P.on₂
    (convPos_chartS hσ₂ P.conv₂) hdinj₂ E.B₂_mem E.A₂_mem
    hAB₂.symm
    (fun y hy hne => face2_lt P.n₂_ne (P.on₂ y hy) (P.on₂ _ E.B₂_mem) (E.B₂_far y hy hne))
    (fun y hy hne => face2_lt P.n₂_ne (P.on₂ _ E.A₂_mem) (P.on₂ y hy) (E.A₂_near y hy hne))
  have hm₁ := hc₁.two
  have hm₂ := hc₂.two
  haveI : NeZero (m₁ + m₂) := ⟨by omega⟩
  set v : ℝ³ := σ₁ • cross n₂ (cross n₁ n₂) + σ₂ • cross (cross n₁ n₂) n₁ with hv
  have hnv₁ : ⟪n₁, v⟫ = σ₁ * ⟪d, d⟫ := by
    rw [hv, inner_add_right, inner_smul_right, inner_smul_right, inner_v1, inner_v2']; ring
  have hnv₂ : ⟪n₂, v⟫ = σ₂ * ⟪d, d⟫ := by
    rw [hv, inner_add_right, inner_smul_right, inner_smul_right, inner_v1', inner_v2]; ring
  set x := xr c₁ c₂ with hx
  have hxV : ∀ i, x i ∈ V := by
    intro i
    rcases rim_cases hm₁ hm₂ c₁ c₂ i with ⟨j, hj, e1, -⟩ | ⟨e1, -⟩ | ⟨j, hj, e1, -⟩ | ⟨e1, -⟩ <;>
      rw [hx, e1]
    · exact hF₁V _ (hc₁.mem _)
    · exact hF₁V _ (hc₁.mem _)
    · exact hF₂V _ (hc₂.mem _)
    · exact hF₂V _ (hc₂.mem _)
  have key : ∀ i, ∀ y ∈ V, y ≠ x i → y ≠ x (i + 1) →
      TiltSignS (-1) (x (i + 1) - x i) (y - x i) d v := by
    intro i y hy hy1 hy2
    rcases rim_cases hm₁ hm₂ c₁ c₂ i with ⟨j, hj, e1, e2⟩ | ⟨e1, e2⟩ | ⟨j, hj, e1, e2⟩ | ⟨e1, e2⟩
    · rw [hx] at hy1 hy2 ⊢
      rw [e1] at hy1 ⊢; rw [e2] at hy2 ⊢
      exact row_chain P.n₁_ne hdd (inner_d1 n₁ n₂) P.on₁ hc₁ hnv₁ hj (V_plane₁ P E hH hy) hy1 hy2
    · rw [hx] at hy1 hy2 ⊢
      rw [e1, hc₁.last (by omega)] at hy1 ⊢; rw [e2, hc₂.first (by omega)] at hy2 ⊢
      exact row_bridge₁ P E hH hy hy1 hy2 v
    · rw [hx] at hy1 hy2 ⊢
      rw [e1] at hy1 ⊢; rw [e2] at hy2 ⊢
      exact row_chain P.n₂_ne hdd (inner_d2 n₁ n₂) P.on₂ hc₂ hnv₂ hj (V_plane₂ P E hH hy) hy1 hy2
    · rw [hx] at hy1 hy2 ⊢
      rw [e1, hc₂.last (by omega)] at hy1 ⊢; rw [e2, hc₁.first (by omega)] at hy2 ⊢
      exact row_bridge₂ P E hH hy hy1 hy2 v
  -- injectivity of the rim and of its depths
  have hxinj : Function.Injective x := by
    refine xr_inj c₁ c₂ ?_ ?_ ?_
    · intro a b hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := hc₁.mono a b hlt; rw [hab] at this; exact lt_irrefl _ this
      · have := hc₁.mono b a hlt; rw [hab] at this; exact lt_irrefl _ this
    · intro a b hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := hc₂.mono a b hlt; rw [hab] at this; exact lt_irrefl _ this
      · have := hc₂.mono b a hlt; rw [hab] at this; exact lt_irrefl _ this
    · intro a b hab
      exact Finset.disjoint_left.mp P.disj (hc₁.mem a) (hab ▸ hc₂.mem b)
  have hdepth : Function.Injective fun i => ⟪x i, d⟫ := by
    intro i j hij
    apply hxinj
    apply hinj (hxV i) (hxV j)
    simpa [hpv, real_inner_comm] using hij
  -- depth lists
  set L₁ := List.ofFn (fun i : Fin m₁ => ⟪d, c₁ i⟫) with hL₁
  set L₂ := List.ofFn (fun i : Fin m₂ => ⟪d, c₂ i⟫) with hL₂
  have hlist : List.ofFn (fun i : Fin (m₁ + m₂) => ⟪d, x ((i : ℕ) : ZMod (m₁ + m₂))⟫) = L₁ ++ L₂ :=
    ofFn_xr c₁ c₂ (fun p => ⟪d, p⟫)
  have hnd : (L₁ ++ L₂).Nodup := by
    rw [← hlist, List.nodup_ofFn]
    intro i j hij
    have h1 : ((i : ℕ) : ZMod (m₁ + m₂)) = ((j : ℕ) : ZMod (m₁ + m₂)) := by
      apply hdepth
      simpa [real_inner_comm] using hij
    have h2 := congrArg ZMod.val h1
    rw [ZMod.val_cast_of_lt (by simpa using i.isLt), ZMod.val_cast_of_lt (by simpa using j.isLt)] at h2
    exact Fin.ext h2
  have hCU' : IsCyclicUnimodal fun i => ⟪x i, d⟫ := by
    rw [← CU_ofFn]
    have : (fun i : Fin (m₁ + m₂) => ⟪x ((i : ℕ) : ZMod (m₁ + m₂)), d⟫) =
        fun i : Fin (m₁ + m₂) => ⟪d, x ((i : ℕ) : ZMod (m₁ + m₂))⟫ := by
      funext i; exact real_inner_comm _ _
    rw [this, hlist]
    -- the extremes lie on the chains
    obtain ⟨i₁, hi₁⟩ := hc₁.ext_mem p₁ hp₁ (fun z hz => hp₁e z hz)
    obtain ⟨i₂, hi₂⟩ := hc₂.ext_mem p₂ hp₂ (fun z hz => hp₂e z hz)
    have hS₁ : CU (L₁ ++ L₂) ↔ CU (skel1 ⟪d, E.A₁⟫ ⟪d, p₁⟫ ⟪d, E.B₁⟫ ++ L₂) :=
      chain_cu hσ₁ hc₁ L₂ ⟪d, p₁⟫ ⟨i₁, by rw [hi₁]⟩ (fun i => hp₁e _ (hc₁.mem i)) hnd
    have hmem₁ : ∀ r ∈ skel1 ⟪d, E.A₁⟫ ⟪d, p₁⟫ ⟪d, E.B₁⟫, r ∈ L₁ := by
      intro r hr
      refine skel1_mem ?_ ?_ ?_ hr
      · rw [hL₁, List.mem_ofFn]; exact ⟨⟨0, by omega⟩, by rw [hc₁.first (by omega)]⟩
      · rw [hL₁, List.mem_ofFn]; exact ⟨i₁, by rw [hi₁]⟩
      · rw [hL₁, List.mem_ofFn]; exact ⟨⟨m₁ - 1, by omega⟩, by rw [hc₁.last (by omega)]⟩
    have hab₁ : ⟪d, E.A₁⟫ ≠ ⟪d, E.B₁⟫ := fun h =>
      hAB₁ (hinj (hF₁V _ E.A₁_mem) (hF₁V _ E.B₁_mem) h)
    have hnd₂ : (L₂ ++ skel1 ⟪d, E.A₁⟫ ⟪d, p₁⟫ ⟪d, E.B₁⟫).Nodup := by
      obtain ⟨-, h2, h3⟩ := List.nodup_append.mp hnd
      refine List.nodup_append.mpr ⟨h2, skel1_nodup hab₁, ?_⟩
      intro a ha b hb hab
      exact h3 b (hmem₁ b hb) a ha hab.symm
    have hS₂ : CU (L₂ ++ skel1 ⟪d, E.A₁⟫ ⟪d, p₁⟫ ⟪d, E.B₁⟫) ↔
        CU (skel1 ⟪d, E.B₂⟫ ⟪d, p₂⟫ ⟪d, E.A₂⟫ ++ skel1 ⟪d, E.A₁⟫ ⟪d, p₁⟫ ⟪d, E.B₁⟫) :=
      chain_cu hσ₂ hc₂ _ ⟪d, p₂⟫ ⟨i₂, by rw [hi₂]⟩ (fun i => hp₂e _ (hc₂.mem i)) hnd₂
    have hCU2 : CU (skel1 ⟪d, E.A₁⟫ ⟪d, p₁⟫ ⟪d, E.B₁⟫ ++ skel1 ⟪d, E.B₂⟫ ⟪d, p₂⟫ ⟪d, E.A₂⟫) := hCU
    exact hS₁.mpr ((CU_rot L₂ _).mp (hS₂.mpr ((CU_rot _ _).mp hCU2)))
  exact isRupert_of_rim_key V d v hd0 (by omega) x hxV (-1) (Or.inr rfl) hdepth key hCU'

/-- **Lemma PV.** A prismatoid with two disjoint faces in non-parallel planes (plus hidden
points) with distinct depths along `d = n₁ × n₂`, unique ends, and not mixed (M∓), is Rupert. -/
theorem lemmaPV (P : IsPrismPair V F₁ F₂ H n₁ n₂ h₁ h₂) (E : PVEnds F₁ F₂ n₁ n₂ h₁ h₂)
    (hinj : Set.InjOn (pvDepth n₁ n₂) V) (hH : ∀ p ∈ H, PVHidden E p)
    (hM₁ : ¬ PVMixedMinus E) (hM₂ : ¬ PVMixedPlus E) : IsRupert V := by
  classical
  have hF₁V : ∀ p ∈ F₁, p ∈ V := fun p hp => by rw [P.union]; simp [hp]
  have hF₂V : ∀ p ∈ F₂, p ∈ V := fun p hp => by rw [P.union]; simp [hp]
  have hne₁ : F₁.Nonempty := Finset.card_pos.mp (by have := P.card₁; omega)
  have hne₂ : F₂.Nonempty := Finset.card_pos.mp (by have := P.card₂; omega)
  obtain ⟨l₁, hl₁, hlo₁⟩ := Finset.exists_min_image F₁ (pvDepth n₁ n₂) hne₁
  obtain ⟨u₁, hu₁, hhi₁⟩ := Finset.exists_max_image F₁ (pvDepth n₁ n₂) hne₁
  obtain ⟨l₂, hl₂, hlo₂⟩ := Finset.exists_min_image F₂ (pvDepth n₁ n₂) hne₂
  obtain ⟨u₂, hu₂, hhi₂⟩ := Finset.exists_max_image F₂ (pvDepth n₁ n₂) hne₂
  have hcross : ∀ p ∈ F₁, ∀ q ∈ F₂, pvDepth n₁ n₂ p ≠ pvDepth n₁ n₂ q := by
    intro p hp q hq h
    have := hinj (hF₁V p hp) (hF₂V q hq) h
    exact Finset.disjoint_left.mp P.disj hp (this ▸ hq)
  have hab₁ : pvDepth n₁ n₂ E.A₁ ≠ pvDepth n₁ n₂ E.B₁ := fun h =>
    P.A₁_ne_B₁ E (hinj (hF₁V _ E.A₁_mem) (hF₁V _ E.B₁_mem) h)
  have hab₂ : pvDepth n₁ n₂ E.A₂ ≠ pvDepth n₁ n₂ E.B₂ := fun h =>
    P.A₂_ne_B₂ E (hinj (hF₂V _ E.A₂_mem) (hF₂V _ E.B₂_mem) h)
  have hsk := pv_skeleton_unimodal (pvDepth n₁ n₂ E.A₁) (pvDepth n₁ n₂ E.B₁) (pvDepth n₁ n₂ E.A₂)
    (pvDepth n₁ n₂ E.B₂) (pvDepth n₁ n₂ l₁) (pvDepth n₁ n₂ u₁) (pvDepth n₁ n₂ l₂)
    (pvDepth n₁ n₂ u₂) hab₁ hab₂
    (by
      have m1 : ∀ r ∈ [pvDepth n₁ n₂ E.A₁, pvDepth n₁ n₂ E.B₁, pvDepth n₁ n₂ l₁, pvDepth n₁ n₂ u₁],
          ∃ p ∈ F₁, pvDepth n₁ n₂ p = r := by
        intro r hr
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        exacts [⟨_, E.A₁_mem, rfl⟩, ⟨_, E.B₁_mem, rfl⟩, ⟨_, hl₁, rfl⟩, ⟨_, hu₁, rfl⟩]
      have m2 : ∀ r ∈ [pvDepth n₁ n₂ E.A₂, pvDepth n₁ n₂ E.B₂, pvDepth n₁ n₂ l₂, pvDepth n₁ n₂ u₂],
          ∃ p ∈ F₂, pvDepth n₁ n₂ p = r := by
        intro r hr
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        exacts [⟨_, E.A₂_mem, rfl⟩, ⟨_, E.B₂_mem, rfl⟩, ⟨_, hl₂, rfl⟩, ⟨_, hu₂, rfl⟩]
      intro x hx y hy
      obtain ⟨p, hp, rfl⟩ := m1 x hx
      obtain ⟨q, hq, rfl⟩ := m2 y hy
      exact hcross p hp q hq)
    ⟨hlo₁ _ E.A₁_mem, hlo₁ _ E.B₁_mem⟩ ⟨hhi₁ _ E.A₁_mem, hhi₁ _ E.B₁_mem⟩
    ⟨hlo₂ _ E.A₂_mem, hlo₂ _ E.B₂_mem⟩ ⟨hhi₂ _ E.A₂_mem, hhi₂ _ E.B₂_mem⟩
    (by
      rintro (⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩)
      · apply hM₁
        refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
        · rintro ⟨-, h⟩; exact h3 (le_antisymm (h _ hl₁) (hlo₁ _ E.A₁_mem))
        · rintro ⟨-, h⟩; exact h4 (le_antisymm (hhi₁ _ E.B₁_mem) (h _ hu₁))
        · rintro ⟨-, h⟩; exact h5 (le_antisymm (hhi₂ _ E.A₂_mem) (h _ hu₂))
        · rintro ⟨-, h⟩; exact h6 (le_antisymm (h _ hl₂) (hlo₂ _ E.B₂_mem))
      · apply hM₂
        refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
        · rintro ⟨-, h⟩; exact h3 (le_antisymm (hhi₁ _ E.A₁_mem) (h _ hu₁))
        · rintro ⟨-, h⟩; exact h4 (le_antisymm (h _ hl₁) (hlo₁ _ E.B₁_mem))
        · rintro ⟨-, h⟩; exact h5 (le_antisymm (h _ hl₂) (hlo₂ _ E.A₂_mem))
        · rintro ⟨-, h⟩; exact h6 (le_antisymm (hhi₂ _ E.B₂_mem) (h _ hu₂)))
  obtain ⟨e₁, he₁, e₂, he₂, hCU⟩ := hsk
  have hlo1 : ∀ z ∈ F₁, (1 : ℝ) * pvDepth n₁ n₂ l₁ ≤ 1 * pvDepth n₁ n₂ z := fun z hz => by
    simpa using hlo₁ z hz
  have hlo2 : ∀ z ∈ F₂, (1 : ℝ) * pvDepth n₁ n₂ l₂ ≤ 1 * pvDepth n₁ n₂ z := fun z hz => by
    simpa using hlo₂ z hz
  have hhi1 : ∀ z ∈ F₁, (-1 : ℝ) * pvDepth n₁ n₂ u₁ ≤ -1 * pvDepth n₁ n₂ z := fun z hz => by
    linarith [hhi₁ z hz]
  have hhi2 : ∀ z ∈ F₂, (-1 : ℝ) * pvDepth n₁ n₂ u₂ ≤ -1 * pvDepth n₁ n₂ z := fun z hz => by
    linarith [hhi₂ z hz]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he₁ he₂
  rcases he₁ with h | h <;> rcases he₂ with h' | h' <;> subst h <;> subst h'
  · exact lemmaPV_core P E hinj hH (Or.inl rfl) (Or.inl rfl) hl₁ hl₂ hlo1 hlo2 hCU
  · exact lemmaPV_core P E hinj hH (Or.inl rfl) (Or.inr rfl) hl₁ hu₂ hlo1 hhi2 hCU
  · exact lemmaPV_core P E hinj hH (Or.inr rfl) (Or.inl rfl) hu₁ hl₂ hhi1 hlo2 hCU
  · exact lemmaPV_core P E hinj hH (Or.inr rfl) (Or.inr rfl) hu₁ hu₂ hhi1 hhi2 hCU

end
end Minimality
