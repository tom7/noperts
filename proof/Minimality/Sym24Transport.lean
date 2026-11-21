module

public import Minimality.Type02Frame
public import Minimality.FaceChordFac
public import Minimality.Type24SAT.Facets24
public import Minimality.RCell24

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.RCell

namespace Minimality.T24.Sym

/-- Vertex involution `π = (2 6)(4 5)` (explicit table, so every evaluation is by `rfl`). -/
def pi24 : Equiv.Perm (Fin 7) where
  toFun := ![0, 1, 6, 3, 5, 4, 2]
  invFun := ![0, 1, 6, 3, 5, 4, 2]
  left_inv := by decide
  right_inv := by decide

/-- Facet involution `σ = (0 1)(2 4)(6 8)`. -/
def sig24 : Equiv.Perm (Fin 9) where
  toFun := ![1, 0, 4, 3, 2, 5, 8, 7, 6]
  invFun := ![1, 0, 4, 3, 2, 5, 8, 7, 6]
  left_inv := by decide
  right_inv := by decide

theorem s24_sym : ∀ (t : Fin 9) (i : Fin 7),
    i ∈ s0x_S24 t ↔ pi24 i ∈ s0x_S24 (sig24 t) := by decide

/-- The mirror facet data of `x ∘ π`. -/
noncomputable def sym24 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    S0xFac 9 s0x_S24 (x ∘ pi24) where
  f t := F.f (sig24 t)
  N t := F.N (sig24 t)
  hN _ y z := F.hN _ y z
  zero t i hi := F.zero _ _ ((s24_sym t i).1 hi)
  neg t i hi := F.neg _ _ (fun h => hi ((s24_sym t i).2 h))

@[simp] theorem sym24_N {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    (sym24 F).N t = F.N (sig24 t) := rfl

@[simp] theorem sym24_f {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    (sym24 F).f t = F.f (sig24 t) := rfl

/-- `IsRupert` transfers along the relabelling. -/
theorem isRupert_of_comp_pi24 {x : Fin 7 → ℝ³} (h : IsRupert (univ.image (x ∘ pi24))) :
    IsRupert (univ.image x) := by
  rwa [Minimality.CaseC18.isRupert_image_comp_perm] at h

/-- Generic transport of `FaceChordView` along a relabelling of vertices and facets. -/
theorem faceChordView_transport {N nf : ℕ} {S S' : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (π : Equiv.Perm (Fin N)) (σ : Equiv.Perm (Fin nf))
    {F : S0xFac nf S x} {F' : S0xFac nf S' (x ∘ π)}
    (hN : ∀ t, F'.N t = F.N (σ t)) (hf : ∀ t, F'.f t = F.f (σ t))
    (hS : ∀ t i, i ∈ S' t ↔ π i ∈ S (σ t)) {t : Fin nf}
    (h : FaceChordView F' t) : FaceChordView F (σ t) := by
  rcases h with ⟨u, k, hne, r, a, w, ρ, hnu, hk, hA, hB, hρ, hcyc, hin, hmid, hinj, hz, hwS, hfar,
    hoff⟩
  have : NeZero k := hne
  refine ⟨u, k, hne, fun i => π (r i), a, w, ρ, ?_, hk, (hS _ _).1 hA, (hS _ _).1 hB, hρ,
    hcyc, ?_, ?_, hinj, hz, fun h => hwS ((hS _ _).2 h), ?_, ?_⟩
  · rw [← hN]; exact hnu
  · intro q hq hqr i
    obtain ⟨q', rfl⟩ := π.surjective q
    exact hin q' (fun h => hq ((hS _ _).1 h)) (fun j h => hqr j (by rw [h])) i
  · intro q hq hqr
    obtain ⟨q', rfl⟩ := π.surjective q
    exact hmid q' ((hS _ _).2 hq) (fun j h => hqr j (by rw [h]))
  · intro m hm hmS
    have := hfar m hm (fun h => hmS ((hS _ _).1 h))
    rwa [hf] at this
  · rw [← hN]; exact hoff

/-- `FaceChordView` of the mirror solid gives `FaceChordView` of `x` at facet `σ t`. -/
theorem faceChordView_sym {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {t : Fin 9}
    (h : FaceChordView (sym24 F) t) : FaceChordView F (sig24 t) :=
  faceChordView_transport pi24 sig24 (F := F) (F' := sym24 F) (fun _ => rfl) (fun _ => rfl)
    s24_sym h

theorem isRupert_of_faceChordView_sym {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {t : Fin 9}
    (h : FaceChordView (sym24 F) t) : IsRupert (univ.image x) :=
  isRupert_of_faceChordView F (faceChordView_sym F h)

/-- `LexAny` transfers along the `(2 6)(4 5)` symmetry `sym24`. -/
theorem lexAny_sym {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : LexAny (sym24 F)) :
    LexAny F := by
  rcases h with ⟨k, hne, c, U, Dn, b, d1, d2, hk, hc, hcyc, hU, hD, hR⟩
  refine ⟨k, hne, pi24 ∘ c, U.map sig24.toEmbedding, Dn.map sig24.toEmbedding, b, d1, d2,
    hk, pi24.injective.comp hc, ?_, ?_, ?_, hR⟩
  · intro i
    obtain ⟨a, ha, b, hb, h1, h2, h3, h4, h5⟩ := hcyc i
    refine ⟨sig24 a, mem_map_of_mem _ ha, sig24 b, mem_map_of_mem _ hb,
      (s24_sym a (c i)).1 h1, (s24_sym b (c i)).1 h2,
      (s24_sym a (c (i + 1))).1 h3, (s24_sym b (c (i + 1))).1 h4, ?_⟩
    intro q hqi hqi1
    obtain ⟨q', rfl⟩ := pi24.surjective q
    rcases h5 q' (fun h => hqi (by simp [h])) (fun h => hqi1 (by simp [h])) with hq | hq
    · exact Or.inl (fun h => hq ((s24_sym a q').2 h))
    · exact Or.inr (fun h => hq ((s24_sym b q').2 h))
  · intro t' ht'
    rcases mem_map.mp ht' with ⟨t, ht, rfl⟩
    exact hU t ht
  · intro t' ht'
    rcases mem_map.mp ht' with ⟨t, ht, rfl⟩
    exact hD t ht

@[simp] theorem pi24_pi24 (i : Fin 7) : pi24 (pi24 i) = i := by
  revert i; decide

@[simp] theorem sig24_sig24 (t : Fin 9) : sig24 (sig24 t) = t := by
  revert t; decide

theorem lexAny_iff_sym {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    LexAny (sym24 F) ↔ LexAny F := by
  constructor
  · exact lexAny_sym F
  · intro h
    rcases h with ⟨k, hne, c, U, Dn, b, d1, d2, hk, hc, hcyc, hU, hD, hR⟩
    refine ⟨k, hne, pi24 ∘ c, U.map sig24.toEmbedding, Dn.map sig24.toEmbedding, b, d1, d2,
      hk, pi24.injective.comp hc, ?_, ?_, ?_, by simpa [Function.comp_apply, pi24_pi24] using hR⟩
    · intro i
      obtain ⟨a, ha, b, hb, h1, h2, h3, h4, h5⟩ := hcyc i
      refine ⟨sig24 a, mem_map_of_mem _ ha, sig24 b, mem_map_of_mem _ hb,
        by simpa [pi24_pi24, sig24_sig24] using (s24_sym (sig24 a) (pi24 (c i))).2 (by simpa),
        by simpa [pi24_pi24, sig24_sig24] using (s24_sym (sig24 b) (pi24 (c i))).2 (by simpa),
        by simpa [pi24_pi24, sig24_sig24] using (s24_sym (sig24 a) (pi24 (c (i + 1)))).2 (by simpa),
        by simpa [pi24_pi24, sig24_sig24] using (s24_sym (sig24 b) (pi24 (c (i + 1)))).2 (by simpa),
        ?_⟩
      intro q hqi hqi1
      obtain ⟨q', rfl⟩ := pi24.surjective q
      rcases h5 q' (fun h => hqi (by simp [h])) (fun h => hqi1 (by simp [h])) with hq | hq
      · exact Or.inl (fun h => hq (by
          have := (s24_sym (sig24 a) (pi24 q')).1 (by simpa using h)
          simpa [sig24_sig24, pi24_pi24] using this))
      · exact Or.inr (fun h => hq (by
          have := (s24_sym (sig24 b) (pi24 q')).1 (by simpa using h)
          simpa [sig24_sig24, pi24_pi24] using this))
    · intro t' ht'
      rcases mem_map.mp ht' with ⟨t, ht, rfl⟩
      simpa [sig24_sig24] using hU t ht
    · intro t' ht'
      rcases mem_map.mp ht' with ⟨t, ht, rfl⟩
      simpa [sig24_sig24] using hD t ht

/-- `SplitAny24` transfers along the `(2 6)(4 5)` symmetry `sym24`. -/
theorem splitAny24_sym {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : SplitAny24 (sym24 F)) :
    SplitAny24 F := by
  rcases h with ⟨k, hne, c, pat, u, v, a, cc, σ, hk, hc, hcyc, hfac, hca, hca1, hrows⟩
  refine ⟨k, hne, pi24 ∘ c, pat ∘ sig24, u, v, a, cc, σ,
    hk, pi24.injective.comp hc, ?_, ?_, hca, hca1, hrows⟩
  · intro i
    obtain ⟨ea, eb, hea, heb, h0a, h0b, h1a, h1b, hs⟩ := hcyc i
    refine ⟨sig24 ea, sig24 eb, by simp [hea], by simp [heb],
      (s24_sym ea (c i)).1 h0a, (s24_sym eb (c i)).1 h0b,
      (s24_sym ea (c (i + 1))).1 h1a, (s24_sym eb (c (i + 1))).1 h1b, ?_⟩
    intro q hqi hqi1
    obtain ⟨q', rfl⟩ := pi24.surjective q
    rcases hs q' (fun h => hqi (by simp [h])) (fun h => hqi1 (by simp [h])) with hq | hq
    · exact Or.inl (fun h => hq ((s24_sym ea q').2 h))
    · exact Or.inr (fun h => hq ((s24_sym eb q').2 h))
  · intro t
    simpa [sig24_sig24] using hfac (sig24 t)

theorem splitAny24_iff_sym {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    SplitAny24 (sym24 F) ↔ SplitAny24 F := by
  constructor
  · exact splitAny24_sym F
  · intro h
    rcases h with ⟨k, hne, c, pat, u, v, a, cc, σ, hk, hc, hcyc, hfac, hca, hca1, hrows⟩
    refine ⟨k, hne, pi24 ∘ c, pat ∘ sig24, u, v, a, cc, σ,
      hk, pi24.injective.comp hc, ?_, ?_, hca, hca1,
      by simpa [Function.comp_apply, pi24_pi24] using hrows⟩
    · intro i
      obtain ⟨ea, eb, hea, heb, h0a, h0b, h1a, h1b, hs⟩ := hcyc i
      refine ⟨sig24 ea, sig24 eb, by simp [hea], by simp [heb],
        by simpa [pi24_pi24, sig24_sig24] using (s24_sym (sig24 ea) (pi24 (c i))).2 (by simpa),
        by simpa [pi24_pi24, sig24_sig24] using (s24_sym (sig24 eb) (pi24 (c i))).2 (by simpa),
        by simpa [pi24_pi24, sig24_sig24] using (s24_sym (sig24 ea) (pi24 (c (i + 1)))).2 (by simpa),
        by simpa [pi24_pi24, sig24_sig24] using (s24_sym (sig24 eb) (pi24 (c (i + 1)))).2 (by simpa),
        ?_⟩
      intro q hqi hqi1
      obtain ⟨q', rfl⟩ := pi24.surjective q
      rcases hs q' (fun h => hqi (by simp [h])) (fun h => hqi1 (by simp [h])) with hq | hq
      · exact Or.inl (fun h => hq (by
          have := (s24_sym (sig24 ea) (pi24 q')).1 (by simpa using h)
          simpa [sig24_sig24, pi24_pi24] using this))
      · exact Or.inr (fun h => hq (by
          have := (s24_sym (sig24 eb) (pi24 q')).1 (by simpa using h)
          simpa [sig24_sig24, pi24_pi24] using this))
    · intro t
      simpa [sig24_sig24] using hfac (sig24 t)

end Minimality.T24.Sym
