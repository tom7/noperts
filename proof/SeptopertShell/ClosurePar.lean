module

public import SeptopertShell.Closure
public import ParallelBool

/-!
# The closure check with the slab checks evaluated in parallel

`ClosureData.check` runs every slab's `SlabData.check` inside it, one after another. Here `checkLight` is the same
check without the slab checks, and `allSlabs` lists the slabs; `checkPar` evaluates the slab checks as parallel tasks
(`Noperts.ParallelBool.allParB`, definitionally a pure computation) and `check_of_checkPar` recovers `check`.
-/

@[expose] public section

namespace SeptopertShell

namespace ClosureData

variable (C : ClosureData)

def slabCheckLight (f : FaceData) : Bool :=
  f.slabs.all fun e =>
    decide (e.1.D0 ≤ C.dm ∧ C.dm ≤ e.1.D1) &&
    decide (∀ k : Fin 3, Poly.normalize (Poly.compose (![e.1.s, e.1.y, e.1.z] k)
      (Poly.sub (Poly.var 0) (Poly.const e.2.1)) (Poly.sub (Poly.var 1) (Poly.const e.2.2))
      (Poly.var 2)) = Poly.normalize (f.chart k))

def faceCheckLight (f : FaceData) : Bool :=
  decide (f.gi < C.gs.length) && C.slabCheckLight f && C.invCheck f && C.regCheck f &&
    coverOk f.slabs (C.hs f) f.tree f.lo0 f.hi0 f.lo1 f.hi1

/-- The closure check without the slab checks. -/
def checkLight : Bool :=
  decide (C.faces.map FaceData.gi = List.range C.gs.length) && C.faces.all C.faceCheckLight && C.b0Check

/-- All slabs of all faces. -/
def allSlabs : List SlabData := C.faces.flatMap fun f => f.slabs.map (·.1)

/-- The closure check with the slab checks in `tasks` parallel tasks. -/
def checkPar (tasks : ℕ) : Bool :=
  C.checkLight &&
    Noperts.ParallelBool.allParB (fun i => match C.allSlabs[i]? with | some sl => sl.check | none => true)
      C.allSlabs.length tasks

theorem check_of_light (h1 : C.checkLight = true)
    (h2 : ∀ f ∈ C.faces, ∀ e ∈ f.slabs, e.1.check = true) : C.check = true := by
  unfold checkLight at h1
  unfold check
  simp only [Bool.and_eq_true, List.all_eq_true] at h1 ⊢
  obtain ⟨⟨hg, hf⟩, hb⟩ := h1
  refine ⟨⟨hg, fun f hfm => ?_⟩, hb⟩
  have hl := hf f hfm
  unfold faceCheckLight at hl
  unfold faceCheck
  simp only [Bool.and_eq_true] at hl ⊢
  obtain ⟨⟨⟨⟨h0, hs⟩, hi⟩, hr⟩, hc⟩ := hl
  refine ⟨⟨⟨⟨h0, ?_⟩, hi⟩, hr⟩, hc⟩
  unfold slabCheckLight at hs
  unfold slabCheck
  simp only [List.all_eq_true, Bool.and_eq_true] at hs ⊢
  intro e he
  obtain ⟨hd, hch⟩ := hs e he
  exact ⟨⟨h2 f hfm e he, hd⟩, hch⟩

theorem check_of_checkPar {tasks : ℕ} (h : C.checkPar tasks = true) : C.check = true := by
  unfold checkPar at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hall := Noperts.ParallelBool.all_of_parB h2
  refine C.check_of_light h1 fun f hf e he => ?_
  have hm : e.1 ∈ C.allSlabs := List.mem_flatMap.mpr ⟨f, hf, List.mem_map.mpr ⟨e, he, rfl⟩⟩
  obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hm
  have := hall i hi
  simpa [List.getElem?_eq_getElem hi, hie] using this

end ClosureData

end SeptopertShell

end
