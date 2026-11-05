import cubical.bipartite_system
import Mathlib.Logic.Relation

/-!
# Propagation through a facet cover

This file separates the graph-theoretic propagation argument from the
geometric task of showing that a cubical boundary supplies the cover.
Every cover assumption is explicit and describes incidence or connectivity;
none asserts the desired edge count or a bound on a solution space.
-/

namespace Cubical

variable {B W E F : Type*}

/-- Incidence data sufficient for crossing from one facet to its neighbor.
For a cube pair sharing a ridge, `crossing` is the matching across that ridge. -/
structure FacetCover (black : E → B) (white : E → W) (F : Type*) where
  blackMem : F → B → Prop
  whiteMem : F → W → Prop
  edgeMem : F → E → Prop
  edgeBlack : ∀ f e, edgeMem f e → blackMem f (black e)
  edgeWhite : ∀ f e, edgeMem f e → whiteMem f (white e)
  coverBlack : ∀ b, ∃ f, blackMem f b
  coverWhite : ∀ w, ∃ f, whiteMem f w
  whiteIncident : ∀ f w, whiteMem f w → ∃ e, edgeMem f e ∧ white e = w
  step : F → F → Prop
  connected : ∀ f g, Relation.ReflTransGen step f g
  crossing : ∀ f g, step f g → ∀ b, blackMem g b →
    blackMem f b ∨ ∃ e, black e = b ∧ whiteMem f (white e)

namespace FacetCover

variable {black : E → B} {white : E → W}

def VanishesOn (C : FacetCover black white F) (d : ℕ)
    (m : Motion B W d) (f : F) : Prop :=
  (∀ b, C.blackMem f b → m.1 b = 0) ∧
  (∀ w, C.whiteMem f w → m.2 w = 0)

/-- The conclusion of the local propagation lemma, expressed at graph level. -/
def LocalPropagation (C : FacetCover black white F) (d : ℕ)
    (p : W → Fin d → ℝ) : Prop :=
  ∀ (m : Motion B W d), m ∈ solutionSpace d black white p →
    ∀ f w, C.whiteMem f w →
      (∀ e, white e = w → C.blackMem f (black e) → m.1 (black e) = 0) →
      ∀ e, white e = w → m.1 (black e) = 0

theorem vanishesOn_step (C : FacetCover black white F)
    (d : ℕ) (p : W → Fin d → ℝ) (hloc : C.LocalPropagation d p)
    (m : Motion B W d) (hm : m ∈ solutionSpace d black white p)
    {f g : F} (hfg : C.step f g) (hf : C.VanishesOn d m f) :
    C.VanishesOn d m g := by
  have hb : ∀ b, C.blackMem g b → m.1 b = 0 := by
    intro b hb
    rcases C.crossing f g hfg b hb with hold | ⟨e, he, hw⟩
    · exact hf.1 b hold
    · subst b
      apply hloc m hm f (white e) hw
      · intro e' _ he'
        exact hf.1 (black e') he'
      · rfl
  refine ⟨hb, ?_⟩
  intro w hw
  obtain ⟨e, he, hew⟩ := C.whiteIncident g w hw
  have h := (mem_solutionSpace_iff d black white p m).mp hm e
  rw [hb (black e) (C.edgeBlack g e he), hew] at h
  simpa using h

theorem vanishesOn_all (C : FacetCover black white F)
    (d : ℕ) (p : W → Fin d → ℝ) (hloc : C.LocalPropagation d p)
    (m : Motion B W d) (hm : m ∈ solutionSpace d black white p)
    (f : F) (hf : C.VanishesOn d m f) : ∀ g, C.VanishesOn d m g := by
  intro g
  have hpath := C.connected f g
  induction hpath with
  | refl => exact hf
  | @tail g h hfg hgh ih => exact C.vanishesOn_step d p hloc m hm hgh ih

/-- A solution zero on one facet is zero on the entire graph. -/
theorem solution_eq_zero (C : FacetCover black white F)
    (d : ℕ) (p : W → Fin d → ℝ) (hloc : C.LocalPropagation d p)
    (m : Motion B W d) (hm : m ∈ solutionSpace d black white p)
    (f : F) (hf : C.VanishesOn d m f) : m = 0 := by
  have hall := C.vanishesOn_all d p hloc m hm f hf
  apply Prod.ext
  · funext b
    obtain ⟨g, hg⟩ := C.coverBlack b
    exact (hall g).1 b hg
  · funext w
    obtain ⟨g, hg⟩ := C.coverWhite w
    exact (hall g).2 w hg

def facetBlack (C : FacetCover black white F) (f : F)
    (e : {e : E // C.edgeMem f e}) : {b : B // C.blackMem f b} :=
  ⟨black e, C.edgeBlack f e e.property⟩

def facetWhite (C : FacetCover black white F) (f : F)
    (e : {e : E // C.edgeMem f e}) : {w : W // C.whiteMem f w} :=
  ⟨white e, C.edgeWhite f e e.property⟩

/-- Restriction to the actual variables and equations of a facet. -/
def restriction (C : FacetCover black white F) (d : ℕ)
    (p : W → Fin d → ℝ) (f : F) :
    solutionSpace d black white p →ₗ[ℝ]
      solutionSpace d (C.facetBlack f) (C.facetWhite f)
        (fun w : {w : W // C.whiteMem f w} ↦ p w) where
  toFun m :=
    ⟨(fun b ↦ m.val.1 b, fun w ↦ m.val.2 w), by
      apply (mem_solutionSpace_iff _ _ _ _ _).mpr
      intro e
      exact (mem_solutionSpace_iff d black white p m.val).mp m.property e.val⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The injective restriction asserted in Proposition 3, once the cubical
cover and the local propagation property have been established. -/
theorem restriction_injective (C : FacetCover black white F)
    (d : ℕ) (p : W → Fin d → ℝ) (hloc : C.LocalPropagation d p)
    (f : F) : Function.Injective (C.restriction d p f) := by
  intro m n h
  have hzero : C.restriction d p f (m - n) = 0 := by
    rw [map_sub, h, sub_self]
  have hvan : C.VanishesOn d ((m - n).val) f := by
    have hv := congrArg Subtype.val hzero
    refine ⟨?_, ?_⟩
    · intro b hb
      exact congrFun (congrArg Prod.fst hv) ⟨b, hb⟩
    · intro w hw
      exact congrFun (congrArg Prod.snd hv) ⟨w, hw⟩
  have hz := C.solution_eq_zero d p hloc (m - n).val (m - n).property f hvan
  have hsub : m - n = 0 := Subtype.ext hz
  exact sub_eq_zero.mp hsub

end FacetCover
end Cubical
