module

public import Papers.GraphicalZonotopes.BookPositiveCircuit
public import Papers.GraphicalZonotopes.BoundaryContexts
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [DecidableEq J]

/-- The paper's rows are unordered hub pairs, each with every conditioning
subset of the remaining hubs. `BoundaryContext` uses the increasing ordering
only to select one representative of each unordered pair. -/
abbrev HubResponseRow (H : Type*) [Fintype H] [LinearOrder H] :=
  BoundaryContext (⊤ : SimpleGraph H)

def centralSlack : graphicalFunctionSpace (⊤ : SimpleGraph H) →ₗ[ℝ]
    (HubResponseRow H → ℝ) := boundarySlackMap ⊤

/-- This is literally the elemental map from all central Möbius coefficients,
including every subset of size at least two. -/
def centralCoefficientSlack : (CliqueIndex (⊤ : SimpleGraph H) → ℝ) →ₗ[ℝ]
    (HubResponseRow H → ℝ) :=
  centralSlack ∘ₗ (graphicalCoordinatesEquiv ⊤).toLinearMap

theorem centralSlack_injective : Function.Injective (centralSlack (H:=H)) :=
  boundarySlackMap_injective ⊤

theorem centralCoefficientSlack_injective :
    Function.Injective (centralCoefficientSlack (H:=H)) :=
  centralSlack_injective.comp (graphicalCoordinatesEquiv ⊤).injective

theorem centralCoefficientSlack_range :
    LinearMap.range (centralCoefficientSlack (H:=H))=
      LinearMap.range (centralSlack (H:=H)) := by
  apply le_antisymm
  · rintro x ⟨c,rfl⟩
    exact ⟨graphicalCoordinatesEquiv ⊤ c,rfl⟩
  · rintro x ⟨z,rfl⟩
    exact ⟨(graphicalCoordinatesEquiv ⊤).symm z,by
      simp only [centralCoefficientSlack,LinearMap.comp_apply,
        LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]⟩

def responseVector (F : SetFunction H) : HubResponseRow H → ℝ :=
  fun r => negativeResponse F r.1.1.1 r.1.1.2 r.2.1

def weightedResponse (F : J → SetFunction H) :
    (J → ℝ) →ₗ[ℝ] (HubResponseRow H → ℝ) where
  toFun w r := ∑ j : J,w j*responseVector (F j) r
  map_add' w t := by ext r; simp [add_mul,sum_add_distrib]
  map_smul' c w := by ext r; simp [mul_assoc,mul_sum]

/-- The complete relation map in the actual response quotient. Its kernel
contains all real relations among the classes, not merely positive ones. -/
def quotientRelation (F : J → SetFunction H) :
    (J → ℝ) →ₗ[ℝ]
      ((HubResponseRow H → ℝ) ⧸ LinearMap.range (centralCoefficientSlack (H:=H))) :=
  (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ ∘ₗ weightedResponse F

theorem negativeResponse_comm (F : SetFunction H) (u v : H) (S : Finset H) :
    negativeResponse F u v S=negativeResponse F v u S := by
  simp only [negativeResponse,delta_comm u v]

theorem central_function {z : SetFunction H} (hz : TranslationNormalized z) :
    z∈graphicalFunctionSpace (⊤ : SimpleGraph H) := by
  refine ⟨hz,?_⟩
  intro u v huv hnon S hu hv
  exact False.elim (hnon ((SimpleGraph.top_adj u v).mpr huv))

theorem remaining_subset_commonNeighbors (u v : H) (S : Finset H)
    (hu : u∉S) (hv : v∉S) : S⊆commonNeighbors (⊤ : SimpleGraph H) u v := by
  intro a ha
  apply (mem_commonNeighbors _ _ _ _).mpr
  constructor
  · apply (SimpleGraph.top_adj u a).mpr
    intro he
    exact hu (he.symm ▸ ha)
  · apply (SimpleGraph.top_adj v a).mpr
    intro he
    exact hv (he.symm ▸ ha)

/-- Quantifying over the row type is equivalent to quantifying over every
actual elemental difference, with no context omitted. -/
theorem compatible_iff_rows {z : SetFunction H} (hz : TranslationNormalized z)
    (F : J → SetFunction H) (w : J → ℝ) :
    Compatible z F w ↔
      centralSlack ⟨z,central_function hz⟩=weightedResponse F w := by
  constructor
  · intro hc
    funext r
    have hu : r.1.1.1∉r.2.1 := by
      intro hm
      exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) hm)
    have hv : r.1.1.2∉r.2.1 := by
      intro hm
      exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) hm)
    exact hc _ _ (ne_of_lt r.1.2.1) _ hu hv
  · intro he u v huv S hu hv
    have hordered : ∀ a b,a<b → a∉S → b∉S →
        delta z a b S=∑ j : J,w j*negativeResponse (F j) a b S := by
      intro a b hab ha hb
      let e : OrientedEdge (⊤ : SimpleGraph H):=
        ⟨(a,b),hab,(SimpleGraph.top_adj a b).mpr (ne_of_lt hab)⟩
      let r : HubResponseRow H:=⟨e,⟨S,mem_powerset.mpr
        (remaining_subset_commonNeighbors a b S ha hb)⟩⟩
      exact congrFun he r
    rcases lt_or_gt_of_ne huv with hlt | hgt
    · exact hordered u v hlt hu hv
    · rw [delta_comm u v,hordered v u hgt hv hu]
      apply sum_congr rfl
      intro j hj
      rw [negativeResponse_comm (F j) v u]

theorem mem_quotientRelation_ker_iff (F : J → SetFunction H) (w : J → ℝ) :
    w∈LinearMap.ker (quotientRelation F) ↔
      ∃ z : SetFunction H,TranslationNormalized z ∧ Compatible z F w := by
  change (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ
      (weightedResponse F w)=0 ↔ _
  rw [← LinearMap.mem_ker,Submodule.ker_mkQ,centralCoefficientSlack_range]
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z.1,z.2.1,(compatible_iff_rows z.2.1 F w).mpr hz⟩
  · rintro ⟨z,hz,hc⟩
    exact ⟨⟨z,central_function hz⟩,(compatible_iff_rows hz F w).mp hc⟩

/-- The basis-free compatibility formulation used in the zero-equation proof
is exactly the paper's one-dimensional quotient relation condition. -/
theorem uniqueIntegrableRelation_iff_ker_eq_span
    (F : J → SetFunction H) (w : J → ℝ)
    (hw : ∃ z : SetFunction H,TranslationNormalized z ∧ Compatible z F w) :
    UniqueIntegrableRelation F w ↔
      LinearMap.ker (quotientRelation F)=Submodule.span ℝ {w} := by
  have hwm : w∈LinearMap.ker (quotientRelation F):=
    (mem_quotientRelation_ker_iff F w).mpr hw
  constructor
  · intro huniq
    apply le_antisymm
    · intro t ht
      obtain ⟨c,hc⟩:=huniq t ((mem_quotientRelation_ker_iff F t).mp ht)
      exact Submodule.mem_span_singleton.mpr ⟨c,hc.symm⟩
    · apply Submodule.span_le.mpr
      intro t ht
      have he : t=w := Set.mem_singleton_iff.mp ht
      subst t
      exact hwm
  · intro hker t ht
    have hm:=(mem_quotientRelation_ker_iff F t).mpr ht
    rw [hker,Submodule.mem_span_singleton] at hm
    obtain ⟨c,hc⟩:=hm
    exact ⟨c,hc.symm⟩

/-- Literal positive-circuit extremality: the relation space is the kernel of
the map to the quotient by the central Möbius image. -/
theorem positive_quotient_circuit_extreme [Nonempty J]
    {z : SetFunction H} (hz : TranslationNormalized z)
    {F : J → SetFunction H} (hF : ∀ j,IsMonotoneBoolean (F j))
    {w : J → ℝ} (hw : ∀ j,0<w j) (hc : Compatible z F w)
    (hd : Module.finrank ℝ (LinearMap.ker (quotientRelation F))=1) :
    ExtremeSupermodular (assembled z F w) := by
  obtain ⟨j₀⟩:=‹Nonempty J›
  have hne : w≠0 := by
    intro he
    have hj:=hw j₀
    rw [he] at hj
    simp at hj
  have hm : w∈LinearMap.ker (quotientRelation F):=
    (mem_quotientRelation_ker_iff F w).mpr ⟨z,hz,hc⟩
  have hker:=eq_span_singleton_of_mem_of_finrank_eq_one hd hm hne
  exact positive_circuit_extreme hz hF (fun j => (hw j).le)
    ⟨j₀,ne_of_gt (hw j₀)⟩ hc
    ((uniqueIntegrableRelation_iff_ker_eq_span F w ⟨z,hz,hc⟩).mpr hker)

end BooleanModule
end GraphicalZonotopes
