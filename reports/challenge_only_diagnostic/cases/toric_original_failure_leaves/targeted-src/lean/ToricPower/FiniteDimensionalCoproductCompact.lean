module

public import ToricPower.FiniteCoproductRetractions
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite-dimensional vector spaces are compact for actual coproducts

Every individual vector in a categorical coproduct has finite support,
proved through the concrete direct-sum comparison. A finite basis gives
one common finite support for an entire linear map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

namespace ToricPower.CompactExtraction

universe u
variable (k : Type u) [Field k]

theorem moduleSupport_mono {I : Type u} (family : I → ModuleCat.{u} k)
    (x : (∐ family : ModuleCat.{u} k)) {s t : Finset I} (subset : s ⊆ t)
    (support : finiteCoproductProjector family s x = x) :
    finiteCoproductProjector family t x = x := by
  have equation := ConcreteCategory.congr_hom (finiteCoproductProjector_mono family subset) x
  simpa only [ModuleCat.comp_apply, support] using equation

theorem module_coproduct_element_support {I : Type u} (family : I → ModuleCat.{u} k)
    (x : (∐ family : ModuleCat.{u} k)) : ∃ s : Finset I, finiteCoproductProjector family s x = x := by
  classical
  let e := ModuleCat.coprodIsoDirectSum family
  have support (y : ⨁ i, family i) :
      ∃ s : Finset I, finiteCoproductProjector family s (e.inv y) = e.inv y := by
    induction y using DirectSum.induction_on with
    | zero => exact ⟨∅, by simp⟩
    | of i y =>
        have value : e.inv (DirectSum.of (fun i => family i) i y) = Sigma.ι family i y := by
          change (ModuleCat.ofHom (DirectSum.lof k I (fun i => family i) i) ≫ e.inv) y = _
          rw [ModuleCat.lof_coprodIsoDirectSum_inv]
        refine ⟨{i}, ?_⟩
        rw [value]
        exact ConcreteCategory.congr_hom
          (ι_finiteCoproductProjector family {i} (Finset.mem_singleton_self i)) y
    | add x y hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨t, ht⟩ := hy
        refine ⟨s ∪ t, ?_⟩
        have hs' := moduleSupport_mono k family (e.inv x) (t := s ∪ t)
          Finset.subset_union_left hs
        have ht' := moduleSupport_mono k family (e.inv y) (t := s ∪ t)
          Finset.subset_union_right ht
        simpa only [map_add, hs', ht']
  obtain ⟨s, hs⟩ := support (e.hom x)
  refine ⟨s, ?_⟩
  have inverse : e.inv (e.hom x) = x := by
    exact ConcreteCategory.congr_hom e.hom_inv_id x
  simpa only [inverse] using hs

/-- The finite-support compactness condition for an actual
finite-dimensional vector space and arbitrary actual coproducts. -/
theorem finiteDimensional_coproductCompact (M : ModuleCat.{u} k) [FiniteDimensional k M] :
    CoproductCompact M := by
  classical
  apply coproductCompact_iff_projector.mpr
  intro I family f
  let basis := Module.finBasis k M
  choose support equations using
    (fun j => module_coproduct_element_support k family (f (basis j)))
  let allSupport := Finset.univ.biUnion support
  refine ⟨allSupport, ?_⟩
  apply ModuleCat.hom_ext
  apply basis.ext
  intro j
  exact moduleSupport_mono k family (f (basis j))
    (Finset.subset_biUnion_of_mem support (Finset.mem_univ j)) (equations j)

end ToricPower.CompactExtraction

end

