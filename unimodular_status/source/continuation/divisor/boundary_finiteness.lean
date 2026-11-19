module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finiteness of the actual codimension-one boundary

This is the generic-point argument from the pinned TauCeti scheme divisor
theory, retained here with its complete short proof and no divisor-theory
import. A proper closed subset of a Noetherian irreducible scheme has only
finitely many codimension-one points.
-/

@[expose] public section
noncomputable section

namespace Unimodular.IntrinsicBoundary

open AlgebraicGeometry Order TopologicalSpace

variable {X : Scheme} [IrreducibleSpace X]

theorem eq_genericPoint_of_isMax {y : X} (hy : IsMax y) :
    y = genericPoint X :=
  (Specializes.antisymm (hy (genericPoint_specializes y))
    (genericPoint_specializes y)).eq

theorem eq_of_specializes_outside {U : X.Opens} (hU : (U : Set X).Nonempty)
    {x y : X} (hx : Order.coheight x = 1) (hyx : y ⤳ x) (hy : y ∉ U) : y = x := by
  by_contra hne
  have hlt : x < y := ⟨hyx, fun hxy ↦ hne (Specializes.antisymm hyx hxy).eq⟩
  have hfin : Order.coheight y < ⊤ :=
    (Order.coheight_anti hlt.le).trans_lt (hx ▸ ENat.one_lt_top)
  have hmax : IsMax y := Order.coheight_eq_zero.mp <| Order.lt_one_iff.mp <|
    hx ▸ Order.coheight_strictAnti hlt hfin
  obtain ⟨u, hu⟩ := hU
  exact hy (eq_genericPoint_of_isMax hmax ▸
    (genericPoint_specializes u).mem_open U.isOpen hu)

/-- The finite set consists of actual points of coheight one outside the
given nonempty open, rather than a chosen finite enumeration. -/
theorem finite_codimensionOne_outside [NoetherianSpace X]
    (U : X.Opens) [Nonempty U] :
    {x : {x : X // Order.coheight x = 1} | (x : X) ∉ U}.Finite := by
  classical
  obtain ⟨S, hSfinite, hSclosed, hSirreducible, hSunion⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  let g : S → X := fun Z ↦ (hSirreducible Z Z.property).genericPoint
  have hfiniteRange : (Set.range g).Finite := by
    letI : Finite S := hSfinite.to_subtype
    exact Set.finite_range g
  apply Set.Finite.of_finite_image
  · refine hfiniteRange.subset ?_
    rintro _ ⟨x, hxU, rfl⟩
    have hxUnion : (x : X) ∈ ⋃₀ S := by
      rw [← hSunion]
      exact hxU
    obtain ⟨Z, hZS, hxZ⟩ := Set.mem_sUnion.mp hxUnion
    have hg : IsGenericPoint (g ⟨Z, hZS⟩) Z :=
      (hSirreducible Z hZS).isGenericPoint_genericPoint (hSclosed Z hZS)
    have hZ : Z ⊆ (U : Set X)ᶜ := hSunion ▸ Set.subset_sUnion_of_mem hZS
    exact ⟨⟨Z, hZS⟩, eq_of_specializes_outside
      (Set.nonempty_coe_sort.mp ‹Nonempty U›) x.property
      (hg.specializes hxZ) (hZ hg.mem)⟩
  · exact Set.injOn_of_injective Subtype.val_injective

#print axioms finite_codimensionOne_outside

end Unimodular.IntrinsicBoundary
