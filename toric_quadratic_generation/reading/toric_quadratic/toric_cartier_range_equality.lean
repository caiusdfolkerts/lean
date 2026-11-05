module

public import PaperVerification.ToricCartierDescent

@[expose] public section

/-! # Local equality of actual fractional sheaves detects Cartier equality -/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PaperVerification.ToricSchemes.CartierData

variable {X : Scheme.{u}} [IsIntegral X] (D E : CartierData X)

set_option backward.isDefEq.respectTransparency false in
theorem localCocycle_generatorRatios_of_ranges
    (h : ∀ (U : X.Opens) [Nonempty U],
      (D.sectionValueRange U : Set X.functionField) = E.sectionValueRange U) :
    D.localCocycle.GeneratorRatioRegular E.localCocycle := by
  intro i j x hxi hxj
  let U := invertibleOpen D.locallyFree i
  let W := invertibleOpen E.locallyFree j
  let V := U⊓W
  letI : Nonempty U := ⟨⟨i,mem_invertibleOpen D.locallyFree i⟩⟩
  letI : Nonempty W := ⟨⟨j,mem_invertibleOpen E.locallyFree j⟩⟩
  letI : Nonempty V := ⟨⟨x,hxi,hxj⟩⟩
  have hq : D.frameRationalGenerator (invertibleFrame D.locallyFree i)∈E.sectionValueRange V := by
    change D.frameRationalGenerator (invertibleFrame D.locallyFree i) ∈
      (E.sectionValueRange V : Set X.functionField)
    rw [← h V]
    exact ⟨D.frameGenerator (invertibleFrame D.locallyFree i) V inf_le_left,
      D.sectionValue_frameGenerator _ inf_le_left⟩
  obtain ⟨a,ha⟩ := (E.mem_sectionValueRange_iff
    (invertibleFrame E.locallyFree j) (V:=V) inf_le_right _).mp hq
  have hav : X.germToFunctionField V a =
      D.frameRationalGenerator (invertibleFrame D.locallyFree i) /
        E.frameRationalGenerator (invertibleFrame E.locallyFree j) :=
    (eq_div_iff (E.frameRationalGenerator_ne_zero _)).mpr ha
  change D.frameRationalGenerator (invertibleFrame D.locallyFree i) /
    E.frameRationalGenerator (invertibleFrame E.locallyFree j) ∈ regularAtSubring X x
  rw [← hav]
  exact regular_germ_mem_regularAt X V a x ⟨hxi,hxj⟩

/-- Equality of all actual fractional section images gives an actual
sheaf isomorphism preserving the rational embedding. -/
theorem equivalent_of_sectionValueRanges
    (h : ∀ (U : X.Opens) [Nonempty U],
      (D.sectionValueRange U : Set X.functionField) = E.sectionValueRange U) :
    D.Equivalent E := by
  have hCE := D.localCocycle.equivalent_of_generatorRatios E.localCocycle
    (D.localCocycle_generatorRatios_of_ranges E h)
    (E.localCocycle_generatorRatios_of_ranges D (fun U _=>(h U).symm))
  exact D.equivalent_trans E.localCocycle.toCartierData E
    (D.equivalent_trans D.localCocycle.toCartierData E.localCocycle.toCartierData
      D.equivalent_localCocycle hCE)
    (E.equivalent_symm E.localCocycle.toCartierData E.equivalent_localCocycle)

theorem sectionValueRanges_eq_of_cover {ι : Type v} (W : ι→X.Opens)
    (hcover : ∀ x : X,∃ i,x∈W i)
    (hlocal : ∀ i (V : X.Opens) [Nonempty V], V≤W i →
      (D.sectionValueRange V : Set X.functionField)=E.sectionValueRange V)
    (U : X.Opens) [Nonempty U] :
    (D.sectionValueRange U : Set X.functionField)=E.sectionValueRange U := by
  have hincl (D E : CartierData X)
      (hlocal : ∀ i (V : X.Opens) [Nonempty V], V≤W i →
        (D.sectionValueRange V : Set X.functionField)=E.sectionValueRange V) :
      (D.sectionValueRange U : Set X.functionField)⊆E.sectionValueRange U := by
    rintro r ⟨s,rfl⟩
    apply E.exists_section_of_locally_in_range U (D.sectionValue U s)
    intro x
    obtain ⟨i,hxi⟩ := hcover x.val
    let V := U⊓W i
    letI : Nonempty V := ⟨⟨x.val,x.property,hxi⟩⟩
    have hr : D.sectionValue U s∈E.sectionValueRange V := by
      change D.sectionValue U s ∈ (E.sectionValueRange V : Set X.functionField)
      rw [← hlocal i V inf_le_right]
      exact ⟨D.sheaf.presheaf.map (homOfLE inf_le_left).op s,D.sectionValue_restrict _ s⟩
    obtain ⟨t,ht⟩ := hr
    exact ⟨V,inf_le_left,⟨x.property,hxi⟩,t,fun _=>ht⟩
  exact Set.Subset.antisymm (hincl D E hlocal)
    (hincl E D (fun i V _ hV=>(hlocal i V hV).symm))

/-- It suffices to compare the genuine fractional modules locally on an
actual open cover. No abstract divisor-dictionary premise is needed. -/
theorem equivalent_of_local_ranges {ι : Type v} (W : ι→X.Opens)
    (hcover : ∀ x : X,∃ i,x∈W i)
    (hlocal : ∀ i (V : X.Opens) [Nonempty V], V≤W i →
      (D.sectionValueRange V : Set X.functionField)=E.sectionValueRange V) :
    D.Equivalent E :=
  D.equivalent_of_sectionValueRanges E
    (fun U _=>D.sectionValueRanges_eq_of_cover E W hcover hlocal U)

end PaperVerification.ToricSchemes.CartierData

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

variable {X : Scheme.{u}} [IsIntegral X] (C : RationalCartierCocycle X)

/-- The actual section image on a framed open is precisely its principal
fractional module, expressed by division by the genuine generator. -/
theorem mem_sectionValueRange_iff (i : C.index) (V : X.Opens) [Nonempty V]
    (hVi : V≤C.openSet i) (r : X.functionField) :
    r∈C.toCartierData.sectionValueRange V ↔
      r/(C.generator i : X.functionField)∈(X.germToFunctionField V).hom.range := by
  constructor
  · rintro ⟨s,rfl⟩
    exact (C.mem_submodule_iff_local i V hVi s.val).mp s.property
  · intro hr
    let t := (rationalValue X V).symm r
    have ht : t∈C.presheafSubmodule.obj (op V) := by
      apply (C.mem_submodule_iff_local i V hVi t).mpr
      simpa only [t,AddEquiv.apply_symm_apply] using hr
    exact ⟨⟨t,ht⟩,(rationalValue X V).apply_symm_apply r⟩

/-- Equality of the constructed actual Cartier sheaves recovers regular
ratios between the original, possibly differently indexed cocycles. -/
theorem generatorRatios_of_equivalent (D : RationalCartierCocycle X)
    (h : C.toCartierData.Equivalent D.toCartierData) : C.GeneratorRatioRegular D := by
  intro i j x hxi hxj
  let V := C.openSet i⊓D.openSet j
  letI : Nonempty V := ⟨⟨x,hxi,hxj⟩⟩
  have hmem : (C.generator i : X.functionField)∈C.toCartierData.sectionValueRange V := by
    apply (C.mem_sectionValueRange_iff i V inf_le_left _).mpr
    exact ⟨1,by simp⟩
  rw [C.toCartierData.equivalent_sectionValueRange D.toCartierData h V] at hmem
  obtain ⟨a,ha⟩ := (D.mem_sectionValueRange_iff j V inf_le_right _).mp hmem
  rw [← ha]
  exact regular_germ_mem_regularAt X V a x ⟨hxi,hxj⟩

/-- Arithmetic via chosen fractional-sheaf frames agrees with arithmetic
via any genuine original Cartier cocycle presentations. -/
theorem toCartierData_add_equivalent (D : RationalCartierCocycle X) :
    (C.toCartierData.add D.toCartierData).Equivalent (C.mul D).toCartierData := by
  let C' := C.toCartierData.localCocycle
  let D' := D.toCartierData.localCocycle
  have hC : C'.toCartierData.Equivalent C.toCartierData :=
    C.toCartierData.equivalent_symm C'.toCartierData C.toCartierData.equivalent_localCocycle
  have hD : D'.toCartierData.Equivalent D.toCartierData :=
    D.toCartierData.equivalent_symm D'.toCartierData D.toCartierData.equivalent_localCocycle
  exact (C'.mul D').equivalent_of_generatorRatios (C.mul D)
    (GeneratorRatioRegular.mul C' C D' D
      (C'.generatorRatios_of_equivalent C hC) (D'.generatorRatios_of_equivalent D hD))
    (GeneratorRatioRegular.mul C C' D D'
      (C.generatorRatios_of_equivalent C' C.toCartierData.equivalent_localCocycle)
      (D.generatorRatios_of_equivalent D' D.toCartierData.equivalent_localCocycle))

end PaperVerification.ToricSchemes.RationalCartierCocycle

#print axioms PaperVerification.ToricSchemes.CartierData.equivalent_of_local_ranges
