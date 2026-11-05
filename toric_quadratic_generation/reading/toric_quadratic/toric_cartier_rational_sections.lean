module

public import PaperVerification.ToricDominantCartierPullback

@[expose] public section

/-! # Actual section membership under dominant pullback -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PaperVerification.ToricSchemes

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

namespace RationalCartierCocycle

variable (C : RationalCartierCocycle X)

theorem mem_sectionValueRange_iff_stalkwise (U : X.Opens) [Nonempty U]
    (r : X.functionField) :
    r∈C.toCartierData.sectionValueRange U ↔
      ∀ i (x : X), x∈U → x∈C.openSet i →
        r/(C.generator i : X.functionField)∈regularAtSubring X x := by
  constructor
  · rintro ⟨s,rfl⟩ i x hx hi
    change rationalValue X U s.val / (C.generator i : X.functionField) ∈
      regularAtSubring X x
    exact (congrArg (fun v : X.functionField =>
      v / (C.generator i : X.functionField) ∈ regularAtSubring X x)
        (rationalValueAt_eq X U ⟨x,hx⟩
          (show Γ(rationalFunctions X,U) from s.val))).mp
            (s.property i ⟨x,hx⟩ hi)
  · intro h
    let s := (rationalValue X U).symm r
    have hs : C.IsSection U s := by
      intro i x hi
      simpa only [rationalValueAt_eq,s,AddEquiv.apply_symm_apply] using
        h i x.val x.property hi
    exact ⟨⟨s,hs⟩,(rationalValue X U).apply_symm_apply r⟩

/-- Pullback of an actual section is a section of the genuinely
constructed Cartier pullback; the proof uses actual stalk maps. -/
theorem dominantPullback_mem_sectionValueRange
    (f : Y ⟶ X) [IsDominant f] (U : X.Opens) [Nonempty U]
    [Nonempty (f ⁻¹ᵁ U)] (r : X.functionField)
    (hr : r∈C.toCartierData.sectionValueRange U) :
    dominantFunctionFieldMap f r∈
      (C.dominantPullback f).toCartierData.sectionValueRange (f ⁻¹ᵁ U) := by
  apply ((C.dominantPullback f).mem_sectionValueRange_iff_stalkwise
    (f ⁻¹ᵁ U) _).mpr
  intro i y hy hi
  have h := (C.mem_sectionValueRange_iff_stalkwise U r).mp hr i (f y) hy hi
  change dominantFunctionFieldMap f r /
    dominantFunctionFieldMap f (C.generator i : X.functionField) ∈ regularAtSubring Y y
  simpa only [map_div₀] using
    dominantFunctionFieldMap_mem_regularAt f y
      (r/(C.generator i : X.functionField)) h

end RationalCartierCocycle

namespace CartierData

variable (D : CartierData X)

theorem mem_sectionValueRange_iff_localStalks (U : X.Opens) [Nonempty U]
    (r : X.functionField) :
    r∈D.sectionValueRange U ↔
      ∀ i (x : X), x∈U → x∈D.localCocycle.openSet i →
        r/(D.localCocycle.generator i : X.functionField)∈regularAtSubring X x := by
  rw [D.equivalent_sectionValueRange D.localCocycle.toCartierData
    D.equivalent_localCocycle U]
  exact D.localCocycle.mem_sectionValueRange_iff_stalkwise U r

theorem dominantPullback_mem_sectionValueRange
    (f : Y ⟶ X) [IsDominant f] (U : X.Opens) [Nonempty U]
    [Nonempty (f ⁻¹ᵁ U)] (r : X.functionField)
    (hr : r∈D.sectionValueRange U) :
    dominantFunctionFieldMap f r∈
      (D.dominantPullback f).sectionValueRange (f ⁻¹ᵁ U) := by
  apply D.localCocycle.dominantPullback_mem_sectionValueRange f U r
  rwa [← D.equivalent_sectionValueRange D.localCocycle.toCartierData
    D.equivalent_localCocycle U]

/-- Local affine neighborhoods suffice for the true global-section
condition. Affineness is not an assumption on the covering cocycle. -/
theorem mem_globalSectionValueRange_of_affine_ratios
    (r : X.functionField)
    (h : ∀ i (U : X.Opens) [Nonempty U], IsAffineOpen U →
      U≤D.localCocycle.openSet i →
        r/(D.localCocycle.generator i : X.functionField)∈
          (X.germToFunctionField U).hom.range) :
    r∈D.sectionValueRange ⊤ := by
  apply (D.mem_sectionValueRange_iff_localStalks ⊤ r).mpr
  intro i x hx hi
  obtain ⟨U,hU,hxU,hUi⟩ := exists_isAffineOpen_mem_and_subset hi
  letI : Nonempty U := ⟨⟨x,hxU⟩⟩
  obtain ⟨a,ha⟩ := h i U hU hUi
  rw [← ha]
  exact regular_germ_mem_regularAt X U a x hxU

end CartierData

end PaperVerification.ToricSchemes
