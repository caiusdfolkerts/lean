module

public import PaperVerification.ToricAmpleCommonPower
public import PaperVerification.ToricCartierBaseSections

@[expose] public section

/-! # Actual regular ratios of sections on nonvanishing opens -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {X : Scheme.{u}} [IsIntegral X] (C : RationalCartierCocycle X)

theorem nonvanishing_iff_value (i : C.index) (s : Γ(C.sheaf,⊤))
    (x : X) (hxi : x∈C.openSet i) :
    x∈C.nonvanishingOpen s ↔
      C.toCartierData.sectionValue ⊤ s≠0 ∧
        (C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s∈
          regularAtSubring X x := by
  rw [C.mem_nonvanishingOpen_iff i s x hxi,
    ← X.mem_basicOpen (C.localCoefficient i s) x hxi,
    C.mem_localNonvanishing_iff i s x hxi]

theorem sectionValue_ne_zero_of_nonvanishing (s : Γ(C.sheaf,⊤))
    [hU : Nonempty (C.nonvanishingOpen s)] : C.toCartierData.sectionValue ⊤ s≠0 := by
  let x := Classical.choice hU
  obtain ⟨i,hxi⟩ := C.covers x.val
  exact ((C.nonvanishing_iff_value i s x.val hxi).mp x.property).1

theorem section_ratio_regular (t s : Γ(C.sheaf,⊤))
    (x : X) (hx : x∈C.nonvanishingOpen s) :
    C.toCartierData.sectionValue ⊤ t/C.toCartierData.sectionValue ⊤ s∈
      regularAtSubring X x := by
  obtain ⟨i,hxi⟩ := C.covers x
  have hs := ((C.nonvanishing_iff_value i s x hxi).mp hx).2
  have ht : C.toCartierData.sectionValue ⊤ t/(C.generator i : X.functionField)∈
      regularAtSubring X x := by
    change rationalValue X ⊤ t.val / (C.generator i : X.functionField) ∈
      regularAtSubring X x
    exact t.property i ⟨x,trivial⟩ hxi
  have he : (C.toCartierData.sectionValue ⊤ t/(C.generator i : X.functionField))*
      ((C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s) =
        C.toCartierData.sectionValue ⊤ t/C.toCartierData.sectionValue ⊤ s := by
    field_simp [Units.ne_zero]
  simpa only [he] using (regularAtSubring X x).mul_mem ht hs

/-- The quotient is an actual section of the structure sheaf on the
actual nonvanishing open, including its unique value on the empty open. -/
def ratioSection (t s : Γ(C.sheaf,⊤)) : Γ(X,C.nonvanishingOpen s) := by
  classical
  by_cases hU : Nonempty (C.nonvanishingOpen s)
  · letI := hU
    exact Classical.choose (exists_regularSection_of_stalkwise X
      (C.nonvanishingOpen s)
      (C.toCartierData.sectionValue ⊤ t/C.toCartierData.sectionValue ⊤ s)
      (C.section_ratio_regular t s))
  · exact 0

theorem ratioSection_value (t s : Γ(C.sheaf,⊤))
    [Nonempty (C.nonvanishingOpen s)] :
    X.germToFunctionField (C.nonvanishingOpen s) (C.ratioSection t s)=
      C.toCartierData.sectionValue ⊤ t/C.toCartierData.sectionValue ⊤ s := by
  unfold ratioSection
  rw [dif_pos (show Nonempty (C.nonvanishingOpen s) from inferInstance)]
  exact Classical.choose_spec (exists_regularSection_of_stalkwise X
    (C.nonvanishingOpen s)
    (C.toCartierData.sectionValue ⊤ t/C.toCartierData.sectionValue ⊤ s)
    (C.section_ratio_regular t s))

@[simp] theorem ratioSection_self (s : Γ(C.sheaf,⊤)) : C.ratioSection s s=1 := by
  classical
  by_cases hU : Nonempty (C.nonvanishingOpen s)
  · letI := hU
    apply X.germToFunctionField_injective (C.nonvanishingOpen s)
    rw [C.ratioSection_value,map_one,div_self (C.sectionValue_ne_zero_of_nonvanishing s)]
  · have hbot : C.nonvanishingOpen s=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hU ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := regularSections_subsingleton_of_empty X (C.nonvanishingOpen s) hbot
    exact Subsingleton.elim _ _

/-- The coordinate ratio cuts out exactly the intersection of the two
actual nonvanishing opens. -/
theorem ratioSection_basicOpen (t s : Γ(C.sheaf,⊤)) :
    X.basicOpen (C.ratioSection t s)=C.nonvanishingOpen s⊓C.nonvanishingOpen t := by
  ext x
  by_cases hx : x∈C.nonvanishingOpen s
  · letI : Nonempty (C.nonvanishingOpen s) := ⟨⟨x,hx⟩⟩
    obtain ⟨i,hxi⟩ := C.covers x
    have hs0 := C.sectionValue_ne_zero_of_nonvanishing s
    have hsInv := ((C.nonvanishing_iff_value i s x hxi).mp hx).2
    have hs : C.toCartierData.sectionValue ⊤ s/(C.generator i : X.functionField)∈
        regularAtSubring X x := by
      change rationalValue X ⊤ s.val / (C.generator i : X.functionField) ∈
        regularAtSubring X x
      exact s.property i ⟨x,trivial⟩ hxi
    refine (X.mem_basicOpen (C.ratioSection t s) x hx).trans ?_
    change IsUnit (X.presheaf.germ (C.nonvanishingOpen s) x hx (C.ratioSection t s)) ↔
      x∈C.nonvanishingOpen s ∧ x∈C.nonvanishingOpen t
    rw [isUnit_stalk_iff,
      X.algebraMap_germ_eq_germToFunctionField hx,C.ratioSection_value]
    simp only [Opens.mem_inf,hx,true_and,inv_div]
    rw [C.nonvanishing_iff_value i t x hxi]
    constructor
    · rintro ⟨hfrac0,ht⟩
      refine ⟨(div_ne_zero_iff.mp hfrac0).1,?_⟩
      have he : ((C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s)*
          (C.toCartierData.sectionValue ⊤ s/C.toCartierData.sectionValue ⊤ t)=
            (C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ t := by
        field_simp [hs0]
      simpa only [he] using (regularAtSubring X x).mul_mem hsInv ht
    · rintro ⟨ht0,ht⟩
      refine ⟨div_ne_zero ht0 hs0,?_⟩
      have he : (C.toCartierData.sectionValue ⊤ s/(C.generator i : X.functionField))*
          ((C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ t)=
            C.toCartierData.sectionValue ⊤ s/C.toCartierData.sectionValue ⊤ t := by
        field_simp [Units.ne_zero]
      simpa only [he] using (regularAtSubring X x).mul_mem hs ht
  · constructor
    · intro h
      exact (hx (X.basicOpen_le _ h)).elim
    · exact fun h=>(hx h.1).elim

end PaperVerification.ToricSchemes.RationalCartierCocycle

namespace PaperVerification.ToricSchemes.BaseSections

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]

theorem germ_scalarMap_top (U : X.Opens) [Nonempty U] (a : k) :
    X.germToFunctionField U (scalarMap k X U a)=
      X.germToFunctionField ⊤ (scalarMap k X ⊤ a) := by
  simp only [scalarMap,RingHom.comp_apply]
  rw [germToFunctionField_restrict,germToFunctionField_restrict]

end PaperVerification.ToricSchemes.BaseSections

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.ratioSection_basicOpen
