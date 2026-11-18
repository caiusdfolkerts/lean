module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part12
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration

/-!
# Actual global generation of fractional Cartier sheaves

The local-frame predicate in the toric dictionary is proved equivalent to
TauCeti's standard invertible-sheaf predicate. A global section whose rational
value equals a local Cartier generator genuinely generates the stalks on that
chart. Thus the resulting global-generation theorem uses ordinary sheaf stalks
and the ordinary nonvanishing locus, not a renamed support-function condition.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u
namespace Unimodular.NefBig

open AlgebraicGeometry CategoryTheory Opposite
open PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X]

/-- The two existing predicates mean the same local rank-one sheaf property. -/
theorem isInvertibleModule_iff_standard (M : X.Modules) :
    IsInvertibleModule M ↔ TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M := by
  constructor
  · intro hM
    choose U hx e using hM
    exact (TauCeti.AlgebraicGeometry.SheafOfModules.LocalTrivializations.ofForallMem
      X U hx (fun x => (e x).some.symm)).isInvertible
  · intro hM
    letI := hM
    intro x
    obtain ⟨U, t, hx⟩ := Scheme.Modules.exists_mem_trivialization M x
    exact ⟨U, hx, ⟨t.symm ≪≫ TauCeti.SheafOfModules.freePUnitIsoUnit
      (X.ringCatSheaf.over U)⟩⟩

/-- The original Cartier sheaf as a standard actual invertible sheaf. -/
def cartierInvertibleSheaf (D : CartierData X) : TauCeti.AlgebraicGeometry.InvertibleSheaf X :=
  ⟨D.sheaf, (isInvertibleModule_iff_standard D.sheaf).mp D.locallyFree⟩

/-- The original cocycle sheaf is retained literally. -/
def cocycleInvertibleSheaf (C : RationalCartierCocycle X) :
    TauCeti.AlgebraicGeometry.InvertibleSheaf X :=
  cartierInvertibleSheaf C.toCartierData

instance cocycle_standard_isInvertible (C : RationalCartierCocycle X) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X C.sheaf :=
  (cocycleInvertibleSheaf C).property

variable (C : RationalCartierCocycle X)

/-- A section with the local generator's actual rational value has local
coordinate one on every smaller open, including the empty open. -/
theorem coordinate_of_global_generator (i : C.index)
    (s : Γ(C.sheaf, ⊤))
    (hs : C.toCartierData.sectionValue ⊤ s = (C.generator i : X.functionField))
    (V : X.Opens) (hVi : V ≤ C.openSet i) :
    C.localCoordinates i V hVi (C.sheaf.presheaf.map V.leTop.op s) = 1 := by
  classical
  by_cases hV : Nonempty V
  · letI := hV
    apply X.germToFunctionField_injective V
    rw [C.localCoordinates_value, map_one]
    change rationalValue X V ((rationalFunctions X).presheaf.map V.leTop.op s.val) /
      (C.generator i : X.functionField) = 1
    rw [rationalValue_restrict]
    change rationalValue X ⊤ s.val = (C.generator i : X.functionField) at hs
    rw [hs, div_self (Units.ne_zero _)]
  · have hvbot : V = ⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hV ⟨⟨x, hx⟩⟩)
      · exact bot_le
    letI := regularSections_subsingleton_of_empty X V hvbot
    exact Subsingleton.elim _ _

/-- The rational generator criterion implies actual stalk generation over
the whole chart, via bijective scalar multiplication on every smaller open. -/
theorem chart_le_nonvanishingLocus (i : C.index)
    (s : Γ(C.sheaf, ⊤))
    (hs : C.toCartierData.sectionValue ⊤ s = (C.generator i : X.functionField)) :
    C.openSet i ≤ C.sheaf.nonvanishingLocus s := by
  apply (Scheme.Modules.le_nonvanishingLocus_iff s (C.openSet i).leTop).mpr
  intro V j
  let e := C.localCoordinates i V j.le
  have hc : e (C.sheaf.presheaf.map (j ≫ (C.openSet i).leTop).op s) = 1 :=
    coordinate_of_global_generator C i s hs V j.le
  have he (a : Γ(X, V)) :
      a • C.sheaf.presheaf.map (j ≫ (C.openSet i).leTop).op s = e.symm a := by
    apply e.injective
    rw [e.map_smul, hc, smul_eq_mul, mul_one, e.apply_symm_apply]
  simpa only [he] using e.symm.bijective

/-- Global sections realizing the actual local generators give standard
global generation of the actual original sheaf. -/
theorem isGloballyGenerated_of_global_generators
    (h : ∀ i : C.index, ∃ s : Γ(C.sheaf, ⊤),
      C.toCartierData.sectionValue ⊤ s = (C.generator i : X.functionField)) :
    (cocycleInvertibleSheaf C).IsGloballyGenerated := by
  apply TauCeti.AlgebraicGeometry.InvertibleSheaf.isGloballyGenerated_iff.mpr
  intro x
  obtain ⟨i, hi⟩ := C.covers x
  obtain ⟨s, hs⟩ := h i
  exact ⟨s, chart_le_nonvanishingLocus C i s hs hi⟩

/-- The conclusion supplies the ordinary epimorphism from a free sheaf,
through the standard library equivalence for generating global sections. -/
theorem generatingSections_of_global_generators
    (h : ∀ i : C.index, ∃ s : Γ(C.sheaf, ⊤),
      C.toCartierData.sectionValue ⊤ s = (C.generator i : X.functionField)) :
    Nonempty C.sheaf.GeneratingSections :=
  (isGloballyGenerated_of_global_generators C h).nonempty_generatingSections

#print axioms isInvertibleModule_iff_standard
#print axioms chart_le_nonvanishingLocus
#print axioms isGloballyGenerated_of_global_generators
#print axioms generatingSections_of_global_generators

end Unimodular.NefBig

#check Unimodular.NefBig.isGloballyGenerated_of_global_generators
