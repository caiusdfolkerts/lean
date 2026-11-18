module

public import ToricPower.LinearSliceCompactCohomology
public import ToricPower.OpenScalarLaurentSum

/-! # Cohomology of every parallel component of the actual closed slice

The degree is the intrinsic dimension of the zero slice. Its top
cohomology has one original oriented generator for each nonempty
parallel slice intersection, with no finite component cutoff. The
comparison is linear over the original coefficient field.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.MorseCoefficients

variable (k : Type) [CommRing k] {p : Prop}

def openScalarPresentIso (present : p) :
    ModuleCat.of k (openScalar k (¬p)) ≅ ModuleCat.of k k :=
  (LinearEquiv.ofBijective (openScalar k (¬p)).subtype
    ⟨Subtype.val_injective,fun x => ⟨⟨x,fun absent => (absent present).elim⟩,rfl⟩⟩).toModuleIso

theorem openScalarAbsent_isZero (absent : ¬p) :
    IsZero (ModuleCat.of k (openScalar k (¬p))) := by
  letI : Subsingleton (openScalar k (¬p)) :=
    ⟨fun x y => Subtype.ext ((x.property absent).trans (y.property absent).symm)⟩
  exact ModuleCat.isZero_of_subsingleton _

end ToricPower.MorseCoefficients

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (selected : Set (Fin s ⊕ Fin n)) (S : Set (Fin s)) (k : Type) [Field k]

local notation "L" => arrangementZeroSlice (augmentedForms A) selected

def closedSliceComponentAllowed (value : IntegralSliceValue A selected) : Prop :=
  (Subtype.val ⁻¹'
    ((shiftedOpenCellSupport A (closedSliceChartSupport A S)
      (sliceValueRepresentative A selected value)).val : Set (Fin n → ℝ)) : Set L).Nonempty

theorem closedSliceComponentSupport_convex (value : IntegralSliceValue A selected) :
    Convex ℝ ((shiftedOpenCellSupport A (closedSliceChartSupport A S)
      (sliceValueRepresentative A selected value)).val : Set (Fin n → ℝ)) :=
  (openWeightRegion_convex (augmentedForms A) (Sum.inl '' S)
    (augmentedLatticePairing A 0)).translate_preimage_left
      (latticeLift (sliceValueRepresentative A selected value))

variable (start : IntegralSliceValue A selected → ℕ)

/-- The top class is the fixed intrinsic class on a nonempty
component, and the zero map on an empty component. -/
def closedSliceComponentTopIso (value : IntegralSliceValue A selected) :
    (closedSliceComponentFamily A selected S k start value).homology
        (Module.finrank ℝ L) ≅
      ModuleCat.of k (MorseCoefficients.openScalar k
        (¬ closedSliceComponentAllowed A selected S value)) := by
  by_cases present : closedSliceComponentAllowed A selected S value
  · exact sliceCompactFullTopClassIso A selected k _
      (closedSliceComponentSupport_convex A selected S value) present (start value) ≪≫
        (MorseCoefficients.openScalarPresentIso k present).symm
  · exact IsZero.iso (sliceCompact_isZero_homology_of_empty A selected k _ present
      (start value) (Module.finrank ℝ L))
        (MorseCoefficients.openScalarAbsent_isZero k present)

theorem closedSliceComponent_isZero_homology
    (value : IntegralSliceValue A selected) (q : ℕ)
    (different : q ≠ Module.finrank ℝ L) :
    IsZero ((closedSliceComponentFamily A selected S k start value).homology q) :=
  sliceCompactFull_isZero_homology A selected k _
    (closedSliceComponentSupport_convex A selected S value) (start value) q different

variable
  (covered : ∀ {q : ℕ} (c : Cell (augmentedForms A) q), selected ⊆ c.val.2 →
    ∃ a : Fin n → ℤ, cellCenter (augmentedForms A) c-latticeLift a ∈
      arrangementZeroSlice (augmentedForms A) selected)

include start covered in
/-- The original actual cellular complex has no cohomology outside
the intrinsic slice degree, including empty parallel intersections. -/
theorem closedSliceCellular_isZero_homology (q : ℕ)
    (different : q ≠ Module.finrank ℝ L) :
    IsZero ((closedSliceCellularComplex A selected S k).homology q) := by
  letI (value : IntegralSliceValue A selected) :
      Subsingleton ((closedSliceComponentFamily A selected S k start value).homology q) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (closedSliceComponent_isZero_homology A selected S k start value q different)
  exact (ModuleCat.isZero_of_subsingleton
    (ModuleCat.of k (Π₀ value : IntegralSliceValue A selected,
      (closedSliceComponentFamily A selected S k start value).homology q))).of_iso
    ((HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) q).mapIso
      (closedSliceCellularComponentIso A selected S covered k start) ≪≫
        ModuleDirectSum.homologyIso k (closedSliceComponentFamily A selected S k start) q)

/-- Every allowed component is retained in the unrestricted supported
Laurent module of the actual top cohomology. -/
def closedSliceCellularTopIso :
    (closedSliceCellularComplex A selected S k).homology (Module.finrank ℝ L) ≅
      ModuleCat.of k (MorseCoefficients.LaurentSupport k
        (closedSliceComponentAllowed A selected S)) :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ)
      (Module.finrank ℝ L)).mapIso
    (closedSliceCellularComponentIso A selected S covered k start) ≪≫
    ModuleDirectSum.homologyIso k (closedSliceComponentFamily A selected S k start)
      (Module.finrank ℝ L) ≪≫
    (DFinsupp.mapRange.linearEquiv (fun value =>
      (closedSliceComponentTopIso A selected S k start value).toLinearEquiv)).toModuleIso ≪≫
    (MorseCoefficients.scalarSumLinearEquiv k
      (closedSliceComponentAllowed A selected S)).toModuleIso

end ToricPower.IntegralArrangement

end
