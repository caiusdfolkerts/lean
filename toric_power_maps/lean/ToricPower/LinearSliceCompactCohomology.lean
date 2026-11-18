module

public import ToricPower.ClosedSliceComponentComplex

/-! # Full convex slice supports, including empty intersections

The compact-support complex does not depend on where its exhaustion
starts. The comparison uses its actual full cell coordinates and its
actual differential. Thus every nonempty convex slice intersection has
the intrinsic top class, while an empty intersection gives the zero
complex. No nonemptiness of an arbitrarily chosen first window is
assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (zeroRows : Set (Fin s ⊕ Fin n)) (k : Type) [Field k]
  (U : OpenCellSupport A)

local notation "L" => arrangementZeroSlice (augmentedForms A) zeroRows

/-- Every exhaustion start gives the same actual cellular complex,
through the identity on all full-support cell coordinates. -/
def sliceCompactStartIso (r₀ r₁ : ℕ) :
    sliceCompactCochainComplex A zeroRows k U r₀ ≅
      sliceCompactCochainComplex A zeroRows k U r₁ :=
  cochainIsoOfFreeCoordinates k _ _ (SliceSupportCell A zeroRows U)
    (sliceCompactCoordinates A zeroRows U k r₀)
    (sliceCompactCoordinates A zeroRows U k r₁) (by
      intro q c r
      ext d
      rw [sliceCompactCoordinates_differential_generator,
        sliceCompactCoordinates_differential_generator])

/-- Empty actual support has no cells in any degree. -/
theorem sliceCompact_isZero_X_of_empty
    (empty : ¬ (Subtype.val ⁻¹' (U.val : Set (Fin n → ℝ)) : Set L).Nonempty)
    (r₀ q : ℕ) : IsZero ((sliceCompactCochainComplex A zeroRows k U r₀).X q) := by
  letI : IsEmpty (SliceSupportCell A zeroRows U q) :=
    ⟨fun c => empty ⟨⟨cellCenter (augmentedForms A) c.val.val,c.val.property⟩,c.property⟩⟩
  exact (ModuleCat.isZero_of_subsingleton
    (ModuleCat.of k (SliceSupportCell A zeroRows U q →₀ k))).of_iso
      (sliceCompactCoordinates A zeroRows U k r₀ q).toModuleIso

theorem sliceCompact_isZero_homology_of_empty
    (empty : ¬ (Subtype.val ⁻¹' (U.val : Set (Fin n → ℝ)) : Set L).Nonempty)
    (r₀ q : ℕ) : IsZero ((sliceCompactCochainComplex A zeroRows k U r₀).homology q) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    (sliceCompact_isZero_X_of_empty A zeroRows k U empty r₀ q)

/-- The genuine top class of every nonempty convex full support,
with an arbitrary exhaustion start and the intrinsic slice dimension. -/
def sliceCompactFullTopClassIso
    (convexU : Convex ℝ (U.val : Set (Fin n → ℝ)))
    (nonemptyU : (Subtype.val ⁻¹' (U.val : Set (Fin n → ℝ)) : Set L).Nonempty)
    (r₀ : ℕ) :
    (sliceCompactCochainComplex A zeroRows k U r₀).homology (Module.finrank ℝ L) ≅
      ModuleCat.of k k := by
  let stage := (sliceOpenSupport_exists_nonempty_window A zeroRows U nonemptyU).choose
  have nonemptyStage := (sliceOpenSupport_exists_nonempty_window A zeroRows U nonemptyU).choose_spec
  exact (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ)
      (Module.finrank ℝ L)).mapIso (sliceCompactStartIso A zeroRows k U r₀ stage) ≪≫
    sliceCompactTopClassIso A zeroRows k U convexU stage nonemptyStage

/-- Every convex support, including the empty one, has no cohomology
outside the intrinsic slice dimension. -/
theorem sliceCompactFull_isZero_homology
    (convexU : Convex ℝ (U.val : Set (Fin n → ℝ))) (r₀ q : ℕ)
    (different : q ≠ Module.finrank ℝ L) :
    IsZero ((sliceCompactCochainComplex A zeroRows k U r₀).homology q) := by
  by_cases nonemptyU : (Subtype.val ⁻¹' (U.val : Set (Fin n → ℝ)) : Set L).Nonempty
  · obtain ⟨stage,nonemptyStage⟩ :=
      sliceOpenSupport_exists_nonempty_window A zeroRows U nonemptyU
    exact (sliceCompactCochainComplex_isZero_homology A zeroRows k U
      convexU stage nonemptyStage q different).of_iso
        ((HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) q).mapIso
          (sliceCompactStartIso A zeroRows k U r₀ stage))
  · exact sliceCompact_isZero_homology_of_empty A zeroRows k U nonemptyU r₀ q

end ToricPower.IntegralArrangement

end
