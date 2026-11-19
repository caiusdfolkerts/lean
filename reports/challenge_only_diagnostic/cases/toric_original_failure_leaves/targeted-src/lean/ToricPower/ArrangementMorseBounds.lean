module

public import ToricPower.ArrangementLocalMorse
public import ToricPower.ProjectiveCochainBounds
public import ToricPower.FiniteDiagramSyzygies

/-! # Finite bounds of the literal cut-region section resolution

The actual resolution terminates because strict geometric face incidence
raises the dimension. Its terms have finite-dimensional coefficients because
the genuine local face star is finite. These are proved properties of the
chosen resolution, with no truncation or boundedness condition on its target.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))

local notation "Region" => UniversalRegionStar A c region

/-- Every term above the ambient dimension is literally zero. -/
theorem universalRegionSectionResolution_term_isZero (m : ℕ) (high : n < m) :
    IsZero ((Cellular.localSectionResolution k (H := Region)).complex.X m) := by
  apply Cellular.diagramProjectiveComplex_isZero_above k
    (fun d : Region => d.val.val.1)
    (fun {_ _} f => universalIncidence_dimension_le A f.le)
    (fun {_ _} f equal => Subtype.ext (Subtype.ext
      (universalIncidence_eq_of_dimension_eq A f.le equal)))
    (Cellular.localConstantDiagram k (H := Region)) n m
  · intro d
    exact cell_dimension_le A d.val.val.2
  · exact high

/-- Every term retains finite-dimensional actual coefficient spaces. -/
theorem universalRegionSectionResolution_term_finite (m : ℕ) (d : Region) :
    FiniteDimensional k
      (((Cellular.localSectionResolution k (H := Region)).complex.X m).obj d) := by
  letI (e : Region) : FiniteDimensional k
      ((Cellular.localConstantDiagram k (H := Region)).obj e) :=
    inferInstanceAs (FiniteDimensional k k)
  exact Cellular.diagramProjectiveTerm_finite k
    (Cellular.localConstantDiagram k (H := Region)) m d

theorem universalRegionSectionCochain_isStrictlyGE :
    (projectiveCochain (Cellular.localSectionResolution k (H := Region))).IsStrictlyGE (-(n : ℤ)) :=
  projectiveCochain_isStrictlyGE (Cellular.localSectionResolution k (H := Region)) n
    (universalRegionSectionResolution_term_isZero A k c region)

/-- Exact actual coefficient rows suffice for the comparison on
every unbounded complex of face diagrams. -/
theorem universalRegionSection_augmentation_quasiIso
    (K : CochainComplex (Region ⥤ ModuleCat k) ℤ)
    (rows : ∀ q (p : ℕ), (projectiveCoefficientComplex k
      (Cellular.localSectionResolution k (H := Region)) (K.X q)).ExactAt (p+1)) :
    QuasiIso (linearHomComplexPrecomp k
      (projectiveCochainAugmentation (Cellular.localSectionResolution k (H := Region))) K) :=
  finiteProjective_linearHomPrecomp_quasiIso k
    (Cellular.localSectionResolution k (H := Region)) n
    (universalRegionSectionResolution_term_isZero A k c region) K rows

end ToricPower.IntegralArrangement

end
