module

public import ToricPower.ArrangementMorseBounds
public import ToricPower.LinearHomComplexCoproducts
public import ToricPower.CoproductCompactFunctor

/-! # Actual local sections preserve unrestricted coefficient sums

The finite geometric face category supplies a bounded projective
resolution with finite-dimensional terms. Its literal signed Hom model
therefore preserves arbitrary coproducts, without a bound on the degree
or dimension of any coefficient complex.
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
local notation "P" => Cellular.localSectionResolution k (H := Region)

theorem universalRegionSectionCochain_finiteSupport (q : ℤ)
    (outside : q ∉ Finset.Icc (-(n : ℤ)) 0) : IsZero ((projectiveCochain P).X q) := by
  letI := universalRegionSectionCochain_isStrictlyGE A k c region
  by_cases low : q < -(n : ℤ)
  · exact (projectiveCochain P).isZero_of_isStrictlyGE (-(n : ℤ)) q low
  · have high : 0 < q := by
      simp only [Finset.mem_Icc] at outside
      omega
    exact (projectiveCochain P).isZero_of_isStrictlyLE 0 q high

theorem universalRegionSectionCochain_term_compact (q : ℤ)
    (inside : q ∈ Finset.Icc (-(n : ℤ)) 0) :
    CompactExtraction.CoproductCompact ((projectiveCochain P).X q) := by
  have nonpositive : q ≤ 0 := (Finset.mem_Icc.mp inside).2
  let m : ℕ := (-q).toNat
  let resolution := Cellular.localSectionResolution k (H := Region)
  let e := resolution.complex.extendXIso ComplexShape.embeddingDownNat
    (show ComplexShape.embeddingDownNat.f m = q by dsimp [m]; omega)
  letI (d : Region) : FiniteDimensional k ((resolution.complex.X m).obj d) :=
    universalRegionSectionResolution_term_finite A k c region m d
  exact CompactExtraction.coproductCompact_of_iso e.symm
    (CompactExtraction.finiteDiagram_coproductCompact k (resolution.complex.X m))

/-- The particular projective section functor used in the local Morse
fiber commutes with every actual coproduct of full coefficient complexes. -/
theorem universalLocalSection_preservesCoproducts (I : Type) :
    PreservesColimitsOfShape (Discrete I)
      (Cellular.localSectionComplexFunctor k (universalRegionInclusion A c region)) := by
  letI : PreservesColimitsOfShape (Discrete I)
      (linearHomComplexFunctor k (projectiveCochain P)) :=
    linearHomComplexFunctor_preservesCoproducts k (projectiveCochain P)
      (Finset.Icc (-(n : ℤ)) 0)
      (universalRegionSectionCochain_finiteSupport A k c region)
      (universalRegionSectionCochain_term_compact A k c region) I
  letI : PreservesColimitsOfShape (Discrete I)
      (Cellular.localDiagramRestriction k (universalRegionInclusion A c region)) := by
    unfold Cellular.localDiagramRestriction
    infer_instance
  change PreservesColimitsOfShape (Discrete I)
    ((Cellular.localDiagramRestriction k (universalRegionInclusion A c region)).mapHomologicalComplex
      (.up ℤ) ⋙ linearHomComplexFunctor k (projectiveCochain P))
  infer_instance

end ToricPower.IntegralArrangement

end
