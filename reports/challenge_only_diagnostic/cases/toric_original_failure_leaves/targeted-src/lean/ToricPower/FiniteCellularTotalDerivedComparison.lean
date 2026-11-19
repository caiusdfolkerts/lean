module

public import ToricPower.FiniteFunctorTotalDerived
public import ToricPower.FiniteFunctorTotalKernelComparison
public import ToricPower.FiniteFunctorTotalSingle
public import ToricPower.CellularConeProjectiveTerms
public import ToricPower.CellularDerivedRealization

/-!
# The finite cellular total and the actual left-derived coend

An original top-degree augmentation which is a local quasi-isomorphism
on projective coefficients gives a natural isomorphism between the full
finite total and the shifted absolute left-derived ordinary functor.
The input complex is arbitrary and unbounded. The proof keeps the
actual finite cone replacement, its augmentation, the original top
quotient, and the canonical single-row projection.

The geometric augmentation and its local calculations are explicit
premises here, to be discharged by the actual toric construction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor HomologicalComplex

namespace ToricPower.FunctorTotal

universe v t

variable (k : Type) [Field k] {C : Type} [Category.{0} C]
  {B : Type v} [Category.{0} B] [Abelian B] [HasFiniteBiproducts B]
  [HasDerivedCategory (C ⥤ ModuleCat.{0} k)] [HasDerivedCategory B]
  (Φ : (C ⥤ ModuleCat.{0} k) ⥤ CochainComplex B ℕ) [Φ.Additive]
  (H : (C ⥤ ModuleCat.{0} k) ⥤ B) [H.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : Φ ⟶ singleCoefficient H n)
  {I : Type t} (detectors : I → B ⥤ ModuleCat.{0} k)
  [∀ i, (detectors i).Additive]
  [∀ i, PreservesFiniteLimits (detectors i)]
  [∀ i, PreservesFiniteColimits (detectors i)]
  (detect : ∀ M : B, (∀ i, IsZero ((detectors i).obj M)) → IsZero M)
  (epi : ∀ M, Epi (τ.app M))
  (onProjectives : ∀ (M : C ⥤ ModuleCat.{0} k), Projective M → ∀ i,
    QuasiIso (((detectors i).mapHomologicalComplex (.up ℕ)).map (τ.app M)))
  (lastZero : ∀ M, IsZero ((Φ.obj M).X width))

include detect epi onProjectives lastZero in
/-- The specified augmentation is a quasi-isomorphism after applying
the genuine finite replacement to any unbounded input complex. -/
theorem resolved_coefficientMap_quasiIso (m : ℕ)
    (K : CochainComplex (C ⥤ ModuleCat.{0} k) ℤ) :
    QuasiIso (coefficientMap τ width ((Cellular.finiteConeResolution k m).functor.obj K)) := by
  apply coefficientMap_quasiIso_of_epi_detectors τ width _ detectors detect
  · intro a
    exact epi _
  · intro i a
    exact onProjectives _ (Cellular.finiteConeResolution_term_projective k m K a) i
  · intro a
    exact lastZero _

/-- The actual natural top-quotient comparison after resolution and
localization, followed by the genuine single-row identification. -/
def resolvedTopComparison (m : ℕ) :
    (Cellular.finiteConeResolution k m).functor ⋙ functor Φ width ⋙ DerivedCategory.Q ⟶
      (Cellular.finiteConeResolution k m).functor ⋙ H.mapHomologicalComplex (.up ℤ) ⋙
        shiftFunctor (CochainComplex B ℤ) (-(n : ℤ)) ⋙ DerivedCategory.Q :=
  whiskerRight (whiskerLeft (Cellular.finiteConeResolution k m).functor
    (comparison τ width ≫ (singleTotalNatIso H n retained).hom)) DerivedCategory.Q

include detect epi onProjectives lastZero in
/-- Every component is invertible for the stated mathematical reasons,
not by a changed definition of the target or the total. -/
theorem resolvedTopComparison_isIso (m : ℕ) :
    IsIso (resolvedTopComparison k Φ H n width retained τ m) := by
  letI (K : CochainComplex (C ⥤ ModuleCat.{0} k) ℤ) :
      IsIso ((resolvedTopComparison k Φ H n width retained τ m).app K) := by
    letI := resolved_coefficientMap_quasiIso k Φ H n width τ detectors detect epi
      onProjectives lastZero m K
    change IsIso (DerivedCategory.Q.map
      (coefficientMap τ width ((Cellular.finiteConeResolution k m).functor.obj K) ≫
        (singleTotalIso H n ((Cellular.finiteConeResolution k m).functor.obj K) retained).hom))
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The original zigzag is a natural isomorphism on the full complex
category after localization. -/
def resolvedTopIso (m : ℕ) :
    (Cellular.finiteConeResolution k m).functor ⋙ functor Φ width ⋙ DerivedCategory.Q ≅
      (Cellular.finiteConeResolution k m).functor ⋙ H.mapHomologicalComplex (.up ℤ) ⋙
        shiftFunctor (CochainComplex B ℤ) (-(n : ℤ)) ⋙ DerivedCategory.Q := by
  letI := resolvedTopComparison_isIso k Φ H n width retained τ detectors detect epi
    onProjectives lastZero m
  exact asIso (resolvedTopComparison k Φ H n width retained τ m)

/-- The target factorization is the actual derived-cone factorization
and the standard localization/shift comparison. -/
def shiftedConeRealizationFactors (m : ℕ) :
    DerivedCategory.Q ⋙
        (Cellular.finiteConeRealizationStageDerived k H m ⋙
          shiftFunctor (DerivedCategory B) (-(n : ℤ))) ≅
      (Cellular.finiteConeResolution k m).functor ⋙ H.mapHomologicalComplex (.up ℤ) ⋙
        shiftFunctor (CochainComplex B ℤ) (-(n : ℤ)) ⋙ DerivedCategory.Q :=
  isoWhiskerRight (Cellular.finiteConeRealizationStageDerivedFactors k H m)
      (shiftFunctor (DerivedCategory B) (-(n : ℤ))) ≪≫
    isoWhiskerLeft ((Cellular.finiteConeResolution k m).functor ⋙
      H.mapHomologicalComplex (.up ℤ)) (DerivedCategory.Q.commShiftIso (-(n : ℤ))).symm

variable
  (preserves : ∀ {K L : CochainComplex (C ⥤ ModuleCat.{0} k) ℤ} (f : K ⟶ L),
    QuasiIso f → QuasiIso ((functor Φ width).map f))
  (m : ℕ)
  (resolution : ∀ K : CochainComplex (C ⥤ ModuleCat.{0} k) ℤ,
    QuasiIso ((Cellular.finiteConeResolution k m).augmentation.app K))

/-- Full unbounded derived comparison. The formula uses the original
augmentation zigzag and is transported by the fully faithful restriction
functor of the actual derived localization. -/
def derivedTotalLeftDerivedIso :
    derivedFunctor Φ width preserves ≅
      Cellular.finiteConeRealizationStageDerived k H m ⋙
        shiftFunctor (DerivedCategory B) (-(n : ℤ)) := by
  apply (Localization.whiskeringLeftFunctor'
    (DerivedCategory.Q (C := C ⥤ ModuleCat.{0} k))
    (HomologicalComplex.quasiIso (C ⥤ ModuleCat.{0} k) (.up ℤ))
    (DerivedCategory B)).preimageIso
  let resolvedAugmentation :
      (Cellular.finiteConeResolution k m).functor ⋙ functor Φ width ⋙ DerivedCategory.Q ≅
        functor Φ width ⋙ DerivedCategory.Q :=
    resolutionCompIso (Cellular.finiteConeResolution k m).functor
      (Cellular.finiteConeResolution k m).augmentation
      (functor Φ width ⋙ DerivedCategory.Q) (fun K => by
        letI := preserves ((Cellular.finiteConeResolution k m).augmentation.app K)
          (resolution K)
        exact inferInstanceAs (IsIso (DerivedCategory.Q.map
          ((functor Φ width).map ((Cellular.finiteConeResolution k m).augmentation.app K)))))
  exact derivedFactors Φ width preserves ≪≫ resolvedAugmentation.symm ≪≫
    resolvedTopIso k Φ H n width retained τ detectors detect epi onProjectives lastZero m ≪≫
    (shiftedConeRealizationFactors k H n m).symm

end ToricPower.FunctorTotal

end
