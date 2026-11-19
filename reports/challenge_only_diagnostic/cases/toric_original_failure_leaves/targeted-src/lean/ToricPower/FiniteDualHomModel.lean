module

public import ToricPower.FiniteHomTotalComparison
public import ToricPower.NegativeFunctorTotalPostcompose
public import ToricPower.NegativeFunctorTotalComparison
public import ToricPower.LinearHomFromCochainToSingleNaturality

/-!
# From coefficient duality to the full signed Hom complex

The first comparison only changes the indexing of a nonnegative source
complex. The second assembles a natural coefficient duality, additive
preservation of finite biproducts, and the proved signs of the total.
The target complex is arbitrary, including unbounded complexes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CochainComplex HomComplex

namespace ToricPower

universe u v w z r

variable (R : Type r) [CommRing R]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

/-- Ordinary contravariant coefficient chains, functorial in the target. -/
def ordinaryCochainCoefficientFunctor (K : CochainComplex C ℕ) :
    C ⥤ ChainComplex (ModuleCat.{v} R) ℕ where
  obj M := ordinaryCochainCoefficients R K M
  map f := ordinaryCochainCoefficientsMap R K f
  map_id M := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Category.comp_id x
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (Category.assoc x f g).symm

instance ordinaryCochainCoefficientFunctor_additive (K : CochainComplex C ℕ) :
    (ordinaryCochainCoefficientFunctor R K).Additive where
  map_add {M N} f g := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Preadditive.comp_add _ _ _ x f g

/-- Restricting an extension by zero restores the original Hom
coefficients, with the original differential. -/
def extendedSourceHomCoefficientsIso (K : CochainComplex C ℕ) (M : C) :
    (finiteSourceHomCoefficients R (K.extend ComplexShape.embeddingUpNat)).obj M ≅
      ordinaryCochainCoefficients R K M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (Linear.homCongr R
      (K.extendXIso ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f q = (q : ℤ) from rfl))
      (Iso.refl M)).toModuleIso)
    (fun q p related => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      change K.d p q ≫
          (((K.extendXIso ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f q = (q : ℤ) from rfl)).inv ≫ f) ≫ 𝟙 M) =
        ((K.extendXIso ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f p = (p : ℤ) from rfl)).inv ≫
          ((K.extend ComplexShape.embeddingUpNat).d (p : ℤ) (q : ℤ) ≫ f)) ≫ 𝟙 M
      rw [K.extend_d_eq ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f p = (p : ℤ) from rfl)
        (show ComplexShape.embeddingUpNat.f q = (q : ℤ) from rfl)]
      simp only [Category.comp_id, Category.assoc, Iso.inv_hom_id_assoc])

/-- The indexing comparison commutes with every target morphism, so it
also applies to every differential of a target resolution. -/
def extendedSourceHomCoefficientsFunctorIso (K : CochainComplex C ℕ) :
    finiteSourceHomCoefficients R (K.extend ComplexShape.embeddingUpNat) ≅
      ordinaryCochainCoefficientFunctor R K :=
  NatIso.ofComponents (extendedSourceHomCoefficientsIso R K) (by
    intro M N f
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((K.extendXIso ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f q = (q : ℤ) from rfl)).inv ≫ (x ≫ f)) ≫ 𝟙 N =
      (((K.extendXIso ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f q = (q : ℤ) from rfl)).inv ≫ x) ≫ 𝟙 M) ≫ f
    simp only [Category.comp_id, Category.assoc])

variable {B : Type w} [Category.{z} B] [Abelian B] [HasFiniteBiproducts B]
  (Φ : C ⥤ ChainComplex B ℕ) [Φ.Additive]
  (H : B ⥤ ModuleCat.{v} R) [H.Additive]

/-- A natural coefficient duality identifies the actual finite total
with the full Hom complex, including its signed differential. -/
def finiteDualHomModelIso (K I : CochainComplex C ℤ) (width : ℕ)
    (outside : ∀ p : ℤ, ¬ (0 ≤ p ∧ p < (width : ℤ)) → IsZero (K.X p))
    (coefficients : NegativeFunctorTotal.postcompose Φ H ≅ finiteSourceHomCoefficients R K) :
    (H.mapHomologicalComplex (.up ℤ)).obj (NegativeFunctorTotal.total Φ width I) ≅
      linearHomComplex R K I :=
  NegativeFunctorTotal.postcomposeIso Φ H width I ≪≫
    (NegativeFunctorTotal.comparisonIso coefficients width).app I ≪≫
      finiteHomTotalIso R K I width outside

/-- A convenient version for the original nonnegative cellular source. -/
def finiteDualHomModelIsoOfNonnegative (K : CochainComplex C ℕ)
    (I : CochainComplex C ℤ) (width : ℕ)
    (outside : ∀ p : ℤ, ¬ (0 ≤ p ∧ p < (width : ℤ)) →
      IsZero ((K.extend ComplexShape.embeddingUpNat).X p))
    (coefficients : NegativeFunctorTotal.postcompose Φ H ≅ ordinaryCochainCoefficientFunctor R K) :
    (H.mapHomologicalComplex (.up ℤ)).obj (NegativeFunctorTotal.total Φ width I) ≅
      linearHomComplex R (K.extend ComplexShape.embeddingUpNat) I :=
  finiteDualHomModelIso R Φ H (K.extend ComplexShape.embeddingUpNat) I width outside
    (coefficients ≪≫ (extendedSourceHomCoefficientsFunctorIso R K).symm)

end ToricPower

end
