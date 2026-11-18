module

public import ToricPower.FiniteFunctorTotalExact
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Localization of the genuine finite total on unbounded complexes -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.FunctorTotal

variable {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
  [HasFiniteBiproducts B] [HasDerivedCategory A] [HasDerivedCategory B]
  (Φ : A ⥤ CochainComplex B ℕ) [Φ.Additive] (width : ℕ)
  (preserves : ∀ {K L : CochainComplex A ℤ} (f : K ⟶ L), QuasiIso f →
    QuasiIso ((functor Φ width).map f))

/-- The actual finite total descends along the genuine localization. -/
def derivedFunctor : DerivedCategory A ⥤ DerivedCategory B :=
  Localization.lift (W := HomologicalComplex.quasiIso A (.up ℤ))
    (functor Φ width ⋙ DerivedCategory.Q) (fun K L f hf => by
      letI := preserves f hf
      exact inferInstanceAs (IsIso (DerivedCategory.Q.map ((functor Φ width).map f))))
    DerivedCategory.Q

/-- Its factorization keeps the original total functor and its maps. -/
def derivedFactors : DerivedCategory.Q ⋙ derivedFunctor Φ width preserves ≅
    functor Φ width ⋙ DerivedCategory.Q := Localization.fac _ _ _

end ToricPower.FunctorTotal

end
