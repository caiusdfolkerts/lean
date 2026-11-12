module

public import ToricPower.LinearHomComplexFunctor
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # A bound for the complete signed linear Hom complex

The source is bounded below and the target bounded above. The conclusion
concerns the actual full product of Hom components; no component is
discarded or replaced by a finite approximation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex

namespace ToricPower

universe u v r

variable (R : Type r) [CommRing R]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  (K L : CochainComplex C ℤ) (a b : ℤ)
  [K.IsStrictlyGE a] [L.IsStrictlyLE b]

theorem linearHomComplex_isZero_X_above (q : ℤ) (high : b-a < q) :
    IsZero ((linearHomComplex R K L).X q) := by
  letI : Subsingleton (Cochain K L q) := ⟨fun f g => by
    apply Cochain.ext
    intro p t equality
    by_cases low : p < a
    · exact (K.isZero_of_isStrictlyGE a p low).eq_of_src _ _
    · exact (L.isZero_of_isStrictlyLE b t (by omega)).eq_of_tgt _ _⟩
  change IsZero (ModuleCat.of R (Cochain K L q))
  exact ModuleCat.isZero_of_subsingleton _

theorem linearHomComplex_isStrictlyLE :
    (linearHomComplex R K L).IsStrictlyLE (b-a) := by
  rw [CochainComplex.isStrictlyLE_iff]
  exact linearHomComplex_isZero_X_above R K L a b

end ToricPower

end
