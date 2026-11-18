module

public import ToricPower.FiniteFunctorTotalComparison
public import ToricPower.FiniteBiproductShortExact

/-!
# Exact sequences of original finite totals

The total of an actual pointwise short exact sequence is short exact in
every integer degree. Its maps are the literal totalized natural maps;
finite biproduct exactness proves the assertion directly.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower.FunctorTotal

universe u v w z

variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type w} [Category.{z} B] [Abelian B] [HasFiniteBiproducts B]
  {Ω Φ Ψ : A ⥤ CochainComplex B ℕ}
  [Ω.Additive] [Φ.Additive] [Ψ.Additive]
  (σ : Ω ⟶ Φ) (τ : Φ ⟶ Ψ) (zero : σ ≫ τ = 0)
  (width : ℕ) (K : CochainComplex A ℤ)

include zero in
theorem coefficientMap_comp_zero :
    coefficientMap σ width K ≫ coefficientMap τ width K = 0 := by
  apply HomologicalComplex.Hom.ext
  funext a
  simp only [HomologicalComplex.comp_f,HomologicalComplex.zero_f,coefficientMap_f]
  apply biproduct_map_comp_zero
  intro q
  have pointwise := congrArg (fun η => η.app (K.X (a + -(q.val : ℤ)))) zero
  exact congrArg (fun f => f.f q.val) pointwise

def shortComplex : ShortComplex (CochainComplex B ℤ) :=
  ShortComplex.mk (coefficientMap σ width K) (coefficientMap τ width K)
    (coefficientMap_comp_zero σ τ zero width K)

/-- No exactness of the coefficient functors themselves is required:
the indicated original sequence need only be short exact on the actual
terms of `K`. -/
theorem shortComplex_shortExact
    (exactAt : ∀ a : ℤ,
      (ShortComplex.mk (σ.app (K.X a)) (τ.app (K.X a))
        (congrArg (fun η => η.app (K.X a)) zero)).ShortExact) :
    (shortComplex σ τ zero width K).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro a
  change (ShortComplex.mk
    (biproduct.map (fun q : Fin width => (σ.app (K.X (a + -(q.val : ℤ)))).f q.val))
    (biproduct.map (fun q : Fin width => (τ.app (K.X (a + -(q.val : ℤ)))).f q.val))
    _).ShortExact
  apply biproduct_shortExact
  intro q
  exact (exactAt (a + -(q.val : ℤ))).map_of_exact
    (HomologicalComplex.eval B (.up ℕ) q.val)

end ToricPower.FunctorTotal

end
