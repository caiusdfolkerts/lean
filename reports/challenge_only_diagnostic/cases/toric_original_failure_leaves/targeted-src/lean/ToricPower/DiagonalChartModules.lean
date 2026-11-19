module

public import ToricPower.DiagonalChartAction
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# The actual product-chart module of diagonal cellular chains

The coefficient ring is the semigroup algebra of the product of the two
actual ray-character monoids.  Its monomial action is induced by literal
translation of the cell and addition of its total weight.  Extending this
action to the semigroup algebra constructs an actual module, not a family
of unrelated weight vector spaces.

The section labels and their finite orbit representatives are retained
explicitly.  No generation or exactness assertion is part of a definition.

Candidate until the pinned compiler checks the complete dependency closure.
-/

@[expose] public noncomputable section

open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (k : Type) [CommRing k] (A : Fin s → Fin n → ℤ)

/-- The coordinate ring of the affine product chart, in its actual
product-character semigroup presentation. -/
abbrev DiagonalChartRing (S T : Set (Fin s)) :=
  AddMonoidAlgebra k (rayCharacterMonoid A S × rayCharacterMonoid A T)

/-- Finite-support chains indexed by every actual weight and every actual
allowed cell in that weight. -/
abbrev DiagonalChartChains (S T : Set (Fin s)) (d : ℕ) :=
  DiagonalChartCell A S T d →₀ k

/-- The monoid action on the actual chain module.  Its multiplication law
comes from the proved geometric translation law on its cell indices. -/
def diagonalChartRepresentation (S T : Set (Fin s)) (d : ℕ) :
    Multiplicative (rayCharacterMonoid A S × rayCharacterMonoid A T) →*
      Module.End k (DiagonalChartChains k A S T d) where
  toFun p := Finsupp.lmapDomain k k (diagonalChartTranslate A S T p.toAdd)
  map_one' := by
    change Finsupp.lmapDomain k k (diagonalChartTranslate A S T 0) = LinearMap.id
    have h : diagonalChartTranslate A S T (0 :
        rayCharacterMonoid A S × rayCharacterMonoid A T) =
        (id : DiagonalChartCell A S T d → DiagonalChartCell A S T d) := by
      funext x
      exact diagonalChartTranslate_zero A S T x
    rw [h, Finsupp.lmapDomain_id]
  map_mul' p q := by
    change Finsupp.lmapDomain k k (diagonalChartTranslate A S T (p.toAdd+q.toAdd)) =
      (Finsupp.lmapDomain k k (diagonalChartTranslate A S T p.toAdd)).comp
        (Finsupp.lmapDomain k k (diagonalChartTranslate A S T q.toAdd))
    rw [← Finsupp.lmapDomain_comp]
    congr 1
    funext x
    exact diagonalChartTranslate_add A S T p.toAdd q.toAdd x

/-- The universal semigroup-algebra extension of the literal monomial
action, valued in the actual module endomorphism ring. -/
def diagonalChartActionAlgebraHom (S T : Set (Fin s)) (d : ℕ) :
    DiagonalChartRing k A S T →ₐ[k] Module.End k (DiagonalChartChains k A S T d) :=
  AddMonoidAlgebra.lift k _ _ (diagonalChartRepresentation k A S T d)

instance diagonalChartChains_module (S T : Set (Fin s)) (d : ℕ) :
    Module (DiagonalChartRing k A S T) (DiagonalChartChains k A S T d) :=
  Module.compHom _ (diagonalChartActionAlgebraHom k A S T d).toRingHom

/-- On a general finite-support chain, a single chart monomial translates
the actual indices and multiplies the coefficient. -/
theorem diagonalChartChains_single_smul (S T : Set (Fin s)) (d : ℕ)
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T)
    (r : k) (x : DiagonalChartChains k A S T d) :
    AddMonoidAlgebra.single p r • x =
      r • Finsupp.mapDomain (diagonalChartTranslate A S T p) x := by
  change (diagonalChartActionAlgebraHom k A S T d (AddMonoidAlgebra.single p r)) x = _
  rw [diagonalChartActionAlgebraHom, AddMonoidAlgebra.lift_single]
  rfl

/-- The basis formula is precisely multiplication of monomials on both
affine factors.  The result carries no additional scalar or orientation
factor. -/
theorem diagonalChartChains_single_smul_single (S T : Set (Fin s)) (d : ℕ)
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T)
    (r a : k) (x : DiagonalChartCell A S T d) :
    SMul.smul (M := DiagonalChartRing k A S T) (α := DiagonalChartChains k A S T d)
      (AddMonoidAlgebra.single p r) (Finsupp.single x a) =
      Finsupp.single (diagonalChartTranslate A S T p x) (r*a) := by
  exact (diagonalChartChains_single_smul k A S T d p r (Finsupp.single x a)).trans (by
    rw [Finsupp.mapDomain_single]
    simpa only [smul_eq_mul] using
      (Finsupp.smul_single r (diagonalChartTranslate A S T p x) a))

/-- The actual injection of one character weight into the product-chart
module.  Its source is the finite-support coefficient module on the cells
of that literal strip. -/
def diagonalWeightInjection (S T : Set (Fin s)) (u : Fin n → ℤ) (d : ℕ) :
    ({c : Cell (augmentedForms A) d // stripCellAllowed A S T u c} →₀ k) →ₗ[k]
      DiagonalChartChains k A S T d :=
  Finsupp.lmapDomain k k (fun c => (⟨u, c⟩ : DiagonalChartCell A S T d))

@[simp]
theorem diagonalWeightInjection_single (S T : Set (Fin s)) (u : Fin n → ℤ)
    (d : ℕ) (c : {c : Cell (augmentedForms A) d // stripCellAllowed A S T u c})
    (r : k) :
    diagonalWeightInjection k A S T u d (Finsupp.single c r) =
      Finsupp.single ⟨u,c⟩ r := by
  exact Finsupp.mapDomain_single

end ToricPower.IntegralArrangement
