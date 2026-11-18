module

public import theorem94.PalomarPart002
import all theorem94.PalomarPart002
public meta import Lean.Util.CollectAxioms
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Order.Atoms.Finite
public import Mathlib.Order.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.PiLex
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public meta import Lean.Elab.Tactic.Omega
public meta import Mathlib.Tactic.Ring.Basic

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factors
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.FractionRing
@[expose] public section
-- Keep editor information enabled for the stock Lean command processor.
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


-- Restore the original anonymous enclosing source scopes at this boundary.
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
/- BEGIN FourPapers/Universal/CyclicParameterBaseChange.lean -/
section


section

/-! # Coefficient change of actual parameter-linear maps

Extension is defined by the images of the already verified descent basis.
The comparison with coefficient change is proved on the complete scalar
parameter basis, including every parameter monomial.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

variable {V K L : Type*} [Fintype V] [LinearOrder V] [CommRing K] [CommRing L]

theorem booleanCoefficientChange_descent (h : K →+* L)
    (σ : VertexOrdering (Fintype.card V) V) :
    booleanCoefficientChange h (descentVector (K := K) σ) = descentVector (K := L) σ := by
  change monomialCoefficientRingHom IsChainExponent isChainExponent_divisorClosed h
    (descentVector (K := K) σ) = _
  rw [descentVector, descentVector, map_prod]
  apply Finset.prod_congr rfl
  intro c hc
  exact booleanCoefficientChange_face h (orderingFace σ c)

theorem booleanCoefficientChange_color (h : K →+* L) (c : Fin (Fintype.card V)) :
    booleanCoefficientChange h (colorSum (K := K) c) = colorSum (K := L) c := by
  rw [← booleanRankParameter_color, booleanCoefficientChange_parameter, booleanRankParameter_color]

theorem booleanCoefficientChange_colorPower (h : K →+* L) (m : ColorExponent V) :
    booleanCoefficientChange h (colorPower (K := K) m) = colorPower (K := L) m := by
  change monomialCoefficientRingHom IsChainExponent isChainExponent_divisorClosed h
    (colorPower (K := K) m) = _
  rw [colorPower, colorPower, map_prod]
  apply Finset.prod_congr rfl
  intro c hc
  rw [map_pow]
  congr 1
  exact booleanCoefficientChange_color h c

theorem booleanCoefficientChange_parameterBasis (h : K →+* L)
    (i : VertexOrdering (Fintype.card V) V × ColorExponent V) :
    booleanCoefficientChange h (booleanParameterBasis (K := K) i) =
      booleanParameterBasis (K := L) i := by
  rw [booleanParameterBasis_apply, booleanParameterBasis_apply, parameterDescentVector,
    parameterDescentVector, booleanCoefficientChange_mul,
    booleanCoefficientChange_colorPower, booleanCoefficientChange_descent]

theorem polynomialCoefficientChange_parameterMonomial (h : K →+* L) (m : ColorExponent V) :
    polynomialCoefficientChange h (polynomialColorMap (K := K) (MvPolynomial.monomial m 1)) =
      polynomialColorMap (K := L) (MvPolynomial.monomial m 1) := by
  change MvPolynomial.map h (polynomialColorMap (K := K) (MvPolynomial.monomial m 1)) = _
  simp only [polynomialColorMap, MvPolynomial.aeval_monomial, map_one, one_mul,
    Finsupp.prod, map_prod, map_pow, MvPolynomial.map_esymm]

theorem polynomialCoefficientChange_degree (h : K →+* L) (n : ℕ)
    (f : MvPolynomial V K) (hf : f ∈ polynomialDegreePiece n) :
    polynomialCoefficientChange h f ∈ polynomialDegreePiece n := by
  intro a ha
  change (MvPolynomial.map h f).coeff a = 0
  rw [MvPolynomial.coeff_map, hf a ha, map_zero]

theorem parameterLinearMap_parameterDescent
    (f : BooleanBarycentricRing V K →ₗ[MvPolynomial (Fin (Fintype.card V)) K] MvPolynomial V K)
    (i : VertexOrdering (Fintype.card V) V × ColorExponent V) :
    f (parameterDescentVector i) =
      polynomialColorMap (MvPolynomial.monomial i.2 1) * f (descentVector i.1) := by
  rw [parameterDescentVector_eq_monomial_smul, map_smul]
  rfl

def extendIntegralParameterMap (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ) :
    BooleanBarycentricRing V L →ₗ[MvPolynomial (Fin (Fintype.card V)) L] MvPolynomial V L :=
  (booleanColorBasis (V := V) (K := L)).constr (MvPolynomial (Fin (Fintype.card V)) L)
    (fun σ => polynomialCoefficientChange (Int.castRingHom L) (f (descentVector σ)))

@[simp] theorem extendIntegralParameterMap_descent (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (σ : VertexOrdering (Fintype.card V) V) :
    extendIntegralParameterMap L f (descentVector σ) =
      polynomialCoefficientChange (Int.castRingHom L) (f (descentVector σ)) := by
  simpa only [extendIntegralParameterMap, booleanColorBasis_apply] using
    (booleanColorBasis (V := V) (K := L)).constr_basis (MvPolynomial (Fin (Fintype.card V)) L)
      (fun τ => polynomialCoefficientChange (Int.castRingHom L) (f (descentVector τ))) σ

theorem extendIntegralParameterMap_commutes (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (x : BooleanBarycentricRing V ℤ) :
    extendIntegralParameterMap L f (booleanCoefficientChange (Int.castRingHom L) x) =
      polynomialCoefficientChange (Int.castRingHom L) (f x) := by
  have he : ((extendIntegralParameterMap L f).restrictScalars L).comp
      (booleanCoefficientChange (Int.castRingHom L)) =
      (polynomialCoefficientChange (Int.castRingHom L)).comp (f.restrictScalars ℤ) := by
    apply (booleanParameterBasis (V := V) (K := ℤ)).ext
    intro i
    change extendIntegralParameterMap L f
        (booleanCoefficientChange (Int.castRingHom L) (booleanParameterBasis i)) =
      polynomialCoefficientChange (Int.castRingHom L) (f (booleanParameterBasis i))
    rw [booleanCoefficientChange_parameterBasis, booleanParameterBasis_apply,
      booleanParameterBasis_apply, parameterLinearMap_parameterDescent,
      parameterLinearMap_parameterDescent, extendIntegralParameterMap_descent]
    change _ = MvPolynomial.map (Int.castRingHom L)
      (polynomialColorMap (MvPolynomial.monomial i.2 1) * f (descentVector i.1))
    rw [map_mul]
    rw [← polynomialCoefficientChange_eq, polynomialCoefficientChange_parameterMonomial]
    rfl
  exact DFunLike.congr_fun he x

theorem extendIntegralParameterMap_degree (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (hf : ∀ σ : VertexOrdering (Fintype.card V) V,
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (σ : VertexOrdering (Fintype.card V) V) :
    extendIntegralParameterMap L f (descentVector σ) ∈
      polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
  rw [extendIntegralParameterMap_descent]
  exact polynomialCoefficientChange_degree _ _ _ (hf σ)

theorem extendIntegralParameterMap_one (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (m : ℤ) (hf : f 1 = MvPolynomial.C m) :
    extendIntegralParameterMap L f 1 = MvPolynomial.C (m : L) := by
  have h := extendIntegralParameterMap_commutes L f 1
  have h₁ : booleanCoefficientChange (V := V) (Int.castRingHom L) 1 = 1 :=
    (monomialCoefficientRingHom IsChainExponent isChainExponent_divisorClosed (Int.castRingHom L)).map_one
  rw [h₁, hf] at h
  simpa [polynomialCoefficientChange_eq] using h

theorem extendIntegralParameterMap_permutation (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (e : Equiv.Perm V)
    (hf : ∀ x, f (booleanPermutationAlgEquiv e x) = MvPolynomial.rename e (f x)) :
    ∀ x, extendIntegralParameterMap L f (booleanPermutationAlgEquiv e x) =
      MvPolynomial.rename e (extendIntegralParameterMap L f x) := by
  have he : ((extendIntegralParameterMap L f).restrictScalars L).comp
      (booleanPermutationAlgEquiv (K := L) e).toLinearMap =
      (MvPolynomial.rename e).toLinearMap.comp ((extendIntegralParameterMap L f).restrictScalars L) := by
    apply (booleanParameterBasis (V := V) (K := L)).ext
    intro i
    have hBi := booleanCoefficientChange_parameterBasis (Int.castRingHom L) i
    change extendIntegralParameterMap L f (booleanPermutationAlgEquiv e (booleanParameterBasis i)) =
      MvPolynomial.rename e (extendIntegralParameterMap L f (booleanParameterBasis i))
    rw [← hBi]
    have hn := booleanCoefficientChange_restriction (Int.castRingHom L) e.symm.toEmbedding
      (booleanParameterBasis (K := ℤ) i)
    change booleanCoefficientChange (Int.castRingHom L)
        (booleanPermutationAlgEquiv e (booleanParameterBasis (K := ℤ) i)) =
      booleanPermutationAlgEquiv e
        (booleanCoefficientChange (Int.castRingHom L) (booleanParameterBasis (K := ℤ) i)) at hn
    rw [← hn, extendIntegralParameterMap_commutes, extendIntegralParameterMap_commutes, hf]
    exact MvPolynomial.map_rename (Int.castRingHom L) e _
  intro x
  exact DFunLike.congr_fun he x

theorem extendIntegralParameterMap_conjugation (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (e : Equiv.Perm V) (x : BooleanBarycentricRing V ℤ) :
    polynomialCoefficientChange (Int.castRingHom L)
        (MvPolynomial.rename e (f (booleanPermutationAlgEquiv e.symm x))) =
      MvPolynomial.rename e (extendIntegralParameterMap L f
        (booleanPermutationAlgEquiv e.symm (booleanCoefficientChange (Int.castRingHom L) x))) := by
  rw [polynomialCoefficientChange_eq, MvPolynomial.map_rename]
  rw [← polynomialCoefficientChange_eq, ← extendIntegralParameterMap_commutes]
  exact congrArg (fun y => MvPolynomial.rename e (extendIntegralParameterMap L f y))
    (booleanCoefficientChange_restriction (Int.castRingHom L) e.toEmbedding x)

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegralDivision.lean -/
section


section

/-! # Dividing integral parameter maps after modular vanishing

Division is performed on the genuine descent-basis images.  The resulting
map is parameter-linear by construction, and the multiplication identity is
checked on that full parameter basis.  Boundary and grading conditions then
descend using torsion freeness of the actual coefficient bases.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

section Basis

variable {I M : Type*} [AddCommGroup M] [Module ℤ M]

theorem integerBasis_nsmul_injective (b : Module.Basis I ℤ M) {p : ℕ} (hp : p ≠ 0) :
    Function.Injective (fun x : M => p • x) := by
  intro x y hxy
  apply b.repr.injective
  ext i
  have hh := congrArg (fun z => b.repr z i) hxy
  simp only [map_nsmul, Finsupp.nsmul_apply, nsmul_eq_mul] at hh
  exact mul_left_cancel₀ (by exact_mod_cast hp) hh

end Basis

variable {V : Type*} [Fintype V] [LinearOrder V]

def divideIntegralParameterMap (p : ℕ)
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ) :
    BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ :=
  (booleanColorBasis (V := V) (K := ℤ)).constr (MvPolynomial (Fin (Fintype.card V)) ℤ)
    (fun σ => divideIntegerPolynomial p (f (descentVector σ)))

@[simp] theorem divideIntegralParameterMap_descent (p : ℕ)
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (σ : VertexOrdering (Fintype.card V) V) :
    divideIntegralParameterMap p f (descentVector σ) = divideIntegerPolynomial p (f (descentVector σ)) := by
  simpa only [divideIntegralParameterMap, booleanColorBasis_apply] using
    (booleanColorBasis (V := V) (K := ℤ)).constr_basis (MvPolynomial (Fin (Fintype.card V)) ℤ)
      (fun τ => divideIntegerPolynomial p (f (descentVector τ))) σ

theorem nsmul_divideIntegralParameterMap (p : ℕ)
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (hf : ∀ σ : VertexOrdering (Fintype.card V) V,
      MvPolynomial.map (Int.castRingHom (ZMod p)) (f (descentVector σ)) = 0) :
    p • divideIntegralParameterMap p f = f := by
  apply (booleanColorBasis (V := V) (K := ℤ)).ext
  intro σ
  simp only [booleanColorBasis_apply, LinearMap.smul_apply, divideIntegralParameterMap_descent]
  exact nsmul_divideIntegerPolynomial p _ (hf σ)

theorem divideIntegralParameterMap_degree (p : ℕ)
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (hf : ∀ σ : VertexOrdering (Fintype.card V) V,
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (σ : VertexOrdering (Fintype.card V) V) :
    divideIntegralParameterMap p f (descentVector σ) ∈
      polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
  rw [divideIntegralParameterMap_descent]
  exact divideIntegerPolynomial_degree p _ _ (hf σ)

theorem divideIntegralParameterMap_boundary (p : ℕ) (hp : p ≠ 0)
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (hf : ∀ σ : VertexOrdering (Fintype.card V) V,
      MvPolynomial.map (Int.castRingHom (ZMod p)) (f (descentVector σ)) = 0)
    (hb : ∀ x, polynomialBooleanBoundaryMap (f x) = 0)
    (x : BooleanBarycentricRing V ℤ) :
    polynomialBooleanBoundaryMap (divideIntegralParameterMap p f x) = 0 := by
  apply integerBasis_nsmul_injective
    (standardMonomialBasis (K := ℤ) (OmitsVertex V) (omitsVertex_divisorClosed V)) hp
  change p • polynomialBooleanBoundaryMap (divideIntegralParameterMap p f x) =
    p • (0 : PolynomialBoundaryRing V ℤ)
  rw [smul_zero, ← map_nsmul]
  have hh := congrArg (fun F : BooleanBarycentricRing V ℤ →ₗ[
    MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ => F x)
      (nsmul_divideIntegralParameterMap p f hf)
  change p • divideIntegralParameterMap p f x = f x at hh
  rw [hh, hb]

theorem divideIntegralParameterMap_zero_at (p : ℕ) (hp : p ≠ 0)
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (hf : ∀ σ : VertexOrdering (Fintype.card V) V,
      MvPolynomial.map (Int.castRingHom (ZMod p)) (f (descentVector σ)) = 0)
    (x : BooleanBarycentricRing V ℤ) (hx : f x = 0) :
    divideIntegralParameterMap p f x = 0 := by
  apply integerPolynomial_nsmul_injective hp
  change p • divideIntegralParameterMap p f x = p • (0 : MvPolynomial V ℤ)
  rw [smul_zero]
  have hh := congrArg (fun F : BooleanBarycentricRing V ℤ →ₗ[
    MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ => F x)
      (nsmul_divideIntegralParameterMap p f hf)
  exact hh.trans hx

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegralCorrection.lean -/
section


section

/-! # Integral correction of an actual prime-cyclic comparison

The input map already has the prescribed integral boundary.  Its failure of
equivariance vanishes after reduction modulo the prime.  We divide this
failure on the actual descent basis and apply the integral affine correction;
the resulting map retains the boundary, ordinary degree, and normalization.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

variable {V : Type*} [Fintype V] [LinearOrder V]

theorem integralParameterMap_graded
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (hf : ∀ σ : VertexOrdering (Fintype.card V) V,
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (n : ℕ) (x : BooleanBarycentricRing V ℤ)
    (hx : x ∈ (booleanScalarGradedBasis (V := V) (K := ℤ)).piece n) :
    f x ∈ polynomialDegreePiece n := by
  rw [booleanScalarGradedBasis_piece_eq] at hx
  exact parameterLinear_ordinary_degree (f.restrictScalars ℤ)
    (fun a y => f.map_smul a y) hf n x hx

variable (p : ℕ) [Fact p.Prime] [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

theorem primeCycle_card : Fintype.card (PrimeCycleGroup p) = p := by
  simp [PrimeCycleGroup, ZMod.card]

theorem exists_integralPrimeCyclic_correction
    (f : BooleanBarycentricRing (ZMod p) ℤ →ₗ[
      MvPolynomial (Fin (Fintype.card (ZMod p))) ℤ] MvPolynomial (ZMod p) ℤ)
    (hfgrade : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (hfboundary : ∀ (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) ℤ),
      polynomialBooleanBoundaryMap (f (cyclicBooleanParameterRepresentation p ℤ g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p ℤ g (f x)))
    (hfmod : ∀ (g : PrimeCycleGroup p) (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)),
      MvPolynomial.map (Int.castRingHom (ZMod p))
        ((parameterHomRepresentation (cyclicBooleanParameterRepresentation p ℤ)
          (cyclicPolynomialParameterRepresentation p ℤ) g f - f) (descentVector σ)) = 0)
    (m : ℤ) (hf₁ : f 1 = MvPolynomial.C m) :
    ∃ F : BooleanBarycentricRing (ZMod p) ℤ →ₗ[
        MvPolynomial (Fin (Fintype.card (ZMod p))) ℤ] MvPolynomial (ZMod p) ℤ,
      RepresentationIntertwines (cyclicBooleanParameterRepresentation p ℤ)
        (cyclicPolynomialParameterRepresentation p ℤ) F ∧
      (∀ x, polynomialBooleanBoundaryMap (F x) = polynomialBooleanBoundaryMap (f x)) ∧
      (∀ n x, x ∈ (booleanScalarGradedBasis (V := ZMod p) (K := ℤ)).piece n →
        F x ∈ polynomialDegreePiece n) ∧ F 1 = MvPolynomial.C m := by
  let ρ := cyclicBooleanParameterRepresentation p ℤ
  let τ := cyclicPolynomialParameterRepresentation p ℤ
  let s := booleanScalarGradedBasis (V := ZMod p) (K := ℤ)
  let δ := fun g : PrimeCycleGroup p => parameterHomRepresentation ρ τ g f - f
  let v := fun g : PrimeCycleGroup p => divideIntegralParameterMap p (δ g)
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hfg : ∀ n x, x ∈ s.piece n → f x ∈ polynomialDegreePiece n :=
    integralParameterMap_graded f hfgrade
  have hρg : ∀ (g : PrimeCycleGroup p) n x,
      x ∈ s.piece n → ρ g x ∈ s.piece n := by
    intro g n x hx
    exact booleanParameterPermutationRepresentation_graded (Equiv.addLeft g.toAdd) n x hx
  have hτg : ∀ (g : PrimeCycleGroup p) n y,
      y ∈ polynomialDegreePiece n → τ g y ∈ polynomialDegreePiece n := by
    intro g n y hy
    exact (cyclicPolynomialRepresentation p ℤ n g ⟨y, hy⟩).property
  have hδg : ∀ (g : PrimeCycleGroup p) n x,
      x ∈ s.piece n → δ g x ∈ polynomialDegreePiece n := by
    intro g n x hx
    exact (polynomialDegreePiece n).sub_mem (hτg g n _ (hfg n _ (hρg g⁻¹ n x hx)))
      (hfg n x hx)
  have hδb : ∀ (g : PrimeCycleGroup p) x,
      polynomialBooleanBoundaryMap (δ g x) = 0 := by
    intro g x
    change polynomialBooleanBoundaryMap (τ g (f (ρ g⁻¹ x)) - f x) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    have hh := hfboundary g (ρ g⁻¹ x)
    have hi : ρ g (ρ g⁻¹ x) = x := by
      change (ρ g * ρ g⁻¹) x = x
      rw [← ρ.map_mul, mul_inv_cancel, ρ.map_one]
      rfl
    rw [hi] at hh
    exact hh.symm
  have hδ₁ : ∀ g : PrimeCycleGroup p, δ g 1 = 0 := by
    intro g
    change MvPolynomial.rename (Equiv.addLeft g.toAdd)
      (f (booleanPermutationAlgEquiv (Equiv.addLeft (g⁻¹).toAdd) 1)) - f 1 = 0
    rw [map_one, hf₁, MvPolynomial.rename_C, sub_self]
  have hv : ∀ g, parameterHomRepresentation ρ τ g f = f + Fintype.card (PrimeCycleGroup p) • v g := by
    intro g
    rw [primeCycle_card]
    have hdiv := nsmul_divideIntegralParameterMap p (δ g) (hfmod g)
    change parameterHomRepresentation ρ τ g f = f + p • divideIntegralParameterMap p (δ g)
    rw [hdiv]
    change parameterHomRepresentation ρ τ g f = f + (parameterHomRepresentation ρ τ g f - f)
    rw [← add_sub_assoc, add_comm f (parameterHomRepresentation ρ τ g f), add_sub_cancel_right]
  have hvb : ∀ g x, polynomialBooleanBoundaryMap (v g x) = 0 := by
    intro g x
    exact divideIntegralParameterMap_boundary p hp (δ g) (hfmod g) (hδb g) x
  have hvg : ∀ g n x, x ∈ s.piece n → v g x ∈ polynomialDegreePiece n := by
    intro g
    apply integralParameterMap_graded
    intro σ
    exact divideIntegralParameterMap_degree p (δ g)
      (fun σ => hδg g _ _ (by
        simpa only [s, booleanScalarGradedBasis, booleanColorBasis_apply] using
          s.generator_mem_piece σ)) σ
  have hv₁ : ∀ g, v g 1 = 0 := by
    intro g
    exact divideIntegralParameterMap_zero_at p hp (δ g) (hfmod g) 1 (hδ₁ g)
  obtain ⟨F, hFeq, hFb, hFg, hF₁⟩ := exists_integralEquivariant_map_correction
    polynomialBooleanBoundaryMap.toLinearMap ρ τ f v
    (by simpa only [primeCycle_card] using (integerPolynomial_nsmul_injective (V := ZMod p) hp))
    hv hvb s.piece polynomialDegreePiece hfg hvg 1 hv₁
  exact ⟨F, hFeq, hFb, hFg, hF₁.trans hf₁⟩

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegralLift.lean -/
section


section

/-! # Lifting a modular comparison with its exact integral boundary

A modular difference with zero boundary is a multiple of the actual top
monomial.  Lift its quotient coefficient by coefficient, then multiply by
the integral top monomial.  This keeps the prescribed integral boundary
exact, rather than merely congruent modulo the prime.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

abbrev BooleanParameterMap (V K : Type*) [Fintype V] [LinearOrder V] [CommRing K] :=
  BooleanBarycentricRing V K →ₗ[MvPolynomial (Fin (Fintype.card V)) K] MvPolynomial V K

variable (p : ℕ) [Fact p.Prime] [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

theorem cyclicPolynomialTop_map {K L : Type*} [CommRing K] [CommRing L]
    (h : K →+* L) :
    MvPolynomial.map h (cyclicPolynomialTop p K) = cyclicPolynomialTop p L := by
  simp only [cyclicPolynomialTop, map_prod, MvPolynomial.map_X]

theorem cyclicPolynomialTop_factor_zero_below {K : Type*} [CommRing K]
    (n : ℕ) (hn : n < p) (y : MvPolynomial (ZMod p) K)
    (hy : cyclicPolynomialTop p K * y ∈ polynomialDegreePiece n) : y = 0 := by
  ext a
  have hdeg : p ≤ vertexDegree (fun v => (fullExponent (ZMod p) + a) v) := by
    change p ≤ vertexDegree ((fun v => fullExponent (ZMod p) v) + (fun v => a v))
    rw [vertexDegree_add]
    simp [vertexDegree]
  have hh := hy (fullExponent (ZMod p) + a) (by omega)
  rw [cyclicPolynomialTop, ← full_monomial_eq_prod,
    MvPolynomial.coeff_monomial_mul, one_mul] at hh
  exact hh

def modularBoundaryDifference (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) : MvPolynomial (ZMod p) (ZMod p) :=
  F (descentVector σ) - MvPolynomial.map (Int.castRingHom (ZMod p)) (f (descentVector σ))

theorem modularBoundaryDifference_boundary (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    polynomialBooleanBoundaryMap (modularBoundaryDifference p f F σ) = 0 := by
  unfold modularBoundaryDifference
  rw [map_sub, hb, extendIntegralParameterMap_descent, polynomialCoefficientChange_eq, sub_self]

def modularBoundaryCofactor (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) : MvPolynomial (ZMod p) (ZMod p) :=
  Classical.choose ((polynomialBooleanBoundaryMap_eq_zero_iff _).mp
    (modularBoundaryDifference_boundary p f F hb σ))

theorem modularBoundaryCofactor_spec (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    cyclicPolynomialTop p (ZMod p) * modularBoundaryCofactor p f F hb σ =
      modularBoundaryDifference p f F σ :=
  Classical.choose_spec ((polynomialBooleanBoundaryMap_eq_zero_iff _).mp
    (modularBoundaryDifference_boundary p f F hb σ))

def liftModularParameterMap (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x)) :
    BooleanParameterMap (ZMod p) ℤ :=
  (booleanColorBasis (V := ZMod p) (K := ℤ)).constr
    (MvPolynomial (Fin (Fintype.card (ZMod p))) ℤ)
    (fun σ => f (descentVector σ) + cyclicPolynomialTop p ℤ *
      liftZModPolynomial p (modularBoundaryCofactor p f F hb σ))

@[simp] theorem liftModularParameterMap_descent (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    liftModularParameterMap p f F hb (descentVector σ) =
      f (descentVector σ) + cyclicPolynomialTop p ℤ *
        liftZModPolynomial p (modularBoundaryCofactor p f F hb σ) := by
  simpa only [liftModularParameterMap, booleanColorBasis_apply] using
    (booleanColorBasis (V := ZMod p) (K := ℤ)).constr_basis
      (MvPolynomial (Fin (Fintype.card (ZMod p))) ℤ) _ σ

theorem liftModularParameterMap_reduction (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x)) :
    extendIntegralParameterMap (ZMod p) (liftModularParameterMap p f F hb) = F := by
  apply (booleanColorBasis (V := ZMod p) (K := ZMod p)).ext
  intro σ
  rw [booleanColorBasis_apply, extendIntegralParameterMap_descent,
    polynomialCoefficientChange_eq, liftModularParameterMap_descent,
    map_add, map_mul, cyclicPolynomialTop_map, liftZModPolynomial_map,
    modularBoundaryCofactor_spec, modularBoundaryDifference]
  rw [← add_sub_assoc, add_comm _ (F (descentVector σ)), add_sub_cancel_right]

theorem liftModularParameterMap_boundary (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (x : BooleanBarycentricRing (ZMod p) ℤ) :
    polynomialBooleanBoundaryMap (liftModularParameterMap p f F hb x) =
      polynomialBooleanBoundaryMap (f x) := by
  let L := liftModularParameterMap p f F hb
  have he := parameterLinear_ext_descent polynomialBoundaryColorMap
    (polynomialBooleanBoundaryMap.toLinearMap.comp (L.restrictScalars ℤ))
    (polynomialBooleanBoundaryMap.toLinearMap.comp (f.restrictScalars ℤ))
    (fun a y => by
      change polynomialBooleanBoundaryMap (L (a • y)) = _
      rw [L.map_smul]
      exact polynomialBooleanBoundaryMap_parameter_mul a (L y))
    (fun a y => by
      change polynomialBooleanBoundaryMap (f (a • y)) = _
      rw [f.map_smul]
      exact polynomialBooleanBoundaryMap_parameter_mul a (f y))
    (fun σ => by
      change polynomialBooleanBoundaryMap (liftModularParameterMap p f F hb (descentVector σ)) = _
      rw [liftModularParameterMap_descent, map_add]
      have hz : polynomialBooleanBoundaryMap (cyclicPolynomialTop p ℤ *
          liftZModPolynomial p (modularBoundaryCofactor p f F hb σ)) = 0 :=
        (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr ⟨_, rfl⟩
      rw [hz, add_zero]
      rfl)
  exact DFunLike.congr_fun he x

theorem liftModularParameterMap_degree (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (hf : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (hF : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      F (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    liftModularParameterMap p f F hb (descentVector σ) ∈
      polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
  let n := colorOrdinaryDegree (descentColorExponent σ)
  let y := modularBoundaryCofactor p f F hb σ
  have hy : cyclicPolynomialTop p (ZMod p) * y ∈ polynomialDegreePiece n := by
    rw [modularBoundaryCofactor_spec]
    exact (polynomialDegreePiece n).sub_mem (hF σ)
      (polynomialCoefficientChange_degree (Int.castRingHom (ZMod p)) n _ (hf σ))
  rw [liftModularParameterMap_descent]
  apply (polynomialDegreePiece n).add_mem (hf σ)
  by_cases hn : p ≤ n
  · have hygrade : y ∈ polynomialDegreePiece (n - p) := by
      apply cyclicPolynomialTop_predecessor_degree p (ZMod p) (n - p) y
      simpa only [Nat.sub_add_cancel hn] using hy
    have hh := polynomialDegreePiece_mul p (n - p) (cyclicPolynomialTop p ℤ)
      (liftZModPolynomial p y) (cyclicPolynomialTop_degree p ℤ)
      (liftZModPolynomial_degree p (n - p) y hygrade)
    simpa only [Nat.add_sub_of_le hn] using hh
  · have hyzero : y = 0 := cyclicPolynomialTop_factor_zero_below p n (by omega) y hy
    have hlift : liftZModPolynomial p y = 0 := by
      ext a
      rw [liftZModPolynomial_coeff, hyzero]
      simp
    change cyclicPolynomialTop p ℤ * liftZModPolynomial p y ∈ polynomialDegreePiece n
    rw [hlift, mul_zero]
    exact (polynomialDegreePiece n).zero_mem

theorem liftModularParameterMap_one (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (m : ℤ) (hf : f 1 = MvPolynomial.C m) (hF : F 1 = MvPolynomial.C (m : ZMod p)) :
    liftModularParameterMap p f F hb 1 = MvPolynomial.C m := by
  let σ := weightOrdering (fun _ : ZMod p => 0)
  have hσ : descentVector (K := ℤ) σ = 1 := by
    rw [descentVector, weightOrdering_zero_no_descents, Finset.prod_empty]
  have hσ' : descentVector (K := ZMod p) σ = 1 := by
    rw [descentVector, weightOrdering_zero_no_descents, Finset.prod_empty]
  have hδ : modularBoundaryDifference p f F σ = 0 := by
    rw [modularBoundaryDifference, hσ, hσ', hf, hF, MvPolynomial.map_C]
    exact sub_self _
  have hy : modularBoundaryCofactor p f F hb σ = 0 := by
    apply cyclicPolynomialTop_mul_injective p (ZMod p)
    change cyclicPolynomialTop p (ZMod p) * modularBoundaryCofactor p f F hb σ =
      cyclicPolynomialTop p (ZMod p) * 0
    rw [mul_zero, modularBoundaryCofactor_spec, hδ]
  rw [← hσ, liftModularParameterMap_descent, hσ, hf]
  have hlift : liftZModPolynomial p (modularBoundaryCofactor p f F hb σ) = 0 := by
    ext a
    rw [liftZModPolynomial_coeff, hy]
    simp
  rw [hlift, mul_zero, add_zero]

theorem integralCyclic_conjugation_vanishes_modular
    (f : BooleanParameterMap (ZMod p) ℤ)
    (hf : RepresentationIntertwines (cyclicBooleanParameterRepresentation p (ZMod p))
      (cyclicPolynomialParameterRepresentation p (ZMod p)) (extendIntegralParameterMap (ZMod p) f))
    (g : PrimeCycleGroup p) (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    MvPolynomial.map (Int.castRingHom (ZMod p))
      ((parameterHomRepresentation (cyclicBooleanParameterRepresentation p ℤ)
        (cyclicPolynomialParameterRepresentation p ℤ) g f - f) (descentVector σ)) = 0 := by
  let ρ := cyclicBooleanParameterRepresentation p (ZMod p)
  let τ := cyclicPolynomialParameterRepresentation p (ZMod p)
  let F := extendIntegralParameterMap (ZMod p) f
  let x := booleanCoefficientChange (Int.castRingHom (ZMod p)) (descentVector (K := ℤ) σ)
  have he : (cyclicVertexPermutation p g).symm = cyclicVertexPermutation p g⁻¹ := by
    exact ((cyclicVertexPermutation p).map_inv g).symm
  change MvPolynomial.map (Int.castRingHom (ZMod p))
    (MvPolynomial.rename (cyclicVertexPermutation p g)
      (f (booleanPermutationAlgEquiv (cyclicVertexPermutation p g⁻¹) (descentVector σ))) -
      f (descentVector σ)) = 0
  rw [map_sub, ← he, ← polynomialCoefficientChange_eq,
    extendIntegralParameterMap_conjugation]
  rw [← polynomialCoefficientChange_eq, ← extendIntegralParameterMap_commutes]
  rw [he]
  change τ g (F (ρ g⁻¹ x)) - F x = 0
  rw [hf]
  have hi : τ g (τ g⁻¹ (F x)) = F x := by
    change (τ g * τ g⁻¹) (F x) = F x
    rw [← τ.map_mul, mul_inv_cancel, τ.map_one]
    rfl
  rw [hi, sub_self]

theorem integralCyclic_boundary_rename_congr (e : Equiv.Perm (ZMod p))
    (f g : MvPolynomial (ZMod p) ℤ)
    (h : polynomialBooleanBoundaryMap f = polynomialBooleanBoundaryMap g) :
    polynomialBooleanBoundaryMap (MvPolynomial.rename e f) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename e g) := by
  have hz : polynomialBooleanBoundaryMap (f - g) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨y, hy⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff (f - g)).mp hz
  change cyclicPolynomialTop p ℤ * y = f - g at hy
  have hr : polynomialBooleanBoundaryMap (MvPolynomial.rename e (f - g)) = 0 := by
    apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
    refine ⟨MvPolynomial.rename e y, ?_⟩
    change cyclicPolynomialTop p ℤ * MvPolynomial.rename e y = MvPolynomial.rename e (f - g)
    rw [← hy, map_mul, cyclicPolynomialTop_rename]
  rw [map_sub, map_sub] at hr
  exact sub_eq_zero.mp hr

theorem exists_integralPrimeCyclic_lift_of_modular
    (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (hfgrade : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (hFgrade : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      F (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (hfboundary : ∀ (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) ℤ),
      polynomialBooleanBoundaryMap (f (cyclicBooleanParameterRepresentation p ℤ g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p ℤ g (f x)))
    (hFequiv : RepresentationIntertwines (cyclicBooleanParameterRepresentation p (ZMod p))
      (cyclicPolynomialParameterRepresentation p (ZMod p)) F)
    (m : ℤ) (hf₁ : f 1 = MvPolynomial.C m) (hF₁ : F 1 = MvPolynomial.C (m : ZMod p)) :
    ∃ L : BooleanParameterMap (ZMod p) ℤ,
      RepresentationIntertwines (cyclicBooleanParameterRepresentation p ℤ)
        (cyclicPolynomialParameterRepresentation p ℤ) L ∧
      (∀ x, polynomialBooleanBoundaryMap (L x) = polynomialBooleanBoundaryMap (f x)) ∧
      (∀ n x, x ∈ (booleanScalarGradedBasis (V := ZMod p) (K := ℤ)).piece n →
        L x ∈ polynomialDegreePiece n) ∧ L 1 = MvPolynomial.C m := by
  let l := liftModularParameterMap p f F hb
  have hlred : extendIntegralParameterMap (ZMod p) l = F :=
    liftModularParameterMap_reduction p f F hb
  have hlb : ∀ x, polynomialBooleanBoundaryMap (l x) = polynomialBooleanBoundaryMap (f x) :=
    liftModularParameterMap_boundary p f F hb
  have hle : ∀ (g : PrimeCycleGroup p) x,
      polynomialBooleanBoundaryMap (l (cyclicBooleanParameterRepresentation p ℤ g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p ℤ g (l x)) := by
    intro g x
    rw [hlb, hfboundary]
    exact (integralCyclic_boundary_rename_congr p (Equiv.addLeft g.toAdd) (l x) (f x) (hlb x)).symm
  obtain ⟨L, hLe, hLb, hLg, hL₁⟩ := exists_integralPrimeCyclic_correction p l
    (liftModularParameterMap_degree p f F hb hfgrade hFgrade) hle
    (integralCyclic_conjugation_vanishes_modular p l (by rwa [hlred]))
    m (liftModularParameterMap_one p f F hb m hf₁ hF₁)
  exact ⟨L, hLe, fun x => (hLb x).trans (hlb x), hLg, hL₁⟩

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicModularLift.lean -/
section


section

/-! # The prime-cyclic controlled lift for actual face rings

This is the exceptional modular construction in the positive direction of
Theorem 1.3.  Every source, action, quotient, and kernel is the one already
defined on the actual Boolean barycentric and polynomial rings.  The sole
input is an ordinary graded normalized boundary lift whose boundary values
are equivariant; equivariance of the full lift is constructed here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
variable [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

theorem cyclicPolynomialParameterRepresentation_graded :
    ∀ (g : PrimeCycleGroup p) (n : ℕ) (f : MvPolynomial (ZMod p) K),
      f ∈ CyclicPolynomialPiece p K n →
        cyclicPolynomialParameterRepresentation p K g f ∈ CyclicPolynomialPiece p K n := by
  intro g n f hf
  exact (cyclicPolynomialRepresentation p K n g ⟨f, hf⟩).property

theorem cyclicBooleanParameterRepresentation_graded :
    ∀ (g : PrimeCycleGroup p) (n : ℕ) (x : BooleanBarycentricRing (ZMod p) K),
      x ∈ (booleanScalarGradedBasis (V := ZMod p) (K := K)).piece n →
        cyclicBooleanParameterRepresentation p K g x ∈
          (booleanScalarGradedBasis (V := ZMod p) (K := K)).piece n := by
  intro g n x hx
  exact booleanParameterPermutationRepresentation_graded (Equiv.addLeft g.toAdd) n x hx

theorem cyclicControlledQuotient_intertwines :
    RepresentationIntertwines (cyclicPolynomialParameterRepresentation p K)
      (cyclicControlledQuotientRepresentation p K) (cyclicControlledKernel p K).mkQ := by
  intro g x
  rfl

def cyclicControlledDegreeMap (n : ℕ) :
    CyclicPolynomialPiece p K n →ₗ[K] CyclicControlledQuotient p K :=
  ((cyclicControlledKernel p K).mkQ.restrictScalars K).comp
    (CyclicPolynomialPiece p K n).subtype

theorem cyclicControlledDegreeKernel_eq (n : ℕ) :
    LinearMap.ker (cyclicControlledDegreeMap p K n) =
      LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n) := by
  ext f
  change (cyclicControlledKernel p K).mkQ f.val = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact (cyclicBoundaryOrbitDegree_mem_kernel p K n f).symm

def cyclicControlledDegreeKernelRepresentation (n : ℕ) :
    CyclicRepresentation K (PrimeCycleGroup p)
      (LinearMap.ker (cyclicControlledDegreeMap p K n)) :=
  ScalarGradedBasis.kernelDegreeRepresentation
    (cyclicPolynomialParameterRepresentation p K) (cyclicControlledQuotientRepresentation p K)
    (CyclicPolynomialPiece p K) (cyclicControlledKernel p K).mkQ
    (cyclicPolynomialParameterRepresentation_graded p K) (cyclicControlledQuotient_intertwines p K) n

theorem cyclicControlledDegreeKernel_isCoinduced (n : ℕ) :
    ∃ J : Type, ∃ e : LinearMap.ker (cyclicControlledDegreeMap p K n) ≃ₗ[K]
      (PrimeCycleGroup p → J → K),
      RepresentationIntertwines (cyclicControlledDegreeKernelRepresentation p K n)
        coinducedRepresentation e.toLinearMap := by
  obtain ⟨J, e, he⟩ := cyclicBoundaryOrbitKernel_isCoinduced p K n
  let t := LinearEquiv.ofEq _ _ (cyclicControlledDegreeKernel_eq p K n)
  have ht : RepresentationIntertwines (cyclicControlledDegreeKernelRepresentation p K n)
      (cyclicBoundaryOrbitKernelRepresentation p K n) t.toLinearMap := by
    intro g x
    apply Subtype.ext
    apply Subtype.ext
    rfl
  refine ⟨J, t.trans e, ?_⟩
  intro g x
  change e (t (cyclicControlledDegreeKernelRepresentation p K n g x)) =
    coinducedRepresentation (K := K) (C := J → K) g (e (t x))
  exact (congrArg e (ht g x)).trans (he g (t x))

theorem cyclicBoundary_rename_congr (e : Equiv.Perm (ZMod p))
    (f g : MvPolynomial (ZMod p) K)
    (h : polynomialBooleanBoundaryMap f = polynomialBooleanBoundaryMap g) :
    polynomialBooleanBoundaryMap (MvPolynomial.rename e f) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename e g) := by
  have hz : polynomialBooleanBoundaryMap (f - g) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨x, hx⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff (f - g)).mp hz
  change cyclicPolynomialTop p K * x = f - g at hx
  have hr : polynomialBooleanBoundaryMap (MvPolynomial.rename e (f - g)) = 0 := by
    apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
    refine ⟨MvPolynomial.rename e x, ?_⟩
    change cyclicPolynomialTop p K * MvPolynomial.rename e x = MvPolynomial.rename e (f - g)
    rw [← hx, map_mul, cyclicPolynomialTop_rename]
  rw [map_sub, map_sub] at hr
  exact sub_eq_zero.mp hr

theorem booleanScalarGradedBasis_one :
    (1 : BooleanBarycentricRing (ZMod p) K) ∈
      (booleanScalarGradedBasis (V := ZMod p) (K := K)).piece 0 := by
  let σ := weightOrdering (fun _ : ZMod p => 0)
  have hd : orderingDescents σ = ∅ := weightOrdering_zero_no_descents
  have hdegree : colorOrdinaryDegree (descentColorExponent σ) = 0 :=
    (descentOrdinaryDegree_eq_zero_iff σ).mpr hd
  have h := (booleanScalarGradedBasis (V := ZMod p) (K := K)).generator_mem_piece σ
  simpa only [booleanScalarGradedBasis, booleanColorBasis_apply, descentVector, hd,
    Finset.prod_empty, hdegree] using h

/-- A full parameter-linear prime-cyclic lift with the prescribed actual
boundary, fixed quotient, ordinary grading, and normalization. -/
theorem exists_primeCyclic_boundary_lift
    (f₀ : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K)
    (hf₀ : IsParameterLinear booleanColorMap polynomialColorMap f₀)
    (h₁ : f₀ 1 = 1)
    (hd₀ : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f₀ (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (hb₀ : ∀ (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) K),
      polynomialBooleanBoundaryMap (f₀ (cyclicBooleanParameterRepresentation p K g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p K g (f₀ x))) :
    ∃ F : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K,
      IsParameterLinear booleanColorMap polynomialColorMap F ∧
      (∀ n x, x ∈ (booleanScalarGradedBasis (V := ZMod p) (K := K)).piece n →
        F x ∈ CyclicPolynomialPiece p K n) ∧
      F 1 = 1 ∧
      (∀ x, polynomialBooleanBoundaryMap (F x) = polynomialBooleanBoundaryMap (f₀ x)) ∧
      (∀ x, primeOrbitRetraction p (F x) = booleanTopEvaluation x) ∧
      (∀ g x, F (cyclicBooleanParameterRepresentation p K g x) =
        cyclicPolynomialParameterRepresentation p K g (F x)) := by
  let s := booleanScalarGradedBasis (V := ZMod p) (K := K)
  let ρ := cyclicBooleanParameterRepresentation p K
  let τ := cyclicPolynomialParameterRepresentation p K
  let υ := cyclicControlledQuotientRepresentation p K
  let H := cyclicControlledKernel p K
  let T := CyclicPolynomialPiece p K
  let f := cyclicOrdinaryCorrectedLift p K f₀
  have hf : IsParameterLinear booleanColorMap polynomialColorMap f :=
    cyclicOrdinaryCorrectedLift_parameterLinear p K f₀
  have hfone : f 1 = 1 := cyclicOrdinaryCorrectedLift_one p K f₀ h₁
  have hfboundary (x) : polynomialBooleanBoundaryMap (f x) = polynomialBooleanBoundaryMap (f₀ x) :=
    cyclicOrdinaryCorrectedLift_boundary p K f₀ hf₀ h₁ hd₀ x
  have hfE (x) : primeOrbitRetraction p (f x) = booleanTopEvaluation x :=
    cyclicOrdinaryCorrectedLift_orbitRetraction p K f₀ x
  have hfgrade : ∀ n x, x ∈ s.piece n → f x ∈ T n := by
    intro n x hx
    rw [booleanScalarGradedBasis_piece_eq] at hx
    exact parameterLinear_ordinary_degree f hf
      (cyclicOrdinaryCorrectedLift_descent_degree p K f₀ hd₀) n x hx
  let fA := parameterLinearMap f hf
  let a := H.mkQ.comp fA
  have ha : RepresentationIntertwines ρ υ a := by
    intro g x
    change H.mkQ (f (ρ g x)) = H.mkQ (τ g (f x))
    apply (Submodule.Quotient.eq H).mpr
    constructor
    · change polynomialBooleanBoundaryMap (f (ρ g x) - τ g (f x)) = 0
      rw [map_sub, hfboundary, hb₀]
      apply sub_eq_zero.mpr
      exact (cyclicBoundary_rename_congr p K (Equiv.addLeft g.toAdd) (f x) (f₀ x)
        (hfboundary x)).symm
    · change primeOrbitRetraction p (f (ρ g x) - τ g (f x)) = 0
      rw [map_sub, hfE, cyclicPolynomialParameterRepresentation_apply,
        primeOrbitRetraction_rename, hfE]
      change booleanTopEvaluation (booleanPermutationAlgEquiv (Equiv.addLeft g.toAdd) x) -
        booleanTopEvaluation x = 0
      rw [booleanTopEvaluation_permutation, sub_self]
  let β : ∀ n, s.piece n →ₗ[K] T n := fun n =>
    LinearMap.codRestrict (T n) (f.comp (s.piece n).subtype)
      (fun x => hfgrade n x.val x.property)
  have hqβ : ∀ n, (ScalarGradedBasis.degreeQuotient T H.mkQ n).comp (β n) =
      s.degreeTarget a n := by intro n; rfl
  choose J e he using cyclicControlledDegreeKernel_isCoinduced p K
  let C : ℕ → Type _ := fun n => J n → K
  letI : ∀ n, AddCommGroup (C n) := fun _ => inferInstance
  letI : ∀ n, Module K (C n) := fun _ => inferInstance
  have hmult : ∀ j y, y ∈ T (s.generatorDegree (s.parent j)) →
      s.multiplier j • y ∈ T (s.degree j) := by
    intro j y hy
    change polynomialColorMap (MvPolynomial.monomial j.2 1) * y ∈
      polynomialDegreePiece (colorOrdinaryDegree j.2 + colorOrdinaryDegree (descentColorExponent j.1))
    exact polynomialDegreePiece_mul _ _ _ _ (polynomialColorMap_monomial_degree j.2) hy
  obtain ⟨F, hFgrade, hFq, hFeq⟩ := s.exists_equivariantGradedLift_of_ordinary_lifts
    ρ τ υ T H.mkQ a (cyclicBooleanParameterRepresentation_graded p K)
    (cyclicPolynomialParameterRepresentation_graded p K) (cyclicControlledQuotient_intertwines p K)
    hmult ha C β hqβ e he
  have hdiff (x : BooleanBarycentricRing (ZMod p) K) : F x - f x ∈ H := by
    apply (Submodule.Quotient.eq H).mp
    exact congrArg (fun L : BooleanBarycentricRing (ZMod p) K →ₗ[
      MvPolynomial (Fin (Fintype.card (ZMod p))) K] CyclicControlledQuotient p K => L x) hFq
  have hFboundary (x) : polynomialBooleanBoundaryMap (F x) = polynomialBooleanBoundaryMap (f₀ x) := by
    have hh := (hdiff x).1
    change polynomialBooleanBoundaryMap (F x - f x) = 0 at hh
    rw [map_sub] at hh
    exact (sub_eq_zero.mp hh).trans (hfboundary x)
  have hFE (x) : primeOrbitRetraction p (F x) = booleanTopEvaluation x := by
    have hh := (hdiff x).2
    change primeOrbitRetraction p (F x - f x) = 0 at hh
    rw [map_sub] at hh
    exact (sub_eq_zero.mp hh).trans (hfE x)
  have hFone : F 1 = 1 := by
    have hd : F 1 - 1 ∈ T 0 := (T 0).sub_mem
      (hFgrade 0 1 (booleanScalarGradedBasis_one p K)) polynomialDegreePiece_one
    have hk : (⟨F 1 - 1, hd⟩ : CyclicPolynomialPiece p K 0) ∈
        LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K 0) := by
      apply (cyclicBoundaryOrbitDegree_mem_kernel p K 0 _).mpr
      have hh := hdiff 1
      change polynomialBooleanBoundaryMap (F 1 - f 1) = 0 ∧
        primeOrbitRetraction p (F 1 - f 1) = 0 at hh
      simpa only [hfone] using hh
    have hz := cyclicBoundaryOrbitKernel_zero_below p K 0 (Fact.out : p.Prime).pos ⟨⟨F 1 - 1, hd⟩, hk⟩
    exact sub_eq_zero.mp (congrArg (fun z => z.val.val) hz)
  refine ⟨F.restrictScalars K, ?_, hFgrade, hFone, hFboundary, hFE, hFeq⟩
  intro b x
  exact F.map_smul b x

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegralPrimeLift.lean -/
section


section

/-! # Integral prime-cyclic boundary lifting

This combines the actual modular controlled lift, exact integral lifting of
its top-monomial corrections, and integral affine averaging.  The conclusion
has no modular lifting, kernel splitting, or torsion-freeness hypotheses:
only an ordinary normalized graded lift of an equivariant boundary is input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

variable (p : ℕ) [Fact p.Prime] [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

theorem cyclicBoundary_coefficient_congr {K L : Type*} [CommRing K] [CommRing L]
    (h : K →+* L) (f g : MvPolynomial (ZMod p) K)
    (he : polynomialBooleanBoundaryMap f = polynomialBooleanBoundaryMap g) :
    polynomialBooleanBoundaryMap (MvPolynomial.map h f) =
      polynomialBooleanBoundaryMap (MvPolynomial.map h g) := by
  have hz : polynomialBooleanBoundaryMap (f - g) = 0 := by rw [map_sub, he, sub_self]
  obtain ⟨y, hy⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff (f - g)).mp hz
  change cyclicPolynomialTop p K * y = f - g at hy
  have hr : polynomialBooleanBoundaryMap (MvPolynomial.map h (f - g)) = 0 := by
    apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
    refine ⟨MvPolynomial.map h y, ?_⟩
    change cyclicPolynomialTop p L * MvPolynomial.map h y = MvPolynomial.map h (f - g)
    rw [← hy, map_mul, cyclicPolynomialTop_map]
  rw [map_sub, map_sub] at hr
  exact sub_eq_zero.mp hr

theorem extendIntegralParameterMap_cyclicBoundary (f : BooleanParameterMap (ZMod p) ℤ)
    (hf : ∀ (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) ℤ),
      polynomialBooleanBoundaryMap (f (cyclicBooleanParameterRepresentation p ℤ g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p ℤ g (f x))) :
    ∀ (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) (ZMod p)),
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f
        (cyclicBooleanParameterRepresentation p (ZMod p) g x)) =
      polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p (ZMod p) g
        (extendIntegralParameterMap (ZMod p) f x)) := by
  intro g
  let F := extendIntegralParameterMap (ZMod p) f
  let ρ := cyclicBooleanParameterRepresentation p (ZMod p)
  let τ := cyclicPolynomialParameterRepresentation p (ZMod p)
  let q : MvPolynomial (ZMod p) (ZMod p) →ₗ[ZMod p] PolynomialBoundaryRing (ZMod p) (ZMod p) :=
    polynomialBooleanBoundaryMap.toLinearMap
  have he : q.comp ((F.restrictScalars (ZMod p)).comp ((ρ g).restrictScalars (ZMod p))) =
      q.comp (((τ g).restrictScalars (ZMod p)).comp (F.restrictScalars (ZMod p))) := by
    apply (booleanParameterBasis (V := ZMod p) (K := ZMod p)).ext
    intro i
    change polynomialBooleanBoundaryMap (F (ρ g (booleanParameterBasis i))) =
      polynomialBooleanBoundaryMap (τ g (F (booleanParameterBasis i)))
    rw [← booleanCoefficientChange_parameterBasis (Int.castRingHom (ZMod p)) i]
    have hact := booleanCoefficientChange_restriction (Int.castRingHom (ZMod p))
      (cyclicVertexPermutation p g).symm.toEmbedding (booleanParameterBasis (K := ℤ) i)
    change booleanCoefficientChange (Int.castRingHom (ZMod p))
        (cyclicBooleanParameterRepresentation p ℤ g (booleanParameterBasis (K := ℤ) i)) =
      ρ g (booleanCoefficientChange (Int.castRingHom (ZMod p))
        (booleanParameterBasis (K := ℤ) i)) at hact
    rw [← hact]
    change polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f
      (booleanCoefficientChange (Int.castRingHom (ZMod p))
        (cyclicBooleanParameterRepresentation p ℤ g (booleanParameterBasis (K := ℤ) i)))) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename (cyclicVertexPermutation p g)
        (extendIntegralParameterMap (ZMod p) f
          (booleanCoefficientChange (Int.castRingHom (ZMod p)) (booleanParameterBasis (K := ℤ) i))))
    rw [extendIntegralParameterMap_commutes, extendIntegralParameterMap_commutes,
      polynomialCoefficientChange_eq, polynomialCoefficientChange_eq,
      ← MvPolynomial.map_rename]
    exact cyclicBoundary_coefficient_congr p (Int.castRingHom (ZMod p)) _ _
      (hf g (booleanParameterBasis i))
  intro x
  exact DFunLike.congr_fun he x

theorem exists_integralPrimeCyclic_boundary_lift
    (f : BooleanParameterMap (ZMod p) ℤ)
    (hfgrade : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (hfboundary : ∀ (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) ℤ),
      polynomialBooleanBoundaryMap (f (cyclicBooleanParameterRepresentation p ℤ g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p ℤ g (f x)))
    (hf₁ : f 1 = 1) :
    ∃ L : BooleanParameterMap (ZMod p) ℤ,
      RepresentationIntertwines (cyclicBooleanParameterRepresentation p ℤ)
        (cyclicPolynomialParameterRepresentation p ℤ) L ∧
      (∀ x, polynomialBooleanBoundaryMap (L x) = polynomialBooleanBoundaryMap (f x)) ∧
      (∀ n x, x ∈ (booleanScalarGradedBasis (V := ZMod p) (K := ℤ)).piece n →
        L x ∈ polynomialDegreePiece n) ∧ L 1 = 1 := by
  let fbar := extendIntegralParameterMap (ZMod p) f
  have hfb : IsParameterLinear booleanColorMap polynomialColorMap
      (fbar.restrictScalars (ZMod p)) := fun a x => fbar.map_smul a x
  have hfbar₁ : fbar 1 = 1 := by
    simpa only [Int.cast_one, map_one] using
      (extendIntegralParameterMap_one (ZMod p) f 1 (by simpa only [map_one] using hf₁))
  obtain ⟨F, hFp, hFg, hF₁, hFb, hFE, hFe⟩ := exists_primeCyclic_boundary_lift p (ZMod p)
    (fbar.restrictScalars (ZMod p)) hfb hfbar₁
    (extendIntegralParameterMap_degree (ZMod p) f hfgrade)
    (extendIntegralParameterMap_cyclicBoundary p f hfboundary)
  let FA := parameterLinearMap F hFp
  have hFgen : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      FA (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
    intro σ
    change F (descentVector σ) ∈ polynomialDegreePiece _
    apply hFg
    simpa only [booleanScalarGradedBasis, booleanColorBasis_apply] using
      (booleanScalarGradedBasis (V := ZMod p) (K := ZMod p)).generator_mem_piece σ
  obtain ⟨L, hLe, hLb, hLg, hL₁⟩ := exists_integralPrimeCyclic_lift_of_modular p f FA hFb
    hfgrade hFgen hfboundary hFe 1
    (by simpa only [map_one] using hf₁)
    (by change F 1 = MvPolynomial.C ((1 : ℤ) : ZMod p);
        simpa only [Int.cast_one, MvPolynomial.C_1] using hF₁)
  exact ⟨L, hLe, hLb, hLg, by simpa only [map_one] using hL₁⟩

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicVertexTransport.lean -/
section


section

/-! # Transport of actual local parameter maps along vertex bijections -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.
open Classical Finset MvPolynomial
open scoped CyclicParameterAction

variable {V W U K : Type*} [Fintype V] [Fintype W] [Fintype U] [CommRing K]

def vertexMapTransport (e : V ≃ W)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K) :
    BooleanBarycentricRing W K →ₗ[K] MvPolynomial W K :=
  (MvPolynomial.rename e).toLinearMap.comp
    (f.comp (booleanVertexRelabelEquiv (K := K) e.symm).toLinearMap)

@[simp] theorem vertexMapTransport_apply (e : V ≃ W)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K) (x : BooleanBarycentricRing W K) :
    vertexMapTransport e f x = MvPolynomial.rename e (f (booleanVertexRelabelEquiv e.symm x)) := rfl

theorem intertwinesAllRanks_parameterLinear [LinearOrder V]
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K) (hf : IntertwinesAllRanks f) :
    IsParameterLinear booleanColorMap polynomialColorMap f := by
  apply (isParameterLinear_iff_X _ _ _).mpr
  intro c x
  rw [booleanColorMap, MvPolynomial.aeval_X, polynomialColorMap, MvPolynomial.aeval_X,
    ← booleanRankParameter_color]
  exact hf c.val x

theorem vertexMapTransport_parameters [LinearOrder V] [LinearOrder W]
    (e : V ≃ W) (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IntertwinesAllRanks f) : IntertwinesAllRanks (vertexMapTransport e f) := by
  intro r x
  erw [vertexMapTransport_apply, map_mul, booleanVertexRelabelEquiv_parameter,
    hf, map_mul, MvPolynomial.rename_esymm]
  rfl

theorem vertexMapTransport_degree (e : V ≃ W)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n)
    (n : ℕ) (x : BooleanBarycentricRing W K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    vertexMapTransport e f x ∈ polynomialDegreePiece n :=
  polynomialRename_degree e n _ (hf n _ (booleanVertexRelabelEquiv_degree e.symm n x hx))

theorem vertexMapTransport_one (e : V ≃ W)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K) (hf : f 1 = 1) :
    vertexMapTransport e f 1 = 1 := by rw [vertexMapTransport_apply, map_one, hf, map_one]

theorem booleanVertexRelabelEquiv_symm_apply (e : V ≃ W) (x : BooleanBarycentricRing V K) :
    booleanVertexRelabelEquiv e.symm (booleanVertexRelabelEquiv e x) = x :=
  (booleanVertexRelabelEquiv (K := K) e).symm_apply_apply x

theorem vertexMapTransport_symm (e : V ≃ W)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K) :
    vertexMapTransport e.symm (vertexMapTransport e f) = f := by
  apply LinearMap.ext
  intro x
  rw [vertexMapTransport_apply, vertexMapTransport_apply, Equiv.symm_symm,
    booleanVertexRelabelEquiv_symm_apply, MvPolynomial.rename_rename]
  have he : (e.symm : W → V) ∘ (e : V → W) = id := by
    funext v
    exact e.symm_apply_apply v
  rw [he, MvPolynomial.rename_id_apply]

theorem rename_fullPolynomialTop (e : V ≃ W) :
    MvPolynomial.rename e (∏ v : V, MvPolynomial.X v : MvPolynomial V K) =
      ∏ w : W, MvPolynomial.X w := by
  rw [map_prod]
  simp only [MvPolynomial.rename_X]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

theorem polynomialBoundary_rename_equiv_congr (e : V ≃ W)
    (f g : MvPolynomial V K) (h : polynomialBooleanBoundaryMap f = polynomialBooleanBoundaryMap g) :
    polynomialBooleanBoundaryMap (MvPolynomial.rename e f) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename e g) := by
  have hz : polynomialBooleanBoundaryMap (f - g) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨y, hy⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff _).mp hz
  have hz' : polynomialBooleanBoundaryMap (MvPolynomial.rename e (f - g)) = 0 := by
    apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
    refine ⟨MvPolynomial.rename e y, ?_⟩
    rw [← hy, map_mul, rename_fullPolynomialTop]
  rw [map_sub, map_sub] at hz'
  exact sub_eq_zero.mp hz'

theorem vertexMapTransport_boundary_congr (e : V ≃ W)
    (f g : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (h : ∀ x, polynomialBooleanBoundaryMap (f x) = polynomialBooleanBoundaryMap (g x)) :
    ∀ x, polynomialBooleanBoundaryMap (vertexMapTransport e f x) =
      polynomialBooleanBoundaryMap (vertexMapTransport e g x) := by
  intro x
  exact polynomialBoundary_rename_equiv_congr e _ _ (h _)

theorem booleanVertexRelabelEquiv_permutation (e : V ≃ W) (h : Equiv.Perm W)
    (x : BooleanBarycentricRing W K) :
    booleanVertexRelabelEquiv e.symm (booleanVertexRelabelEquiv h x) =
      booleanVertexRelabelEquiv (e.symm.permCongr h) (booleanVertexRelabelEquiv e.symm x) := by
  rw [← booleanVertexRelabelEquiv_trans, ← booleanVertexRelabelEquiv_trans]
  have he : h.trans e.symm = e.symm.trans (e.symm.permCongr h) := by
    apply Equiv.ext
    intro v
    simp only [Equiv.trans_apply, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  exact congrArg (fun q : W ≃ V => booleanVertexRelabelEquiv (K := K) q x) he

theorem polynomialRename_permutation (e : V ≃ W) (h : Equiv.Perm W) (f : MvPolynomial V K) :
    MvPolynomial.rename e (MvPolynomial.rename (e.symm.permCongr h) f) =
      MvPolynomial.rename h (MvPolynomial.rename e f) := by
  rw [MvPolynomial.rename_rename, MvPolynomial.rename_rename]
  apply congrArg (fun q : V → W => MvPolynomial.rename q f)
  funext v
  exact e.apply_symm_apply (h (e v))

theorem vertexMapTransport_boundary_permutation [LinearOrder V] [LinearOrder W]
    (e : V ≃ W) (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (h : Equiv.Perm W)
    (hf : ∀ x, polynomialBooleanBoundaryMap (f (booleanPermutationAlgEquiv (e.symm.permCongr h) x)) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename (e.symm.permCongr h) (f x))) :
    ∀ x, polynomialBooleanBoundaryMap (vertexMapTransport e f (booleanPermutationAlgEquiv h x)) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename h (vertexMapTransport e f x)) := by
  intro x
  change polynomialBooleanBoundaryMap (MvPolynomial.rename e
      (f (booleanVertexRelabelEquiv e.symm (booleanVertexRelabelEquiv h x)))) = _
  rw [booleanVertexRelabelEquiv_permutation]
  have hh := polynomialBoundary_rename_equiv_congr e _ _ (hf (booleanVertexRelabelEquiv e.symm x))
  rw [polynomialRename_permutation] at hh
  exact hh

theorem vertexMapTransport_equivariant [LinearOrder V] [LinearOrder W]
    (e : V ≃ W) (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (h : Equiv.Perm W)
    (hf : ∀ x, f (booleanPermutationAlgEquiv (e.symm.permCongr h) x) =
      MvPolynomial.rename (e.symm.permCongr h) (f x)) :
    ∀ x, vertexMapTransport e f (booleanPermutationAlgEquiv h x) =
      MvPolynomial.rename h (vertexMapTransport e f x) := by
  intro x
  change MvPolynomial.rename e (f (booleanVertexRelabelEquiv e.symm
    (booleanVertexRelabelEquiv h x))) = _
  change ∀ x, f (booleanVertexRelabelEquiv (e.symm.permCongr h) x) =
    MvPolynomial.rename (e.symm.permCongr h) (f x) at hf
  rw [booleanVertexRelabelEquiv_permutation, hf, polynomialRename_permutation]
  rfl

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimeVertexLift.lean -/
section


section

/-! # The integral prime lift on an arbitrary prime-sized vertex set -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.
open Classical MvPolynomial
open scoped CyclicParameterAction

variable (p : ℕ) [Fact p.Prime] [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem exists_integralPrime_vertex_lift (e : V ≃ ZMod p)
    (f : BooleanBarycentricRing V ℤ →ₗ[ℤ] MvPolynomial V ℤ)
    (hfp : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hfd : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n)
    (hf₁ : f 1 = 1)
    (hfb : ∀ (g : PrimeCycleGroup p) x,
      polynomialBooleanBoundaryMap (f (booleanPermutationAlgEquiv
        (e.symm.permCongr (Equiv.addLeft g.toAdd)) x)) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename
        (e.symm.permCongr (Equiv.addLeft g.toAdd)) (f x))) :
    ∃ L : BooleanBarycentricRing V ℤ →ₗ[ℤ] MvPolynomial V ℤ,
      IsParameterLinear booleanColorMap polynomialColorMap L ∧
      (∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => chainOrdinaryDegree a.val) n → L x ∈ polynomialDegreePiece n) ∧
      L 1 = 1 ∧
      (∀ x, polynomialBooleanBoundaryMap (L x) = polynomialBooleanBoundaryMap (f x)) ∧
      ∀ (g : PrimeCycleGroup p) x,
        L (booleanPermutationAlgEquiv (e.symm.permCongr (Equiv.addLeft g.toAdd)) x) =
          MvPolynomial.rename (e.symm.permCongr (Equiv.addLeft g.toAdd)) (L x) := by
  let fQ := vertexMapTransport e f
  have hQp : IsParameterLinear booleanColorMap polynomialColorMap fQ :=
    intertwinesAllRanks_parameterLinear fQ
      (vertexMapTransport_parameters e f (parameterLinear_intertwinesAllRanks f hfp))
  let fQA := parameterLinearMap fQ hQp
  have hQd : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      fQA (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
    intro σ
    apply vertexMapTransport_degree e f hfd
    change descentVector σ ∈ basisOrdinaryDegreePiece
      (booleanChainBasis (V := ZMod p) (K := ℤ))
      (fun a => chainOrdinaryDegree a.val) (colorOrdinaryDegree (descentColorExponent σ))
    have hh := (booleanScalarGradedBasis (V := ZMod p) (K := ℤ)).generator_mem_piece σ
    rw [booleanScalarGradedBasis_piece_eq] at hh
    simpa only [booleanScalarGradedBasis, booleanColorBasis_apply,
      booleanOrdinaryDegree_eq_chainOrdinaryDegree] using hh
  have hQb : ∀ (g : PrimeCycleGroup p) x,
      polynomialBooleanBoundaryMap (fQA (cyclicBooleanParameterRepresentation p ℤ g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p ℤ g (fQA x)) := by
    intro g x
    exact vertexMapTransport_boundary_permutation e f (Equiv.addLeft g.toAdd) (hfb g) x
  obtain ⟨LQ, hLQe, hLQb, hLQd, hLQ₁⟩ := exists_integralPrimeCyclic_boundary_lift p fQA
    hQd hQb (vertexMapTransport_one e f hf₁)
  let L := vertexMapTransport e.symm (LQ.restrictScalars ℤ)
  have hLQp : IsParameterLinear booleanColorMap polynomialColorMap (LQ.restrictScalars ℤ) :=
    fun a x => LQ.map_smul a x
  refine ⟨L, ?_, ?_, vertexMapTransport_one e.symm (LQ.restrictScalars ℤ) hLQ₁, ?_, ?_⟩
  · exact intertwinesAllRanks_parameterLinear L
      (vertexMapTransport_parameters e.symm (LQ.restrictScalars ℤ)
        (parameterLinear_intertwinesAllRanks _ hLQp))
  · intro n x hx
    apply vertexMapTransport_degree e.symm (LQ.restrictScalars ℤ) _ n x hx
    intro m y hy
    apply hLQd m y
    rwa [booleanScalarGradedBasis_piece_eq]
  · intro x
    have hh := vertexMapTransport_boundary_congr e.symm (LQ.restrictScalars ℤ) fQ hLQb x
    rw [vertexMapTransport_symm] at hh
    exact hh
  · intro g x
    let h : Equiv.Perm (ZMod p) := Equiv.addLeft g.toAdd
    have he : e.permCongr (e.symm.permCongr h) = h := e.permCongr.apply_symm_apply h
    apply vertexMapTransport_equivariant e.symm (LQ.restrictScalars ℤ)
      (e.symm.permCongr h) _ x
    intro y
    rw [Equiv.symm_symm, he]
    exact hLQe g y

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicStalkInduction.lean -/
section


section

/-! # Orbitwise induction for actual coherent stalk maps

The generic orbit choice is applied to families supported at one face.  A
rank stage therefore stores actual maps on exactly the previously constructed
stalks.  Its boundary map is obtained by reading those components, and the
compatibility predicate is the genuine restriction equation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal


open Classical

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

def stalkFamilySingle (p : P) (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p) :
    StalkLinearFamily (P := P) K := Pi.single p f

@[simp] theorem stalkFamilySingle_same (p : P) (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p) :
    stalkFamilySingle K p f p = f := by simp [stalkFamilySingle]

@[simp] theorem stalkFamilySingle_ne (p q : P) (h : q ≠ p)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p) :
    stalkFamilySingle K p f q = 0 := by simp [stalkFamilySingle, h]

theorem stalkFamilySingle_eq_of_supported (p : P) (F : StalkLinearFamily (P := P) K)
    (hF : ∀ q, q ≠ p → F q = 0) : stalkFamilySingle K p (F p) = F := by
  funext q
  by_cases hq : q = p
  · subst q
    exact stalkFamilySingle_same K p (F p)
  · rw [stalkFamilySingle_ne K p q hq, hF q hq]

def StalkLocalGood (p : P) (F : StalkLinearFamily (P := P) K) : Prop :=
  (∀ q, q ≠ p → F q = 0) ∧ F ∈ parameterStalkFamilySubmodule K ∧
    F ∈ gradedStalkFamilySubmodule K ∧ F p 1 = 1

def StalkLocalCompatible (p q : P) (F H : StalkLinearFamily (P := P) K) : Prop :=
  ∀ (h : q ≤ p) x, polynomialRestriction K h (F p x) =
    H q (booleanRestriction (faceVertexInclusion h) x)

theorem stalkFamilySingle_good (p : P)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p)
    (hp : ∀ r x, f (booleanRankParameter (r + 1) * x) = polynomialParameter K p (r + 1) * f x)
    (hd : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n)
    (h₁ : f 1 = 1) : StalkLocalGood K p (stalkFamilySingle K p f) := by
  refine ⟨fun q hq => stalkFamilySingle_ne K p q hq f, ?_, ?_, ?_⟩
  · intro q r x
    by_cases hq : q = p
    · subst q; simpa only [stalkFamilySingle_same] using hp r x
    · rw [stalkFamilySingle_ne K p q hq f]
      simp
  · intro q n x hx
    by_cases hq : q = p
    · subst q; simpa only [stalkFamilySingle_same] using hd n x hx
    · rw [stalkFamilySingle_ne K p q hq f]
      exact (polynomialDegreePiece n).zero_mem
  · simpa only [stalkFamilySingle_same] using h₁

theorem stalkFamilyRelabel_good (e : P ≃o P) (p : P) (F : StalkLinearFamily (P := P) K)
    (hF : StalkLocalGood K p F) :
    StalkLocalGood K (e p) (stalkFamilyRelabel K e F) := by
  refine ⟨?_, stalkFamilyRelabel_parameter K e F hF.2.1,
    stalkFamilyRelabel_graded K e F hF.2.2.1, ?_⟩
  · intro q hq
    have hn : e.symm q ≠ p := by
      intro he
      exact hq ((e.apply_symm_apply q).symm.trans (congrArg e he))
    apply LinearMap.ext
    intro x
    rw [stalkFamilyRelabel_apply, hF.1 _ hn]
    simp
  · rw [stalkFamilyRelabel_apply, map_one]
    have hhq (q : P) (hq : q = p) : F q 1 = 1 := by
      subst q
      exact hF.2.2.2
    have hh : F (e.symm (e p)) 1 = 1 := hhq _ (e.symm_apply_apply p)
    rw [hh, map_one]

theorem stalkFamilyRelabel_compatible (e : P ≃o P) (p q : P)
    (F H : StalkLinearFamily (P := P) K) (hFH : StalkLocalCompatible K p q F H) :
    StalkLocalCompatible K (e p) (e q) (stalkFamilyRelabel K e F) (stalkFamilyRelabel K e H) := by
  intro h x
  apply (polynomialStalkOrderEquiv K e.symm (e q)).injective
  have hn := polynomialStalkOrderEquiv_restriction K e.symm h
    ((polynomialStalkOrderEquiv K e.symm (e p)).symm
      (F (e.symm (e p)) (barycentricStalkOrderEquiv K e.symm (e p) x)))
  change polynomialStalkOrderEquiv K e.symm (e q)
      (polynomialRestriction K h ((polynomialStalkOrderEquiv K e.symm (e p)).symm
        (F (e.symm (e p)) (barycentricStalkOrderEquiv K e.symm (e p) x)))) =
    polynomialStalkOrderEquiv K e.symm (e q)
      ((polynomialStalkOrderEquiv K e.symm (e q)).symm
        (H (e.symm (e q)) (barycentricStalkOrderEquiv K e.symm (e q)
          (booleanRestriction (faceVertexInclusion h) x))))
  rw [← hn, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  rw [← barycentricStalkOrderEquiv_restriction]
  have hh : StalkLocalCompatible K (e.symm (e p)) (e.symm (e q)) F H := by
    simpa only [e.symm_apply_apply] using hFH
  exact hh (e.symm.monotone h) _

section Stage

variable {G : Type*} [Group G] [MulAction G P] [MulAction G (StalkLinearFamily (P := P) K)]
variable (hs : IsSimplicialPoset P)
variable (hrank : ∀ (g : G) (p : P), faceRank (g • p) = faceRank p)

def EquivariantRankStage.stalkBoundary {n : ℕ}
    (old : EquivariantRankStage faceRank hrank (StalkLocalGood K) (StalkLocalCompatible K) n)
    (p : P) (hp : faceRank p = n) :
    CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)) where
  component q := old.value ⟨q.val, by
    change faceRank q.val < n
    rw [← hp]
    exact faceRank_strictMono hs q.property⟩ q.val
  naturality q r h x := by
    by_cases he : r = q
    · subst r
      simp only [polynomialRestriction_refl, faceVertexInclusion_refl,
        booleanRestriction_refl, AlgHom.toLinearMap_apply, AlgHom.id_apply]
    · have hlt : r.val < q.val := lt_of_le_of_ne h (fun h' => he (Subtype.ext h'))
      exact old.compatible
        ⟨q.val, by change faceRank q.val < n; rw [← hp]; exact faceRank_strictMono hs q.property⟩
        ⟨r.val, by change faceRank r.val < n; rw [← hp]; exact faceRank_strictMono hs r.property⟩
        hlt h x

theorem EquivariantRankStage.stalkBoundary_parameter {n : ℕ}
    (old : EquivariantRankStage faceRank hrank (StalkLocalGood K) (StalkLocalCompatible K) n)
    (p : P) (hp : faceRank p = n) (q : Set.Iio p) (r : ℕ) (x : BarycentricStalk K q.val) :
    (old.stalkBoundary K hs hrank p hp).component q (booleanRankParameter (r + 1) * x) =
      polynomialParameter K q.val (r + 1) * (old.stalkBoundary K hs hrank p hp).component q x :=
  (old.good ⟨q.val, by change faceRank q.val < n; rw [← hp]; exact faceRank_strictMono hs q.property⟩).2.1 q.val r x

theorem EquivariantRankStage.stalkBoundary_degree {n : ℕ}
    (old : EquivariantRankStage faceRank hrank (StalkLocalGood K) (StalkLocalCompatible K) n)
    (p : P) (hp : faceRank p = n) (q : Set.Iio p) (m : ℕ) (x : BarycentricStalk K q.val)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) m) :
    (old.stalkBoundary K hs hrank p hp).component q x ∈ polynomialDegreePiece m :=
  (old.good ⟨q.val, by change faceRank q.val < n; rw [← hp]; exact faceRank_strictMono hs q.property⟩).2.2.1 q.val m x hx

theorem EquivariantRankStage.stalkBoundary_one {n : ℕ}
    (old : EquivariantRankStage faceRank hrank (StalkLocalGood K) (StalkLocalCompatible K) n)
    (p : P) (hp : faceRank p = n) (q : Set.Iio p) :
    (old.stalkBoundary K hs hrank p hp).component q 1 = 1 :=
  (old.good ⟨q.val, by change faceRank q.val < n; rw [← hp]; exact faceRank_strictMono hs q.property⟩).2.2.2

end Stage

section ActualAction

variable {G : Type*} [Group G]
variable (act : G → P ≃o P)
  (h₁ : act 1 = OrderIso.refl P)
  (hmul : ∀ g h, act (g * h) = (act h).trans (act g))

def orderActionMulAction : MulAction G P where
  smul g p := act g p
  one_smul p := by change act 1 p = p; rw [h₁]; rfl
  mul_smul g h p := by change act (g * h) p = act g (act h p); rw [hmul]; rfl

theorem exists_equivariant_coherent_stalk_family (hs : IsSimplicialPoset P)
    (hlift :
      letI := orderActionMulAction act h₁ hmul
      letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
      ∀ n (old : EquivariantRankStage faceRank
          (fun g p => faceRank_eq_of_orderIso (act g) p)
          (StalkLocalGood K) (StalkLocalCompatible K) n)
        (p : P), faceRank p = n → ∃ y : StalkLinearFamily (P := P) K,
          StalkLocalGood K p y ∧
          (∀ q : rankCut faceRank n, q.val < p →
            StalkLocalCompatible K p q.val y (old.value q)) ∧
          ∀ g : G, act g p = p → stalkFamilyRelabel K (act g) y = y) :
    ∃ F : StalkLinearFamily (P := P) K,
      F ∈ coherentStalkFamilySubmodule K ∧
      F ∈ parameterStalkFamilySubmodule K ∧
      F ∈ gradedStalkFamilySubmodule K ∧
      (∀ p, F p 1 = 1) ∧ ∀ g : G, stalkFamilyRelabel K (act g) F = F := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  obtain ⟨f, hfg, hfc, hfe⟩ := exists_equivariant_rank_family faceRank
    (faceRank_strictMono hs) (fun g p => faceRank_eq_of_orderIso (act g) p)
    (fun g _ _ h => (act g).strictMono h)
    (StalkLocalGood K) (StalkLocalCompatible K)
    (fun g p y hy => stalkFamilyRelabel_good K (act g) p y hy)
    (fun g p q y z hy => stalkFamilyRelabel_compatible K (act g) p q y z hy)
    hlift
  let F : StalkLinearFamily (P := P) K := fun p => f p p
  refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q h x
    by_cases he : q = p
    · subst q
      simpa only [polynomialRestriction_refl, faceVertexInclusion_refl,
        booleanRestriction_refl, AlgHom.id_apply, AlgHom.toLinearMap_apply]
    · exact hfc p q (lt_of_le_of_ne h he) h x
  · intro p r x
    exact (hfg p).2.1 p r x
  · intro p n x hx
    exact (hfg p).2.2.1 p n x hx
  · intro p
    exact (hfg p).2.2.2
  · intro g
    funext p
    apply LinearMap.ext
    intro x
    have hh := congrArg (fun z : StalkLinearFamily (P := P) K => z p x)
      (hfe g ((act g).symm p))
    change f (act g ((act g).symm p)) p x =
      stalkFamilyRelabel K (act g) (f ((act g).symm p)) p x at hh
    rw [(act g).apply_symm_apply] at hh
    exact hh.symm

end ActualAction
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicSimplexGeometry.lean -/
section


section

/-! # The actual Boolean simplex and its prime-cycle action

Faces are literal finite subsets.  Their atoms are literal singleton subsets,
and the resulting simplicial-poset stalk vertices are identified with the
vertices of the subset.  Nonempty proper faces have trivial stabilizer under
a prime cycle.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset

variable (p : ℕ) [Fact p.Prime]

def cyclicSimplexOrderAction (g : PrimeCycleGroup p) : Finset (ZMod p) ≃o Finset (ZMod p) :=
  finsetOrderCongr (cyclicVertexPermutation p g)

theorem cyclicSimplexOrderAction_one : cyclicSimplexOrderAction p 1 = OrderIso.refl _ := by
  rw [cyclicSimplexOrderAction, (cyclicVertexPermutation p).map_one]
  exact simplexOrderAction_one

theorem cyclicSimplexOrderAction_mul (g h : PrimeCycleGroup p) :
    cyclicSimplexOrderAction p (g * h) =
      (cyclicSimplexOrderAction p h).trans (cyclicSimplexOrderAction p g) := by
  rw [cyclicSimplexOrderAction, (cyclicVertexPermutation p).map_mul]
  exact simplexOrderAction_mul _ _

theorem cyclicSimplex_proper_face_free (s : Finset (ZMod p)) (hs : s.Nonempty)
    (ht : s ≠ Finset.univ) (g : PrimeCycleGroup p)
    (hfix : cyclicSimplexOrderAction p g s = s) : g = 1 := by
  by_contra hg
  have hg0 : g.toAdd ≠ 0 := by intro h; exact hg (congrArg Multiplicative.ofAdd h)
  have hmem : ∀ x : ZMod p, (g.toAdd + x ∈ s) = (x ∈ s) := by
    intro x
    have hh : s.map (Equiv.addLeft g.toAdd).toEmbedding = s := hfix
    have hm := congrArg (fun t : Finset (ZMod p) => (Equiv.addLeft g.toAdd) x ∈ t) hh
    simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply] at hm
    exact hm.symm
  have hc := primeShift_invariant_constant p (fun x => x ∈ s) g.toAdd hg0 hmem
  obtain ⟨a, ha⟩ := hs
  apply ht
  apply Finset.eq_univ_iff_forall.mpr
  intro b
  rw [hc b, ← hc a]
  exact ha

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicFixedStalk.lean -/
section


section

/-! # Fixed-face actions and the literal prime-cycle action at the top stalk

Equality transports of face indices are made explicit and proved to act by
the corresponding vertex bijection.  This connects the action on whole
families with the polynomial and Boolean permutation actions in the local
prime lift.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal

open Classical Finset MvPolynomial

/-- An additive map is linear for the specified integer-module structures.
The explicit conversion prevents a diamond between quotient and canonical
integer actions at an integral stalk. -/
def integralLinearMapOfAddHom {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (f : M →+ N) : M →ₗ[ℤ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    convert f.map_zsmul c x using 1
    · exact congrArg f (int_smul_eq_zsmul _ c x)
    · exact int_smul_eq_zsmul _ c (f x)


variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

def faceVertexCast {p q : P} (h : p = q) : FaceVertex p ≃ FaceVertex q :=
  Equiv.cast (congrArg FaceVertex h)

@[simp] theorem faceVertexCast_val {p q : P} (h : p = q) (a : FaceVertex p) :
    (faceVertexCast h a).val = a.val := by cases h; rfl

def polynomialStalkCast {p q : P} (h : p = q) : PolynomialStalk K p ≃ₐ[K] PolynomialStalk K q :=
  MvPolynomial.renameEquiv K (faceVertexCast h)

def barycentricStalkCast {p q : P} (h : p = q) : BarycentricStalk K p ≃ₐ[K] BarycentricStalk K q :=
  booleanVertexRelabelEquiv (faceVertexCast h)

@[simp] theorem polynomialStalkCast_refl (p : P) (x : PolynomialStalk K p) :
    polynomialStalkCast K (rfl : p = p) x = x := by
  change MvPolynomial.rename (id : FaceVertex p → FaceVertex p) x = x
  exact MvPolynomial.rename_id_apply x

@[simp] theorem barycentricStalkCast_refl (p : P) (x : BarycentricStalk K p) :
    barycentricStalkCast K (rfl : p = p) x = x :=
  booleanVertexRelabelEquiv_refl x

theorem stalkFamily_cast (F : StalkLinearFamily (P := P) K) {p q : P} (h : p = q)
    (x : BarycentricStalk K p) :
    polynomialStalkCast K h (F p x) = F q (barycentricStalkCast K h x) := by
  cases h
  rw [polynomialStalkCast_refl, barycentricStalkCast_refl]

def fixedFaceVertexPermutation (e : P ≃o P) (p : P) (h : e p = p) : Equiv.Perm (FaceVertex p) :=
  (faceVertexOrderEquiv e p).trans (faceVertexCast h)

@[simp] theorem fixedFaceVertexPermutation_val (e : P ≃o P) (p : P) (h : e p = p)
    (a : FaceVertex p) : (fixedFaceVertexPermutation e p h a).val = e a.val := by
  rw [fixedFaceVertexPermutation, Equiv.trans_apply, faceVertexCast_val]
  rfl

theorem fixedFaceVertexPermutation_polynomial (e : P ≃o P) (p : P) (h : e p = p)
    (x : PolynomialStalk K p) :
    MvPolynomial.rename (fixedFaceVertexPermutation e p h) x =
      polynomialStalkCast K h (polynomialStalkOrderEquiv K e p x) := by
  change MvPolynomial.rename ((faceVertexOrderEquiv e p).trans (faceVertexCast h)) x =
    MvPolynomial.rename (faceVertexCast h) (MvPolynomial.rename (faceVertexOrderEquiv e p) x)
  rw [MvPolynomial.rename_rename]
  rfl

theorem fixedFaceVertexPermutation_barycentric (e : P ≃o P) (p : P) (h : e p = p)
    (x : BarycentricStalk K p) :
    booleanVertexRelabelEquiv (fixedFaceVertexPermutation e p h) x =
      barycentricStalkCast K h (barycentricStalkOrderEquiv K e p x) :=
  booleanVertexRelabelEquiv_trans (faceVertexOrderEquiv e p) (faceVertexCast h) x

theorem stalkFamilyRelabel_fixed_conjugate (e : P ≃o P) (p : P) (h : e.symm p = p)
    (F : StalkLinearFamily (P := P) K) (x : BarycentricStalk K p) :
    MvPolynomial.rename (fixedFaceVertexPermutation e.symm p h)
      (stalkFamilyRelabel K e F p x) =
        F p (booleanVertexRelabelEquiv (fixedFaceVertexPermutation e.symm p h) x) := by
  rw [fixedFaceVertexPermutation_polynomial, stalkFamilyRelabel_apply,
    AlgEquiv.apply_symm_apply, stalkFamily_cast,
    ← fixedFaceVertexPermutation_barycentric]

theorem stalkFamilyRelabel_fixed_at (e : P ≃o P) (p : P) (h : e.symm p = p)
    (F : StalkLinearFamily (P := P) K)
    (hF : ∀ x, F p (booleanVertexRelabelEquiv (fixedFaceVertexPermutation e.symm p h) x) =
      MvPolynomial.rename (fixedFaceVertexPermutation e.symm p h) (F p x)) :
    ∀ x, stalkFamilyRelabel K e F p x = F p x := by
  intro x
  apply (MvPolynomial.renameEquiv K (fixedFaceVertexPermutation e.symm p h)).injective
  change MvPolynomial.rename (fixedFaceVertexPermutation e.symm p h)
      (stalkFamilyRelabel K e F p x) =
    MvPolynomial.rename (fixedFaceVertexPermutation e.symm p h) (F p x)
  rw [stalkFamilyRelabel_fixed_conjugate, hF]

theorem stalkFamilyRelabel_fixed_single (e : P ≃o P) (p : P) (h : e.symm p = p)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p)
    (hf : ∀ x, f (booleanVertexRelabelEquiv (fixedFaceVertexPermutation e.symm p h) x) =
      MvPolynomial.rename (fixedFaceVertexPermutation e.symm p h) (f x)) :
    stalkFamilyRelabel K e (stalkFamilySingle K p f) = stalkFamilySingle K p f := by
  funext q
  apply LinearMap.ext
  intro x
  by_cases hq : q = p
  · subst q
    apply stalkFamilyRelabel_fixed_at K e p h
    intro y
    simpa only [stalkFamilySingle_same] using hf y
  · have hq' : e.symm q ≠ p := by
      intro he
      exact hq (e.symm.injective (he.trans h.symm))
    rw [stalkFamilyRelabel_apply, stalkFamilySingle_ne K p q hq,
      stalkFamilySingle_ne K p (e.symm q) hq']
    simp

section Simplex
variable {V : Type*} [Fintype V]

@[simp] theorem simplexTopVertexEquiv_symm_val (v : V) :
    ((simplexTopVertexEquiv (V := V)).symm v).val = {v} := rfl

theorem simplexTopVertexEquiv_val (a : FaceVertex (Finset.univ : Finset V)) :
    a.val = {simplexTopVertexEquiv a} := by
  have hh := congrArg Subtype.val ((simplexTopVertexEquiv (V := V)).symm_apply_apply a)
  exact hh.symm

theorem simplex_fixed_top_permutation (e : Equiv.Perm V)
    (h : finsetOrderCongr e (Finset.univ : Finset V) = Finset.univ) :
    fixedFaceVertexPermutation (finsetOrderCongr e) Finset.univ h =
      (simplexTopVertexEquiv (V := V)).symm.permCongr e := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  rw [fixedFaceVertexPermutation_val, simplexTopVertexEquiv_val a,
    finsetOrderCongr_apply, Finset.map_singleton]
  change {e (simplexTopVertexEquiv a)} =
    ((simplexTopVertexEquiv (V := V)).symm (e (simplexTopVertexEquiv a))).val
  rw [simplexTopVertexEquiv_symm_val]

theorem simplex_top_single_fixed (e : Equiv.Perm V)
    (f : BarycentricStalk K (Finset.univ : Finset V) →ₗ[K]
      PolynomialStalk K (Finset.univ : Finset V))
    (hf : ∀ x, f (booleanVertexRelabelEquiv
      ((simplexTopVertexEquiv (V := V)).symm.permCongr e.symm) x) =
        MvPolynomial.rename ((simplexTopVertexEquiv (V := V)).symm.permCongr e.symm) (f x)) :
    stalkFamilyRelabel K (finsetOrderCongr e) (stalkFamilySingle K Finset.univ f) =
      stalkFamilySingle K Finset.univ f := by
  have hsymm : (finsetOrderCongr e).symm = finsetOrderCongr e.symm := rfl
  apply stalkFamilyRelabel_fixed_single K (finsetOrderCongr e) Finset.univ
    (by rw [hsymm, finsetOrderCongr_univ]) f
  intro x
  change f (booleanVertexRelabelEquiv
      (fixedFaceVertexPermutation (finsetOrderCongr e.symm) Finset.univ (finsetOrderCongr_univ e.symm)) x) =
    MvPolynomial.rename
      (fixedFaceVertexPermutation (finsetOrderCongr e.symm) Finset.univ (finsetOrderCongr_univ e.symm)) (f x)
  rw [simplex_fixed_top_permutation]
  exact hf x

end Simplex
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimePowerStabilizers.lean -/
section


section

/-! # Actual face stabilizers in prime-orbit coordinates

The stabilizer acts on the original simplex atoms. Faces which are not
unions of prime orbits have trivial stabilizer. For a union of prime orbits,
the induced local action is again a centralizing prime-orbit action, with
the literal action on the orbit-label face.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset

section General
variable {V G : Type*} [Fintype V] [Group G]
variable (ρ : G →* Equiv.Perm V)

/-- The subgroup fixes an actual face of the vertex simplex. -/
def simplexPermutationStabilizer (F : Finset V) : Subgroup G where
  carrier := {g | finsetOrderCongr (ρ g) F = F}
  one_mem' := by
    change finsetOrderCongr (ρ 1) F = F
    rw [ρ.map_one, simplexOrderAction_one]
    rfl
  mul_mem' := by
    intro g h hg hh
    change finsetOrderCongr (ρ (g*h)) F = F
    rw [ρ.map_mul, simplexOrderAction_mul]
    change finsetOrderCongr (ρ g) (finsetOrderCongr (ρ h) F) = F
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    apply (finsetOrderCongr (ρ g)).injective
    change finsetOrderCongr (ρ g) (finsetOrderCongr (ρ g⁻¹) F) = finsetOrderCongr (ρ g) F
    rw [← OrderIso.trans_apply, ← simplexOrderAction_mul, ← ρ.map_mul,
      mul_inv_cancel, ρ.map_one, simplexOrderAction_one]
    exact hg.symm

/-- The actual permutation of atoms under a face stabilizer. -/
def simplexStabilizerVertexPermutation (F : Finset V) :
    simplexPermutationStabilizer ρ F →* Equiv.Perm (FaceVertex F) where
  toFun g := fixedFaceVertexPermutation (finsetOrderCongr (ρ g.val)) F g.property
  map_one' := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    rw [fixedFaceVertexPermutation_val, Subgroup.coe_one, ρ.map_one, simplexOrderAction_one]
    rfl
  map_mul' g h := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    change (fixedFaceVertexPermutation (finsetOrderCongr (ρ (g*h).val)) F (g*h).property a).val =
      (fixedFaceVertexPermutation (finsetOrderCongr (ρ g.val)) F g.property
        (fixedFaceVertexPermutation (finsetOrderCongr (ρ h.val)) F h.property a)).val
    rw [fixedFaceVertexPermutation_val, fixedFaceVertexPermutation_val,
      fixedFaceVertexPermutation_val, Subgroup.coe_mul, ρ.map_mul, simplexOrderAction_mul]
    rfl

@[simp] theorem simplexStabilizerVertexPermutation_val (F : Finset V)
    (g : simplexPermutationStabilizer ρ F) (a : FaceVertex F) :
    (simplexStabilizerVertexPermutation ρ F g a).val = finsetOrderCongr (ρ g.val) a.val :=
  fixedFaceVertexPermutation_val _ _ _ _

theorem simplexVertexEquiv_atom (F : Finset V) (a : FaceVertex F) :
    a.val = {(simplexVertexEquiv F a).val} := by
  have h := congrArg Subtype.val ((simplexVertexEquiv F).symm_apply_apply a)
  exact h.symm

theorem simplexStabilizerVertexPermutation_element (F : Finset V)
    (g : simplexPermutationStabilizer ρ F) (a : FaceVertex F) :
    (simplexVertexEquiv F (simplexStabilizerVertexPermutation ρ F g a)).val =
      ρ g.val (simplexVertexEquiv F a).val := by
  apply Finset.singleton_injective
  rw [← simplexVertexEquiv_atom, simplexStabilizerVertexPermutation_val,
    simplexVertexEquiv_atom F a, finsetOrderCongr_apply, Finset.map_singleton]
  rfl

end General

variable (p : ℕ) [Fact p.Prime]
variable {W G : Type*} [Fintype W] [Group G]
variable (ρ : G →* Equiv.Perm (ZMod p × W))
variable (hρ : ∀ g, CommutesPrimeTranslations p (ρ g))
local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _

section Nonstable
variable [Finite G] [IsCyclic G]
variable (hG : IsPGroup p G) (Z : Subgroup G) (hZ : Nat.card Z = p)
variable (htranslations : ∀ t : ZMod p, ∃ z : Z,
  ρ z.val = primeOrbitRelabel p (Equiv.refl W) (fun _ => t))

include hG hZ htranslations in
theorem nonstableFace_stabilizer_trivial (F : Finset (ZMod p × W))
    (hF : ¬ PrimeTranslationStable p F) (g : simplexPermutationStabilizer ρ F) : g = 1 := by
  apply Subtype.ext
  by_contra hg
  let act := fun g : G => finsetOrderCongr (ρ g)
  have hact1 : act 1 = OrderIso.refl _ := by
    change finsetOrderCongr (ρ 1) = _
    rw [ρ.map_one]
    exact simplexOrderAction_one
  have hactmul (g h : G) : act (g*h) = (act h).trans (act g) := by
    change finsetOrderCongr (ρ (g*h)) = _
    rw [ρ.map_mul]
    exact simplexOrderAction_mul _ _
  letI : MulAction G (Finset (ZMod p × W)) := ScalarFamilies.orderAction act hact1 hactmul
  have hzfix := primeSubgroup_fixed_of_nonidentity_fixed hG Z hZ hg g.property
  apply hF
  intro t
  obtain ⟨z, hz⟩ := htranslations t
  have hh := hzfix z
  change finsetOrderCongr (ρ z.val) F = F at hh
  rw [hz, finsetOrderCongr_apply, Finset.map_eq_image] at hh
  exact hh

end Nonstable

section Stable
variable (S : Finset W)

/-- The induced action on the literal atom coordinates of a stable face. -/
def primeOrbitFaceLocalPermutation : simplexPermutationStabilizer ρ (primeOrbitFace p S) →*
    Equiv.Perm (ZMod p × FaceVertex S) :=
  (primeOrbitFaceVertexEquiv p S).permCongrHom.toMonoidHom.comp
    (simplexStabilizerVertexPermutation ρ (primeOrbitFace p S))

@[simp] theorem primeOrbitFaceLocalPermutation_apply
    (g : simplexPermutationStabilizer ρ (primeOrbitFace p S))
    (v : ZMod p × FaceVertex S) :
    primeOrbitFaceLocalPermutation p ρ S g v =
      primeOrbitFaceVertexEquiv p S (simplexStabilizerVertexPermutation ρ (primeOrbitFace p S) g
        ((primeOrbitFaceVertexEquiv p S).symm v)) := rfl

theorem primeOrbitFace_parent_fixed (g : simplexPermutationStabilizer ρ (primeOrbitFace p S)) :
    finsetOrderCongr (primeOrbitParentAction p ρ hρ g.val) S = S := by
  have hg := g.property
  change finsetOrderCongr (ρ g.val) (primeOrbitFace p S) = primeOrbitFace p S at hg
  rw [primeOrbitParentAction_normalForm p ρ hρ g.val, primeOrbitFace_relabel] at hg
  have hs := congrArg (primeStableFaceLabels p) hg
  simpa only [primeStableFaceLabels_orbitFace] using hs

def primeOrbitFaceParentPermutation : simplexPermutationStabilizer ρ (primeOrbitFace p S) →*
    Equiv.Perm (FaceVertex S) :=
  (simplexStabilizerVertexPermutation (primeOrbitParentAction p ρ hρ) S).comp {
    toFun g := ⟨g.val, primeOrbitFace_parent_fixed p ρ hρ S g⟩
    map_one' := Subtype.ext rfl
    map_mul' _ _ := Subtype.ext rfl }

theorem primeOrbitFaceLocalPermutation_normalForm
    (g : simplexPermutationStabilizer ρ (primeOrbitFace p S)) :
    primeOrbitFaceLocalPermutation p ρ S g =
      primeOrbitRelabel p (primeOrbitFaceParentPermutation p ρ hρ S g)
        (fun a => (ρ g.val (0, (simplexVertexEquiv S a).val)).1) := by
  apply Equiv.ext
  rintro ⟨x,a⟩
  apply (primeOrbitFaceVertexEquiv p S).symm.injective
  rw [primeOrbitFaceLocalPermutation_apply, Equiv.symm_apply_apply]
  apply Subtype.ext
  change (simplexStabilizerVertexPermutation ρ (primeOrbitFace p S) g
      ((primeOrbitFaceVertexEquiv p S).symm (x,a))).val = _
  rw [simplexStabilizerVertexPermutation_val, primeOrbitFaceVertexEquiv_symm_val,
    finsetOrderCongr_apply, Finset.map_singleton, primeOrbitFaceVertexEquiv_symm_val]
  apply congrArg (fun v : ZMod p × W => ({v} : Finset (ZMod p × W)))
  rw [primeOrbitParentAction_normalForm p ρ hρ g.val]
  apply Prod.ext
  · change (ρ g.val (0, (simplexVertexEquiv S a).val)).1 + x =
      ((ρ g.val (0, (simplexVertexEquiv S a).val)).1 + 0) + x
    rw [add_zero]
  · change primeOrbitParentAction p ρ hρ g.val (simplexVertexEquiv S a).val =
      (simplexVertexEquiv S (primeOrbitFaceParentPermutation p ρ hρ S g a)).val
    exact (simplexStabilizerVertexPermutation_element (primeOrbitParentAction p ρ hρ) S
      ⟨g.val, primeOrbitFace_parent_fixed p ρ hρ S g⟩ a).symm

include hρ in
theorem primeOrbitFaceLocalPermutation_commutes
    (g : simplexPermutationStabilizer ρ (primeOrbitFace p S)) :
    CommutesPrimeTranslations p (primeOrbitFaceLocalPermutation p ρ S g) := by
  rw [primeOrbitFaceLocalPermutation_normalForm p ρ hρ S g]
  exact primeOrbitRelabel_translation p _ _

theorem primeOrbitFaceLocalPermutation_parent
    (g : simplexPermutationStabilizer ρ (primeOrbitFace p S)) :
    primeOrbitParentAction p (primeOrbitFaceLocalPermutation p ρ S)
      (primeOrbitFaceLocalPermutation_commutes p ρ hρ S) g =
        primeOrbitFaceParentPermutation p ρ hρ S g := by
  apply Equiv.ext
  intro a
  rw [primeOrbitParentAction_apply, primeOrbitFaceLocalPermutation_normalForm]
  rfl

/-- The minimal prime subgroup remains an actual subgroup of the stabilizer. -/
theorem primeSubgroup_le_orbitFace_stabilizer (Z : Subgroup G)
    (hZtranslation : ∀ z : Z, ∃ t : ZMod p,
      ρ z.val = primeOrbitRelabel p (Equiv.refl W) (fun _ => t)) :
    Z ≤ simplexPermutationStabilizer ρ (primeOrbitFace p S) := by
  intro z hz
  obtain ⟨t, ht⟩ := hZtranslation ⟨z,hz⟩
  change finsetOrderCongr (ρ z) (primeOrbitFace p S) = primeOrbitFace p S
  rw [ht, finsetOrderCongr_apply, Finset.map_eq_image]
  exact primeOrbitFace_stable p S t

/-- Realization of every prime translation in the local stabilizer action. -/
theorem primeOrbitFaceLocalPermutation_hasTranslations (Z : Subgroup G)
    (hZle : Z ≤ simplexPermutationStabilizer ρ (primeOrbitFace p S))
    (htranslations : ∀ t : ZMod p, ∃ z : Z,
      ρ z.val = primeOrbitRelabel p (Equiv.refl W) (fun _ => t)) :
    ∀ t : ZMod p, ∃ z : Z.subgroupOf (simplexPermutationStabilizer ρ (primeOrbitFace p S)),
      primeOrbitFaceLocalPermutation p ρ S z.val =
        primeOrbitRelabel p (Equiv.refl (FaceVertex S)) (fun _ => t) := by
  intro t
  obtain ⟨z, hz⟩ := htranslations t
  refine ⟨⟨⟨z.val, hZle z.property⟩, z.property⟩, ?_⟩
  apply Equiv.ext
  rintro ⟨x,a⟩
  apply (primeOrbitFaceVertexEquiv p S).symm.injective
  rw [primeOrbitFaceLocalPermutation_apply, Equiv.symm_apply_apply]
  apply Subtype.ext
  change (simplexStabilizerVertexPermutation ρ (primeOrbitFace p S)
      ⟨z.val, hZle z.property⟩ ((primeOrbitFaceVertexEquiv p S).symm (x,a))).val = _
  rw [simplexStabilizerVertexPermutation_val, hz, primeOrbitFaceVertexEquiv_symm_val,
    finsetOrderCongr_apply, Finset.map_singleton, primeOrbitFaceVertexEquiv_symm_val]
  rfl

end Stable
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ScalarVertexTransport.lean -/
section

section
/-! # Transport of actual scalar families along vertex embeddings

A coherent family on a finite simplex restricts along any vertex embedding.
No symmetry hypothesis is needed for this construction.  A commuting pair
of vertex permutations transports the corresponding invariance, and a vertex
equivalence therefore transports every normalized equivariant comparison.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal.ScalarFamilies
open Classical Finset MvPolynomial

section SimplexGeometry
variable {U : Type*} [Fintype U]

/-- The actual atom of a finite face, regarded as its unique vertex. -/
def simplexFaceEmbedding (S : Finset U) : FaceVertex S ↪ U :=
  (simplexVertexEquiv S).toEmbedding.trans (Function.Embedding.subtype (fun u => u ∈ S))

theorem simplexFaceEmbedding_singleton (S : Finset U) (a : FaceVertex S) :
    a.val = {simplexFaceEmbedding S a} :=
  (congrArg Subtype.val ((simplexVertexEquiv S).symm_apply_apply a)).symm

theorem simplexFaceEmbedding_inclusion {S T : Finset U} (h : S ⊆ T) :
    (faceVertexInclusion h).trans (simplexFaceEmbedding T) = simplexFaceEmbedding S := by
  apply Function.Embedding.ext
  intro a
  apply Finset.singleton_injective
  change {simplexFaceEmbedding T (faceVertexInclusion h a)} = {simplexFaceEmbedding S a}
  rw [← simplexFaceEmbedding_singleton T (faceVertexInclusion h a),
    ← simplexFaceEmbedding_singleton S a]
  rfl

theorem simplexFaceEmbedding_order (σ : Equiv.Perm U) (S : Finset U) :
    (faceVertexOrderEquiv (finsetOrderCongr σ) S).toEmbedding.trans
        (simplexFaceEmbedding (finsetOrderCongr σ S)) =
      (simplexFaceEmbedding S).trans σ.toEmbedding := by
  apply Function.Embedding.ext
  intro a
  apply Finset.singleton_injective
  change ({(simplexFaceEmbedding (finsetOrderCongr σ S)
      (faceVertexOrderEquiv (finsetOrderCongr σ) S a))} : Finset U) =
    ({(σ (simplexFaceEmbedding S a))} : Finset U)
  rw [← simplexFaceEmbedding_singleton, faceVertexOrderEquiv_apply,
    finsetOrderCongr_apply, simplexFaceEmbedding_singleton S a, Finset.map_singleton]
  rfl

end SimplexGeometry

section TransportMaps
variable {A B V K : Type*} [Fintype A] [Fintype B] [Fintype V] [CommRing K]

theorem reverseVertexTransport_bijective
    (f : MvPolynomial B K →ₗ[K] BooleanBarycentricRing B K) (e : A ≃ B)
    (hf : Function.Bijective f) : Function.Bijective (reverseVertexTransport f e) := by
  change Function.Bijective (fun x => booleanVertexRelabelEquiv e.symm (f (rename e x)))
  exact (booleanVertexRelabelEquiv e.symm).bijective.comp
    (hf.comp (MvPolynomial.renameEquiv K e).bijective)

theorem reverseVertexTransport_eq_natural
    (f : MvPolynomial B K →ₗ[K] BooleanBarycentricRing B K)
    (g : MvPolynomial A K →ₗ[K] BooleanBarycentricRing A K) (e : A ≃ B)
    (h : reverseVertexTransport f e = g) (x : MvPolynomial A K) :
    f (rename e x) = booleanVertexRelabelEquiv e (g x) := by
  have hh := congrArg (booleanVertexRelabelEquiv (K := K) e) (LinearMap.congr_fun h x)
  change booleanVertexRelabelEquiv e
    ((booleanVertexRelabelEquiv e).symm (f (rename e x))) = _ at hh
  rw [AlgEquiv.apply_symm_apply] at hh
  exact hh

/-- Invariance under one specified ambient permutation suffices. -/
theorem embeddedScalarMap_postcompose_fixed (F : comparisonModule (P := Finset V) K)
    (i : A ↪ V) (σ : Equiv.Perm V)
    (hF : relabelComparison K (finsetOrderCongr σ.symm) F = F) :
    embeddedScalarMap F (i.trans σ.toEmbedding) = embeddedScalarMap F i := by
  apply reverseVertexTransport_stalk_order F (finsetOrderCongr σ)
    (by simpa only [finsetOrderCongr_symm] using hF)
    (embeddingPlacementFace i) (embeddingPlacementFace (i.trans σ.toEmbedding))
    (embeddingPlacementVertex i) (embeddingPlacementVertex (i.trans σ.toEmbedding))
  · simp only [embeddingPlacementFace, finsetOrderCongr_apply, Finset.map_map]
  · intro a
    simp only [embeddingPlacementVertex_val, finsetOrderCongr_apply, Finset.map_singleton]
    rfl

/-- Coordinate change on the source vertex set is exact, without symmetry. -/
theorem embeddedScalarMap_precompose_equiv (F : comparisonModule (P := Finset V) K)
    (i : B ↪ V) (e : A ≃ B) :
    embeddedScalarMap F (e.toEmbedding.trans i) = reverseVertexTransport (embeddedScalarMap F i) e := by
  have hface : embeddingPlacementFace (e.toEmbedding.trans i) = embeddingPlacementFace i := by
    simp only [embeddingPlacementFace, ← Finset.map_map, Finset.map_univ_equiv]
  have hfixed : relabelComparison K (OrderIso.refl (Finset V)).symm F = F := by
    apply Subtype.ext
    exact relabel_refl K F.val
  calc
    _ = reverseVertexTransport (F.val (embeddingPlacementFace i))
        (e.trans (embeddingPlacementVertex i)) := by
      apply reverseVertexTransport_stalk_order F (OrderIso.refl (Finset V)) hfixed
        (embeddingPlacementFace i) (embeddingPlacementFace (e.toEmbedding.trans i))
        (e.trans (embeddingPlacementVertex i))
        (embeddingPlacementVertex (e.toEmbedding.trans i)) hface
      intro a
      simp only [embeddingPlacementVertex_val, Equiv.trans_apply]
      rfl
    _ = _ := (reverseVertexTransport_trans _ e (embeddingPlacementVertex i)).symm

end TransportMaps

section Families
variable {U V K : Type*} [Fintype U] [Fintype V] [CommRing K]

/-- Restriction of the actual comparison module along an arbitrary vertex
embedding; the source family need not be symmetric. -/
def vertexEmbeddingFamily (F : comparisonModule (P := Finset V) K) (i : U ↪ V) :
    comparisonModule (P := Finset U) K :=
  ⟨fun S => embeddedScalarMap F ((simplexFaceEmbedding S).trans i), by
    refine ⟨?_, ?_, ?_⟩
    · intro S T h x
      rw [polynomialRestriction_eq_killCompl]
      have he : (faceVertexInclusion h).trans ((simplexFaceEmbedding S).trans i) =
          (simplexFaceEmbedding T).trans i := by
        rw [← Function.Embedding.trans_assoc, simplexFaceEmbedding_inclusion]
      have hh := embeddedScalarMap_restriction F ((simplexFaceEmbedding S).trans i)
        (faceVertexInclusion h) x
      rw [he] at hh
      exact hh
    · intro S r x
      exact reverseVertexTransport_parameter _ _
        (fun r x => F.property.2.1 _ r x) r x
    · intro S n x hx
      exact reverseVertexTransport_graded _ _
        (fun n x hx => F.property.2.2 _ n x hx) n x hx⟩

@[simp] theorem vertexEmbeddingFamily_apply (F : comparisonModule (P := Finset V) K)
    (i : U ↪ V) (S : Finset U) :
    (vertexEmbeddingFamily F i).val S = embeddedScalarMap F ((simplexFaceEmbedding S).trans i) := rfl

theorem vertexEmbeddingFamily_scalar (F : comparisonModule (P := Finset V) K) (i : U ↪ V) :
    scalar K (vertexEmbeddingFamily F i) = scalar K F := by
  change constantCoefficient (embeddedScalarMap F ((simplexFaceEmbedding ⊥).trans i) 1) = _
  rw [embeddedScalarMap,
    reverseVertexTransport_scalar _ _ (scalar K F) (component_one K F _),
    constantCoefficient_smul_one]

theorem vertexEmbeddingFamily_bijective (F : comparisonModule (P := Finset V) K) (i : U ↪ V)
    (hF : ∀ S, Function.Bijective (F.val S)) (S : Finset U) :
    Function.Bijective ((vertexEmbeddingFamily F i).val S) :=
  reverseVertexTransport_bijective _ _ (hF _)

/-- Covariance for one commuting pair of actual vertex permutations. -/
theorem vertexEmbeddingFamily_natural (F : comparisonModule (P := Finset V) K) (i : U ↪ V)
    (σ : Equiv.Perm U) (τ : Equiv.Perm V)
    (hi : i.trans τ.toEmbedding = σ.toEmbedding.trans i)
    (hF : relabelComparison K (finsetOrderCongr τ.symm) F = F)
    (S : Finset U) (x : PolynomialStalk K S) :
    barycentricStalkOrderEquiv K (finsetOrderCongr σ) S ((vertexEmbeddingFamily F i).val S x) =
      (vertexEmbeddingFamily F i).val (finsetOrderCongr σ S)
        (polynomialStalkOrderEquiv K (finsetOrderCongr σ) S x) := by
  let a := faceVertexOrderEquiv (finsetOrderCongr σ) S
  let j := (simplexFaceEmbedding S).trans i
  let k := (simplexFaceEmbedding (finsetOrderCongr σ S)).trans i
  have hj : a.toEmbedding.trans k = j.trans τ.toEmbedding := by
    change (faceVertexOrderEquiv (finsetOrderCongr σ) S).toEmbedding.trans
      ((simplexFaceEmbedding (finsetOrderCongr σ S)).trans i) =
      ((simplexFaceEmbedding S).trans i).trans τ.toEmbedding
    rw [← Function.Embedding.trans_assoc, simplexFaceEmbedding_order,
      Function.Embedding.trans_assoc, ← hi, ← Function.Embedding.trans_assoc]
  have hh : reverseVertexTransport (embeddedScalarMap F k) a = embeddedScalarMap F j := by
    rw [← embeddedScalarMap_precompose_equiv, hj]
    exact embeddedScalarMap_postcompose_fixed F j τ hF
  exact (reverseVertexTransport_eq_natural _ _ a hh x).symm

theorem vertexEmbeddingFamily_fixed (F : comparisonModule (P := Finset V) K) (i : U ↪ V)
    (σ : Equiv.Perm U) (τ : Equiv.Perm V)
    (hi : i.trans τ.toEmbedding = σ.toEmbedding.trans i)
    (hF : relabelComparison K (finsetOrderCongr τ) F = F) :
    relabelComparison K (finsetOrderCongr σ) (vertexEmbeddingFamily F i) =
      vertexEmbeddingFamily F i := by
  have hinv : i.trans τ.symm.toEmbedding = σ.symm.toEmbedding.trans i := by
    apply Function.Embedding.ext
    intro u
    apply τ.injective
    have hh := congrArg (fun j : U ↪ V => j (σ.symm u)) hi
    change τ (i (σ.symm u)) = i (σ (σ.symm u)) at hh
    change τ (τ.symm (i u)) = τ (i (σ.symm u))
    simpa only [Equiv.apply_symm_apply] using hh.symm
  apply Subtype.ext
  funext S
  apply LinearMap.ext
  intro x
  change (barycentricStalkOrderEquiv K (finsetOrderCongr σ).symm S).symm
      ((vertexEmbeddingFamily F i).val ((finsetOrderCongr σ).symm S)
        (polynomialStalkOrderEquiv K (finsetOrderCongr σ).symm S x)) = _
  apply (barycentricStalkOrderEquiv K (finsetOrderCongr σ).symm S).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (vertexEmbeddingFamily_natural F i σ.symm τ.symm hinv
    (by simpa only [Equiv.symm_symm] using hF) S x).symm

/-- In particular, any vertex equivalence transports the actual family;
all its algebraic, grading and scalar conditions remain in the module type. -/
def vertexEquivFamily (F : comparisonModule (P := Finset V) K) (e : U ≃ V) :
    comparisonModule (P := Finset U) K := vertexEmbeddingFamily F e.toEmbedding

end Families
end FourPapers.Universal.ScalarFamilies

end
end
end

/- BEGIN FourPapers/Universal/CyclicScalarControl.lean -/
section

section
/-! # The actual fixed-face control condition in equivariant rank induction

Control means bijectivity and the precise fixed-face equation, with equality
of face indices handled by the genuine stalk casts.  This predicate is
preserved by the actual action on families whenever the smaller comparison
is invariant under the induced action on orbit labels.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

namespace ScalarFamilies
section Casts
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

/-- Equality of indices transports an actual reverse-direction family
component to exactly the component at the equal face. -/
theorem scalarFamily_cast (F : Family (P := P) K) {s t : P} (h : s = t)
    (x : PolynomialStalk K s) :
    barycentricStalkCast K h (F s x) = F t (polynomialStalkCast K h x) := by
  cases h
  rw [polynomialStalkCast_refl, barycentricStalkCast_refl]

/-- The actual family action at a fixed face is conjugation by the literal
fixed-face vertex permutation, in the paper's `R → B` direction. -/
theorem relabel_fixed_conjugate (e : P ≃o P) (s : P) (h : e.symm s = s)
    (F : Family (P := P) K) (x : PolynomialStalk K s) :
    booleanVertexRelabelEquiv (fixedFaceVertexPermutation e.symm s h)
      (relabel K e F s x) =
        F s (MvPolynomial.rename (fixedFaceVertexPermutation e.symm s h) x) := by
  rw [fixedFaceVertexPermutation_barycentric, relabel_apply,
    AlgEquiv.apply_symm_apply, scalarFamily_cast,
    ← fixedFaceVertexPermutation_polynomial]

theorem relabel_fixed_at (e : P ≃o P) (s : P) (h : e.symm s = s)
    (F : Family (P := P) K)
    (hF : ∀ x, F s (MvPolynomial.rename (fixedFaceVertexPermutation e.symm s h) x) =
      booleanVertexRelabelEquiv (fixedFaceVertexPermutation e.symm s h) (F s x)) :
    ∀ x, relabel K e F s x = F s x := by
  intro x
  apply (booleanVertexRelabelEquiv (K := K) (fixedFaceVertexPermutation e.symm s h)).injective
  rw [relabel_fixed_conjugate, hF]

/-- Equivariance of one actual stalk map gives a fixed single-face family. -/
theorem relabel_fixed_single (e : P ≃o P) (s : P) (h : e.symm s = s)
    (f : PolynomialStalk K s →ₗ[K] BarycentricStalk K s)
    (hf : ∀ x, f (MvPolynomial.rename (fixedFaceVertexPermutation e.symm s h) x) =
      booleanVertexRelabelEquiv (fixedFaceVertexPermutation e.symm s h) (f x)) :
    relabel K e (single K s f) = single K s f := by
  funext q
  apply LinearMap.ext
  intro x
  by_cases hq : q = s
  · subst q
    apply relabel_fixed_at K e s h
    intro y
    simpa only [single_same] using hf y
  · have hq' : e.symm q ≠ s := by
      intro he
      exact hq (e.symm.injective (he.trans h.symm))
    rw [relabel_apply, single_ne K s q hq f, single_ne K s (e.symm q) hq' f]
    simp

end Casts
end ScalarFamilies

variable (p : ℕ) [Fact p.Prime] {W : Type*} [Fintype W]
variable (K : Type*) [CommRing K]
local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _

/-- The exact local condition needed in the actual rank induction. -/
def PrimeOrbitLocalControl (ψ : ScalarFamilies.comparisonModule (P := Finset W) K)
    (F : Finset (ZMod p × W))
    (f : PolynomialStalk K F →ₗ[K] BarycentricStalk K F) : Prop :=
  Function.Bijective f ∧ ∀ (S : Finset W) (h : F = primeOrbitFace p S)
    (x : PolynomialStalk K F),
    primeOrbitStalkQuotient p K S (barycentricStalkCast K h (f x)) =
      ψ.val S (primeOrbitStalkMoment p K S (polynomialStalkCast K h x))

theorem primeOrbitLocalControl_at_orbitFace
    (ψ : ScalarFamilies.comparisonModule (P := Finset W) K) (S : Finset W)
    (f : PolynomialStalk K (primeOrbitFace p S) →ₗ[K] BarycentricStalk K (primeOrbitFace p S)) :
    PrimeOrbitLocalControl p K ψ (primeOrbitFace p S) f ↔
      Function.Bijective f ∧ ∀ x, primeOrbitStalkQuotient p K S (f x) =
        ψ.val S (primeOrbitStalkMoment p K S x) := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro x
    simpa only [polynomialStalkCast_refl, barycentricStalkCast_refl] using h.2 S rfl x
  · rintro ⟨hf, hπ⟩
    refine ⟨hf, ?_⟩
    intro T h x
    have hST : S = T := by
      have hh := congrArg (primeStableFaceLabels p) h
      simpa only [primeStableFaceLabels_orbitFace] using hh
    subst T
    simpa only [polynomialStalkCast_refl, barycentricStalkCast_refl] using hπ x

theorem primeOrbitLocalControl_of_not_stable
    (ψ : ScalarFamilies.comparisonModule (P := Finset W) K)
    (F : Finset (ZMod p × W)) (hF : ¬ PrimeTranslationStable p F)
    (f : PolynomialStalk K F →ₗ[K] BarycentricStalk K F) (hf : Function.Bijective f) :
    PrimeOrbitLocalControl p K ψ F f := by
  refine ⟨hf, ?_⟩
  intro S h x
  exact False.elim (hF (h.symm ▸ primeOrbitFace_stable p S))

/-- The normalized empty component automatically satisfies the control
condition; this is the base case of rank induction. -/
theorem primeOrbitLocalControl_empty
    (ψ : ScalarFamilies.comparisonModule (P := Finset W) K)
    (hψ : ψ.val ∅ 1 = 1)
    (f : PolynomialStalk K (∅ : Finset (ZMod p × W)) →ₗ[K]
      BarycentricStalk K (∅ : Finset (ZMod p × W)))
    (hf : Function.Bijective f) (hf₁ : f 1 = 1) :
    PrimeOrbitLocalControl p K ψ ∅ f := by
  refine ⟨hf, ?_⟩
  intro S h x
  have hS : S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hh := (mem_primeOrbitFace p S 0 w).mpr hw
    rw [← h] at hh
    exact Finset.notMem_empty (0, w) hh
  subst S
  letI : IsEmpty (FaceVertex (∅ : Finset (ZMod p × W))) :=
    ⟨fun v => v.property.1.ne_bot (le_bot_iff.mp v.property.2)⟩
  obtain ⟨c, rfl⟩ := MvPolynomial.C_surjective
    (FaceVertex (∅ : Finset (ZMod p × W))) x
  rw [show (MvPolynomial.C c : PolynomialStalk K (∅ : Finset (ZMod p × W))) = c • 1 by
    rw [MvPolynomial.smul_eq_C_mul, mul_one]]
  simp only [map_smul, hf₁, map_one, primeOrbitStalkMoment_one, hψ]

theorem primeOrbitLocalControl_component
    (ψ : ScalarFamilies.comparisonModule (P := Finset W) K)
    (H : ScalarFamilies.Family (P := Finset (ZMod p × W)) K)
    (F : Finset (ZMod p × W)) (hH : PrimeOrbitLocalControl p K ψ F (H F))
    (S : Finset W) (h : F = primeOrbitFace p S)
    (x : PolynomialStalk K (primeOrbitFace p S)) :
    primeOrbitStalkQuotient p K S (H (primeOrbitFace p S) x) =
      ψ.val S (primeOrbitStalkMoment p K S x) := by
  obtain ⟨y, rfl⟩ := (polynomialStalkCast K h).surjective x
  rw [← ScalarFamilies.scalarFamily_cast K H h y]
  exact hH.2 S h y

section Relabeling
variable (σ : Equiv.Perm W) (g : W → ZMod p)

theorem primeOrbitFaceStalkRelabel_polynomial (S : Finset W)
    (x : PolynomialStalk K (primeOrbitFace p S)) :
    MvPolynomial.rename (primeOrbitFaceStalkRelabel p σ g S) x =
      polynomialStalkCast K (primeOrbitFace_relabel p σ g S)
        (polynomialStalkOrderEquiv K (finsetOrderCongr (primeOrbitRelabel p σ g))
          (primeOrbitFace p S) x) := by
  change MvPolynomial.rename
      ((faceVertexOrderEquiv (finsetOrderCongr (primeOrbitRelabel p σ g))
        (primeOrbitFace p S)).trans (faceVertexCast (primeOrbitFace_relabel p σ g S))) x =
    MvPolynomial.rename (faceVertexCast (primeOrbitFace_relabel p σ g S))
      (MvPolynomial.rename
        (faceVertexOrderEquiv (finsetOrderCongr (primeOrbitRelabel p σ g))
          (primeOrbitFace p S)) x)
  rw [MvPolynomial.rename_rename]
  rfl

theorem primeOrbitFaceStalkRelabel_barycentric (S : Finset W)
    (x : BarycentricStalk K (primeOrbitFace p S)) :
    booleanVertexRelabelEquiv (primeOrbitFaceStalkRelabel p σ g S) x =
      barycentricStalkCast K (primeOrbitFace_relabel p σ g S)
        (barycentricStalkOrderEquiv K (finsetOrderCongr (primeOrbitRelabel p σ g))
          (primeOrbitFace p S) x) :=
  booleanVertexRelabelEquiv_trans
    (faceVertexOrderEquiv (finsetOrderCongr (primeOrbitRelabel p σ g)) (primeOrbitFace p S))
    (faceVertexCast (primeOrbitFace_relabel p σ g S)) x

/-- Conjugation on a canonical orbit face is the literal relabeled family
component, including the equality transport of the target face. -/
theorem scalarFamily_relabel_orbit_backward
    (H : ScalarFamilies.Family (P := Finset (ZMod p × W)) K)
    (S : Finset W) (x : PolynomialStalk K (primeOrbitFace p S)) :
    booleanVertexRelabelEquiv (primeOrbitFaceStalkRelabel p σ g S)
        (ScalarFamilies.relabel K (finsetOrderCongr (primeOrbitRelabel p σ g)).symm H
          (primeOrbitFace p S) x) =
      H (primeOrbitFace p (finsetOrderCongr σ S))
        (MvPolynomial.rename (primeOrbitFaceStalkRelabel p σ g S) x) := by
  have hb : barycentricStalkOrderEquiv K (finsetOrderCongr (primeOrbitRelabel p σ g))
        (primeOrbitFace p S)
        (ScalarFamilies.relabel K (finsetOrderCongr (primeOrbitRelabel p σ g)).symm H
          (primeOrbitFace p S) x) =
      H (finsetOrderCongr (primeOrbitRelabel p σ g) (primeOrbitFace p S))
        (polynomialStalkOrderEquiv K (finsetOrderCongr (primeOrbitRelabel p σ g))
          (primeOrbitFace p S) x) := by
    rw [ScalarFamilies.relabel_apply]
    simp only [OrderIso.symm_symm, AlgEquiv.apply_symm_apply]
  have hh := congrArg (barycentricStalkCast K (primeOrbitFace_relabel p σ g S)) hb
  rw [← primeOrbitFaceStalkRelabel_barycentric, ScalarFamilies.scalarFamily_cast,
    ← primeOrbitFaceStalkRelabel_polynomial] at hh
  exact hh

/-- Relabeling by the inverse centralizing permutation preserves control.
The inverse form matches the literal definition of the family action. -/
theorem primeOrbitLocalControl_relabel_symm
    (ψ : ScalarFamilies.comparisonModule (P := Finset W) K)
    (hψ : ScalarFamilies.relabelComparison K (finsetOrderCongr σ.symm) ψ = ψ)
    (H : ScalarFamilies.Family (P := Finset (ZMod p × W)) K)
    (F : Finset (ZMod p × W)) (hH : PrimeOrbitLocalControl p K ψ F (H F)) :
    PrimeOrbitLocalControl p K ψ
      ((finsetOrderCongr (primeOrbitRelabel p σ g)).symm F)
      (ScalarFamilies.relabel K (finsetOrderCongr (primeOrbitRelabel p σ g)).symm H
        ((finsetOrderCongr (primeOrbitRelabel p σ g)).symm F)) := by
  refine ⟨ScalarFamilies.relabel_component_bijective K
    (finsetOrderCongr (primeOrbitRelabel p σ g)).symm F H hH.1, ?_⟩
  intro S hS x
  have hF : F = primeOrbitFace p (finsetOrderCongr σ S) := by
    calc
      F = finsetOrderCongr (primeOrbitRelabel p σ g)
          ((finsetOrderCongr (primeOrbitRelabel p σ g)).symm F) :=
        ((finsetOrderCongr (primeOrbitRelabel p σ g)).apply_symm_apply F).symm
      _ = finsetOrderCongr (primeOrbitRelabel p σ g) (primeOrbitFace p S) :=
        congrArg (finsetOrderCongr (primeOrbitRelabel p σ g)) hS
      _ = _ := primeOrbitFace_relabel p σ g S
  rw [ScalarFamilies.scalarFamily_cast]
  apply (barycentricStalkOrderEquiv K (finsetOrderCongr σ) S).injective
  rw [← primeOrbitStalkQuotient_relabel,
    scalarFamily_relabel_orbit_backward,
    primeOrbitLocalControl_component p K ψ H F hH (finsetOrderCongr σ S) hF,
    primeOrbitStalkMoment_relabel]
  exact (ScalarFamilies.invariantFamily_natural ψ (finsetOrderCongr σ)
    (by simpa only [finsetOrderCongr_symm] using hψ) S _).symm

end Relabeling

theorem primeOrbitLocalControl_relabel_centralizer_symm
    (ψ : ScalarFamilies.comparisonModule (P := Finset W) K)
    (e : Equiv.Perm (ZMod p × W)) (he : CommutesPrimeTranslations p e)
    (hψ : ScalarFamilies.relabelComparison K
      (finsetOrderCongr (primeOrbitLabelEquiv p e he).symm) ψ = ψ)
    (H : ScalarFamilies.Family (P := Finset (ZMod p × W)) K)
    (F : Finset (ZMod p × W)) (hH : PrimeOrbitLocalControl p K ψ F (H F)) :
    PrimeOrbitLocalControl p K ψ ((finsetOrderCongr e).symm F)
      (ScalarFamilies.relabel K (finsetOrderCongr e).symm H ((finsetOrderCongr e).symm F)) := by
  have hh := primeOrbitLocalControl_relabel_symm p K
    (primeOrbitLabelEquiv p e he) (fun w => (e (0, w)).1) ψ hψ H F hH
  exact (congrArg (fun q : Equiv.Perm (ZMod p × W) =>
    PrimeOrbitLocalControl p K ψ ((finsetOrderCongr q).symm F)
      (ScalarFamilies.relabel K (finsetOrderCongr q).symm H
        ((finsetOrderCongr q).symm F)))
    (primeOrbitCentralizer_normalForm p e he)).mpr hh

/-- The exact relabel-stability premise for the group rank-induction theorem. -/
theorem primeOrbitLocalControl_relabel
    {G : Type*} [Group G] (ρ : G →* Equiv.Perm (ZMod p × W))
    (hρ : ∀ g, CommutesPrimeTranslations p (ρ g))
    (ψ : ScalarFamilies.comparisonModule (P := Finset W) K)
    (hψ : ∀ g, ScalarFamilies.relabelComparison K
      (finsetOrderCongr (primeOrbitParentAction p ρ hρ g)) ψ = ψ)
    (g : G) (H : ScalarFamilies.Family (P := Finset (ZMod p × W)) K)
    (F : Finset (ZMod p × W)) (hH : PrimeOrbitLocalControl p K ψ F (H F)) :
    PrimeOrbitLocalControl p K ψ (finsetOrderCongr (ρ g) F)
      (ScalarFamilies.relabel K (finsetOrderCongr (ρ g)) H (finsetOrderCongr (ρ g) F)) := by
  have hlabel : (primeOrbitLabelEquiv p (ρ g⁻¹) (hρ g⁻¹)).symm =
      primeOrbitParentAction p ρ hρ g := by
    change (primeOrbitParentAction p ρ hρ g⁻¹).symm = _
    rw [map_inv]
    rfl
  have he : (ρ g⁻¹).symm = ρ g := by
    rw [map_inv]
    rfl
  have ho : (finsetOrderCongr (ρ g⁻¹)).symm = finsetOrderCongr (ρ g) := by
    rw [← finsetOrderCongr_symm, he]
  have hh := primeOrbitLocalControl_relabel_centralizer_symm p K ψ (ρ g⁻¹) (hρ g⁻¹)
    (by rw [hlabel]; exact hψ g) H F hH
  exact (congrArg (fun q : Finset (ZMod p × W) ≃o Finset (ZMod p × W) =>
    PrimeOrbitLocalControl p K ψ (q F) (ScalarFamilies.relabel K q H (q F))) ho).mp hh

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicReverseVertexEquivalence.lean -/
section


section

/-! # Exact coordinate transport for reverse local equivalences

These are actual variable-renaming equivalences and their original grading
and parameter actions.  The inverse grading law is proved from homogeneous
basis projections, so choosing atom coordinates adds no hypothesis.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical MvPolynomial
open scoped CyclicParameterAction

section Parameter
variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

theorem reverseParameterLinear_allRanks
    (f : MvPolynomial V K →ₗ[K] BooleanBarycentricRing V K)
    (hf : IsParameterLinear polynomialColorMap booleanColorMap f) (r : ℕ)
    (x : MvPolynomial V K) :
    f (MvPolynomial.esymm V K (r+1) * x) = booleanRankParameter (r+1) * f x := by
  by_cases hr : r + 1 ≤ Fintype.card V
  · let c : Fin (Fintype.card V) := ⟨r, Nat.lt_of_succ_le hr⟩
    have hh := hf (MvPolynomial.X c) x
    simp only [polynomialColorMap, booleanColorMap, MvPolynomial.aeval_X] at hh
    rw [← booleanRankParameter_color] at hh
    exact hh
  · have hlt : Fintype.card V < r+1 := Nat.lt_of_not_ge hr
    rw [esymm_above_card _ hlt, booleanRankParameter_above _ hlt,
      zero_mul, map_zero, zero_mul]

theorem reverseAllRanks_parameterLinear
    (f : MvPolynomial V K →ₗ[K] BooleanBarycentricRing V K)
    (hf : ∀ r x, f (MvPolynomial.esymm V K (r+1) * x) = booleanRankParameter (r+1) * f x) :
    IsParameterLinear polynomialColorMap booleanColorMap f := by
  apply (isParameterLinear_iff_X _ _ f).mpr
  intro c x
  simp only [polynomialColorMap, booleanColorMap, MvPolynomial.aeval_X]
  rw [← booleanRankParameter_color]
  exact hf c.val x

def reverseParameterLinearEquiv
    (f : MvPolynomial V K ≃ₗ[K] BooleanBarycentricRing V K)
    (hf : IsParameterLinear polynomialColorMap booleanColorMap f.toLinearMap) :
    MvPolynomial V K ≃ₗ[MvPolynomial (Fin (Fintype.card V)) K] BooleanBarycentricRing V K :=
  { f.toAddEquiv with map_smul' := hf }

end Parameter

section Transport
variable {A B K : Type*} [Fintype A] [Fintype B] [CommRing K]

def reverseVertexEquiv (f : MvPolynomial B K ≃ₗ[K] BooleanBarycentricRing B K) (e : A ≃ B) :
    MvPolynomial A K ≃ₗ[K] BooleanBarycentricRing A K :=
  (MvPolynomial.renameEquiv K e).toLinearEquiv.trans
    (f.trans (booleanVertexRelabelEquiv e.symm).toLinearEquiv)

@[simp] theorem reverseVertexEquiv_apply
    (f : MvPolynomial B K ≃ₗ[K] BooleanBarycentricRing B K) (e : A ≃ B)
    (x : MvPolynomial A K) :
    reverseVertexEquiv f e x = ScalarFamilies.reverseVertexTransport f.toLinearMap e x := rfl

/-- Inverse grading follows from commuting with all actual basis projections. -/
theorem reverseVertexEquiv_inverse_graded
    (e : MvPolynomial A K ≃ₗ[K] BooleanBarycentricRing A K)
    (he : ∀ n x, x ∈ polynomialDegreePiece n → e x ∈
      basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) n)
    (n : ℕ) (y : BooleanBarycentricRing A K)
    (hy : y ∈ basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) n) :
    e.symm y ∈ polynomialDegreePiece n := by
  apply (basisDegreeProjection_eq_self_iff_mem (MvPolynomial.basisMonomials A K)
    (fun a => vertexDegree (fun v => a v)) n (e.symm y)).mp
  apply e.injective
  have hg : ∀ m x, x ∈ basisOrdinaryDegreePiece (MvPolynomial.basisMonomials A K)
      (fun a => vertexDegree (fun v => a v)) m → e x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => booleanOrdinaryDegree a.val) m := fun m x hx => he m x hx
  have hp := ordinaryProjection_natural (MvPolynomial.basisMonomials A K) booleanChainBasis
    (fun a => vertexDegree (fun v => a v)) (fun a => booleanOrdinaryDegree a.val)
    e.toLinearMap hg n (e.symm y)
  have hh : e (e.symm y) ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n := by
    rw [LinearEquiv.apply_symm_apply]
    exact hy
  simpa only [LinearEquiv.coe_coe] using hp.symm.trans
    ((basisDegreeProjection_eq_self_iff_mem _ _ _ _).mpr hh)

theorem reverseVertexEquiv_grade_iff
    (e : MvPolynomial A K ≃ₗ[K] BooleanBarycentricRing A K)
    (he : ∀ n x, x ∈ polynomialDegreePiece n → e x ∈
      basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) n)
    (n : ℕ) (x : BooleanBarycentricRing A K) :
    x ∈ basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) n ↔
      e.symm x ∈ polynomialDegreePiece n := by
  constructor
  · exact reverseVertexEquiv_inverse_graded e he n x
  · intro hx
    have hh := he n (e.symm x) hx
    simpa only [LinearEquiv.apply_symm_apply] using hh

@[simp] theorem booleanVertexRelabel_apply_symm (e : A ≃ B)
    (x : BooleanBarycentricRing B K) :
    booleanVertexRelabelEquiv e (booleanVertexRelabelEquiv e.symm x) = x :=
  (booleanVertexRelabelEquiv e).apply_symm_apply x

@[simp] theorem booleanVertexRelabel_symm_apply (e : A ≃ B)
    (x : BooleanBarycentricRing A K) :
    booleanVertexRelabelEquiv e.symm (booleanVertexRelabelEquiv e x) = x :=
  (booleanVertexRelabelEquiv e).symm_apply_apply x

/-- The literal top face is preserved by every vertex bijection. -/
theorem booleanVertexRelabelEquiv_top_general [Nonempty A] [Nonempty B]
    (e : A ≃ B) : booleanVertexRelabelEquiv (K := K) e booleanTop = booleanTop := by
  rw [← booleanRankParameter_top, booleanVertexRelabelEquiv_parameter,
    Fintype.card_congr e, booleanRankParameter_top]

/-- The actual boundary kernel is invariant under a bijection of vertices. -/
theorem booleanBoundary_vertexRelabel_eq_zero [Nonempty A] [Nonempty B]
    (e : A ≃ B) (x : BooleanBarycentricRing A K)
    (hx : booleanBoundaryMap x = 0) :
    booleanBoundaryMap (booleanVertexRelabelEquiv e x) = 0 := by
  obtain ⟨y, hy⟩ := (booleanBoundaryMap_eq_zero_iff x).mp hx
  apply (booleanBoundaryMap_eq_zero_iff _).mpr
  refine ⟨booleanVertexRelabelEquiv e y, ?_⟩
  rw [← hy, map_mul, booleanVertexRelabelEquiv_top_general]

/-- Equality of actual boundary values is preserved by vertex coordinates. -/
theorem booleanBoundary_vertexRelabel_congr [Nonempty A] [Nonempty B]
    (e : A ≃ B) (x y : BooleanBarycentricRing A K)
    (hxy : booleanBoundaryMap x = booleanBoundaryMap y) :
    booleanBoundaryMap (booleanVertexRelabelEquiv e x) =
      booleanBoundaryMap (booleanVertexRelabelEquiv e y) := by
  have hz : booleanBoundaryMap (x-y) = 0 := by rw [map_sub, hxy, sub_self]
  have hh := booleanBoundary_vertexRelabel_eq_zero e (x-y) hz
  rw [map_sub, map_sub] at hh
  exact sub_eq_zero.mp hh

/-- Literal naturality of conjugation by a vertex equivalence. -/
theorem reverseVertexEquiv_conjugate
    (f : MvPolynomial B K ≃ₗ[K] BooleanBarycentricRing B K)
    (e : A ≃ B) (x : MvPolynomial A K) :
    booleanVertexRelabelEquiv e (reverseVertexEquiv f e x) = f (MvPolynomial.rename e x) := by
  change booleanVertexRelabelEquiv e
    ((booleanVertexRelabelEquiv e).symm (f (MvPolynomial.rename e x))) = _
  exact (booleanVertexRelabelEquiv e).apply_symm_apply _

end Transport

section Empty
variable {V K N : Type*} [Fintype V] [CommRing K] [IsEmpty V]
  [AddCommGroup N] [Module K N]

theorem polynomial_empty_linear_ext_one (f g : MvPolynomial V K →ₗ[K] N) (h : f 1 = g 1) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨c,rfl⟩ := MvPolynomial.C_surjective V x
  have hc : MvPolynomial.C c = c • (1 : MvPolynomial V K) := by
    rw [Algebra.smul_def, mul_one]
    rfl
  rw [hc, map_smul, map_smul, h]

end Empty
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ScalarRankBoundaryEquivariance.lean -/
section

section
/-! # Equivariance of the actual boundary prescription at a fixed face -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical

/-- Relabeling carries equal actual boundary classes to equal boundary classes. -/
theorem booleanBoundaryRelabel_congr {V K : Type*} [Fintype V] [decV : DecidableEq V] [Nonempty V] [CommRing K]
    (e : Equiv.Perm V) (x y : BooleanBarycentricRing V K)
    (hxy : booleanBoundaryMap (V := V) (K := K) x = booleanBoundaryMap (V := V) (K := K) y) :
    booleanBoundaryMap (V := V) (K := K) (booleanVertexRelabelEquiv e x) =
      booleanBoundaryMap (V := V) (K := K) (booleanVertexRelabelEquiv e y) := by
  have hdec : decV = Classical.decEq V := Subsingleton.elim _ _
  subst decV
  have hz : booleanBoundaryMap (V := V) (K := K) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨z, htop⟩ := (booleanBoundaryMap_eq_zero_iff (V := V) (K := K) (x - y)).mp hz
  have hzero : booleanBoundaryMap (V := V) (K := K) (booleanVertexRelabelEquiv e (x - y)) = 0 := by
    apply (booleanBoundaryMap_eq_zero_iff (V := V) (K := K) _).mpr
    refine ⟨booleanVertexRelabelEquiv e z, ?_⟩
    rw [← htop, map_mul]
    have ht : booleanVertexRelabelEquiv (K := K) e (booleanTop (V := V)) = booleanTop := by
      change booleanVertexRelabelEquiv e (faceVariable booleanTopFace) = faceVariable booleanTopFace
      rw [booleanVertexRelabelEquiv_face]
      apply congrArg (faceVariable (K := K))
      apply Subtype.ext
      change (Finset.univ : Finset V).map e.toEmbedding = Finset.univ
      simp
    rw [ht]
  rw [map_sub, map_sub] at hzero
  exact sub_eq_zero.mp hzero

namespace ScalarFamilies
variable {P G : Type*} [PartialOrder P] [OrderBot P] [Fintype P] [Group G]
variable (K : Type*) [CommRing K]
variable (Control : ∀ p : P, (PolynomialStalk K p →ₗ[K] BarycentricStalk K p) → Prop)
variable (act : G → P ≃o P) (h₁ : act 1 = OrderIso.refl P)
  (hmul : ∀ g h, act (g * h) = (act h).trans (act g))

include h₁ hmul in
theorem orderAction_inv (g : G) : act g⁻¹ = (act g).symm := by
  apply OrderIso.ext
  funext q
  apply (act g).injective
  rw [(act g).apply_symm_apply]
  have h := congrArg (fun e : P ≃o P => e q) (hmul g g⁻¹)
  simpa only [mul_inv_cancel, h₁, OrderIso.refl_apply, OrderIso.trans_apply] using h.symm

variable (hs : IsSimplicialPoset P) (n : ℕ) (old : RankStage K Control act h₁ hmul n)
variable (p : P) (hp : faceRank p = n)
variable (f : PolynomialStalk K p →ₗ[K] BarycentricStalk K p)
variable (hf : ∀ (q : Set.Iio p) x,
  booleanRestriction (faceVertexInclusion q.property.le) (f x) =
    rankStageComponent K Control act h₁ hmul n old (rankStageLowerIndex n hs p hp q)
      (polynomialRestriction K q.property.le x))

include hf in
/-- Relabeling a candidate local map preserves its complete lower-face
boundary because that boundary is the actual equivariant old rank stage. -/
theorem rankStageLocal_relabel_boundary [Nonempty (FaceVertex p)]
    (g : G) (hg : act g p = p) (x : PolynomialStalk K p) :
    booleanBoundaryMap (V := FaceVertex p) (K := K) (relabel K (act g) (single K p f) p x) = booleanBoundaryMap (V := FaceVertex p) (K := K) (f x) := by
  letI := orderAction act h₁ hmul
  letI := familyAction K act h₁ hmul
  have hlocal (q : equivariantRankCut (fun p : P => faceRank p) n) (hq : q.val < p) :
      LocalCompatible K p q.val (single K p f) (rankStageValue K Control act h₁ hmul n old q) := by
    rcases q with ⟨q, hqn⟩
    intro h y
    simpa only [single_same, rankStageComponent, rankStageValue, rankStageLowerIndex] using hf ⟨q, hq⟩ y
  have hrel (q : Set.Iio p) :
      LocalCompatible K p q.val (relabel K (act g) (single K p f))
        (rankStageValue K Control act h₁ hmul n old (rankStageLowerIndex n hs p hp q)) := by
    let a := rankStageLowerIndex n hs p hp q
    let b := rankStageInverseIndex act n g a
    have hginv : (act g).symm p = p := by
      apply (act g).injective
      rw [(act g).apply_symm_apply, hg]
    have hb : b.val < p := by
      change (act g).symm q.val < p
      simpa only [hginv] using (act g).symm.strictMono q.property
    have hindex : (⟨act g b.val, by
        change faceRank (act g b.val) < n
        rw [faceRank_eq_of_orderIso]
        exact b.property⟩ : equivariantRankCut (fun p : P => faceRank p) n) = a := by
      apply Subtype.ext
      exact (act g).apply_symm_apply q.val
    have hv := old.equivariant g b
    change old.value ⟨act g b.val, _⟩ = relabel K (act g) (old.value b) at hv
    rw [hindex] at hv
    have hh := relabel_compatible K (act g) p b.val (single K p f)
      (rankStageValue K Control act h₁ hmul n old b) (hlocal b hb)
    have hgb : act g b.val = q.val := (act g).apply_symm_apply q.val
    change LocalCompatible K (act g p) (act g b.val) (relabel K (act g) (single K p f))
      (relabel K (act g) (old.value b)) at hh
    rw [hg, hgb, ← hv] at hh
    exact hh
  have hz : stalkBoundaryRestriction (barycentricDiagram K) p
      (relabel K (act g) (single K p f) p x - f x) = 0 := by
    apply Subtype.ext
    funext q
    change booleanRestriction (faceVertexInclusion q.property.le)
      (relabel K (act g) (single K p f) p x - f x) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    exact ((hrel q) q.property.le x).trans (hf q x).symm
  have hh := (booleanBoundaryMap_eq_zero_iff (V := FaceVertex p) (K := K) _).mpr
    ((barycentricStalkBoundary_eq_zero_iff K hs p _).mp hz)
  rw [map_sub] at hh
  exact sub_eq_zero.mp hh

include hf in
/-- The precise boundary equation required by the integral controlled lift,
for the literal vertex permutation of each element of the face stabilizer. -/
theorem rankStageLocal_boundary_equivariant [Nonempty (FaceVertex p)]
    (g : G) (hg : act g p = p) (x : PolynomialStalk K p) :
    booleanBoundaryMap (V := FaceVertex p) (K := K) (f (MvPolynomial.rename (fixedFaceVertexPermutation (act g) p hg) x)) =
      booleanBoundaryMap (V := FaceVertex p) (K := K) (booleanVertexRelabelEquiv (fixedFaceVertexPermutation (act g) p hg)
        (f x)) := by
  have hginv : act g⁻¹ p = p := by
    rw [orderAction_inv act h₁ hmul]
    apply (act g).injective
    rw [(act g).apply_symm_apply, hg]
  have hsym : (act g⁻¹).symm p = p := by
    rw [orderAction_inv act h₁ hmul, OrderIso.symm_symm]
    exact hg
  have hb := rankStageLocal_relabel_boundary K Control act h₁ hmul hs n old p hp f hf
    g⁻¹ hginv x
  have hr := booleanBoundaryRelabel_congr (fixedFaceVertexPermutation (act g⁻¹).symm p hsym)
    _ _ hb
  rw [relabel_fixed_conjugate] at hr
  simpa only [single_same, orderAction_inv act h₁ hmul, OrderIso.symm_symm] using hr

end ScalarFamilies
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicStableFaceLocalDiscrepancy.lean -/
section

section
/-! # The actual stalk discrepancy in the prime-power induction

The smaller family and the already constructed proper-face maps imply the
fixed-face boundary condition. All restrictions in this proof are the
original simplicial-poset stalk restrictions, including the empty face.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset

section StalkBoundary
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

include hs in
/-- Equality in the actual top quotient is equality on every proper stalk. -/
theorem stalkRestriction_eq_of_booleanBoundary_eq (s : P) [Nonempty (FaceVertex s)]
    (x y : BarycentricStalk K s) (h : booleanBoundaryMap x = booleanBoundaryMap y)
    (q : Set.Iio s) :
    booleanRestriction (faceVertexInclusion q.property.le) x =
      booleanRestriction (faceVertexInclusion q.property.le) y := by
  have hz : booleanBoundaryMap (x-y) = 0 := by rw [map_sub, h, sub_self]
  have hr := (barycentricStalkBoundary_eq_zero_iff K hs s (x-y)).mpr
    ((booleanBoundaryMap_eq_zero_iff (x-y)).mp hz)
  have hq := congrArg (fun z => z.val q) hr
  change booleanRestriction (faceVertexInclusion q.property.le) (x-y) = 0 at hq
  rw [map_sub] at hq
  exact sub_eq_zero.mp hq

end StalkBoundary

variable (p : ℕ) [Fact p.Prime] {W : Type*} [Fintype W]
variable (K : Type*) [CommRing K]
local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _
local instance (priority := 2100) : DecidableEq (Finset W) := Classical.decEq _
local instance (priority := 2100) : DecidableEq (Finset (ZMod p × W)) := Classical.decEq _

/-- Strict inclusion is preserved by taking the union of full prime orbits. -/
theorem primeOrbitFace_strictMono : StrictMono (primeOrbitFace (W := W) p) := by
  intro S T h
  apply lt_of_le_of_ne ((primeOrbitFace_subset_iff p S T).mpr h.le)
  intro he
  have hh := congrArg (primeStableFaceLabels p) he
  have hST : S = T := by simpa only [primeStableFaceLabels_orbitFace] using hh
  exact h.ne hST

/-- Literal proper-face restrictions detect the ordinary Boolean boundary. -/
theorem booleanStalkBoundary_zero_of_restrictions (S : Finset W)
    [Nonempty (FaceVertex S)] (x : BarycentricStalk K S)
    (hx : ∀ (T : Set.Iio S), booleanRestriction (faceVertexInclusion T.property.le) x = 0) :
    booleanBoundaryMap (V := FaceVertex S) (K := K) x = 0 := by
  have hr : stalkBoundaryRestriction (barycentricDiagram K) S x = 0 := by
    apply Subtype.ext
    funext T
    exact hx T
  exact (@booleanBoundaryMap_eq_zero_iff (FaceVertex S) K inferInstance
    (fun a b => Subtype.instDecidableEq a b) inferInstance inferInstance x).mpr
      ((barycentricStalkBoundary_eq_zero_iff K simplex_isSimplicialPoset S x).mp hr)

/-- The actual old maps force the fixed-face discrepancy to have zero boundary. -/
theorem primeOrbitStalk_discrepancy_boundary
    (ψ : ScalarFamilies.comparisonModule (P := Finset W) K)
    (S : Finset W) [Nonempty (FaceVertex S)]
    (f : PolynomialStalk K (primeOrbitFace p S) →ₗ[K] BarycentricStalk K (primeOrbitFace p S))
    (lower : ∀ T : Set.Iio S,
      PolynomialStalk K (primeOrbitFace p T.val) →ₗ[K]
        BarycentricStalk K (primeOrbitFace p T.val))
    (hf : ∀ (T : Set.Iio S) x,
      booleanRestriction (faceVertexInclusion (primeOrbitFace_strictMono p T.property).le) (f x) =
        lower T (polynomialRestriction K (primeOrbitFace_strictMono p T.property).le x))
    (hlower : ∀ (T : Set.Iio S) x,
      primeOrbitStalkQuotient p K T.val (lower T x) =
        ψ.val T.val (primeOrbitStalkMoment p K T.val x))
    (x : PolynomialStalk K (primeOrbitFace p S)) :
    booleanBoundaryMap (V := FaceVertex S) (K := K) (ψ.val S (primeOrbitStalkMoment p K S x) -
      primeOrbitStalkQuotient p K S (f x)) = 0 := by
  apply booleanStalkBoundary_zero_of_restrictions K S
  intro T
  rw [map_sub]
  apply sub_eq_zero.mpr
  calc
    _ = ψ.val T.val (polynomialRestriction K T.property.le (primeOrbitStalkMoment p K S x)) :=
      ψ.property.1 S T.val T.property.le _
    _ = ψ.val T.val (primeOrbitStalkMoment p K T.val
        (polynomialRestriction K (primeOrbitFace_strictMono p T.property).le x)) :=
      congrArg (ψ.val T.val) (primeOrbitStalkMoment_restriction p K T.property.le x).symm
    _ = primeOrbitStalkQuotient p K T.val (lower T
        (polynomialRestriction K (primeOrbitFace_strictMono p T.property).le x)) :=
      (hlower T _).symm
    _ = primeOrbitStalkQuotient p K T.val
        (booleanRestriction (faceVertexInclusion (primeOrbitFace_strictMono p T.property).le) (f x)) :=
      congrArg (primeOrbitStalkQuotient p K T.val) (hf T x).symm
    _ = _ := primeOrbitStalkQuotient_restriction p K T.property.le (f x)

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimePowerStableLocal.lean -/
section

section
/-! # The controlled local equivalence on an actual stable simplex face

This is the coordinate bridge from the integral simultaneous lifting theorem
to the stalks used in rank induction. The input ordinary equivalence and its
boundary are transported by the actual atom bijection; the output is
transported back and retains every rank-parameter and degree identity.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
open scoped CyclicParameterAction

variable (p : ℕ) [Fact p.Prime]
variable {W G : Type*} [Fintype W] [Group G] [Finite G] [IsCyclic G]
variable (K : Type*) [CommRing K]
variable (ρ : G →* Equiv.Perm (ZMod p × W))
variable (hρ : ∀ g, CommutesPrimeTranslations p (ρ g))
variable (hG : IsPGroup p G) (Z : Subgroup G) (hZ : Nat.card Z = p)
variable (htranslations : ∀ t : ZMod p, ∃ z : Z,
  ρ z.val = primeOrbitRelabel p (Equiv.refl W) (fun _ => t))
variable (hZtranslations : ∀ z : Z, ∃ t : ZMod p,
  ρ z.val = primeOrbitRelabel p (Equiv.refl W) (fun _ => t))
variable (ψ : ScalarFamilies.comparisonModule (P := Finset W) K)
variable (hψ : ∀ g, ScalarFamilies.relabelComparison K
  (finsetOrderCongr (primeOrbitParentAction p ρ hρ g)) ψ = ψ)
variable (S : Finset W) [Nonempty (FaceVertex S)]
local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _
local instance (priority := 2100) : DecidableEq (Finset W) := Classical.decEq _
local instance (priority := 2100) : DecidableEq (Finset (ZMod p × W)) := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × FaceVertex S) := Classical.decEq _
local instance (priority := 2000) : LinearOrder (ZMod p × FaceVertex S) := primePowerVertexOrder p
local instance : Nonempty (FaceVertex (primeOrbitFace p S)) :=
  ⟨(primeOrbitFaceVertexEquiv p S).symm (0, Classical.choice inferInstance)⟩

include hψ in
/-- Invariance of the smaller family gives the literal action on its stable stalk. -/
theorem primeOrbitParent_component_equivariant
    (g : simplexPermutationStabilizer ρ (primeOrbitFace p S))
    (x : PolynomialStalk K S) :
    ψ.val S (rename (primeOrbitFaceParentPermutation p ρ hρ S g) x) =
      booleanVertexRelabelEquiv (primeOrbitFaceParentPermutation p ρ hρ S g) (ψ.val S x) := by
  let e := finsetOrderCongr (primeOrbitParentAction p ρ hρ g.val)
  have he : e S = S := primeOrbitFace_parent_fixed p ρ hρ S g
  have hinv : ScalarFamilies.relabelComparison K e.symm ψ = ψ := by
    have hh := hψ g.val⁻¹
    change ScalarFamilies.relabelComparison K
      (finsetOrderCongr (primeOrbitParentAction p ρ hρ g.val⁻¹)) ψ = ψ at hh
    rw [map_inv] at hh
    change ScalarFamilies.relabelComparison K
      (finsetOrderCongr (primeOrbitParentAction p ρ hρ g.val).symm) ψ = ψ at hh
    simpa only [finsetOrderCongr_symm] using hh
  have hv : ScalarFamilies.relabel K e.symm ψ.val = ψ.val := congrArg Subtype.val hinv
  have hh := ScalarFamilies.relabel_fixed_conjugate K e.symm S
    (by simpa only [OrderIso.symm_symm] using he) ψ.val x
  rw [hv] at hh
  exact hh.symm

include hG hZ htranslations hZtranslations hψ in
/-- A genuine normalized graded equivalence on the actual stable face,
with the exact old boundary and fixed-face equation. -/
theorem exists_primeOrbitStalk_controlled_local_equiv
    (f₀ : PolynomialStalk K (primeOrbitFace p S) ≃ₗ[K]
      BarycentricStalk K (primeOrbitFace p S))
    (hf₀p : ∀ r x, f₀ (polynomialParameter K (primeOrbitFace p S) (r+1) * x) =
      booleanRankParameter (r+1) * f₀ x)
    (hf₀g : ∀ n x, x ∈ polynomialDegreePiece n → f₀ x ∈
      basisOrdinaryDegreePiece (booleanChainBasis (V := FaceVertex (primeOrbitFace p S)) (K := K)) (fun a => booleanOrdinaryDegree a.val) n)
    (hf₀one : f₀ 1 = 1)
    (hdiscrepancy : ∀ x, booleanBoundaryMap (V := FaceVertex S) (K := K)
      (ψ.val S (primeOrbitStalkMoment p K S x) - primeOrbitStalkQuotient p K S (f₀ x)) = 0)
    (hboundary : ∀ (g : simplexPermutationStabilizer ρ (primeOrbitFace p S)) x,
      booleanBoundaryMap (V := FaceVertex (primeOrbitFace p S)) (K := K) (f₀ (rename (simplexStabilizerVertexPermutation ρ (primeOrbitFace p S) g) x)) =
        booleanBoundaryMap (V := FaceVertex (primeOrbitFace p S)) (K := K) (booleanVertexRelabelEquiv
          (simplexStabilizerVertexPermutation ρ (primeOrbitFace p S) g) (f₀ x))) :
    ∃ f : PolynomialStalk K (primeOrbitFace p S) ≃ₗ[K]
        BarycentricStalk K (primeOrbitFace p S),
      (∀ r x, f (polynomialParameter K (primeOrbitFace p S) (r+1) * x) =
        booleanRankParameter (r+1) * f x) ∧
      (∀ n x, x ∈ polynomialDegreePiece n → f x ∈
        basisOrdinaryDegreePiece (booleanChainBasis (V := FaceVertex (primeOrbitFace p S)) (K := K)) (fun a => booleanOrdinaryDegree a.val) n) ∧
      f 1 = 1 ∧
      (∀ x, booleanBoundaryMap (V := FaceVertex (primeOrbitFace p S)) (K := K) (f x) = booleanBoundaryMap (V := FaceVertex (primeOrbitFace p S)) (K := K) (f₀ x)) ∧
      (∀ x, primeOrbitStalkQuotient p K S (f x) =
        ψ.val S (primeOrbitStalkMoment p K S x)) ∧
      (∀ (g : simplexPermutationStabilizer ρ (primeOrbitFace p S)) x,
        f (rename (simplexStabilizerVertexPermutation ρ (primeOrbitFace p S) g) x) =
          booleanVertexRelabelEquiv
            (simplexStabilizerVertexPermutation ρ (primeOrbitFace p S) g) (f x)) := by
  let e := primeOrbitFaceVertexEquiv p S
  let ψS : MvPolynomial (FaceVertex S) K →ₗ[K] BooleanBarycentricRing (FaceVertex S) K := ψ.val S
  let H := simplexPermutationStabilizer ρ (primeOrbitFace p S)
  let σ := primeOrbitFaceLocalPermutation p ρ S
  let hσ := primeOrbitFaceLocalPermutation_commutes p ρ hρ S
  have hZle : Z ≤ H := primeSubgroup_le_orbitFace_stabilizer p ρ S Z hZtranslations
  let ZH : Subgroup H := Z.subgroupOf H
  have hZH : Nat.card ZH = p := (Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe hZle).toEquiv).trans hZ
  let f₁ := reverseVertexEquiv f₀ e.symm
  have hf₁p : ∀ r x, f₁ (esymm (ZMod p × FaceVertex S) K (r+1) * x) =
      booleanRankParameter (r+1) * f₁ x :=
    ScalarFamilies.reverseVertexTransport_parameter f₀.toLinearMap e.symm hf₀p
  have hf₁g : ∀ n x, x ∈ polynomialDegreePiece n → f₁ x ∈
      basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) n :=
    ScalarFamilies.reverseVertexTransport_graded f₀.toLinearMap e.symm hf₀g
  let A := PrimePowerParameterRing (W := FaceVertex S) p K
  let F₁ : MvPolynomial (ZMod p × FaceVertex S) K ≃ₗ[A]
      BooleanBarycentricRing (ZMod p × FaceVertex S) K :=
    reverseParameterLinearEquiv f₁ (reverseAllRanks_parameterLinear f₁.toLinearMap hf₁p)
  let L := F₁.symm
  have hLsymm (x : MvPolynomial (ZMod p × FaceVertex S) K) :
      L.symm x = booleanVertexRelabelEquiv e (f₀ (rename e.symm x)) := rfl
  have hLg : ∀ n x, x ∈ PrimeBooleanDegreePiece p K n ↔ L x ∈ polynomialDegreePiece n :=
    reverseVertexEquiv_grade_iff f₁ hf₁g
  have hf₁one : f₁ 1 = 1 := by
    change booleanVertexRelabelEquiv e (f₀ (rename e.symm 1)) = 1
    rw [map_one, hf₀one, map_one]
  have hLone : L 1 = 1 := by
    apply F₁.injective
    exact (F₁.apply_symm_apply 1).trans hf₁one.symm
  have hδ : ∀ x, booleanBoundaryMap (V := FaceVertex S) (K := K)
      (ψS (primeOrbitMomentRetraction p K x) - primeFixedFaceQuotient p K (L.symm x)) = 0 := by
    intro x
    rw [hLsymm]
    have hh := hdiscrepancy (rename e.symm x)
    change booleanBoundaryMap (V := FaceVertex S) (K := K)
      (ψS (primeOrbitMomentRetraction p K (rename e (rename e.symm x))) -
        primeFixedFaceQuotient p K (booleanVertexRelabelEquiv e (f₀ (rename e.symm x)))) = 0 at hh
    have hr : rename e (rename e.symm x) = x := (MvPolynomial.renameEquiv K e).apply_symm_apply x
    rw [hr] at hh
    exact hh
  have hbe : ∀ (g : H) x,
      booleanBoundaryMap (L.symm (rename (σ g) x)) =
        booleanBoundaryMap (booleanVertexRelabelEquiv (σ g) (L.symm x)) := by
    intro g x
    have hh := booleanBoundary_vertexRelabel_congr e _ _ (hboundary g (rename e.symm x))
    have hr : rename e.symm (rename (σ g) x) =
        rename (simplexStabilizerVertexPermutation ρ (primeOrbitFace p S) g)
          (rename e.symm x) := by
      rw [rename_rename, rename_rename]
      apply congrArg (fun u => rename u x)
      funext v
      exact e.symm_apply_apply _
    have hb : booleanVertexRelabelEquiv e
        (booleanVertexRelabelEquiv (simplexStabilizerVertexPermutation ρ (primeOrbitFace p S) g)
          (f₀ (rename e.symm x))) =
      booleanVertexRelabelEquiv (σ g) (booleanVertexRelabelEquiv e (f₀ (rename e.symm x))) := by
      rw [← booleanVertexRelabelEquiv_trans, ← booleanVertexRelabelEquiv_trans]
      apply congrArg (fun u => booleanVertexRelabelEquiv u (f₀ (rename e.symm x)))
      apply Equiv.ext
      intro v
      change e (simplexStabilizerVertexPermutation ρ (primeOrbitFace p S) g v) =
        e (simplexStabilizerVertexPermutation ρ (primeOrbitFace p S) g (e.symm (e v)))
      rw [Equiv.symm_apply_apply]
    change booleanBoundaryMap (booleanVertexRelabelEquiv e (f₀ (rename e.symm (rename (σ g) x)))) = _
    rw [hr]
    exact hh.trans (congrArg booleanBoundaryMap hb)
  have hψe : ∀ (g : H) x,
      ψS (rename (primeOrbitParentAction p σ hσ g) x) =
        booleanVertexRelabelEquiv (primeOrbitParentAction p σ hσ g) (ψS x) := by
    intro g x
    rw [primeOrbitFaceLocalPermutation_parent p ρ hρ S g]
    exact primeOrbitParent_component_equivariant p K ρ hρ ψ hψ S g x
  obtain ⟨F, hFg, hFone, hFb, hFπ, hFe⟩ :=
    exists_primePower_prescribed_local_equiv p K σ hσ (hG.to_subgroup H) ZH hZH
      (primeOrbitFaceLocalPermutation_hasTranslations p ρ S Z hZle htranslations)
      L hLg hLone ψS (ψ.property.2.1 S) (ψ.property.2.2 S) hψe hδ hbe
  let f : PolynomialStalk K (primeOrbitFace p S) ≃ₗ[K] BarycentricStalk K (primeOrbitFace p S) :=
    reverseVertexEquiv (F.restrictScalars K) e
  have hfcoord (x : PolynomialStalk K (primeOrbitFace p S)) :
      booleanVertexRelabelEquiv e (f x) = F (rename e x) :=
    reverseVertexEquiv_conjugate (F.restrictScalars K) e x
  have hfp : ∀ r x, f (polynomialParameter K (primeOrbitFace p S) (r+1) * x) =
      booleanRankParameter (r+1) * f x :=
    ScalarFamilies.reverseVertexTransport_parameter (F.restrictScalars K).toLinearMap e
      (reverseParameterLinear_allRanks (F.restrictScalars K).toLinearMap (fun a x => F.map_smul a x))
  have hfg : ∀ n x, x ∈ polynomialDegreePiece n → f x ∈
      basisOrdinaryDegreePiece (booleanChainBasis (V := FaceVertex (primeOrbitFace p S)) (K := K))
        (fun a => booleanOrdinaryDegree a.val) n :=
    ScalarFamilies.reverseVertexTransport_graded (F.restrictScalars K).toLinearMap e hFg
  refine ⟨f, hfp, hfg, ?_, ?_, ?_, ?_⟩
  · change booleanVertexRelabelEquiv e.symm (F (rename e 1)) = 1
    rw [map_one, hFone, map_one]
  · intro x
    have hh := booleanBoundary_vertexRelabel_congr e.symm _ _ (hFb (rename e x))
    rw [hLsymm, booleanVertexRelabel_symm_apply] at hh
    have hr : rename e.symm (rename e x) = x := (MvPolynomial.renameEquiv K e).symm_apply_apply x
    rw [hr] at hh
    exact hh
  · intro x
    change primeFixedFaceQuotient p K (booleanVertexRelabelEquiv e (f x)) =
      ψS (primeOrbitMomentRetraction p K (rename e x))
    rw [hfcoord, hFπ]
  · intro g x
    apply (booleanVertexRelabelEquiv (K := K) e).injective
    rw [hfcoord]
    have hr : rename e (rename (simplexStabilizerVertexPermutation ρ (primeOrbitFace p S) g) x) =
        rename (σ g) (rename e x) := by
      rw [rename_rename, rename_rename]
      apply congrArg (fun u => rename u x)
      funext v
      change e (simplexStabilizerVertexPermutation ρ (primeOrbitFace p S) g v) =
        e (simplexStabilizerVertexPermutation ρ (primeOrbitFace p S) g (e.symm (e v)))
      rw [Equiv.symm_apply_apply]
    rw [hr, hFe]
    have hb : booleanVertexRelabelEquiv e
        (booleanVertexRelabelEquiv (simplexStabilizerVertexPermutation ρ (primeOrbitFace p S) g) (f x)) =
        booleanVertexRelabelEquiv (σ g) (booleanVertexRelabelEquiv e (f x)) := by
      rw [← booleanVertexRelabelEquiv_trans, ← booleanVertexRelabelEquiv_trans]
      apply congrArg (fun u => booleanVertexRelabelEquiv u (f x))
      apply Equiv.ext
      intro v
      change e (simplexStabilizerVertexPermutation ρ (primeOrbitFace p S) g v) =
        e (simplexStabilizerVertexPermutation ρ (primeOrbitFace p S) g (e.symm (e v)))
      rw [Equiv.symm_apply_apply]
    rw [hb, hfcoord]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ScalarOrdinaryBijective.lean -/
section

section
/-! # A normalized actual ordinary family with every component invertible -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal.ScalarFamilies
open Classical
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

/-- The ordinary comparison already proved in Theorem 1.1 supplies actual
bijections, not merely a scalar-one element of the family module. -/
theorem exists_normalized_bijective_comparisonFamily (hs : IsSimplicialPoset P) :
    ∃ F : comparisonModule (P := P) K,
      scalar K F = 1 ∧ ∀ s, Function.Bijective (F.val s) := by
  let d := Fintype.card P
  have hrank : ∀ s : P, faceRank s ≤ d := fun s => Finset.card_le_univ (faceVertices s)
  let E := universalCoherentComparison K hs d hrank
  have hp : ∀ s r x, E.component s (booleanRankParameter (r+1) * x) =
      polynomialParameter K s (r+1) * E.component s x :=
    fun s => (universalCoherentComparison_spec K hs d hrank s).2.1
  have hd : ∀ s n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → E.component s x ∈ polynomialDegreePiece n :=
    fun s => ordinaryDegree_of_hasStandardDegree hs s (E.component s).toLinearMap
      (universalCoherentComparison_spec K hs d hrank s).2.2
  have hE : ∀ s, E.component s 1 = 1 := fun s =>
    hasStandardLeadingDegree_one hs d s (E.component s).toLinearMap
      (universalCoherentComparison_spec K hs d hrank s).1
      (universalCoherentComparison_spec K hs d hrank s).2.2
  refine ⟨⟨inverseCoherentFamily K E, inverseCoherentFamily_mem K E hp hd⟩, ?_, ?_⟩
  · change constantCoefficient (inverseCoherentFamily K E ⊥ 1) = 1
    rw [inverseCoherentFamily_one K E hE, constantCoefficient_one]
  · intro s
    exact (E.component s).symm.bijective

end FourPapers.Universal.ScalarFamilies

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimePowerRankConstruction.lean -/
section

section
/-! # Integral coherent families from a comparison on the orbit simplex

The rank induction has three genuine cases: the empty face, a face with
trivial stabilizer, and a union of prime orbits. In the last case the checked
controlled local equivalence retains the exact previously constructed
boundary and the exact fixed-face prescription. No group order is divided.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

section OrderAction
variable {V G : Type*} [Fintype V] [Group G] (ρ : G →* Equiv.Perm V)
def simplexGroupOrderAction (g : G) : Finset V ≃o Finset V := finsetOrderCongr (ρ g)
@[simp] theorem simplexGroupOrderAction_one : simplexGroupOrderAction ρ 1 = OrderIso.refl _ := by
  change finsetOrderCongr (ρ 1) = _
  rw [ρ.map_one]
  exact simplexOrderAction_one

theorem simplexGroupOrderAction_mul (g h : G) :
    simplexGroupOrderAction ρ (g*h) = (simplexGroupOrderAction ρ h).trans (simplexGroupOrderAction ρ g) := by
  change finsetOrderCongr (ρ (g*h)) = _
  rw [ρ.map_mul]
  exact simplexOrderAction_mul _ _
end OrderAction

variable (p : ℕ) [Fact p.Prime]
variable {W G : Type*} [Fintype W] [Group G] [Finite G] [IsCyclic G]
variable (K : Type*) [CommRing K]
variable (ρ : G →* Equiv.Perm (ZMod p × W))
variable (hρ : ∀ g, CommutesPrimeTranslations p (ρ g))
variable (hG : IsPGroup p G) (Z : Subgroup G) (hZ : Nat.card Z = p)
variable (htranslations : ∀ t : ZMod p, ∃ z : Z,
  ρ z.val = primeOrbitRelabel p (Equiv.refl W) (fun _ => t))
variable (hZtranslations : ∀ z : Z, ∃ t : ZMod p,
  ρ z.val = primeOrbitRelabel p (Equiv.refl W) (fun _ => t))
variable (ψ : ScalarFamilies.comparisonModule (P := Finset W) K)
variable (hψone : ScalarFamilies.scalar K ψ = 1)
variable (hψ : ∀ g, ScalarFamilies.relabelComparison K
  (finsetOrderCongr (primeOrbitParentAction p ρ hρ g)) ψ = ψ)
local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _
local instance (priority := 2100) : DecidableEq (Finset W) := Classical.decEq _
local instance (priority := 2100) : DecidableEq (Finset (ZMod p × W)) := Classical.decEq _

include hG hZ htranslations hZtranslations hψone hψ in
/-- The actual integral rank construction from the smaller orbit family. -/
theorem exists_primeOrbit_controlled_comparisonFamily :
    ∃ F : ScalarFamilies.comparisonModule (P := Finset (ZMod p × W)) K,
      ScalarFamilies.scalar K F = 1 ∧
      (∀ g, ScalarFamilies.relabelComparison K (finsetOrderCongr (ρ g)) F = F) ∧
      ∀ s, PrimeOrbitLocalControl p K ψ s (F.val s) := by
  let Control := PrimeOrbitLocalControl p K ψ
  let act := simplexGroupOrderAction ρ
  let h₁ := simplexGroupOrderAction_one ρ
  let hmul := simplexGroupOrderAction_mul ρ
  have hs : IsSimplicialPoset (Finset (ZMod p × W)) := simplex_isSimplicialPoset
  have hbij : ∀ s f, Control s f → Function.Bijective f := fun s f hf => hf.1
  apply ScalarFamilies.exists_controlled_equivariant_family K Control act h₁ hmul hs
    (fun g s H hH => primeOrbitLocalControl_relabel p K ρ hρ ψ hψ g H s hH)
  intro n old F hF_rank
  by_cases hFempty : F = ∅
  · subst F
    obtain ⟨B, hBscalar, hBbij⟩ := ScalarFamilies.exists_normalized_bijective_comparisonFamily K hs
    let f := B.val ∅
    have hf₁ : f 1 = 1 := by
      change B.val ∅ 1 = 1
      rw [ScalarFamilies.component_one, hBscalar, one_smul]
    have hψ₁ : ψ.val ∅ 1 = 1 := by
      rw [ScalarFamilies.component_one, hψone, one_smul]
    refine ⟨ScalarFamilies.single K ∅ f,
      ScalarFamilies.single_good K Control ∅ f (B.property.2.1 ∅) (B.property.2.2 ∅)
        hf₁ (primeOrbitLocalControl_empty p K ψ hψ₁ f (hBbij ∅) hf₁), ?_, ?_⟩
    · intro q hq
      exact False.elim (not_lt_bot hq)
    · intro g hg
      have hi : (act g).symm ∅ = ∅ := (act g).symm.map_bot
      apply ScalarFamilies.relabel_fixed_single K (act g) ∅ hi
      intro x
      letI : IsEmpty (FaceVertex (∅ : Finset (ZMod p × W))) := ⟨fun v => v.property.1.ne_bot (le_bot_iff.mp v.property.2)⟩
      have he : fixedFaceVertexPermutation (act g).symm ∅ hi = Equiv.refl _ := Subsingleton.elim _ _
      rw [he]
      change f (rename (id : FaceVertex (∅ : Finset (ZMod p × W)) → _) x) = _
      rw [rename_id_apply, booleanVertexRelabelEquiv_refl]
  · have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hFempty
    letI : Nonempty (FaceVertex F) := by
      obtain ⟨v,hv⟩ := hFne
      exact ⟨(simplexVertexEquiv F).symm ⟨v,hv⟩⟩
    letI : LinearOrder (FaceVertex F) := linearOrderWithDecidableEq
      (LinearOrder.lift' (Fintype.equivFin (FaceVertex F))
        (Fintype.equivFin (FaceVertex F)).injective) inferInstance
    obtain ⟨f₀, hf₀p, hf₀res, hf₀g, hf₀one⟩ :=
      ScalarFamilies.exists_rankStage_ordinaryLocal K Control act h₁ hmul n old hbij hs F hF_rank
    have hf₀rank : ∀ r x, f₀ (polynomialParameter K F (r+1) * x) =
        booleanRankParameter (r+1) * f₀ x :=
      reverseParameterLinear_allRanks f₀.toLinearMap hf₀p
    have hex : ∃ f : PolynomialStalk K F ≃ₗ[K] BarycentricStalk K F,
        (∀ r x, f (polynomialParameter K F (r+1) * x) = booleanRankParameter (r+1) * f x) ∧
        (∀ j x, x ∈ polynomialDegreePiece j → f x ∈
          basisOrdinaryDegreePiece (booleanChainBasis (V := FaceVertex F) (K := K)) (fun a => booleanOrdinaryDegree a.val) j) ∧
        f 1 = 1 ∧ Control F f.toLinearMap ∧
        (∀ (q : Set.Iio F) x, booleanRestriction (faceVertexInclusion q.property.le) (f x) =
          ScalarFamilies.rankStageComponent K Control act h₁ hmul n old
            (ScalarFamilies.rankStageLowerIndex n hs F hF_rank q)
              (polynomialRestriction K q.property.le x)) ∧
        (∀ (g : simplexPermutationStabilizer ρ F) x,
          f (rename (simplexStabilizerVertexPermutation ρ F g) x) =
            booleanVertexRelabelEquiv (simplexStabilizerVertexPermutation ρ F g) (f x)) := by
      by_cases hstable : PrimeTranslationStable p F
      · obtain ⟨S, rfl⟩ : ∃ S, F = primeOrbitFace p S :=
          ⟨primeStableFaceLabels p F, (primeTranslationStable_iff p F).mp hstable⟩
        letI : Nonempty (FaceVertex S) := by
          obtain ⟨⟨v,w⟩,hw⟩ := hFne
          exact ⟨(simplexVertexEquiv S).symm ⟨w,(mem_primeOrbitFace p S v w).mp hw⟩⟩
        let lower := fun T : Set.Iio S => ScalarFamilies.rankStageComponent K Control act h₁ hmul n old
          (ScalarFamilies.rankStageLowerIndex n hs (primeOrbitFace p S) hF_rank
            ⟨primeOrbitFace p T.val, primeOrbitFace_strictMono p T.property⟩)
        have hlower : ∀ (T : Set.Iio S) x,
            primeOrbitStalkQuotient p K T.val (lower T x) =
              ψ.val T.val (primeOrbitStalkMoment p K T.val x) := by
          intro T x
          have hh := (ScalarFamilies.rankStageComponent_good K Control act h₁ hmul n old
            (ScalarFamilies.rankStageLowerIndex n hs (primeOrbitFace p S) hF_rank
              ⟨primeOrbitFace p T.val, primeOrbitFace_strictMono p T.property⟩)).2.2.2
          exact ((primeOrbitLocalControl_at_orbitFace p K ψ T.val (lower T)).mp hh).2 x
        have hδ := primeOrbitStalk_discrepancy_boundary p K ψ S f₀.toLinearMap lower
          (fun T x => hf₀res ⟨primeOrbitFace p T.val, primeOrbitFace_strictMono p T.property⟩ x) hlower
        have hb : ∀ (g : simplexPermutationStabilizer ρ (primeOrbitFace p S)) x,
            booleanBoundaryMap (V := FaceVertex (primeOrbitFace p S)) (K := K) (f₀ (rename (simplexStabilizerVertexPermutation ρ (primeOrbitFace p S) g) x)) =
              booleanBoundaryMap (V := FaceVertex (primeOrbitFace p S)) (K := K) (booleanVertexRelabelEquiv
                (simplexStabilizerVertexPermutation ρ (primeOrbitFace p S) g) (f₀ x)) := by
          intro g x
          exact ScalarFamilies.rankStageLocal_boundary_equivariant K Control act h₁ hmul hs n old
            (primeOrbitFace p S) hF_rank f₀.toLinearMap hf₀res g.val g.property x
        obtain ⟨f, hfp, hfg, hf₁, hfb, hfπ, hfe⟩ :=
          exists_primeOrbitStalk_controlled_local_equiv p K ρ hρ hG Z hZ htranslations hZtranslations
            ψ hψ S f₀ hf₀rank hf₀g hf₀one hδ hb
        refine ⟨f, hfp, hfg, hf₁,
          (primeOrbitLocalControl_at_orbitFace p K ψ S f.toLinearMap).mpr ⟨f.bijective,hfπ⟩,
          ?_, hfe⟩
        intro q x
        exact (stalkRestriction_eq_of_booleanBoundary_eq K hs (primeOrbitFace p S)
          (f x) (f₀ x) (hfb x) q).trans (hf₀res q x)
      · refine ⟨f₀, hf₀rank, hf₀g, hf₀one,
          primeOrbitLocalControl_of_not_stable p K ψ F hstable f₀.toLinearMap f₀.bijective,
          hf₀res, ?_⟩
        intro g x
        have hg := nonstableFace_stabilizer_trivial p ρ hG Z hZ htranslations F hstable g
        subst g
        rw [map_one]
        change f₀ (rename (id : FaceVertex F → _) x) = _
        rw [rename_id_apply]
        exact (booleanVertexRelabelEquiv_refl (f₀ x)).symm
    obtain ⟨f,hfp,hfg,hf₁,hfc,hfres,hfe⟩ := hex
    refine ⟨ScalarFamilies.single K F f.toLinearMap,
      ScalarFamilies.single_good K Control F f.toLinearMap hfp hfg hf₁ hfc, ?_, ?_⟩
    · intro q hq h x
      rw [ScalarFamilies.single_same]
      change booleanRestriction (faceVertexInclusion h) (f x) =
        ScalarFamilies.rankStageComponent K Control act h₁ hmul n old q (polynomialRestriction K h x)
      have hh := hfres ⟨q.val,hq⟩ x
      simpa only [ScalarFamilies.rankStageComponent, ScalarFamilies.rankStageLowerIndex,
        ScalarFamilies.rankStageValue] using hh
    · intro g hg
      have hi : (act g).symm F = F := by
        apply (act g).injective
        rw [(act g).apply_symm_apply, hg]
      have hgi : act g⁻¹ F = F := by
        rw [ScalarFamilies.orderAction_inv act h₁ hmul]
        exact hi
      apply ScalarFamilies.relabel_fixed_single K (act g) F hi
      intro x
      let a : simplexPermutationStabilizer ρ F := ⟨g⁻¹,hgi⟩
      have hp : simplexStabilizerVertexPermutation ρ F a =
          fixedFaceVertexPermutation (act g).symm F hi := by
        apply Equiv.ext
        intro v
        apply Subtype.ext
        rw [simplexStabilizerVertexPermutation_val, fixedFaceVertexPermutation_val]
        exact congrArg (fun e : Finset (ZMod p × W) ≃o _ => e v.val)
          (ScalarFamilies.orderAction_inv act h₁ hmul g)
      change f (rename (fixedFaceVertexPermutation (act g).symm F hi) x) =
        booleanVertexRelabelEquiv (fixedFaceVertexPermutation (act g).symm F hi) (f x)
      rw [← hp]
      exact hfe a x

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimePowerReduction.lean -/
section

section
/-! # The actual quotient step for finite cyclic prime-power induction

Cauchy's theorem supplies a subgroup of order p.  Its prime-order coordinate
isomorphism, the smaller cyclic p-group quotient, and the actual free action
on its orbit set are all exposed.  The coordinate permutation contains the
literal prime translations used by the controlled local lifting theorem.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical

/-- The mathematical data of one strict group-order reduction. -/
structure CyclicPrimePowerReduction (p : ℕ) (G : Type*) [CommGroup G] where
  subgroup : Subgroup G
  card_subgroup : Nat.card subgroup = p
  primeCoordinates : Multiplicative (ZMod p) ≃* subgroup
  quotient_cyclic : IsCyclic (G ⧸ subgroup)
  quotient_pgroup : IsPGroup p (G ⧸ subgroup)
  quotient_smaller : Nat.card (G ⧸ subgroup) < Nat.card G

section Existence
variable (p : ℕ) [Fact p.Prime]
variable (G : Type*) [CommGroup G] [Finite G] [IsCyclic G]

/-- Every nontrivial finite cyclic p-group has the literal reduction data. -/
theorem exists_cyclicPrimePowerReduction (hG : IsPGroup p G) (hcard : Nat.card G ≠ 1) :
    Nonempty (CyclicPrimePowerReduction p G) := by
  have hd : p ∣ Nat.card G := hG.card_eq_or_dvd.resolve_left hcard
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := G) p hd
  let Z : Subgroup G := Subgroup.zpowers z
  have hZ : Nat.card Z = p := (Nat.card_zpowers z).trans hz
  have hp : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  refine ⟨{
    subgroup := Z
    card_subgroup := hZ
    primeCoordinates := mulEquivOfPrimeCardEq hp hZ
    quotient_cyclic := isCyclic_of_surjective (QuotientGroup.mk' Z) Quotient.mk''_surjective
    quotient_pgroup := hG.to_quotient Z
    quotient_smaller := ?_ }⟩
  apply quotient_card_lt Z
  rw [hZ]
  exact (Fact.out : p.Prime).one_lt

theorem cyclicPrimePower_card_one_or_reduction (hG : IsPGroup p G) :
    Nat.card G = 1 ∨ Nonempty (CyclicPrimePowerReduction p G) := by
  by_cases h : Nat.card G = 1
  · exact Or.inl h
  · exact Or.inr (exists_cyclicPrimePowerReduction p G hG h)

end Existence

section FreeAction
variable (p : ℕ) [Fact p.Prime]
variable {G V : Type*} [CommGroup G] [Fintype V] [MulAction G V]
variable (R : CyclicPrimePowerReduction p G)
variable (hf : ∀ (g : G) (v : V), g • v = v → g = 1)

include hf in
/-- The recursion uses the actual quotient-group action on actual subgroup
orbits, and that action is free because the original action is free. -/
theorem cyclicPrimePowerReduction_quotient_free :
    letI := quotientOrbitAction (V := V) R.subgroup
    ∀ (g : G ⧸ R.subgroup) (v : SubgroupOrbit (V := V) R.subgroup),
      g • v = v → g = 1 :=
  quotientOrbitAction_free R.subgroup hf

/-- Freeness after the explicit prime-orbit coordinate change. -/
theorem cyclicPrimePowerReduction_coordinate_free
    (g : G) (v : ZMod p × SubgroupOrbit (V := V) R.subgroup)
    (h : primeOrbitCoordinatePermutation R.subgroup hf p R.primeCoordinates g v = v) : g = 1 := by
  have hh := congrArg (primeOrbitCoordinates R.subgroup hf p R.primeCoordinates) h
  rw [primeOrbitCoordinatePermutation_apply, Equiv.apply_symm_apply] at hh
  exact hf g _ hh

/-- The minimal subgroup acts by every literal prime translation in these
coordinates; this supplies the exact hypothesis used in the kernel proof. -/
theorem cyclicPrimePowerReduction_translations (t : ZMod p) :
    ∃ z : R.subgroup,
      primeOrbitCoordinatePermutation R.subgroup hf p R.primeCoordinates z.val =
        primeOrbitRelabel p (Equiv.refl (SubgroupOrbit (V := V) R.subgroup)) (fun _ => t) := by
  refine ⟨R.primeCoordinates (Multiplicative.ofAdd t), ?_⟩
  apply Equiv.ext
  intro v
  apply (primeOrbitCoordinates R.subgroup hf p R.primeCoordinates).injective
  rw [primeOrbitCoordinatePermutation_apply, Equiv.apply_symm_apply]
  exact (primeOrbitCoordinates_translate R.subgroup hf p R.primeCoordinates t v).symm

/-- Conversely, every element of the chosen subgroup is one literal
translation, as required when restricting the prescribed quotient map. -/
theorem cyclicPrimePowerReduction_subgroup_translation (z : R.subgroup) :
    ∃ t : ZMod p,
      primeOrbitCoordinatePermutation R.subgroup hf p R.primeCoordinates z.val =
        primeOrbitRelabel p (Equiv.refl (SubgroupOrbit (V := V) R.subgroup)) (fun _ => t) := by
  obtain ⟨t, rfl⟩ := R.primeCoordinates.surjective z
  exact ⟨Multiplicative.toAdd t,
    primeOrbitCoordinatePermutation_translation R.subgroup hf p R.primeCoordinates
      (Multiplicative.toAdd t)⟩

end FreeAction
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/PrimePowerPermutationTemplates.lean -/
section

section
/-! # Literal cyclic prime-power permutation groups for scalar transfers

The regular action on equally sized vertex blocks realizes each largest
prime-power divisor of the vertex cardinality. Its image subgroup has exactly
that order, so the later coset trace has the exact factorial index.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical

abbrev PrimePowerCycleGroup (p a : ℕ) := Multiplicative (ZMod (p ^ a))

variable (p : ℕ) [Fact p.Prime] (a : ℕ)

theorem primePowerCycleGroup_card : Nat.card (PrimePowerCycleGroup p a) = p ^ a := by
  letI : NeZero (p ^ a) := ⟨pow_ne_zero a (Fact.out : p.Prime).ne_zero⟩
  simp [PrimePowerCycleGroup, Nat.card_eq_fintype_card]

theorem primePowerCycleGroup_isPGroup : IsPGroup p (PrimePowerCycleGroup p a) :=
  IsPGroup.of_card (primePowerCycleGroup_card p a)

variable {V : Type*} [Fintype V] [Nonempty V]

/-- The action is free on every vertex, and the permutation subgroup has
exactly the stated prime-power order. -/
theorem exists_primePower_free_permutation
    (hdiv : p ^ a ∣ Fintype.card V) :
    ∃ ρ : PrimePowerCycleGroup p a →* Equiv.Perm V,
      Function.Injective ρ ∧
      (∀ (g : PrimePowerCycleGroup p a) (v : V), ρ g v = v → g = 1) ∧
      Nat.card ρ.range = p ^ a := by
  letI : NeZero (p ^ a) := ⟨pow_ne_zero a (Fact.out : p.Prime).ne_zero⟩
  have hcard : Fintype.card (PrimePowerCycleGroup p a) = p ^ a := by
    simpa only [Nat.card_eq_fintype_card] using primePowerCycleGroup_card p a
  obtain ⟨ρ, hρ, hf⟩ := exists_free_permutation_hom
    (G := PrimePowerCycleGroup p a) (V := V) (hcard.symm ▸ hdiv)
  exact ⟨ρ, hρ, hf, (free_permutation_range_card ρ hρ).trans
    (primePowerCycleGroup_card p a)⟩

theorem exists_maximal_primePower_free_permutation :
    ∃ ρ : PrimePowerCycleGroup p ((Fintype.card V).factorization p) →* Equiv.Perm V,
      Function.Injective ρ ∧
      (∀ (g : PrimePowerCycleGroup p ((Fintype.card V).factorization p)) (v : V),
        ρ g v = v → g = 1) ∧
      Nat.card ρ.range = p ^ (Fintype.card V).factorization p :=
  exists_primePower_free_permutation p _
    (((Fact.out : p.Prime).pow_dvd_iff_le_factorization (Fintype.card_ne_zero)).mpr le_rfl)

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimePowerFamily.lean -/
section

section
/-! # Integral normalized comparison families for all free cyclic p-group actions

The proof is a well-founded induction on the actual order of the acting
group. It descends to the actual orbit simplex for a subgroup of prime
order, invokes the complete controlled rank construction there, and returns
through a literal vertex equivalence. All coefficient rings are allowed.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical
universe uG uV uK

variable (p : ℕ) [Fact p.Prime] (K : Type uK) [CommRing K]

private theorem cyclicPrimePower_comparison_by_card (n : ℕ) :
    ∀ (G : Type uG) [CommGroup G] [Finite G] [IsCyclic G]
      (V : Type uV) [Fintype V] (ρ : G →* Equiv.Perm V),
      Nat.card G = n → IsPGroup p G →
      (∀ g v, ρ g v = v → g = 1) →
      ∃ F : ScalarFamilies.comparisonModule (P := Finset V) K,
        ScalarFamilies.scalar K F = 1 ∧
        (∀ g, ScalarFamilies.relabelComparison K (finsetOrderCongr (ρ g)) F = F) ∧
        ∀ S, Function.Bijective (F.val S) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ _ V _ ρ hn hG hfree
    by_cases hcard : Nat.card G = 1
    · letI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hcard).1
      obtain ⟨F,hF,hbij⟩ := ScalarFamilies.exists_normalized_bijective_comparisonFamily K
        (simplex_isSimplicialPoset (V := V))
      refine ⟨F,hF,?_,hbij⟩
      intro g
      have hg : g = 1 := Subsingleton.elim _ _
      rw [hg, ρ.map_one, simplexOrderAction_one]
      apply Subtype.ext
      exact ScalarFamilies.relabel_refl K F.val
    · let R : CyclicPrimePowerReduction p G :=
        Classical.choice (exists_cyclicPrimePowerReduction p G hG hcard)
      let Z := R.subgroup
      letI : MulAction G V := MulAction.compHom V ρ
      have hf : ∀ (g : G) (v : V), g • v = v → g = 1 := hfree
      let W := SubgroupOrbit (V := V) Z
      letI : Fintype W := Fintype.ofFinite W
      letI : IsCyclic (G ⧸ Z) := R.quotient_cyclic
      letI : MulAction (G ⧸ Z) W := quotientOrbitAction (V := V) Z
      let ρQ : (G ⧸ Z) →* Equiv.Perm W := MulAction.toPermHom (G ⧸ Z) W
      have hQfree : ∀ g v, ρQ g v = v → g = 1 := quotientOrbitAction_free Z hf
      have hless : Nat.card (G ⧸ Z) < n := R.quotient_smaller.trans_eq hn
      obtain ⟨ψ,hψone,hψfixed,hψbij⟩ := ih (Nat.card (G ⧸ Z)) hless
        (G ⧸ Z) W ρQ rfl R.quotient_pgroup hQfree
      let e : (ZMod p × W) ≃ V := primeOrbitCoordinates Z hf p R.primeCoordinates
      let σ : G →* Equiv.Perm (ZMod p × W) :=
        primeOrbitCoordinatePermutation Z hf p R.primeCoordinates
      let hσ := primeOrbitCoordinatePermutation_commutes Z hf p R.primeCoordinates
      have hparent (g : G) : primeOrbitParentAction p σ hσ g = ρQ (QuotientGroup.mk g) := by
        apply Equiv.ext
        intro w
        exact primeOrbitCoordinatePermutation_label Z hf p R.primeCoordinates g w
      have hψparent : ∀ g, ScalarFamilies.relabelComparison K
          (finsetOrderCongr (primeOrbitParentAction p σ hσ g)) ψ = ψ := by
        intro g
        rw [hparent]
        exact hψfixed _
      have hZtranslations : ∀ z : Z, ∃ t : ZMod p,
          σ z.val = primeOrbitRelabel p (Equiv.refl W) (fun _ => t) := by
        intro z
        obtain ⟨a,rfl⟩ := R.primeCoordinates.surjective z
        refine ⟨Multiplicative.toAdd a, ?_⟩
        exact primeOrbitCoordinatePermutation_translation Z hf p R.primeCoordinates
          (Multiplicative.toAdd a)
      obtain ⟨F,hFone,hFfixed,hFcontrol⟩ :=
        exists_primeOrbit_controlled_comparisonFamily p K σ hσ hG Z R.card_subgroup
          (primeOrbitCoordinatePermutation_hasTranslations Z hf p R.primeCoordinates)
          hZtranslations ψ hψone hψparent
      let F' := ScalarFamilies.vertexEquivFamily F e.symm
      refine ⟨F', ?_, ?_, ?_⟩
      · exact (ScalarFamilies.vertexEmbeddingFamily_scalar F e.symm.toEmbedding).trans hFone
      · intro g
        apply ScalarFamilies.vertexEmbeddingFamily_fixed F e.symm.toEmbedding (ρ g) (σ g)
        · apply Function.Embedding.ext
          intro v
          change e.symm (g • e (e.symm v)) = e.symm (ρ g v)
          rw [Equiv.apply_symm_apply]
          rfl
        · exact hFfixed g
      · exact ScalarFamilies.vertexEmbeddingFamily_bijective F e.symm.toEmbedding
          (fun S => (hFcontrol S).1)

/-- An actual integral normalized comparison for every free action of every
finite cyclic p-group, over an arbitrary commutative coefficient ring.
The face and group universes are independent. -/
theorem exists_cyclicPrimePower_comparisonFamily
    (G : Type uG) [CommGroup G] [Finite G] [IsCyclic G]
    (V : Type uV) [Fintype V] (ρ : G →* Equiv.Perm V)
    (hG : IsPGroup p G) (hfree : ∀ g v, ρ g v = v → g = 1) :
    ∃ F : ScalarFamilies.comparisonModule (P := Finset V) K,
      ScalarFamilies.scalar K F = 1 ∧
      (∀ g, ScalarFamilies.relabelComparison K (finsetOrderCongr (ρ g)) F = F) ∧
      ∀ S, Function.Bijective (F.val S) :=
  cyclicPrimePower_comparison_by_card p K (Nat.card G) G V ρ rfl hG hfree

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ScalarTheoremNineFour.lean -/
section

section
/-! # Theorem 9.4: the exact factorial scalar ideal and obstruction module

A free cyclic p-group comparison is traced from its actual permutation
subgroup. Integer Bezout coefficients for the resulting indices produce
one symmetric family of scalar `(d-1)!`. Necessity, the actual connecting
class, and transport to every bounded-rank simplicial poset then give all
three assertions of the theorem.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal.ScalarFamilies
open Classical
universe u

section Simplex
variable {V : Type u} [Fintype V] (K : Type u) [CommRing K]

/-- An actual coherent graded parameter-linear `R → B` family, fixed by
all vertex permutations, with exactly the factorial scalar over every ring. -/
theorem exists_factorial_scalar_family :
    ∃ F : comparisonModule (P := Finset V) K,
      (∀ σ : Equiv.Perm V, relabelComparison K (finsetOrderCongr σ) F = F) ∧
        scalar K F = ((Fintype.card V - 1).factorial : K) := by
  by_cases hd : Fintype.card V ≤ 1
  · exact exists_factorial_scalar_family_of_card_le_one K hd
  · have hd' : 1 < Fintype.card V := by omega
    letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    apply exists_factorial_scalar_family_of_primePowerTemplates K hd'
    intro p hp
    letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    let a := (Fintype.card V).factorization p
    letI : NeZero (p ^ a) := ⟨pow_ne_zero a (Fact.out : p.Prime).ne_zero⟩
    obtain ⟨ρ, hρ, hfree, hcard⟩ := exists_maximal_primePower_free_permutation (V := V) p
    obtain ⟨F, hFone, hFfixed, hFbij⟩ := exists_cyclicPrimePower_comparisonFamily p K
      (PrimePowerCycleGroup p a) V ρ (primePowerCycleGroup_isPGroup p a) hfree
    refine ⟨ρ.range, hcard, F, ?_, hFone⟩
    intro h
    obtain ⟨g, hg⟩ := h.property
    have hh : ρ g = h.val := hg
    exact (congrArg (fun σ : Equiv.Perm V => relabelComparison K (finsetOrderCongr σ) F)
      hh).symm.trans (hFfixed g)

def factorialSimplexFamily : comparisonModule (P := Finset V) K :=
  Classical.choose (exists_factorial_scalar_family (V := V) K)

theorem factorialSimplexFamily_fixed (σ : Equiv.Perm V) :
    relabelComparison K (finsetOrderCongr σ) (factorialSimplexFamily (V := V) K) =
      factorialSimplexFamily K :=
  (Classical.choose_spec (exists_factorial_scalar_family (V := V) K)).1 σ

@[simp] theorem factorialSimplexFamily_scalar :
    scalar K (factorialSimplexFamily (V := V) K) = ((Fintype.card V - 1).factorial : K) :=
  (Classical.choose_spec (exists_factorial_scalar_family (V := V) K)).2

/-- **Theorem 9.4, exact scalar ideal.** The source is the actual invariant
module of coherent graded parameter-linear maps on every face. -/
theorem theorem_9_4_scalarIdeal :
    invariantScalarIdeal K (fun σ : Equiv.Perm V => finsetOrderCongr σ)
      simplexOrderAction_one simplexOrderAction_mul =
      Ideal.span {((Fintype.card V - 1).factorial : K)} :=
  simplex_invariantScalarIdeal_eq_of_family K (factorialSimplexFamily (V := V) K)
    (factorialSimplexFamily_fixed K) (factorialSimplexFamily_scalar K)

/-- **Theorem 9.4, cyclic obstruction module.** This is a linear equivalence
from the submodule generated by the actual comparison class in Mathlib `H¹`
to the quotient by the exact factorial ideal. -/
def theorem_9_4_obstructionModule :
    Submodule.span K {(comparisonObstruction K (simplex_isSimplicialPoset (V := V))
      (fun σ : Equiv.Perm V => finsetOrderCongr σ) simplexOrderAction_one simplexOrderAction_mul)} ≃ₗ[K]
      (K ⧸ Ideal.span {((Fintype.card V - 1).factorial : K)}) :=
  (simplex_obstructionSpanEquiv_of_family K (factorialSimplexFamily (V := V) K)
    (factorialSimplexFamily_fixed K) (factorialSimplexFamily_scalar K)).symm

end Simplex

section Universal
variable {P K G : Type u} [PartialOrder P] [OrderBot P] [Fintype P]
  [CommRing K] [Group G]
variable (K) (hs : IsSimplicialPoset P)
variable (act : G → P ≃o P) (h₁ : act 1 = OrderIso.refl P)
  (hmul : ∀ g h, act (g * h) = (act h).trans (act g))

/-- **Theorem 9.4, universal annihilator.** The actual comparison obstruction
is annihilated for every poset of the rank bound and every automorphism action.
The proof also includes rank zero, where the family is the scalar identity. -/
theorem theorem_9_4_universalAnnihilator (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) :
    ((d - 1).factorial : K) • comparisonObstruction K hs act h₁ hmul = 0 := by
  let V := ULift.{u} (Fin d)
  have hcard : Fintype.card V = d := by simp [V]
  have hP : ∀ p : P, faceRank p ≤ Fintype.card V := by
    simpa only [hcard] using hrank
  have h := factorial_annihilates_of_simplexFamily K hs act h₁ hmul
    (factorialSimplexFamily (V := V) K) (factorialSimplexFamily_fixed K)
    (factorialSimplexFamily_scalar K) hP
  simpa only [hcard] using h

end Universal
end FourPapers.Universal.ScalarFamilies

end
end
end
