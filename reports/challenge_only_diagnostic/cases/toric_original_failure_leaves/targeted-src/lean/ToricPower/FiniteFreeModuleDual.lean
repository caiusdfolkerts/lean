module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The actual module dual of a finite free complex

This construction uses linear Hom into the coefficient ring. No exactness
of this contravariant functor is asserted. The finite free basis identifies
its terms with the literal transposed matrix, over the original ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower

variable (R : Type) [CommRing R]

abbrev moduleDual : (ModuleCat.{0} R)ᵒᵖ ⥤ ModuleCat.{0} R :=
  (linearYoneda R (ModuleCat.{0} R)).obj (ModuleCat.of R R)

/-- Linear duality on the actual chain complex, without an injectivity
or homology-preservation assumption. -/
def moduleDualComplex (K : ChainComplex (ModuleCat.{0} R) ℕ) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  ((moduleDual R).mapHomologicalComplex _).obj K.op

/-- The finite free module dual, in the actual dual basis. -/
def finiteFreeModuleDualEquiv (I : Type) [Finite I] :
    (ModuleCat.of R (I →₀ R) ⟶ ModuleCat.of R R) ≃ₗ[R] (I →₀ R) :=
  ModuleCat.homLinearEquiv.trans
    ((Finsupp.llift R R R I).symm.trans
      (Finsupp.linearEquivFunOnFinite R R I).symm)

@[simp]
theorem finiteFreeModuleDualEquiv_apply (I : Type) [Finite I]
    (f : ModuleCat.of R (I →₀ R) ⟶ ModuleCat.of R R) (i : I) :
    finiteFreeModuleDualEquiv R I f i = f (Finsupp.single i 1) := rfl

/-- Evaluation is the finite coefficient pairing over the original
ring. This is the matrix transpose formula used below. -/
theorem finiteFreeModuleDualEquiv_evaluate (I : Type) [Finite I]
    (f : ModuleCat.of R (I →₀ R) ⟶ ModuleCat.of R R) (v : I →₀ R) :
    f v = v.sum (fun i a => a * finiteFreeModuleDualEquiv R I f i) := by
  have inverse := (finiteFreeModuleDualEquiv R I).symm_apply_apply f
  apply Eq.trans (congrArg (fun g : ModuleCat.of R (I →₀ R) ⟶
    ModuleCat.of R R => g v) inverse.symm) ?_
  rfl

end ToricPower
