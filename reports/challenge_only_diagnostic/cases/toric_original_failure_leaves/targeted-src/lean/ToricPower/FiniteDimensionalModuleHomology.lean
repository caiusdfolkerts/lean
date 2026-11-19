module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.DFinsupp

/-!
# Finite-dimensional homology and finitely many nonzero summands

The homology comparison is the canonical quotient of cycles by
boundaries. The sum argument restricts to precisely the summands that
are nonzero; it does not change the definition of the unrestricted sum.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable {k : Type*} [Field k]

/-- Homology is a quotient of a subspace of the middle term. -/
theorem moduleHomology_finiteDimensional (S : ShortComplex (ModuleCat k))
    [FiniteDimensional k S.X₂] : FiniteDimensional k S.homology := by
  letI : FiniteDimensional k S.moduleCatLeftHomologyData.H := by
    change FiniteDimensional k (S.g.hom.ker ⧸ S.moduleCatToCycles.range)
    infer_instance
  exact Module.Finite.equiv S.moduleCatHomologyIso.symm.toLinearEquiv

/-- Only the term in the chosen degree needs to be finite-dimensional. -/
theorem complexHomology_finiteDimensional {ι : Type*} {shape : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat k) shape) (q : ι)
    [FiniteDimensional k (K.X q)] : FiniteDimensional k (K.homology q) := by
  letI : FiniteDimensional k (K.sc q).X₂ := by
    change FiniteDimensional k (K.X q)
    infer_instance
  exact moduleHomology_finiteDimensional (K.sc q)

/-- An unrestricted dependent sum of finite-dimensional spaces is
finite-dimensional when only finitely many summands are nonzero. -/
theorem dfinsupp_finiteDimensional_of_finite_nonzero
    {I : Type*} (M : I → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
    [∀ i, FiniteDimensional k (M i)]
    (finite : Set.Finite {i : I | Nontrivial (M i)}) :
    FiniteDimensional k (Π₀ i, M i) := by
  classical
  let support := {i : I | Nontrivial (M i)}
  letI : Finite support := finite.to_subtype
  let restriction : (Π₀ i, M i) →ₗ[k] (∀ i : support, M i.val) :=
    { toFun := fun x i => x i.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply FiniteDimensional.of_injective restriction
  intro x y h
  apply DFinsupp.ext
  intro i
  by_cases hi : Nontrivial (M i)
  · exact congrFun h ⟨i,hi⟩
  · haveI : Subsingleton (M i) := not_nontrivial_iff_subsingleton.mp hi
    exact Subsingleton.elim _ _

end ToricPower

end
