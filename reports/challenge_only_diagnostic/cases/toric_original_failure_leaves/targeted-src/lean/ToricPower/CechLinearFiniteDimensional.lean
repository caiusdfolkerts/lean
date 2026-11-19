module

public import ToricPower.CechLinearCharacterSum
public import ToricPower.LinearRelativeCechComparison
public import ToricPower.ToricCohomologyFiniteWeights
public import ToricPower.FiniteDimensionalModuleHomology

/-!
# Finite-dimensional actual complex-linear Cartier Čech cohomology

Each character coefficient is a finite tuple space, so its cohomology is
finite-dimensional over the specified field. Completeness proves that
only finitely many characters contribute. The actual scalar-linear
complex isomorphism, followed by exactness of the unrestricted direct
sum, therefore proves finite-dimensionality of the full Čech homology.
No additive-only comparison is used to transfer dimension.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {Index : Type} [Fintype Index] (charts : Index → fan.cones) (b : fan.Ray → ℤ)

/-- Every relative character degree is a finite-dimensional tuple module. -/
theorem toricCechLinearWeightDegree_finite (m : N →+ ℤ) (q : ℕ) :
    FiniteDimensional ℂ ((toricCechLinearWeightComplex fan charts b m).X q) := by
  change FiniteDimensional ℂ (∀ tuple : Fin (q+1) → Index,
    LinearRelativeCech.scalar ℂ (toricCechRayIncidence fan charts)
      (toricCharacterNegative fan b m) q tuple)
  infer_instance

theorem toricCechLinearWeightHomology_finite (m : N →+ ℤ) (q : ℕ) :
    FiniteDimensional ℂ ((toricCechLinearWeightComplex fan charts b m).homology q) := by
  letI := toricCechLinearWeightDegree_finite fan charts b m q
  exact complexHomology_finiteDimensional _ q

variable (surjective : Function.Surjective charts) (regular : fan.IsRegular)
  (complete : fan.IsComplete) (anchor : Index)

include surjective regular complete anchor

/-- The actual Laurent complex has finite-dimensional homology over ℂ. -/
theorem toricCechLaurentLinearHomology_finite (q : ℕ) :
    FiniteDimensional ℂ ((toricCechLaurentLinearComplex fan charts b).homology q) := by
  let family := fun m : N →+ ℤ => toricCechLinearWeightComplex fan charts b m
  haveI : ∀ m, FiniteDimensional ℂ ((family m).homology q) :=
    fun m => toricCechLinearWeightHomology_finite fan charts b m q
  have finite : Set.Finite {m : N →+ ℤ | Nontrivial ((family m).homology q)} := by
    apply (toricCechCohomology_nonzeroWeightSet_finite fan charts surjective
      regular complete b anchor).subset
    intro m hm
    exact ⟨q, (LinearRelativeCech.homology_nontrivial_iff ℂ
      (toricCechRayIncidence fan charts) (toricCharacterNegative fan b m) q).mp hm⟩
  haveI : FiniteDimensional ℂ (Π₀ m : N →+ ℤ, (family m).homology q) :=
    dfinsupp_finiteDimensional_of_finite_nonzero _ finite
  let e := (HomologicalComplex.homologyFunctor (ModuleCat ℂ) (.up ℕ) q).mapIso
      (toricCechLinearCharacterSumIso fan charts b (Equiv.refl (N →+ ℤ))).symm ≪≫
    ModuleDirectSum.homologyIso ℂ family q
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-- The genuine base-field section Čech complex has finite-dimensional
homology, via the actual linear Laurent coordinate isomorphism. -/
theorem toricCechActualLinearHomology_finite (nonempty : Nonempty fan.cones) (q : ℕ) :
    FiniteDimensional ℂ
      ((toricCechActualLinearComplex fan charts b nonempty regular).homology q) := by
  letI : Module.Finite ℂ
      ((HomologicalComplex.homologyFunctor (ModuleCat ℂ) (.up ℕ) q).obj
        (toricCechLaurentLinearComplex fan charts b)) := by
    change FiniteDimensional ℂ ((toricCechLaurentLinearComplex fan charts b).homology q)
    exact toricCechLaurentLinearHomology_finite fan charts b surjective regular complete anchor q
  exact Module.Finite.equiv
    ((HomologicalComplex.homologyFunctor (ModuleCat ℂ) (.up ℕ) q).mapIso
      (toricCechLinearComplexIso fan charts b nonempty regular)).symm.toLinearEquiv

end ToricPower

end
