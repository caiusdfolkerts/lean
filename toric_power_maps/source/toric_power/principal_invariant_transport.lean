module

public import ToricPower.PrincipalStatements
public import ToricPower.ToricInvariantLineBundleClassification

/-!
# Isomorphism invariance of the literal principal statements

Normalising a line bundle to an invariant Cartier representative must preserve
both sides of the paper's criterion. These lemmas use actual isomorphisms of
module sheaves, their actual pullbacks and pushforwards, and the cohomology
functor. They do not define either side of the criterion using a representative.

Every Cartier divisor is transported to its constructed invariant
representative. No equivalence with the bounded coherent part of the derived
category of all module sheaves is needed. These transport lemmas do not
assert Theorem 1.1.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

universe u v

/-- Actual sheaf isomorphisms preserve nonvanishing of total sheaf cohomology,
including degree zero. -/
theorem totalCohomologyNonzero_iff_of_iso {X : Scheme.{u}}
    {F G : X.Modules} (e : F ≅ G) :
    totalCohomologyNonzero X F ↔ totalCohomologyNonzero X G := by
  unfold totalCohomologyNonzero
  apply exists_congr
  intro p
  exact ((TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyFunctor X p).mapIso e).addCommGroupIsoToAddEquiv.toEquiv.nontrivial_congr

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The full family of rational linear tests depends only on the actual
line bundle, without any completeness restriction on the test varieties. -/
theorem linearCohomologyCriterion_iff_of_sheaf_iso (fan : Fan i)
    (hne : fan.cones.Nonempty) {D E : toricCartierDivisor fan hne}
    (e : toricDivisorSheaf fan hne D ≅ toricDivisorSheaf fan hne E) :
    linearCohomologyCriterion fan hne D ↔ linearCohomologyCriterion fan hne E := by
  unfold linearCohomologyCriterion
  exact forall_congr' fun W => totalCohomologyNonzero_iff_of_iso
    ((Scheme.Modules.pullback (linearToricInclusion fan W)).mapIso e)

/-- For every positive exponent, actual isomorphic Cartier line bundles
have isomorphic direct images and therefore the same classical-generation
property in the literal bounded derived category of coherent sheaves. -/
theorem toricPowerGeneratesDbCoh_iff_of_sheaf_iso (fan : Fan i)
    (regular : fan.IsRegular) (hne : fan.cones.Nonempty)
    {D E : toricCartierDivisor fan hne}
    (e : toricDivisorSheaf fan hne D ≅ toricDivisorSheaf fan hne E)
    (ell : ℕ) (hell : 0 < ell) :
    toricPowerGeneratesDbCoh fan regular hne D ell hell ↔
      toricPowerGeneratesDbCoh fan regular hne E ell hell := by
  letI := toricScheme_isNoetherian fan
  exact coherentSingle_generates_iff_of_iso (X := fan.algebraicRealization)
    ((SheafOfModules.isFinitePresentation fan.algebraicRealization.ringCatSheaf).fullyFaithfulι.preimageIso
      ((Scheme.Modules.pushforward (toricPowerMap fan ell)).mapIso e))

/-- This transports the complete goal proposition, including its uniform
all-large-integers clause, along an actual Cartier-sheaf isomorphism.
It does not supply a proof of either goal proposition. -/
theorem principalTheoremDbCohClaim_iff_of_sheaf_iso (fan : Fan i)
    (regular : fan.IsRegular) (hne : fan.cones.Nonempty)
    {D E : toricCartierDivisor fan hne}
    (e : toricDivisorSheaf fan hne D ≅ toricDivisorSheaf fan hne E) :
    principalTheoremDbCohClaim fan regular hne D ↔
      principalTheoremDbCohClaim fan regular hne E := by
  unfold principalTheoremDbCohClaim
  simp_rw [toricPowerGeneratesDbCoh_iff_of_sheaf_iso fan regular hne e,
    linearCohomologyCriterion_iff_of_sheaf_iso fan hne e]

/-- Every actual Cartier line bundle has the invariant representative
constructed from its genuine local rational frames. -/
def toricCartierInvariantRepresentative (fan : Fan i)
    (regular : fan.IsRegular) (hne : fan.cones.Nonempty)
    (D : toricCartierDivisor fan hne) : toricCartierDivisor fan hne := by
  letI := toricScheme_isIntegral fan hne
  letI := D.isInvertible_sheaf
  exact invariantCartierDivisor fan hne.coe_sort regular
    (toricLineBundleInvariantCoefficients fan hne.coe_sort regular D.sheaf)

/-- The representative comparison is an actual module-sheaf isomorphism,
not an assumption of invariant presentation or equivariant structure. -/
def toricCartierInvariantRepresentativeIso (fan : Fan i)
    (regular : fan.IsRegular) (hne : fan.cones.Nonempty)
    (D : toricCartierDivisor fan hne) :
    toricDivisorSheaf fan hne D ≅
      toricDivisorSheaf fan hne (toricCartierInvariantRepresentative fan regular hne D) := by
  letI := toricScheme_isIntegral fan hne
  letI := D.isInvertible_sheaf
  exact toricLineBundleInvariantIso fan hne.coe_sort regular D.sheaf

/-- All quantifiers in the principal goal, including every sufficiently
large integer, are preserved by the constructed invariant representative. -/
theorem principalTheoremDbCohClaim_iff_invariantRepresentative (fan : Fan i)
    (regular : fan.IsRegular) (hne : fan.cones.Nonempty)
    (D : toricCartierDivisor fan hne) :
    principalTheoremDbCohClaim fan regular hne D ↔
      principalTheoremDbCohClaim fan regular hne
        (toricCartierInvariantRepresentative fan regular hne D) :=
  principalTheoremDbCohClaim_iff_of_sheaf_iso fan regular hne
    (toricCartierInvariantRepresentativeIso fan regular hne D)

/-- Proving the literal principal statement for all invariant coefficient
vectors is equivalent to proving it for every actual Cartier divisor.
The equivalence itself does not prove either universal statement. -/
theorem principalTheoremDbCohClaim_forall_iff_invariant (fan : Fan i)
    (regular : fan.IsRegular) (hne : fan.cones.Nonempty) :
    (∀ D : toricCartierDivisor fan hne, principalTheoremDbCohClaim fan regular hne D) ↔
      (letI := toricScheme_isIntegral fan hne
       ∀ b : fan.Ray → ℤ, principalTheoremDbCohClaim fan regular hne
         (invariantCartierDivisor fan hne.coe_sort regular b)) := by
  letI := toricScheme_isIntegral fan hne
  constructor
  · intro all b
    exact all _
  · intro invariant D
    letI := D.isInvertible_sheaf
    apply (principalTheoremDbCohClaim_iff_invariantRepresentative fan regular hne D).mpr
    exact invariant (toricLineBundleInvariantCoefficients fan hne.coe_sort regular D.sheaf)

end ToricPower

end
