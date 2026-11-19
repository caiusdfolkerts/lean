module

public import ToricPower.LinearRelativeCechComparison
public import ToricPower.ArrangementWeightedIncidence
public import ToricPower.ArrangementCartierDiagram
public import ToricPower.CechCharacterComplex

/-!
# The actual character-graded Čech diagram on the universal arrangement

An object `(c,m)` consists of a normalized cell and an arbitrary integral
weight. Its coefficient is the full relative Čech complex for the
character `-m` of `O(b) ⊗ L(c)⁻¹`. An incidence with translation `a`
changes the weight to `m+a`; its map is the literal inclusion of allowed
tuple coefficients. These maps retain the scalar action, all cochain
degrees, and all lattice translates.

This constructs a diagram before passing to a derived category. The
comparison with the additive toric character complex is an isomorphism
of complexes, rather than an identification of dimensions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V} (fan : Fan latticeMap)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ))
  (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "W" => WeightedIncidenceObject A

/-- The target divisor minus the actual right Cartier label. -/
def arrangementLiftedCechCoefficients (b : fan.Ray → ℤ) (c : IncidenceObject A) :
    fan.Ray → ℤ :=
  b - diagonalRightCoefficients fan basis rays c.2

/-- The sign records precomposition by the actual character `χ^(-a)`. -/
def arrangementLiftedCechNegative (b : fan.Ray → ℤ) (c : W) : fan.Ray → Prop :=
  toricCharacterNegative fan (arrangementLiftedCechCoefficients fan basis rays b c.1)
    (-(basis.equivFun.symm c.2))

/-- Cartier regularity proves that every forbidden target ray is
already forbidden at the source of the weighted incidence. -/
theorem arrangementLiftedCechNegative_antitone (b : fan.Ray → ℤ)
    {c d : W} (f : c ⟶ d) (ρ : fan.Ray) :
    arrangementLiftedCechNegative fan basis rays b d ρ →
      arrangementLiftedCechNegative fan basis rays b c ρ := by
  have regularity := (diagonalEntryRegular_of_incidence fan basis rays f.val).2 ρ
  have weight : basis.equivFun.symm d.2 (fanRayPrimitiveGenerator fan ρ) =
      basis.equivFun.symm c.2 (fanRayPrimitiveGenerator fan ρ) +
        basis.equivFun.symm f.val.val (fanRayPrimitiveGenerator fan ρ) := by
    simpa only [map_add, AddMonoidHom.add_apply] using
      congrArg (fun m => basis.equivFun.symm m (fanRayPrimitiveGenerator fan ρ)) f.property
  simp only [arrangementLiftedCechNegative, toricCharacterNegative,
    arrangementLiftedCechCoefficients, Pi.sub_apply, AddMonoidHom.neg_apply]
  omega

variable {Index : Type} (charts : Index → fan.cones) (b : fan.Ray → ℤ)

/-- The genuine scalar-linear Čech diagram over all integral cell lifts. -/
def arrangementLiftedCech : W ⥤ CochainComplex (ModuleCat ℂ) ℕ :=
  LinearRelativeCech.complexDiagram ℂ (toricCechRayIncidence fan charts)
    (arrangementLiftedCechNegative fan basis rays b)
    (fun f => arrangementLiftedCechNegative_antitone fan basis rays b f)

/-- At every lift, forgetting scalars gives exactly the established
toric weight complex, including its differential. -/
def arrangementLiftedCechForgetIso (c : W) :
    toricCechWeightComplex fan charts
        (arrangementLiftedCechCoefficients fan basis rays b c.1)
        (-(basis.equivFun.symm c.2)) ≅
      ((forget₂ (ModuleCat ℂ) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj
        ((arrangementLiftedCech fan basis rays charts b).obj c) :=
  LinearRelativeCech.complexForgetIso ℂ (toricCechRayIncidence fan charts)
    (arrangementLiftedCechNegative fan basis rays b c)

/-- In particular, the nonzero character cohomology is unchanged. -/
theorem arrangementLiftedCech_nontrivial_iff (c : W) (q : ℕ) :
    Nontrivial (((arrangementLiftedCech fan basis rays charts b).obj c).homology q) ↔
      Nontrivial ((toricCechWeightComplex fan charts
        (arrangementLiftedCechCoefficients fan basis rays b c.1)
        (-(basis.equivFun.symm c.2))).homology q) :=
  LinearRelativeCech.homology_nontrivial_iff ℂ (toricCechRayIncidence fan charts)
    (arrangementLiftedCechNegative fan basis rays b c) q

end ToricPower

end
