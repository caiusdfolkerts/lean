module

public import ToricPower.GeometricCore
public import ToricPower.RestrictedFan
public import ToricPower.FinitePushforward
public import ToricPower.Cohomology.SchemeBasic

/-! ## Literal sheaf and derived-category interfaces for the manuscript

These are the actual Cartier sheaf, ordinary finite pushforward, and ordinary
localization of complexes of sheaves of modules. The statement of generation
is a thick-envelope equality with bounded finite-presentation homology.
No generation theorem is assumed in this interface.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TauCeti.Toric
namespace ToricPower
universe u

/-- A chosen derived category constructed by Mathlib's standard localization.
This is a proved instance, not an additional mathematical hypothesis. -/
local instance standardSchemeDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard X.Modules

/-- Bounded complexes with coherent homology, on a Noetherian scheme.
Finite presentation is the literal local finite-presentation predicate on
sheaves of `𝒪_X`-modules. -/
def boundedCoherent (X : Scheme.{u}) : ObjectProperty (DerivedCategory X.Modules) :=
  fun K => (∃ a b : ℤ, K.IsGE a ∧ K.IsLE b) ∧
    ∀ j : ℤ, _root_.SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf)
      ((DerivedCategory.homologyFunctor X.Modules j).obj K)

/-- Classical generation of the bounded coherent category by an actual object:
its thick envelope, in the actual derived category, is exactly the bounded
coherent subcategory. -/
def classicallyGeneratesBoundedCoherent (X : Scheme.{u})
    (G : DerivedCategory X.Modules) : Prop :=
  (ObjectProperty.singleton G).triangEnvelope = boundedCoherent X

/-- Literal nonvanishing of total Zariski sheaf cohomology. All degrees occur;
for a sheaf in degree zero the negative derived cohomology groups vanish. -/
def totalCohomologyNonzero (X : Scheme.{u}) (M : X.Modules) : Prop :=
  ∃ p : ℕ, Nontrivial (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology M p)

/-- The zero sheaf has a finite presentation, obtained from the free sheaf on
an empty indexing type. This also applies to any sheaf isomorphic to zero. -/
theorem finitePresentation_of_isZero {X : Scheme.{u}} (M : X.Modules) (hM : IsZero M) :
    _root_.SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) M := by
  let F : X.Modules := _root_.SheafOfModules.free (R := X.ringCatSheaf) (PEmpty : Type u)
  have hF : IsZero F := by
    apply (IsZero.iff_id_eq_zero F).mpr
    apply (_root_.SheafOfModules.freeHomEquiv F).injective
    funext j
    exact PEmpty.elim j
  have hFP : _root_.SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) F := by
    dsimp only [F]
    infer_instance
  exact (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    (hF.iso hM) hFP

/-- A finitely presented sheaf, placed in degree zero, has bounded coherent
homology in the actual derived category. -/
theorem single_boundedCoherent (X : Scheme.{u}) (M : X.Modules)
    [_root_.SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) M] :
    boundedCoherent X ((DerivedCategory.singleFunctor X.Modules 0).obj M) := by
  refine ⟨⟨0, 0, inferInstance, inferInstance⟩, ?_⟩
  intro j
  by_cases hj : j = 0
  · subst j
    exact (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app M).symm
      (inferInstanceAs (_root_.SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) M))
  · apply finitePresentation_of_isZero
    obtain hlt | hgt := lt_or_gt_of_ne hj
    · exact (DerivedCategory.isGE_iff _ 0).mp inferInstance j hlt
    · exact (DerivedCategory.isLE_iff _ 0).mp inferInstance j hgt

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- Cartier divisors on the actual integral toric scheme; integrality is proved
from the nonempty fan, rather than postulated as data. -/
def toricCartierDivisor (Φ : Fan i) (hne : Φ.cones.Nonempty) : Type u :=
  letI := toricScheme_isIntegral Φ hne
  TauCeti.AlgebraicGeometry.Scheme.CartierDivisor Φ.algebraicRealization

/-- The genuine line bundle `𝒪_X(D)` of a Cartier divisor. -/
def toricDivisorSheaf (Φ : Fan i) (hne : Φ.cones.Nonempty)
    (D : toricCartierDivisor Φ hne) : Φ.algebraicRealization.Modules := by
  letI := toricScheme_isIntegral Φ hne
  exact TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheaf D

/-- The literal ordinary power-map direct image of the Cartier line bundle. -/
def toricPowerDivisorSheaf (Φ : Fan i) (hne : Φ.cones.Nonempty)
    (D : toricCartierDivisor Φ hne) (ell : ℕ) : Φ.algebraicRealization.Modules :=
  (Scheme.Modules.pushforward (toricPowerMap Φ ell)).obj (toricDivisorSheaf Φ hne D)

theorem toricDivisorSheaf_isFinitePresentation (Φ : Fan i) (hne : Φ.cones.Nonempty)
    (D : toricCartierDivisor Φ hne) :
    _root_.SheafOfModules.IsFinitePresentation (R := Φ.algebraicRealization.ringCatSheaf) (toricDivisorSheaf Φ hne D) := by
  letI := toricScheme_isIntegral Φ hne
  change _root_.SheafOfModules.IsFinitePresentation (R := Φ.algebraicRealization.ringCatSheaf)
    (TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheaf D)
  letI : TauCeti.SheafOfModules.IsInvertible
      (R := Φ.algebraicRealization.ringCatSheaf) D.sheaf := D.isInvertible_sheaf
  exact TauCeti.SheafOfModules.IsInvertible.isFinitePresentation (M := D.sheaf)

/-- Coherence of the literal finite pushforward; no monomial-splitting formula
or categorical generation hypothesis is used. -/
theorem toricPowerDivisorSheaf_isFinitePresentation (Φ : Fan i)
    (hreg : Φ.IsRegular) (hne : Φ.cones.Nonempty)
    (D : toricCartierDivisor Φ hne) (ell : ℕ) (hell : 0 < ell) :
    _root_.SheafOfModules.IsFinitePresentation (R := Φ.algebraicRealization.ringCatSheaf) (toricPowerDivisorSheaf Φ hne D ell) := by
  letI := toricScheme_isNoetherian Φ
  letI := toricPowerMap_finite Φ hreg ell hell
  letI := toricDivisorSheaf_isFinitePresentation Φ hne D
  letI : (toricDivisorSheaf Φ hne D).IsQuasicoherent :=
    _root_.SheafOfModules.instIsQuasicoherentOfIsFinitePresentation
      (toricDivisorSheaf Φ hne D)
  letI : (toricDivisorSheaf Φ hne D).IsFiniteType :=
    _root_.SheafOfModules.instIsFiniteTypeOfIsFinitePresentation
      (toricDivisorSheaf Φ hne D)
  exact Scheme.Modules.isFinitePresentation_pushforward_of_isFinite
    (toricPowerMap Φ ell) (toricDivisorSheaf Φ hne D)

/-- The actual degree-zero derived object appearing in Theorem 1.1. -/
def toricPowerDivisorObject (Φ : Fan i) (hne : Φ.cones.Nonempty)
    (D : toricCartierDivisor Φ hne) (ell : ℕ) :
    DerivedCategory Φ.algebraicRealization.Modules :=
  (DerivedCategory.singleFunctor Φ.algebraicRealization.Modules 0).obj
    (toricPowerDivisorSheaf Φ hne D ell)

theorem toricPowerDivisorObject_boundedCoherent (Φ : Fan i)
    (hreg : Φ.IsRegular) (hne : Φ.cones.Nonempty)
    (D : toricCartierDivisor Φ hne) (ell : ℕ) (hell : 0 < ell) :
    boundedCoherent Φ.algebraicRealization (toricPowerDivisorObject Φ hne D ell) := by
  letI := toricPowerDivisorSheaf_isFinitePresentation Φ hreg hne D ell hell
  exact single_boundedCoherent Φ.algebraicRealization (toricPowerDivisorSheaf Φ hne D ell)

/-- The exact generation assertion for exponent `ell`; a definition of the
unproved principal target, not a theorem claiming that it holds. -/
def toricPowerGenerates (Φ : Fan i) (hne : Φ.cones.Nonempty)
    (D : toricCartierDivisor Φ hne) (ell : ℕ) : Prop :=
  classicallyGeneratesBoundedCoherent Φ.algebraicRealization
    (toricPowerDivisorObject Φ hne D ell)

end ToricPower
end

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TauCeti.Toric
namespace ToricPower
universe u
variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The exact cohomological condition in Theorem 1.1, including every rational
linear subspace and all cohomological degrees. -/
def linearCohomologyCriterion (Φ : Fan i) (hne : Φ.cones.Nonempty)
    (D : toricCartierDivisor Φ hne) : Prop :=
  ∀ W : LinearSubspace Φ,
    totalCohomologyNonzero (restrictedFan Φ W.space W.rational).algebraicRealization
      ((Scheme.Modules.pullback (linearToricInclusion Φ W)).obj (toricDivisorSheaf Φ hne D))

/-- The complete principal assertion, recorded as a goal proposition.
There is deliberately no theorem asserting this proposition until the
remaining categorical dependency chain has a kernel-checked proof. The
regular-fan hypothesis is explicit, as required by the smoothness assumption. -/
def principalTheoremClaim (Φ : Fan i) (hne : Φ.cones.Nonempty)
    (D : toricCartierDivisor Φ hne) : Prop :=
  Φ.IsRegular →
  ((∃ ell : ℕ, 0 < ell ∧ toricPowerGenerates Φ hne D ell) ↔
    linearCohomologyCriterion Φ hne D) ∧
  (linearCohomologyCriterion Φ hne D →
    ∃ L : ℕ, 0 < L ∧ ∀ ell : ℕ, L ≤ ell → toricPowerGenerates Φ hne D ell)

end ToricPower
end

