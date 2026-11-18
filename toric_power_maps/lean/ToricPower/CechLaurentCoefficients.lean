module

public import ToricPower.CechToricCover

/-!
# Literal Laurent coefficients of the actual toric Čech sections

The coefficient module is a supported submodule of the finitely supported
functions on the full character lattice. It is identified with the actual
Cartier sheaf sections, and restriction to a face preserves every Laurent
coefficient. This retains the torus coordinates of lower-dimensional cones.

Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TauCeti.Toric
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)

/-- Coefficients on the full character lattice, with exactly the actual
chart divisor inequalities on their support. -/
abbrev ToricChartLaurentCoefficients (b : fan.Ray → ℤ) (cone : fan.cones) :=
  Finsupp.supported ℂ ℂ {m : N →+ ℤ | toricCharacterAllowed fan b cone m}

/-- Every actual Cartier section has a unique full Laurent coefficient
family; no adjoined formal sections occur in this equivalence. -/
def toricDivisorLaurentCoefficientsEquiv (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    Γ((invariantCartierDivisor fan nonempty regular b).sheaf,
      (fan.affineToricChartι cone).opensRange) ≃+
        ToricChartLaurentCoefficients fan b cone :=
  (toricDivisorSectionCoefficientsEquiv fan nonempty regular b cone).symm.trans
    ((Finsupp.domLCongr (R := ℂ) (toricChartWeightGlobalEquiv fan b cone)).toAddEquiv.trans
      (Finsupp.supportedEquivFinsupp (R := ℂ)
        {m : N →+ ℤ | toricCharacterAllowed fan b cone m}).symm.toAddEquiv)

@[simp]
theorem toricDivisorLaurentCoefficientsEquiv_single (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (cone : fan.cones)
    (m : ToricChartDivisorWeight fan b cone) (a : ℂ) :
    letI := toricSchemeIntegral fan nonempty
    (toricDivisorLaurentCoefficientsEquiv fan nonempty regular b cone
      (toricDivisorSectionCoefficientsEquiv fan nonempty regular b cone
        (Finsupp.single m a))).val = Finsupp.single m.val a := by
  letI := toricSchemeIntegral fan nonempty
  change ((Finsupp.supportedEquivFinsupp (R := ℂ)
      {m : N →+ ℤ | toricCharacterAllowed fan b cone m}).symm
      (Finsupp.domLCongr (R := ℂ) (toricChartWeightGlobalEquiv fan b cone)
        ((toricDivisorSectionCoefficientsEquiv fan nonempty regular b cone).symm
          (toricDivisorSectionCoefficientsEquiv fan nonempty regular b cone
            (Finsupp.single m a)))) : (N →+ ℤ) →₀ ℂ) = _
  rw [AddEquiv.symm_apply_apply, Finsupp.domLCongr_single]
  exact Finsupp.supportedEquivFinsupp_symm_single _ _ _

/-- Restriction of supported coefficient families is literally the
identity on the Laurent polynomial. -/
def toricLaurentCoefficientRestriction (b : fan.Ray → ℤ)
    {face cone : fan.cones} (included : face ≤ cone) :
    ToricChartLaurentCoefficients fan b cone →+
      ToricChartLaurentCoefficients fan b face where
  toFun p := ⟨p.val, (Finsupp.mem_supported ℂ p.val).mpr (by
    intro m hm ray onFace
    exact ((Finsupp.mem_supported ℂ p.val).mp p.property) hm ray (onFace.trans included))⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem toricLaurentCoefficientRestriction_val (b : fan.Ray → ℤ)
    {face cone : fan.cones} (included : face ≤ cone)
    (p : ToricChartLaurentCoefficients fan b cone) :
    (toricLaurentCoefficientRestriction fan b included p).val = p.val := rfl

/-- The actual sheaf restriction preserves the full Laurent polynomial
in all characters, including those perpendicular to all fan rays. -/
theorem toricDivisorLaurentCoefficientsEquiv_restrict (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ)
    {face cone : fan.cones} (included : face ≤ cone)
    (s : letI := toricSchemeIntegral fan nonempty
      Γ((invariantCartierDivisor fan nonempty regular b).sheaf,
        (fan.affineToricChartι cone).opensRange)) :
    letI := toricSchemeIntegral fan nonempty
    toricDivisorLaurentCoefficientsEquiv fan nonempty regular b face
      ((invariantCartierDivisor fan nonempty regular b).sheaf.presheaf.map
        (homOfLE (toricCechChartOpen_mono fan included)).op s) =
    toricLaurentCoefficientRestriction fan b included
      (toricDivisorLaurentCoefficientsEquiv fan nonempty regular b cone s) := by
  letI := toricSchemeIntegral fan nonempty
  obtain ⟨p, rfl⟩ :=
    (toricDivisorSectionCoefficientsEquiv fan nonempty regular b cone).surjective s
  rw [toricDivisorSectionCoefficientsEquiv_restrict fan nonempty regular b included]
  apply Subtype.ext
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
    simpa only [Finsupp.mapDomain_add, map_add, Submodule.coe_add,
      toricLaurentCoefficientRestriction_val, hp, hq]
  | single m a =>
    rw [Finsupp.mapDomain_single, toricDivisorLaurentCoefficientsEquiv_single,
      toricLaurentCoefficientRestriction_val, toricDivisorLaurentCoefficientsEquiv_single]
    rfl

/-- Equality of open subsets induces the actual equality transport on
section objects. -/
def toricSectionOpenEquiv (X : Scheme) (F : X.Modules)
    {U W : X.Opens} (h : U = W) :
    F.presheaf.obj (op U) ≃+ F.presheaf.obj (op W) :=
  (eqToIso (congrArg (fun U => F.presheaf.obj (op U)) h)).addCommGroupIsoToAddEquiv

/-- Actual restriction commutes with equality transport of its opens. -/
theorem toricSectionOpenEquiv_restrict (X : Scheme) (F : X.Modules)
    {U U' W W' : X.Opens} (h : U = W) (h' : U' = W')
    (actual : U' ≤ U) (chart : W' ≤ W) (s : F.presheaf.obj (op U)) :
    toricSectionOpenEquiv X F h' (F.presheaf.map (homOfLE actual).op s) =
      F.presheaf.map (homOfLE chart).op (toricSectionOpenEquiv X F h s) := by
  subst U
  subst U'
  rfl

variable {Index : Type} (charts : Index → fan.cones)

/-- The literal sections appearing in a degree of Mathlib's actual Čech
complex, with no replacement of the coefficient sheaf. -/
abbrev toricCechActualCoefficient (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Index) : AddCommGrpCat :=
  letI := toricSchemeIntegral fan nonempty
  (invariantCartierDivisor fan nonempty regular b).sheaf.presheaf.obj
    (op (BondalThomsen.FiniteAffineCechHigherComparison.cechIntersection
      (toricCechChartOpen fan charts) degree tuple))

abbrev toricCechLaurentCoefficient (b : fan.Ray → ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Index) : AddCommGrpCat :=
  AddCommGrpCat.of (ToricChartLaurentCoefficients fan b
    (toricCechCone fan charts degree tuple))

/-- An actual coefficient isomorphism from the ordinary Čech section
object to its literal Laurent coefficient object. -/
def toricCechCoefficientEquiv (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Index) :
    toricCechActualCoefficient fan charts nonempty regular b degree tuple ≃+
      toricCechLaurentCoefficient fan charts b degree tuple := by
  letI := toricSchemeIntegral fan nonempty
  let D := invariantCartierDivisor fan nonempty regular b
  exact (toricSectionOpenEquiv fan.algebraicRealization D.sheaf
      (toricCechIntersection_eq_chart fan charts degree tuple)).trans
    (toricDivisorLaurentCoefficientsEquiv fan nonempty regular b
      (toricCechCone fan charts degree tuple))

/-- The coefficient map associated to any tuple selection leaves each
Laurent coefficient unchanged. -/
def toricCechLaurentRestriction (b : fan.Ray → ℤ) {degree next : ℕ}
    (selection : Fin (degree + 1) → Fin (next + 1))
    (tuple : Fin (next + 1) → Index) :
    toricCechLaurentCoefficient fan charts b degree (tuple ∘ selection) ⟶
      toricCechLaurentCoefficient fan charts b next tuple :=
  AddCommGrpCat.ofHom (toricLaurentCoefficientRestriction fan b
    (toricCechCone_le_selection fan charts selection tuple))

/-- The actual restriction map used by the ordinary Čech cosimplicial
object, for an arbitrary selection of tuple positions. -/
def toricCechActualRestriction (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) {degree next : ℕ}
    (selection : Fin (degree + 1) → Fin (next + 1))
    (tuple : Fin (next + 1) → Index) :
    toricCechActualCoefficient fan charts nonempty regular b degree (tuple ∘ selection) ⟶
      toricCechActualCoefficient fan charts nonempty regular b next tuple :=
  letI := toricSchemeIntegral fan nonempty
  (invariantCartierDivisor fan nonempty regular b).sheaf.presheaf.map
    (Limits.Pi.lift (fun column : Fin (degree + 1) =>
      Limits.Pi.π (toricCechChartOpen fan charts ∘ tuple) (selection column))).op

/-- The genuine Čech restriction becomes the literal Laurent inclusion
under the actual coefficient equivalences, in every cosimplicial degree. -/
theorem toricCechCoefficientEquiv_selection (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) {degree next : ℕ}
    (selection : Fin (degree + 1) → Fin (next + 1))
    (tuple : Fin (next + 1) → Index)
    (s : toricCechActualCoefficient fan charts nonempty regular b degree (tuple ∘ selection)) :
    toricCechCoefficientEquiv fan charts nonempty regular b next tuple
      (toricCechActualRestriction fan charts nonempty regular b selection tuple s) =
    toricCechLaurentRestriction fan charts b selection tuple
      (toricCechCoefficientEquiv fan charts nonempty regular b degree (tuple ∘ selection) s) := by
  letI := toricSchemeIntegral fan nonempty
  let D := invariantCartierDivisor fan nonempty regular b
  let actual := (Limits.Pi.lift (fun column : Fin (degree + 1) =>
    Limits.Pi.π (toricCechChartOpen fan charts ∘ tuple) (selection column))).le
  let included := toricCechCone_le_selection fan charts selection tuple
  have transported := toricSectionOpenEquiv_restrict fan.algebraicRealization D.sheaf
    (toricCechIntersection_eq_chart fan charts degree (tuple ∘ selection))
    (toricCechIntersection_eq_chart fan charts next tuple)
    actual (toricCechChartOpen_mono fan included) s
  change toricDivisorLaurentCoefficientsEquiv fan nonempty regular b
      (toricCechCone fan charts next tuple)
      (toricSectionOpenEquiv fan.algebraicRealization D.sheaf
        (toricCechIntersection_eq_chart fan charts next tuple)
        (D.sheaf.presheaf.map (homOfLE actual).op s)) =
    toricLaurentCoefficientRestriction fan b included
      (toricDivisorLaurentCoefficientsEquiv fan nonempty regular b
        (toricCechCone fan charts degree (tuple ∘ selection))
        (toricSectionOpenEquiv fan.algebraicRealization D.sheaf
          (toricCechIntersection_eq_chart fan charts degree (tuple ∘ selection)) s))
  exact (congrArg (toricDivisorLaurentCoefficientsEquiv fan nonempty regular b
    (toricCechCone fan charts next tuple)) transported).trans
      (toricDivisorLaurentCoefficientsEquiv_restrict fan nonempty regular b included _)

end ToricPower
