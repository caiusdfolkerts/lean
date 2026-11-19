module

public import ToricPower.CechLaurentCoefficients

/-!
# The actual toric Čech complex in Laurent coordinates

This is an isomorphism of complete cochain complexes, not just an
identification of their terms. Every coface is the actual sheaf restriction,
and its comparison with the literal Laurent inclusion was proved on actual
sections. Neither completeness nor maximal cones occur.

Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open TauCeti.Toric
open scoped Classical Simplicial

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {Index : Type} (charts : Index → fan.cones) (b : fan.Ray → ℤ)

def toricCechLaurentDegree (degree : ℕ) : AddCommGrpCat :=
  ∏ᶜ (toricCechLaurentCoefficient fan charts b degree)

def toricCechLaurentTupleMap {degree next : ℕ}
    (selection : Fin (degree + 1) → Fin (next + 1)) :
    toricCechLaurentDegree fan charts b degree ⟶ toricCechLaurentDegree fan charts b next :=
  Limits.Pi.lift (fun tuple =>
    Limits.Pi.π (toricCechLaurentCoefficient fan charts b degree) (tuple ∘ selection) ≫
      toricCechLaurentRestriction fan charts b selection tuple)

/-- The actual Laurent inclusions satisfy every cosimplicial identity
because they retain the identical polynomial. -/
def toricCechLaurentCosimplicial : CosimplicialObject AddCommGrpCat where
  obj simplex := toricCechLaurentDegree fan charts b simplex.len
  map selection := toricCechLaurentTupleMap fan charts b selection.toOrderHom
  map_id simplex := by
    apply Limits.Pi.hom_ext
    intro tuple
    simp only [toricCechLaurentTupleMap, Limits.Pi.lift_comp_π, Category.id_comp]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro cochain
    rfl
  map_comp first second := by
    apply Limits.Pi.hom_ext
    intro tuple
    simp only [toricCechLaurentTupleMap, Category.assoc, Limits.Pi.lift_comp_π]
    rw [← Category.assoc, Limits.Pi.lift_comp_π]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro cochain
    rfl

def toricCechLaurentComplex : CochainComplex AddCommGrpCat ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.obj (toricCechLaurentCosimplicial fan charts b)

theorem toricCechLaurentComplex_d (degree : ℕ) :
    (toricCechLaurentComplex fan charts b).d degree (degree + 1) =
      ∑ deleted : Fin (degree + 2), (-1 : ℤ) ^ deleted.val •
        toricCechLaurentTupleMap fan charts b deleted.succAbove := by
  simp only [toricCechLaurentComplex, AlgebraicTopology.AlternatingCofaceMapComplex.obj,
    CochainComplex.of_d]
  rfl

variable (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)

/-- Mathlib's ordinary Čech complex of the actual invariant Cartier sheaf. -/
abbrev toricCechActualComplex : CochainComplex AddCommGrpCat ℕ :=
  letI := toricSchemeIntegral fan nonempty
  BondalThomsen.FiniteAffineCechHigherComparison.schemeCechComplex
    (toricCechChartOpen fan charts)
    (invariantCartierDivisor fan nonempty regular b).sheaf

def toricCechActualCoface (degree : ℕ) (deleted : Fin (degree + 2)) :
    (toricCechActualComplex fan charts b nonempty regular).X degree ⟶
      (toricCechActualComplex fan charts b nonempty regular).X (degree + 1) :=
  Limits.Pi.lift (fun tuple =>
    Limits.Pi.π (toricCechActualCoefficient fan charts nonempty regular b degree)
      (tuple ∘ deleted.succAbove) ≫
        toricCechActualRestriction fan charts nonempty regular b deleted.succAbove tuple)

theorem toricCechActualComplex_d (degree : ℕ) :
    (toricCechActualComplex fan charts b nonempty regular).d degree (degree + 1) =
      ∑ deleted : Fin (degree + 2), (-1 : ℤ) ^ deleted.val •
        toricCechActualCoface fan charts b nonempty regular degree deleted := by
  change (AlgebraicTopology.AlternatingCofaceMapComplex.obj _).d degree (degree + 1) = _
  dsimp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rw [CochainComplex.of_d]
  rfl

/-- Every actual degree object is identified by the genuine sectionwise
Laurent coefficient equivalence. -/
def toricCechLaurentDegreeIso (degree : ℕ) :
    (toricCechActualComplex fan charts b nonempty regular).X degree ≅
      (toricCechLaurentComplex fan charts b).X degree :=
  Limits.Pi.mapIso (fun tuple =>
    (toricCechCoefficientEquiv fan charts nonempty regular b degree tuple).toAddCommGrpIso)

/-- The degree isomorphisms commute with every actual coface. -/
theorem toricCechLaurentDegreeIso_coface (degree : ℕ) (deleted : Fin (degree + 2)) :
    (toricCechLaurentDegreeIso fan charts b nonempty regular degree).hom ≫
        toricCechLaurentTupleMap fan charts b deleted.succAbove =
      toricCechActualCoface fan charts b nonempty regular degree deleted ≫
        (toricCechLaurentDegreeIso fan charts b nonempty regular (degree + 1)).hom := by
  apply Limits.Pi.hom_ext
  intro tuple
  simp only [Category.assoc, toricCechLaurentTupleMap, toricCechActualCoface,
    Limits.Pi.lift_comp_π, Limits.Pi.lift_comp_π_assoc, toricCechLaurentDegreeIso,
    Limits.Pi.mapIso_hom_π, Limits.Pi.mapIso_hom_π_assoc]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro cochain
  exact (toricCechCoefficientEquiv_selection fan charts nonempty regular b
    deleted.succAbove tuple
    (Limits.Pi.π (toricCechActualCoefficient fan charts nonempty regular b degree)
      (tuple ∘ deleted.succAbove) cochain)).symm

/-- The complete ordinary Čech complex is isomorphic to the literal
Laurent coefficient complex, with all differentials retained. -/
def toricCechLaurentComplexIso :
    toricCechActualComplex fan charts b nonempty regular ≅ toricCechLaurentComplex fan charts b :=
  HomologicalComplex.Hom.isoOfComponents
    (toricCechLaurentDegreeIso fan charts b nonempty regular)
    (fun degree next related => by
      change degree + 1 = next at related
      subst next
      rw [toricCechLaurentComplex_d, toricCechActualComplex_d]
      simp only [comp_sum, sum_comp, comp_zsmul, zsmul_comp]
      apply Finset.sum_congr rfl
      intro deleted _
      exact congrArg (fun f => (-1 : ℤ) ^ deleted.val • f)
        (toricCechLaurentDegreeIso_coface fan charts b nonempty regular degree deleted))

end ToricPower
