module

public import ToricPower.CechToricComplex

/-!
# Actual character summands of the toric Čech complex

A character is extracted by its literal Laurent coefficient and inserted
as its literal monomial. These maps commute with every Čech restriction.
Their split composite identifies the corresponding character summand
with the relative incidence complex of the negative rays. No reduced
simplicial-cohomology comparison is assumed here.

Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open TauCeti.Toric
open scoped Classical BigOperators

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {Index : Type} (charts : Index → fan.cones) (b : fan.Ray → ℤ) (m : N →+ ℤ)

abbrev toricCechWeightCoefficient (degree : ℕ) (tuple : Fin (degree + 1) → Index) :=
  NegativeSupportCech.relativeScalarCoefficient ℂ (toricCechRayIncidence fan charts)
    (toricCharacterNegative fan b m) degree tuple

/-- Insert a scalar as the actual Laurent monomial of the selected
character. A forbidden tuple forces that scalar to be zero. -/
def toricCechWeightScalarToLaurent (degree : ℕ) (tuple : Fin (degree + 1) → Index) :
    toricCechWeightCoefficient fan charts b m degree tuple →+
      toricCechLaurentCoefficient fan charts b degree tuple where
  toFun scalar := ⟨Finsupp.single m scalar.val, by
    by_cases available : toricCharacterAllowed fan b (toricCechCone fan charts degree tuple) m
    · exact Finsupp.single_mem_supported ℂ scalar.val available
    · have forbidden : NegativeSupportCech.tupleForbidden (toricCechRayIncidence fan charts)
          (toricCharacterNegative fan b m) degree tuple := by
        by_contra h
        exact available ((toricCechCharacterAllowed_iff_not_forbidden fan charts b m degree tuple).mpr h)
      rw [scalar.property forbidden, Finsupp.single_zero]
      exact (ToricChartLaurentCoefficients fan b (toricCechCone fan charts degree tuple)).zero_mem⟩
  map_zero' := by apply Subtype.ext; exact Finsupp.single_zero _
  map_add' first second := by apply Subtype.ext; exact Finsupp.single_add _ _ _

/-- Extract the literal coefficient of the selected character. The
actual support inequality makes it zero on every forbidden tuple. -/
def toricCechWeightLaurentToScalar (degree : ℕ) (tuple : Fin (degree + 1) → Index) :
    toricCechLaurentCoefficient fan charts b degree tuple →+
      toricCechWeightCoefficient fan charts b m degree tuple where
  toFun p := ⟨p.val m, by
    intro forbidden
    apply (Finsupp.mem_supported' ℂ p.val).mp p.property m
    intro available
    exact (toricCechCharacterAllowed_iff_not_forbidden fan charts b m degree tuple).mp
      available forbidden⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem toricCechWeight_coefficient_split (degree : ℕ)
    (tuple : Fin (degree + 1) → Index)
    (scalar : toricCechWeightCoefficient fan charts b m degree tuple) :
    toricCechWeightLaurentToScalar fan charts b m degree tuple
      (toricCechWeightScalarToLaurent fan charts b m degree tuple scalar) = scalar := by
  apply Subtype.ext
  exact Finsupp.single_eq_same

/-- Both coordinate maps commute with every tuple selection because the
Laurent restriction is literally the identity on coefficients. -/
theorem toricCechWeight_inclusion_selection {degree next : ℕ}
    (selection : Fin (degree + 1) → Fin (next + 1))
    (tuple : Fin (next + 1) → Index)
    (scalar : toricCechWeightCoefficient fan charts b m degree (tuple ∘ selection)) :
    toricCechLaurentRestriction fan charts b selection tuple
      (toricCechWeightScalarToLaurent fan charts b m degree (tuple ∘ selection) scalar) =
    toricCechWeightScalarToLaurent fan charts b m next tuple
      (NegativeSupportCech.relativeScalarRestriction ℂ (toricCechRayIncidence fan charts)
        (toricCharacterNegative fan b m) selection tuple scalar) := rfl

theorem toricCechWeight_retraction_selection {degree next : ℕ}
    (selection : Fin (degree + 1) → Fin (next + 1))
    (tuple : Fin (next + 1) → Index)
    (p : toricCechLaurentCoefficient fan charts b degree (tuple ∘ selection)) :
    NegativeSupportCech.relativeScalarRestriction ℂ (toricCechRayIncidence fan charts)
        (toricCharacterNegative fan b m) selection tuple
        (toricCechWeightLaurentToScalar fan charts b m degree (tuple ∘ selection) p) =
      toricCechWeightLaurentToScalar fan charts b m next tuple
        (toricCechLaurentRestriction fan charts b selection tuple p) := rfl

/-- The exact incidence complex associated to one genuine character. -/
abbrev toricCechWeightComplex : CochainComplex AddCommGrpCat ℕ :=
  NegativeSupportCech.relativeComplex ℂ (toricCechRayIncidence fan charts)
    (toricCharacterNegative fan b m)

def toricCechWeightDegreeInclusion (degree : ℕ) :
    (toricCechWeightComplex fan charts b m).X degree ⟶
      (toricCechLaurentComplex fan charts b).X degree :=
  Limits.Pi.map (fun tuple => AddCommGrpCat.ofHom
    (toricCechWeightScalarToLaurent fan charts b m degree tuple))

def toricCechWeightDegreeRetraction (degree : ℕ) :
    (toricCechLaurentComplex fan charts b).X degree ⟶
      (toricCechWeightComplex fan charts b m).X degree :=
  Limits.Pi.map (fun tuple => AddCommGrpCat.ofHom
    (toricCechWeightLaurentToScalar fan charts b m degree tuple))

theorem toricCechWeight_degree_split (degree : ℕ) :
    toricCechWeightDegreeInclusion fan charts b m degree ≫
      toricCechWeightDegreeRetraction fan charts b m degree =
        𝟙 ((toricCechWeightComplex fan charts b m).X degree) := by
  rw [toricCechWeightDegreeInclusion, toricCechWeightDegreeRetraction,
    Limits.Pi.map_comp_map]
  apply Limits.Pi.hom_ext
  intro tuple
  simp only [Limits.Pi.map_π, Category.id_comp]
  have component : AddCommGrpCat.ofHom
      (toricCechWeightScalarToLaurent fan charts b m degree tuple) ≫
        AddCommGrpCat.ofHom (toricCechWeightLaurentToScalar fan charts b m degree tuple) =
      𝟙 (NegativeSupportCech.relativeCoefficient ℂ (toricCechRayIncidence fan charts)
        (toricCharacterNegative fan b m) degree tuple) := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    exact toricCechWeight_coefficient_split fan charts b m degree tuple
  rw [component]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Product naturality applied to the proved scalar/monomial restriction
square; this is a general categorical calculation. -/
theorem cechProductMaps_restriction {I J : Type}
    (source target : I → AddCommGrpCat) (nextSource nextTarget : J → AddCommGrpCat)
    (maps : ∀ index, source index ⟶ target index)
    (nextMaps : ∀ tuple, nextSource tuple ⟶ nextTarget tuple)
    (selection : J → I)
    (sourceRestriction : ∀ tuple, source (selection tuple) ⟶ nextSource tuple)
    (targetRestriction : ∀ tuple, target (selection tuple) ⟶ nextTarget tuple)
    (compatible : ∀ tuple, maps (selection tuple) ≫ targetRestriction tuple =
      sourceRestriction tuple ≫ nextMaps tuple) :
    Limits.Pi.map maps ≫
        Limits.Pi.lift (fun tuple => Limits.Pi.π target (selection tuple) ≫ targetRestriction tuple) =
      Limits.Pi.lift (fun tuple => Limits.Pi.π source (selection tuple) ≫ sourceRestriction tuple) ≫
        Limits.Pi.map nextMaps := by
  apply Limits.Pi.hom_ext (f := nextTarget)
  intro tuple
  simp only [Category.assoc, Limits.Pi.lift_comp_π, Limits.Pi.lift_comp_π_assoc,
    Limits.Pi.map_π, Limits.Pi.map_π_assoc]
  rw [compatible]

theorem toricCechWeightDegreeInclusion_coface (degree : ℕ) (deleted : Fin (degree + 2)) :
    toricCechWeightDegreeInclusion fan charts b m degree ≫
        toricCechLaurentTupleMap fan charts b deleted.succAbove =
      NegativeSupportCech.relativeTupleMap ℂ (toricCechRayIncidence fan charts)
          (toricCharacterNegative fan b m) deleted.succAbove ≫
        toricCechWeightDegreeInclusion fan charts b m (degree + 1) := by
  apply cechProductMaps_restriction
  intro tuple
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  exact toricCechWeight_inclusion_selection fan charts b m deleted.succAbove tuple

theorem toricCechWeightDegreeRetraction_coface (degree : ℕ) (deleted : Fin (degree + 2)) :
    toricCechWeightDegreeRetraction fan charts b m degree ≫
        NegativeSupportCech.relativeTupleMap ℂ (toricCechRayIncidence fan charts)
          (toricCharacterNegative fan b m) deleted.succAbove =
      toricCechLaurentTupleMap fan charts b deleted.succAbove ≫
        toricCechWeightDegreeRetraction fan charts b m (degree + 1) := by
  apply cechProductMaps_restriction
  intro tuple
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  exact toricCechWeight_retraction_selection fan charts b m deleted.succAbove tuple

def toricCechWeightInclusion :
    toricCechWeightComplex fan charts b m ⟶ toricCechLaurentComplex fan charts b :=
  CochainComplex.ofHom (toricCechWeightDegreeInclusion fan charts b m)
    (fun degree => by
      rw [toricCechLaurentComplex_d, NegativeSupportCech.relativeComplex_d,
        comp_sum, sum_comp]
      apply Finset.sum_congr rfl
      intro deleted _
      rw [comp_zsmul, zsmul_comp, toricCechWeightDegreeInclusion_coface])

def toricCechWeightRetraction :
    toricCechLaurentComplex fan charts b ⟶ toricCechWeightComplex fan charts b m :=
  CochainComplex.ofHom (toricCechWeightDegreeRetraction fan charts b m)
    (fun degree => by
      rw [toricCechLaurentComplex_d, NegativeSupportCech.relativeComplex_d,
        comp_sum, sum_comp]
      apply Finset.sum_congr rfl
      intro deleted _
      rw [comp_zsmul, zsmul_comp, toricCechWeightDegreeRetraction_coface])

/-- The incidence complex is a genuine split character summand of the
actual Laurent Čech complex, in every cohomological degree. -/
theorem toricCechWeight_split :
    toricCechWeightInclusion fan charts b m ≫ toricCechWeightRetraction fan charts b m = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext degree
  exact toricCechWeight_degree_split fan charts b m degree

end ToricPower
