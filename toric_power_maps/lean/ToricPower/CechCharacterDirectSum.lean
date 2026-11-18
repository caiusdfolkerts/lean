module

public import ToricPower.CechCharacterComplex
public import ToricPower.CechDirectSumHomology

/-!
# The actual finite-support character decomposition

For a finite toric affine cover, every cochain has only finitely many
characters across all its finitely many coordinates. This gives an actual
direct-sum isomorphism of complexes, followed by the genuine AB4 homology
comparison. No complete-fan or full-dimensional-cone hypothesis occurs.

Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open TauCeti.Toric
open scoped Classical BigOperators DirectSum

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {Index : Type} (charts : Index → fan.cones) (b : fan.Ray → ℤ)

/-- The literal coefficient projection followed by the literal monomial insertion. -/
def toricCechWeightCoefficientProjector (m : N →+ ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Index) :
    toricCechLaurentCoefficient fan charts b degree tuple →+
      toricCechLaurentCoefficient fan charts b degree tuple :=
  (toricCechWeightScalarToLaurent fan charts b m degree tuple).comp
    (toricCechWeightLaurentToScalar fan charts b m degree tuple)

@[simp]
theorem toricCechWeightCoefficientProjector_val (m : N →+ ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Index)
    (p : toricCechLaurentCoefficient fan charts b degree tuple) :
    (toricCechWeightCoefficientProjector fan charts b m degree tuple p).val =
      Finsupp.single m (p.val m) := rfl

theorem toricCechWeightCoefficientProjector_eq_zero (m : N →+ ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Index)
    (p : toricCechLaurentCoefficient fan charts b degree tuple) (absent : m ∉ p.val.support) :
    toricCechWeightCoefficientProjector fan charts b m degree tuple p = 0 := by
  apply Subtype.ext
  rw [toricCechWeightCoefficientProjector_val, Finsupp.notMem_support_iff.mp absent,
    Finsupp.single_zero]
  rfl

theorem toricCechWeightCoefficientProjector_sum_support (degree : ℕ)
    (tuple : Fin (degree + 1) → Index)
    (p : toricCechLaurentCoefficient fan charts b degree tuple) :
    ∑ m ∈ p.val.support, toricCechWeightCoefficientProjector fan charts b m degree tuple p = p := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  simp only [toricCechWeightCoefficientProjector_val]
  exact Finsupp.sum_single p.val

theorem toricCechWeightCoefficientProjector_sum_of_support_subset (degree : ℕ)
    (tuple : Fin (degree + 1) → Index)
    (p : toricCechLaurentCoefficient fan charts b degree tuple)
    (weights : Finset (N →+ ℤ)) (supported : p.val.support ⊆ weights) :
    ∑ m ∈ weights, toricCechWeightCoefficientProjector fan charts b m degree tuple p = p := by
  calc
    _ = ∑ m ∈ p.val.support,
        toricCechWeightCoefficientProjector fan charts b m degree tuple p :=
      (Finset.sum_subset supported (fun m _ absent =>
        toricCechWeightCoefficientProjector_eq_zero fan charts b m degree tuple p absent)).symm
    _ = p := toricCechWeightCoefficientProjector_sum_support fan charts b degree tuple p

/-- Distinct characters are genuinely orthogonal in each Laurent coefficient module. -/
theorem toricCechWeight_coefficient_other (first second : N →+ ℤ)
    (different : first ≠ second) (degree : ℕ) (tuple : Fin (degree + 1) → Index)
    (scalar : toricCechWeightCoefficient fan charts b first degree tuple) :
    toricCechWeightLaurentToScalar fan charts b second degree tuple
      (toricCechWeightScalarToLaurent fan charts b first degree tuple scalar) = 0 := by
  apply Subtype.ext
  change (Finsupp.single first scalar.val) second = 0
  exact Finsupp.single_eq_of_ne different.symm

theorem toricCechWeight_degree_other (first second : N →+ ℤ)
    (different : first ≠ second) (degree : ℕ) :
    toricCechWeightDegreeInclusion fan charts b first degree ≫
      toricCechWeightDegreeRetraction fan charts b second degree = 0 := by
  change Limits.Pi.map _ ≫ Limits.Pi.map _ = _
  rw [Limits.Pi.map_comp_map]
  apply Limits.Pi.hom_ext
  intro tuple
  rw [Limits.Pi.map_π]
  have composite : AddCommGrpCat.ofHom
      (toricCechWeightScalarToLaurent fan charts b first degree tuple) ≫
      AddCommGrpCat.ofHom
        (toricCechWeightLaurentToScalar fan charts b second degree tuple) =
      (0 : NegativeSupportCech.relativeCoefficient ℂ (toricCechRayIncidence fan charts)
          (toricCharacterNegative fan b first) degree tuple ⟶
        NegativeSupportCech.relativeCoefficient ℂ (toricCechRayIncidence fan charts)
          (toricCharacterNegative fan b second) degree tuple) := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    exact toricCechWeight_coefficient_other fan charts b first second different degree tuple
  rw [composite]
  simp only [comp_zero, zero_comp]

def toricCechWeightDegreeProjector (m : N →+ ℤ) (degree : ℕ) :
    (toricCechLaurentComplex fan charts b).X degree ⟶
      (toricCechLaurentComplex fan charts b).X degree :=
  toricCechWeightDegreeRetraction fan charts b m degree ≫
    toricCechWeightDegreeInclusion fan charts b m degree

theorem toricCechWeightDegreeProjector_coordinate (m : N →+ ℤ) (degree : ℕ)
    (p : (toricCechLaurentComplex fan charts b).X degree)
    (tuple : Fin (degree + 1) → Index) :
    Limits.Pi.π (toricCechLaurentCoefficient fan charts b degree) tuple
        (toricCechWeightDegreeProjector fan charts b m degree p) =
      toricCechWeightCoefficientProjector fan charts b m degree tuple
        (Limits.Pi.π (toricCechLaurentCoefficient fan charts b degree) tuple p) := by
  have equality : toricCechWeightDegreeProjector fan charts b m degree =
      Limits.Pi.map (fun tuple => AddCommGrpCat.ofHom
        (toricCechWeightCoefficientProjector fan charts b m degree tuple)) := by
    unfold toricCechWeightDegreeProjector toricCechWeightDegreeRetraction
      toricCechWeightDegreeInclusion
    rw [Limits.Pi.map_comp_map]
    rfl
  rw [equality]
  exact ConcreteCategory.congr_hom (Limits.Pi.map_π _ tuple) p

section FiniteCover

variable [Fintype Index]

/-- A genuine finite union of the finite supports of all cochain coordinates. -/
def toricCechDegreeCharacterSupport (degree : ℕ)
    (p : (toricCechLaurentComplex fan charts b).X degree) : Finset (N →+ ℤ) :=
  Finset.univ.biUnion (fun tuple =>
    (Limits.Pi.π (toricCechLaurentCoefficient fan charts b degree) tuple p).val.support)

theorem toricCechWeightDegreeProjector_sum_support (degree : ℕ)
    (p : (toricCechLaurentComplex fan charts b).X degree) :
    ∑ m ∈ toricCechDegreeCharacterSupport fan charts b degree p,
      toricCechWeightDegreeProjector fan charts b m degree p = p := by
  apply (Concrete.productEquiv (toricCechLaurentCoefficient fan charts b degree)).injective
  funext tuple
  simp only [Concrete.productEquiv_apply_apply]
  rw [map_sum]
  refine (Finset.sum_congr rfl (fun m _ =>
    toricCechWeightDegreeProjector_coordinate fan charts b m degree p tuple)).trans ?_
  apply toricCechWeightCoefficientProjector_sum_of_support_subset
  intro m supported
  exact Finset.mem_biUnion.mpr ⟨tuple, Finset.mem_univ _, supported⟩

end FiniteCover

/-- The literal direct sum, indexed by the entire character lattice. -/
abbrev ToricCechCharacterSumDegree (degree : ℕ) :=
  DirectSum (N →+ ℤ) (fun m => ↑((toricCechWeightComplex fan charts b m).X degree))

def toricCechCharacterSumComplex : CochainComplex AddCommGrpCat ℕ :=
  (CechDirectSumHomology.directSumFunctor.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (CechDirectSumHomology.familyComplex (toricCechWeightComplex fan charts b))

def toricCechCharacterSumDegreeMap (degree : ℕ) :
    ToricCechCharacterSumDegree fan charts b degree →+
      (toricCechLaurentComplex fan charts b).X degree :=
  DirectSum.toAddMonoid
    (β := fun m => ↑((toricCechWeightComplex fan charts b m).X degree))
    (fun m => (toricCechWeightDegreeInclusion fan charts b m degree).hom)

@[simp]
theorem toricCechCharacterSumDegreeMap_of (degree : ℕ) (m : N →+ ℤ)
    (scalar : (toricCechWeightComplex fan charts b m).X degree) :
    toricCechCharacterSumDegreeMap fan charts b degree
      (DirectSum.of (fun m => ↑((toricCechWeightComplex fan charts b m).X degree)) m scalar) =
        toricCechWeightDegreeInclusion fan charts b m degree scalar :=
  DirectSum.toAddMonoid_of _ _ _

theorem toricCechCharacterSumDegreeMap_retraction (degree : ℕ) (m : N →+ ℤ)
    (p : ToricCechCharacterSumDegree fan charts b degree) :
    toricCechWeightDegreeRetraction fan charts b m degree
      (toricCechCharacterSumDegreeMap fan charts b degree p) = p m := by
  induction p using DirectSum.induction_on with
  | zero => simp only [map_zero, DirectSum.zero_apply]
  | of other scalar =>
    simp only [toricCechCharacterSumDegreeMap, DirectSum.of_apply]
    rw [DirectSum.toAddMonoid_of]
    by_cases same : other = m
    · subst other
      simpa using ConcreteCategory.congr_hom
        (toricCechWeight_degree_split fan charts b m degree) scalar
    · simp only [dite_eq_right same]
      exact ConcreteCategory.congr_hom
        (toricCechWeight_degree_other fan charts b other m same degree) scalar
  | add first second first_eq second_eq =>
    simp only [map_add, DirectSum.add_apply, first_eq, second_eq]

theorem toricCechCharacterSumDegreeMap_d (degree next : ℕ) :
    AddCommGrpCat.ofHom (toricCechCharacterSumDegreeMap fan charts b degree) ≫
      (toricCechLaurentComplex fan charts b).d degree next =
    (toricCechCharacterSumComplex fan charts b).d degree next ≫
      AddCommGrpCat.ofHom (toricCechCharacterSumDegreeMap fan charts b next) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro p
  induction p using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of m scalar =>
    change (toricCechLaurentComplex fan charts b).d degree next
        (toricCechCharacterSumDegreeMap fan charts b degree (DirectSum.of _ m scalar)) =
      toricCechCharacterSumDegreeMap fan charts b next
        (DirectSum.map (fun m => ((toricCechWeightComplex fan charts b m).d degree next).hom)
          (DirectSum.of _ m scalar))
    rw [toricCechCharacterSumDegreeMap_of, DirectSum.map_of,
      toricCechCharacterSumDegreeMap_of]
    exact ConcreteCategory.congr_hom
      ((toricCechWeightInclusion fan charts b m).comm degree next) scalar
  | add first second first_eq second_eq =>
    simp only [map_add, first_eq, second_eq]

section FiniteCover

variable [Fintype Index]

theorem toricCechCharacterSumDegreeMap_bijective (degree : ℕ) :
    Function.Bijective (toricCechCharacterSumDegreeMap fan charts b degree) := by
  constructor
  · intro first second same
    apply DirectSum.ext
    intro m
    rw [← toricCechCharacterSumDegreeMap_retraction fan charts b degree m first,
      ← toricCechCharacterSumDegreeMap_retraction fan charts b degree m second, same]
  · intro p
    refine ⟨∑ m ∈ toricCechDegreeCharacterSupport fan charts b degree p,
      DirectSum.of (fun m => ↑((toricCechWeightComplex fan charts b m).X degree)) m
        (toricCechWeightDegreeRetraction fan charts b m degree p), ?_⟩
    rw [map_sum]
    simp only [toricCechCharacterSumDegreeMap_of]
    exact toricCechWeightDegreeProjector_sum_support fan charts b degree p

def toricCechCharacterSumDegreeEquiv (degree : ℕ) :
    ToricCechCharacterSumDegree fan charts b degree ≃+
      (toricCechLaurentComplex fan charts b).X degree :=
  AddEquiv.ofBijective (toricCechCharacterSumDegreeMap fan charts b degree)
    (toricCechCharacterSumDegreeMap_bijective fan charts b degree)

theorem toricCechCharacterSumDegreeEquiv_hom (degree : ℕ) :
    (toricCechCharacterSumDegreeEquiv fan charts b degree).toAddCommGrpIso.hom =
      AddCommGrpCat.ofHom (toricCechCharacterSumDegreeMap fan charts b degree) := rfl

/-- Full finite-support decomposition of the actual Laurent Čech complex. -/
def toricCechCharacterSumIso :
    toricCechCharacterSumComplex fan charts b ≅ toricCechLaurentComplex fan charts b :=
  HomologicalComplex.Hom.isoOfComponents
    (fun degree => (toricCechCharacterSumDegreeEquiv fan charts b degree).toAddCommGrpIso)
    (fun degree next _ => by
      rw [toricCechCharacterSumDegreeEquiv_hom, toricCechCharacterSumDegreeEquiv_hom]
      exact toricCechCharacterSumDegreeMap_d fan charts b degree next)

/-- Homology commutes with this genuine direct sum through the proved AB4
property of abelian groups. -/
def toricCechLaurentHomologyWeightSumIso (degree : ℕ) :
    (toricCechLaurentComplex fan charts b).homology degree ≅
      AddCommGrpCat.of (DirectSum (N →+ ℤ)
        (fun m => ↑((toricCechWeightComplex fan charts b m).homology degree))) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) degree).mapIso
    (toricCechCharacterSumIso fan charts b).symm ≪≫
      CechDirectSumHomology.directSumFamilyComplexHomologyIso
        (toricCechWeightComplex fan charts b) degree

end FiniteCover

end ToricPower
