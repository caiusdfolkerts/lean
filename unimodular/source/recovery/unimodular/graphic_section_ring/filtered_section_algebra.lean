module

public import Recovery.Unimodular.GraphicSectionRing.SectionAlgebra
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Logic.Equiv.Option

/-!
# The actual homogeneous basis and height filtration of the section algebra

Every basis vector is an actual lattice monomial. Its canonical compatible
factorization supplies the filtration height. Multiplication preserves that
height exactly when the union of the two normal exponents is compatible;
otherwise it lowers the height strictly. The augmentation and the positive
internal grading are constructed from the actual additive semigroup.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Unimodular.GraphicSectionRing

variable {n : ℕ}

def normalExponent (C : Set (Constraint n)) (z : sectionSemigroup C) : Point C →₀ ℕ :=
  Classical.choose (exists_standard_section_preimage C z)

@[simp] theorem sectionDegree_normalExponent (C : Set (Constraint n))
    (z : sectionSemigroup C) : sectionDegree C (normalExponent C z) = z :=
  (Classical.choose_spec (exists_standard_section_preimage C z)).1

theorem normalExponent_standard (C : Set (Constraint n)) (z : sectionSemigroup C) :
    StandardExponent Subtype.val (normalExponent C z) :=
  (Classical.choose_spec (exists_standard_section_preimage C z)).2

theorem toricDegree_normalExponent (C : Set (Constraint n)) (z : sectionSemigroup C) :
    toricDegree Subtype.val (normalExponent C z) = z.val :=
  congrArg Subtype.val (sectionDegree_normalExponent C z)

/-- Normal exponent uniqueness follows from the checked lattice normal form. -/
theorem normalExponent_eq_of_standard {C : Set (Constraint n)}
    {u : Point C →₀ ℕ} (hu : StandardExponent Subtype.val u) :
    normalExponent C (sectionDegree C u) = u := by
  apply standard_exponent_unique Subtype.val_injective (normalExponent_standard C _) hu
  exact toricDegree_normalExponent C _

@[simp] theorem normalExponent_zero (C : Set (Constraint n)) :
    normalExponent C 0 = 0 := by
  have hs : StandardExponent (Subtype.val : Point C → Lattice n) 0 := by
    simp [StandardExponent, Standard]
  simpa only [map_zero] using normalExponent_eq_of_standard hs

theorem normalExponent_add_iff (C : Set (Constraint n)) (s t : sectionSemigroup C) :
    normalExponent C (s + t) = normalExponent C s + normalExponent C t ↔
      StandardExponent Subtype.val (normalExponent C s + normalExponent C t) := by
  constructor
  · intro h
    rw [← h]
    exact normalExponent_standard C _
  · intro h
    have he : sectionDegree C (normalExponent C s + normalExponent C t) = s + t := by
      rw [map_add, sectionDegree_normalExponent, sectionDegree_normalExponent]
    rw [← he]
    exact normalExponent_eq_of_standard h

def sectionHeight (C : Set (Constraint n)) (z : sectionSemigroup C) : ℕ :=
  monomialWeight Subtype.val (normalExponent C z)

@[simp] theorem sectionHeight_zero (C : Set (Constraint n)) : sectionHeight C 0 = 0 := by
  simp [sectionHeight]

theorem sectionHeight_add_eq {C : Set (Constraint n)} {s t : sectionSemigroup C}
    (h : StandardExponent Subtype.val (normalExponent C s + normalExponent C t)) :
    sectionHeight C (s + t) = sectionHeight C s + sectionHeight C t := by
  unfold sectionHeight
  rw [(normalExponent_add_iff C s t).mpr h, map_add]

/-- A forbidden pair in a product causes strict filtration descent. -/
theorem sectionHeight_add_lt {C : Set (Constraint n)} {s t : sectionSemigroup C}
    (h : ¬ StandardExponent Subtype.val (normalExponent C s + normalExponent C t)) :
    sectionHeight C (s + t) < sectionHeight C s + sectionHeight C t := by
  have he : toricDegree Subtype.val (normalExponent C (s + t)) =
      toricDegree Subtype.val (normalExponent C s + normalExponent C t) := by
    rw [map_add, toricDegree_normalExponent, toricDegree_normalExponent,
      toricDegree_normalExponent]
    rfl
  have hne : normalExponent C (s + t) ≠ normalExponent C s + normalExponent C t :=
    fun e => h ((normalExponent_add_iff C s t).mp e)
  have hw := standard_exponent_weight_lt Subtype.val_injective
    (normalExponent_standard C (s + t)) he hne
  simpa only [map_add, sectionHeight] using hw

theorem sectionHeight_add_le (C : Set (Constraint n)) (s t : sectionSemigroup C) :
    sectionHeight C (s + t) ≤ sectionHeight C s + sectionHeight C t := by
  classical
  by_cases h : StandardExponent Subtype.val (normalExponent C s + normalExponent C t)
  · exact (sectionHeight_add_eq h).le
  · exact (sectionHeight_add_lt h).le

/-- The original homogeneous degree, independently of the filtration height. -/
def internalDegree (C : Set (Constraint n)) : sectionSemigroup C →+ ℕ where
  toFun z := z.val.1
  map_zero' := rfl
  map_add' _ _ := rfl

theorem internalDegree_eq_zero_iff {C : Set (Constraint n)} (z : sectionSemigroup C) :
    internalDegree C z = 0 ↔ z = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    exact Prod.ext h (z.2.1 h)
  · rintro rfl
    rfl

abbrev PositiveSection (C : Set (Constraint n)) := {z : sectionSemigroup C // z ≠ 0}

theorem positive_internalDegree {C : Set (Constraint n)} (z : PositiveSection C) :
    0 < internalDegree C z.val :=
  Nat.pos_of_ne_zero (fun h => z.2 ((internalDegree_eq_zero_iff z.val).mp h))

def positiveAdd {C : Set (Constraint n)} (s t : PositiveSection C) : PositiveSection C :=
  ⟨s.val + t.val, by
    intro h
    have he := congrArg (internalDegree C) h
    rw [map_add, map_zero] at he
    have hs := positive_internalDegree s
    omega⟩

def sectionBasis (C : Set (Constraint n)) (K : Type*) [CommSemiring K] :
    Module.Basis (sectionSemigroup C) K (SectionAlgebra C K) :=
  AddMonoidAlgebra.basis _ K

/-- The unit together with all nonzero lattice monomials is a genuine basis. -/
def augmentedSectionBasis (C : Set (Constraint n)) (K : Type*) [CommSemiring K] :
    Module.Basis (Option (PositiveSection C)) K (SectionAlgebra C K) :=
  (sectionBasis C K).reindex (Equiv.optionSubtypeNe (0 : sectionSemigroup C)).symm

@[simp] theorem augmentedSectionBasis_none (C : Set (Constraint n)) (K : Type*)
    [CommSemiring K] : augmentedSectionBasis C K none = 1 := by
  simp [augmentedSectionBasis, sectionBasis, AddMonoidAlgebra.basis_apply,
    AddMonoidAlgebra.one_def]

@[simp] theorem augmentedSectionBasis_some (C : Set (Constraint n)) (K : Type*)
    [CommSemiring K] (s : PositiveSection C) :
    augmentedSectionBasis C K (some s) = AddMonoidAlgebra.single s.val 1 := by
  simp [augmentedSectionBasis, sectionBasis, AddMonoidAlgebra.basis_apply]

/-- Multiplication in the original algebra is the actual lattice-monomial product. -/
theorem augmentedSectionBasis_mul (C : Set (Constraint n)) (K : Type*) [CommSemiring K]
    (s t : PositiveSection C) :
    augmentedSectionBasis C K (some s) * augmentedSectionBasis C K (some t) =
      augmentedSectionBasis C K (some (positiveAdd s t)) := by
  simp only [augmentedSectionBasis_some, AddMonoidAlgebra.single_mul_single, one_mul]
  rfl

def degreeZeroCharacter (C : Set (Constraint n)) (K : Type*) [CommSemiring K] :
    Multiplicative (sectionSemigroup C) →* K where
  toFun z := if internalDegree C z.toAdd = 0 then 1 else 0
  map_one' := by simp
  map_mul' s t := by
    change (if internalDegree C (s.toAdd + t.toAdd) = 0 then 1 else 0) = _
    rw [map_add]
    by_cases hs : internalDegree C s.toAdd = 0 <;>
      by_cases ht : internalDegree C t.toAdd = 0 <;>
      simp [hs, ht, Nat.add_eq_zero_iff]

/-- The augmentation is an actual algebra homomorphism. -/
def sectionAugmentation (C : Set (Constraint n)) (K : Type*) [CommSemiring K] :
    SectionAlgebra C K →ₐ[K] K :=
  AddMonoidAlgebra.lift K K (sectionSemigroup C) (degreeZeroCharacter C K)

@[simp] theorem sectionAugmentation_single (C : Set (Constraint n)) (K : Type*)
    [CommSemiring K] (s : sectionSemigroup C) (a : K) :
    sectionAugmentation C K (AddMonoidAlgebra.single s a) =
      if internalDegree C s = 0 then a else 0 := by
  rw [sectionAugmentation, AddMonoidAlgebra.lift_single]
  change a • (if internalDegree C s = 0 then (1 : K) else 0) = _
  split_ifs <;> simp

@[simp] theorem sectionAugmentation_positive (C : Set (Constraint n)) (K : Type*)
    [CommSemiring K] (s : PositiveSection C) :
    sectionAugmentation C K (augmentedSectionBasis C K (some s)) = 0 := by
  rw [augmentedSectionBasis_some, sectionAugmentation_single]
  exact if_neg (Nat.ne_of_gt (positive_internalDegree s))

#print axioms normalExponent_add_iff
#print axioms sectionHeight_add_lt
#print axioms augmentedSectionBasis_none
#print axioms augmentedSectionBasis_mul
#print axioms sectionAugmentation_positive

end Unimodular.GraphicSectionRing
