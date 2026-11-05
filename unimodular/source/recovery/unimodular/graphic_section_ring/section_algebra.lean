module

public import Recovery.Unimodular.GraphicSectionRing.InitialIdeal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The actual graded lattice semigroup algebra is generated in degree one

The semigroup contains all lattice points satisfying the inequalities in every
positive integral degree, with its genuine zero element. Surjectivity is
proved from the explicit all-degree decomposition. The polynomial quotient
is then identified with this algebra through the ordinary first isomorphism
theorem; no normality or generation assertion is placed in a definition.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Unimodular.GraphicSectionRing

variable {n : ℕ}

theorem difference_add (x y : Lattice n) (a b : Coordinate n) :
    difference (x + y) a b = difference x a b + difference y a b := by
  cases a <;> cases b <;> simp [difference, anchored] <;> ring

/-- Degree zero is the zero lattice vector; positive degrees use the literal
scaled integral inequalities. -/
def sectionSemigroup (C : Set (Constraint n)) : AddSubmonoid (ℕ × Lattice n) where
  carrier := {z | (z.1 = 0 → z.2 = 0) ∧
    ∀ c ∈ C, difference z.2 c.left c.right ≤ (z.1 : ℤ) * c.bound}
  zero_mem' := by
    constructor
    · intro _; rfl
    · intro c hc
      cases c.left <;> cases c.right <;> simp [difference, anchored]
  add_mem' := by
    intro a b ha hb
    constructor
    · intro h
      have ha0 : a.1 = 0 := by change a.1 + b.1 = 0 at h; omega
      have hb0 : b.1 = 0 := by change a.1 + b.1 = 0 at h; omega
      change a.2 + b.2 = 0
      rw [ha.1 ha0, hb.1 hb0, add_zero]
    · intro c hc
      change difference (a.2 + b.2) c.left c.right ≤ ((a.1 + b.1 : ℕ) : ℤ) * c.bound
      rw [difference_add, Nat.cast_add, add_mul]
      exact add_le_add (ha.2 c hc) (hb.2 c hc)

def degreeOnePoint {C : Set (Constraint n)} (a : Point C) : sectionSemigroup C :=
  ⟨(1, a.1), by
    constructor
    · intro h; omega
    · intro c hc
      simpa using a.2 c hc⟩

theorem point_multiset_mem {C : Set (Constraint n)} (M : Multiset (Point C)) :
    ((M.map Subtype.val).card, (M.map Subtype.val).sum) ∈ sectionSemigroup C := by
  induction M using Multiset.induction_on with
  | empty => exact (sectionSemigroup C).zero_mem
  | cons a M ih =>
    have h := (sectionSemigroup C).add_mem (degreeOnePoint a).2 ih
    change (1 + (M.map Subtype.val).card, a.val + (M.map Subtype.val).sum) ∈
      sectionSemigroup C at h
    simpa only [Multiset.map_cons, Multiset.card_cons, Multiset.sum_cons,
      Nat.add_comm] using h

/-- The map of additive monoids underlying the ordinary degree-one monomial map. -/
def sectionDegree (C : Set (Constraint n)) :
    (Point C →₀ ℕ) →+ sectionSemigroup C :=
  (toricDegree Subtype.val).codRestrict (sectionSemigroup C)
    (fun u => point_multiset_mem u.toMultiset)

@[simp] theorem sectionDegree_val (C : Set (Constraint n)) (u : Point C →₀ ℕ) :
    (sectionDegree C u).val = toricDegree Subtype.val u := rfl

@[simp] theorem sectionDegree_single (C : Set (Constraint n)) (a : Point C) :
    sectionDegree C (Finsupp.single a 1) = degreeOnePoint a := by
  apply Subtype.ext
  exact toricDegree_single Subtype.val a

/-- Every homogeneous lattice point, in every positive degree, is the sum of
degree-one points satisfying the original inequalities. -/
theorem exists_standard_section_preimage (C : Set (Constraint n)) (z : sectionSemigroup C) :
    ∃ u, sectionDegree C u = z ∧ StandardExponent Subtype.val u := by
  classical
  by_cases hz : z.val.1 = 0
  · refine ⟨0, ?_, ?_⟩
    · apply Subtype.ext
      change (0 : ℕ × Lattice n) = z.val
      exact (Prod.ext hz (z.2.1 hz)).symm
    · simp [StandardExponent, monomialPoints, Standard]
  · have hk : 0 < z.val.1 := Nat.pos_of_ne_zero hz
    let points : Fin z.val.1 → Point C := fun r =>
      ⟨balanced z.val.2 r, balanced_satisfies hk z.val.2 z.2.2 r⟩
    let M : Multiset (Point C) := Finset.univ.val.map points
    let u : Point C →₀ ℕ := M.toFinsupp
    have hpoints : monomialPoints Subtype.val u = canonical z.val.1 z.val.2 := by
      simp only [monomialPoints, u, Multiset.toFinsupp_toMultiset, M, Multiset.map_map]
      rfl
    refine ⟨u, ?_, ?_⟩
    · apply Subtype.ext
      change toricDegree Subtype.val u = z.val
      change ((monomialPoints Subtype.val u).card, (monomialPoints Subtype.val u).sum) = z.val
      rw [hpoints, canonical_card, canonical_sum hk]
    · change Standard (monomialPoints Subtype.val u)
      rw [hpoints]
      exact canonical_standard _

theorem sectionDegree_surjective (C : Set (Constraint n)) :
    Function.Surjective (sectionDegree C) := by
  intro z
  obtain ⟨u, hu, _⟩ := exists_standard_section_preimage C z
  exact ⟨u, hu⟩

abbrev SectionAlgebra (C : Set (Constraint n)) (K : Type*) [CommSemiring K] :=
  AddMonoidAlgebra K (sectionSemigroup C)

/-- The genuine map from degree-one polynomial generators to the section semigroup algebra. -/
def sectionMap (C : Set (Constraint n)) (K : Type*) [CommSemiring K] :
    MvPolynomial (Point C) K →ₐ[K] SectionAlgebra C K :=
  AddMonoidAlgebra.mapDomainAlgHom K K (sectionDegree C)

@[simp] theorem sectionMap_X (C : Set (Constraint n)) (K : Type*) [CommSemiring K]
    (a : Point C) : sectionMap C K (MvPolynomial.X a) =
      AddMonoidAlgebra.single (degreeOnePoint a) 1 := by
  change AddMonoidAlgebra.mapDomain (sectionDegree C)
    (AddMonoidAlgebra.single (Finsupp.single a 1) 1) = _
  rw [AddMonoidAlgebra.mapDomain_single, sectionDegree_single]

/-- Normal generation of the actual semigroup algebra. -/
theorem sectionMap_surjective (C : Set (Constraint n)) (K : Type*) [CommSemiring K] :
    Function.Surjective (sectionMap C K) := by
  intro f
  obtain ⟨g, hg⟩ := Finsupp.mapDomain_surjective (sectionDegree_surjective C) f.coeff
  refine ⟨AddMonoidAlgebra.ofCoeff g, ?_⟩
  apply AddMonoidAlgebra.coeff_injective
  exact hg

def ambientMap (C : Set (Constraint n)) (K : Type*) [CommSemiring K] :
    SectionAlgebra C K →ₐ[K] AddMonoidAlgebra K (ℕ × Lattice n) :=
  AddMonoidAlgebra.mapDomainAlgHom K K (sectionSemigroup C).subtype

theorem ambientMap_injective (C : Set (Constraint n)) (K : Type*) [CommSemiring K] :
    Function.Injective (ambientMap C K) :=
  AddMonoidAlgebra.mapDomain_injective Subtype.val_injective

theorem ambientMap_comp_sectionMap (C : Set (Constraint n)) (K : Type*) [CommSemiring K] :
    (ambientMap C K).comp (sectionMap C K) = toricMap (Subtype.val : Point C → Lattice n) K := by
  exact (AddMonoidAlgebra.mapDomainAlgHom_comp (R := K) (A := K)
    (sectionDegree C) (sectionSemigroup C).subtype).symm

/-- The relation ideal is exactly the original lattice-point toric ideal. -/
theorem sectionMap_ker (C : Set (Constraint n)) (K : Type*) [CommSemiring K] :
    RingHom.ker (sectionMap C K).toRingHom = toricIdeal (Subtype.val : Point C → Lattice n) K := by
  ext f
  change sectionMap C K f = 0 ↔ toricMap Subtype.val K f = 0
  constructor
  · intro h
    have hc := DFunLike.congr_fun (ambientMap_comp_sectionMap C K) f
    rw [AlgHom.comp_apply, h, map_zero] at hc
    exact hc.symm
  · intro h
    apply ambientMap_injective C K
    rw [map_zero]
    change (ambientMap C K).comp (sectionMap C K) f = 0
    rw [ambientMap_comp_sectionMap, h]

/-- A proved algebra equivalence with the ordinary polynomial quotient. -/
def quotientEquivSectionAlgebra (C : Set (Constraint n)) (K : Type*) [CommRing K] :
    (MvPolynomial (Point C) K ⧸ toricIdeal (Subtype.val : Point C → Lattice n) K) ≃ₐ[K]
      SectionAlgebra C K := by
  rw [← sectionMap_ker C K]
  exact Ideal.quotientKerAlgEquivOfSurjective (sectionMap_surjective C K)

#print axioms sectionDegree_surjective
#print axioms sectionMap_surjective
#print axioms sectionMap_ker
#print axioms quotientEquivSectionAlgebra

end Unimodular.GraphicSectionRing
