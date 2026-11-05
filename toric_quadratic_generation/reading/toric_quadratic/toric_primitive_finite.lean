module

public import PaperVerification.ToricNefCriterion

@[expose] public section

/-!
# A genuine finite family of all primitive relation vectors

PrimitiveRelation allows arbitrary coefficient values away from its focus,
so that structure itself need not be a finite type. The displayed relation
vector, however, is uniquely determined by its positive primitive collection.
This is proved by integral basis coordinates before taking a finite family.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} {«Σ» : SmoothCompleteFan n}

namespace PrimitiveRelation

variable (R S : «Σ».PrimitiveRelation)

/-- Positive integral coefficients in the actual smooth focus cone are
uniquely determined by the lattice vector. -/
theorem coefficient_eq_of_positive_eq (hpos : R.positive = S.positive)
    {v : Lattice n} (hv : v ∈ R.negative) : R.coefficient v = S.coefficient v := by
  have hneg := R.negative_unique S hpos
  obtain ⟨b, I, hI⟩ := «Σ».smooth R.negative R.negative_cone
  obtain ⟨i, hi, hiv⟩ := Finset.mem_image.mp (hI ▸ hv)
  subst v
  have hcoord (c : Lattice n → ℕ) :
      b.repr (∑ v ∈ I.image b, (c v : ℤ) • v) i = (c (b i) : ℤ) := by
    rw [Finset.sum_image]
    · simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
        Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero]
      simp [hi]
    · exact fun j _ k _ hjk => b.injective hjk
  have hR : b.repr (∑ v ∈ R.positive, v) i = (R.coefficient (b i) : ℤ) := by
    rw [R.equation, hI]
    exact hcoord R.coefficient
  have hS : b.repr (∑ v ∈ S.positive, v) i = (S.coefficient (b i) : ℤ) := by
    rw [S.equation, ← hneg, hI]
    exact hcoord S.coefficient
  rw [hpos] at hR
  exact_mod_cast hR.symm.trans hS

/-- The actual relation vector is unique, regardless of unused coefficient
values outside its focus cone. -/
theorem vector_eq_of_positive_eq (hpos : R.positive = S.positive) :
    R.vector = S.vector := by
  have hneg := R.negative_unique S hpos
  funext v
  by_cases hv : (v : Lattice n) ∈ R.negative
  · have hvS : (v : Lattice n) ∈ S.negative := hneg ▸ hv
    have hc := R.coefficient_eq_of_positive_eq S hpos hv
    simp only [vector, hpos, if_pos hv, if_pos hvS, hc]
  · have hvS : (v : Lattice n) ∉ S.negative := by simpa only [← hneg] using hv
    simp only [vector, hpos, if_neg hv, if_neg hvS]

end PrimitiveRelation

variable («Σ»)

/-- All genuine primitive collections form a subset of the finite ray powerset. -/
def primitiveCollections : Finset (Finset (Lattice n)) :=
  «Σ».rays.powerset.filter «Σ».IsPrimitiveCollection

theorem mem_primitiveCollections (Q : Finset (Lattice n)) :
    Q ∈ «Σ».primitiveCollections ↔ «Σ».IsPrimitiveCollection Q := by
  simp only [primitiveCollections, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- One actual primitive relation for each primitive collection. -/
def canonicalPrimitive (Q : «Σ».primitiveCollections) : «Σ».PrimitiveRelation :=
  Classical.choose («Σ».exists_primitiveRelation
    ((«Σ».mem_primitiveCollections Q).mp Q.property))

theorem canonicalPrimitive_positive (Q : «Σ».primitiveCollections) :
    («Σ».canonicalPrimitive Q).positive = (Q : Finset (Lattice n)) :=
  Classical.choose_spec («Σ».exists_primitiveRelation
    ((«Σ».mem_primitiveCollections Q).mp Q.property))

/-- This finite family contains every primitive relation vector exactly up
to the proved equality, rather than by a bounded-coefficient restriction. -/
theorem exists_canonicalPrimitive_vector (R : «Σ».PrimitiveRelation) :
    ∃ Q : «Σ».primitiveCollections, R.vector = («Σ».canonicalPrimitive Q).vector := by
  let Q : «Σ».primitiveCollections :=
    ⟨R.positive, («Σ».mem_primitiveCollections R.positive).mpr R.primitive⟩
  refine ⟨Q, R.vector_eq_of_positive_eq («Σ».canonicalPrimitive Q) ?_⟩
  exact («Σ».canonicalPrimitive_positive Q).symm

/-- The finite primitive inequality family is equivalent to the unrestricted
primitive criterion and hence to genuine convex support. -/
theorem isNef_iff_canonicalPrimitive_nonneg (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (a : Lattice n → ℝ) :
    «Σ».IsNef a ↔ ∀ Q : «Σ».primitiveCollections,
      0 ≤ («Σ».canonicalPrimitive Q).degree a := by
  rw [«Σ».isNef_iff_primitive_nonneg hpure H hH a]
  constructor
  · intro ha Q
    exact ha («Σ».canonicalPrimitive Q)
  · intro ha R
    obtain ⟨Q, hQ⟩ := «Σ».exists_canonicalPrimitive_vector R
    rw [← R.vector_pairing, hQ, («Σ».canonicalPrimitive Q).vector_pairing]
    exact ha Q

end SmoothCompleteFan

end PaperVerification.ToricGeometry
