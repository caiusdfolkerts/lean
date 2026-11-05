module
public import PaperVerification.ToricFanFoundations
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
@[expose] public section
/-!
# Primitive relations in actual smooth complete fans

A primitive relation is obtained by expanding the sum of a minimal noncone
collection in the unique positive cone of the fan. Positivity and integrality
are proved from completeness and smoothness. Disjointness of its positive and
negative rays is a theorem, not part of the definition.

The combinatorial contractibility condition below is precisely the cone
replacement condition in Casagrande, Theorem 2.2(ii). No equivalence with a
scheme-level contraction is asserted here without a separate proof.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- A primitive relation with genuine positive integral coefficients in its
focus cone. The ray sets need not be assumed disjoint. -/
structure PrimitiveRelation where
  positive : Finset (Lattice n)
  negative : Finset (Lattice n)
  coefficient : Lattice n → ℕ
  primitive : «Σ».IsPrimitiveCollection positive
  negative_cone : negative ∈ «Σ».cones
  coefficient_pos : ∀ v ∈ negative, 0 < coefficient v
  equation : ∑ v ∈ positive, v = ∑ v ∈ negative, (coefficient v : ℤ) • v

/-- Every primitive collection has a primitive relation; no relation is
postulated independently of the actual lattice vectors. -/
theorem exists_primitiveRelation {P : Finset (Lattice n)}
    (hP : «Σ».IsPrimitiveCollection P) :
    ∃ R : «Σ».PrimitiveRelation, R.positive = P := by
  obtain ⟨t, ht, c, hc, he⟩ := «Σ».exists_positive_integral_cone_expansion (∑ v ∈ P, v)
  exact ⟨⟨P, t, c, hP, ht, hc, he.symm⟩, rfl⟩

namespace PrimitiveRelation

variable {«Σ»} (R : «Σ».PrimitiveRelation)

/-- A primitive collection is disjoint from the focus of its relation
(Batyrev's primitive-collection disjointness lemma). -/
theorem disjoint : Disjoint R.positive R.negative := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxP hxT
  let P' := R.positive.erase x
  have hP' : P' ∈ «Σ».cones := R.primitive.2.2 _ (Finset.erase_ssubset hxP)
  let d : Lattice n → ℝ := fun v =>
    (R.coefficient v : ℝ) - if v = x then 1 else 0
  have hd (v : Lattice n) (hv : v ∈ R.negative) : 0 ≤ d v := by
    by_cases hvx : v = x
    · subst v
      have hx : (1 : ℝ) ≤ R.coefficient x := by exact_mod_cast R.coefficient_pos x hxT
      simp only [d, if_pos rfl, ite_true]
      linarith
    · simp only [d, if_neg hvx, sub_zero]
      exact Nat.cast_nonneg _
  have he : (∑ v ∈ R.negative, (R.coefficient v : ℝ) • embed n v) =
      ∑ v ∈ R.positive, embed n v := by
    have h := congrArg (embed n) R.equation
    simpa only [map_sum, embed_int_smul, Int.cast_natCast] using h.symm
  have hdsum : (∑ v ∈ R.negative, d v • embed n v) = ∑ v ∈ P', embed n v := by
    calc
      (∑ v ∈ R.negative, d v • embed n v) =
          (∑ v ∈ R.negative, (R.coefficient v : ℝ) • embed n v) - embed n x := by
        simp [d, sub_smul, Finset.sum_sub_distrib, ite_smul, hxT]
      _ = (∑ v ∈ R.positive, embed n v) - embed n x := by rw [he]
      _ = ∑ v ∈ P', embed n v := by
        rw [← Finset.sum_erase_add R.positive (fun v => embed n v) hxP]
        simp [P']
  have hsumCone : (∑ v ∈ P', embed n v) ∈ latticeRayCone R.negative := by
    rw [← hdsum]
    exact Submodule.sum_mem _ (fun v hv =>
      PointedCone.smul_mem _ (hd v hv) (latticeRayCone_generator R.negative hv))
  have hsubset : P' ⊆ R.negative :=
    «Σ».sum_mem_cone_implies_subset hP' R.negative_cone hsumCone
  have hall : R.positive ⊆ R.negative := by
    intro v hv
    by_cases hvx : v = x
    · simpa only [hvx] using hxT
    · exact hsubset (Finset.mem_erase.mpr ⟨hvx, hv⟩)
  exact R.primitive.2.1 («Σ».downward R.negative R.negative_cone R.positive hall)

/-- The positive focus cone is uniquely determined by the primitive collection. -/
theorem negative_unique (S : «Σ».PrimitiveRelation) (hPS : R.positive = S.positive) :
    R.negative = S.negative := by
  have hincl (R S : «Σ».PrimitiveRelation) (hPS : R.positive = S.positive) :
      R.negative ⊆ S.negative := by
    have he : (∑ v ∈ R.negative, (R.coefficient v : ℝ) • embed n v) =
        ∑ v ∈ S.negative, (S.coefficient v : ℝ) • embed n v := by
      have hZ : (∑ v ∈ R.negative, (R.coefficient v : ℤ) • v) =
          ∑ v ∈ S.negative, (S.coefficient v : ℤ) • v := by
        rw [← R.equation, ← S.equation, hPS]
      simpa only [map_sum, embed_int_smul, Int.cast_natCast] using congrArg (embed n) hZ
    apply «Σ».positive_sum_mem_cone_implies_subset R.negative_cone S.negative_cone
      (fun v => (R.coefficient v : ℝ)) (fun v hv => by exact_mod_cast R.coefficient_pos v hv)
    rw [he]
    exact Submodule.sum_mem _ (fun v hv => PointedCone.smul_mem _ (Nat.cast_nonneg _)
      (latticeRayCone_generator S.negative hv))
  exact Finset.Subset.antisymm (hincl R S hPS) (hincl S R hPS.symm)

/-- The positive integer coefficients on the focus are unique as well.
They are read off in a genuine integral basis containing that cone. -/
theorem coefficient_unique_on_negative (S : «Σ».PrimitiveRelation)
    (hPS : R.positive = S.positive) {v : Lattice n} (hv : v ∈ R.negative) :
    R.coefficient v = S.coefficient v := by
  have hN := R.negative_unique S hPS
  obtain ⟨b, I, hI⟩ := «Σ».smooth R.negative R.negative_cone
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (hI ▸ hv)
  have hsum (c : Lattice n → ℕ) :
      b.repr (∑ v ∈ R.negative, (c v : ℤ) • v) j = (c (b j) : ℤ) := by
    rw [hI, Finset.sum_image]
    · simp only [map_sum, LinearEquiv.map_smul, Finsupp.finsetSum_apply,
        Finsupp.smul_apply, Module.Basis.repr_self_apply]
      simp [hj, smul_eq_mul]
    · exact fun i _ k _ hik => b.injective hik
  have he : (∑ v ∈ R.negative, (R.coefficient v : ℤ) • v) =
      ∑ v ∈ R.negative, (S.coefficient v : ℤ) • v := by
    rw [R.equation.symm, hN, S.equation.symm, hPS]
  have hc := congrArg (fun z : Lattice n => b.repr z j) he
  rw [hsum, hsum] at hc
  exact_mod_cast hc

/-- The number `r` in the manuscript's relation `x₀+...+xᵣ = Σ aⱼyⱼ`. -/
def fiberDimension : ℕ := R.positive.card - 1

theorem fiberDimension_pos : 1 ≤ R.fiberDimension := by
  have h := («Σ».primitiveCollection_card_bounds R.primitive).1
  unfold fiberDimension
  omega

/-- The exact combinatorial replacement condition used in the contraction
theorem. It is a condition on all actual cones of the fan. -/
def IsCombinatoriallyContractible : Prop :=
  ∀ ν ∈ «Σ».cones, Disjoint ν (R.positive ∪ R.negative) →
    R.negative ∪ ν ∈ «Σ».cones → ∀ x ∈ R.positive,
      (R.positive.erase x) ∪ R.negative ∪ ν ∈ «Σ».cones

/-- The core negative rays and all but one positive ray form a genuine cone
for every combinatorially contractible relation. -/
theorem contractible_core_cone (hR : R.IsCombinatoriallyContractible)
    {x : Lattice n} (hx : x ∈ R.positive) :
    R.positive.erase x ∪ R.negative ∈ «Σ».cones := by
  simpa only [Finset.union_empty] using
    hR ∅ «Σ».empty_mem (Finset.disjoint_empty_left _) (by simpa using R.negative_cone) x hx

/-- The dimension inequality `r+q≤n` follows from a genuine smooth cone and
the proved disjointness, rather than being included as relation data. -/
theorem contractible_dimension_bound (hR : R.IsCombinatoriallyContractible) :
    R.fiberDimension + R.negative.card ≤ n := by
  obtain ⟨x, hx⟩ := «Σ».primitiveCollection_nonempty R.primitive
  have h := «Σ».card_cone_le (R.contractible_core_cone hR hx)
  rw [Finset.card_union_of_disjoint
    (R.disjoint.mono_left (Finset.erase_subset x R.positive)),
    Finset.card_erase_of_mem hx] at h
  exact h

/-- No cone contains the entire positive primitive collection. Consequently
it contains at most `r` positive rays. -/
theorem positive_rays_in_cone_bound {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) :
    (R.positive ∩ s).card ≤ R.fiberDimension := by
  have hproper : R.positive ∩ s ⊂ R.positive := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
    intro heq
    have hsub : R.positive ⊆ s := by
      rw [← heq]
      exact Finset.inter_subset_right
    exact R.primitive.2.1 («Σ».downward s hs R.positive hsub)
  have hcard := Finset.card_lt_card hproper
  unfold fiberDimension
  omega

/-- Pairing the primitive relation with arbitrary real invariant divisor
coefficients. This is the actual displayed coefficient pairing. -/
def degree (a : Lattice n → ℝ) : ℝ :=
  (∑ v ∈ R.positive, a v) - ∑ v ∈ R.negative, (R.coefficient v : ℝ) * a v

theorem degree_unique (S : «Σ».PrimitiveRelation) (hP : R.positive = S.positive)
    (a : Lattice n → ℝ) : R.degree a = S.degree a := by
  have hN := R.negative_unique S hP
  have hsum : (∑ v ∈ R.negative, (R.coefficient v : ℝ) * a v) =
      ∑ v ∈ R.negative, (S.coefficient v : ℝ) * a v := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [R.coefficient_unique_on_negative S hP hv]
  unfold degree
  rw [hsum, hP, hN]

theorem degree_add (a b : Lattice n → ℝ) : R.degree (a + b) = R.degree a + R.degree b := by
  simp only [degree, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem degree_sub (a b : Lattice n → ℝ) : R.degree (a - b) = R.degree a - R.degree b := by
  simp only [degree, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

theorem degree_smul (t : ℝ) (a : Lattice n → ℝ) :
    R.degree (t • a) = t * R.degree a := by
  simp only [degree, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  ring

/-- A selection of invariant divisors from a cone has relation degree at most
`r`: the cone omits at least one positive ray, and all negative contributions
can only lower the degree. This is the numerical bound in Lemma 3.1. -/
theorem degree_cone_selection_le {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) :
    R.degree (fun v => if v ∈ t then 1 else 0) ≤ R.fiberDimension := by
  have hnegative : 0 ≤ ∑ v ∈ R.negative,
      (R.coefficient v : ℝ) * (if v ∈ t then 1 else 0) := by
    apply Finset.sum_nonneg
    intro v hv
    split_ifs <;> simp
  have hpos : (∑ v ∈ R.positive, if v ∈ t then (1 : ℝ) else 0) =
      ((R.positive ∩ t).card : ℝ) := by
    rw [Finset.sum_boole]
    congr 1
  have hcard : (R.positive ∩ t).card ≤ R.fiberDimension :=
    (Finset.card_le_card (Finset.inter_subset_inter_left hts)).trans
      (R.positive_rays_in_cone_bound hs)
  have hcardR : ((R.positive ∩ t).card : ℝ) ≤ R.fiberDimension := by exact_mod_cast hcard
  unfold degree
  rw [hpos]
  linarith

/-- The corner-criterion hypothesis makes every selected-divisor subtraction
nonnegative on that primitive relation. -/
theorem degree_sub_corner_selection_nonneg {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) (a : Lattice n → ℝ) (side : ℝ)
    (hside : 0 ≤ side) (hdegree : side * R.fiberDimension ≤ R.degree a) :
    0 ≤ R.degree (a - side • (fun v => if v ∈ t then 1 else 0)) := by
  rw [R.degree_sub, R.degree_smul]
  have hbound := mul_le_mul_of_nonneg_left (R.degree_cone_selection_le hs hts) hside
  linarith

end PrimitiveRelation

end SmoothCompleteFan

end PaperVerification.ToricGeometry
