module

public import higher_specht.verified.remaining03_parameter_basis
public import Mathlib.GroupTheory.GroupAction.Embedding
public import tau_ceti.representation_theory.coinduced
public import Mathlib.RepresentationTheory.FiniteIndex

/- Generated ordinary source-preserving proof stage. See audit/staged_specht_remaining/Remaining03Ordered/manifest.json. -/

@[expose] public section

section CanonicalSource66
/- Source: HigherSpecht/OrderedRoots.lean -/



/-!
# The integral ordered-root localization

The root-variable type is `Fin m × Unit`, to distinguish it from the
formal elementary-parameter variables.  Renaming along the evident
bijection gives the usual polynomial ring in `c₁,...,cₘ`.  The displayed
localizing element is precisely the product of the roots and their
pairwise differences.  Its image, and therefore each of those factors,
is a unit.
-/

noncomputable section

open Finset MvPolynomial TauCeti
open scoped Polynomial BigOperators Classical

namespace HigherSpecht

abbrev OrderedRootPolynomial (R : Type*) [CommRing R] (m : ℕ) :=
  MvPolynomial (Fin m × Unit) R

def orderedRootDiscriminant (R : Type*) [CommRing R] (m : ℕ) : OrderedRootPolynomial R m :=
  (∏ i : Fin m, MvPolynomial.X (i, ())) *
    ∏ ij ∈ (Finset.univ : Finset (Fin m × Fin m)).filter (fun ij => ij.1 < ij.2),
      (MvPolynomial.X (ij.1, ()) - MvPolynomial.X (ij.2, ()))

abbrev OrderedRootRing (R : Type*) [CommRing R] (m : ℕ) :=
  Localization.Away (orderedRootDiscriminant R m)

variable {R : Type*} [CommRing R]

noncomputable instance orderedRootCoefficientAlgebra (m : ℕ) :
    Algebra R (OrderedRootRing R m) :=
  inferInstanceAs (Algebra R (Localization.Away (orderedRootDiscriminant R m)))

/-- Use the coefficient algebra's existing integer scalar action in tensor products. -/
@[reducible] noncomputable instance orderedRootIntModule (m : ℕ) :
    Module ℤ (OrderedRootRing ℤ m) :=
  @Algebra.toModule ℤ (OrderedRootRing ℤ m) _ _
    (orderedRootCoefficientAlgebra (R := ℤ) m)

theorem orderedRootIntModule_eq (m : ℕ) :
    orderedRootIntModule m =
      (AddCommGroup.toIntModule (OrderedRootRing ℤ m) : Module ℤ (OrderedRootRing ℤ m)) :=
  Subsingleton.elim _ _

@[simp] theorem orderedRootCoefficient_algebraMap (m : ℕ) (r : R) :
    algebraMap R (OrderedRootRing R m) r =
      algebraMap (OrderedRootPolynomial R m) (OrderedRootRing R m) (MvPolynomial.C r) := rfl

noncomputable instance orderedRootCoefficientTower (m : ℕ) :
    IsScalarTower R (OrderedRootPolynomial R m) (OrderedRootRing R m) :=
  IsScalarTower.of_algebraMap_eq' (R := R) (S := OrderedRootPolynomial R m)
    (A := OrderedRootRing R m) rfl

def orderedRoot (m : ℕ) (i : Fin m) : OrderedRootRing R m :=
  algebraMap (OrderedRootPolynomial R m) (OrderedRootRing R m) (MvPolynomial.X (i, ()))

theorem orderedRootDiscriminant_ne_zero [IsDomain R] (m : ℕ) :
    orderedRootDiscriminant R m ≠ 0 := by
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact MvPolynomial.X_ne_zero _
  · apply Finset.prod_ne_zero_iff.mpr
    intro ij hij
    have hlt := (Finset.mem_filter.mp hij).2
    apply sub_ne_zero.mpr
    intro h
    have heq := congrArg Prod.fst (MvPolynomial.X_injective h)
    exact (ne_of_lt hlt) heq

noncomputable instance orderedRootRing_isDomain [IsDomain R] (m : ℕ) :
    IsDomain (OrderedRootRing R m) :=
  IsLocalization.Away.isDomain (S := OrderedRootRing R m) (orderedRootDiscriminant_ne_zero (R := R) m)

theorem orderedRoot_isUnit (m : ℕ) (i : Fin m) : IsUnit (orderedRoot (R := R) m i) := by
  apply IsLocalization.Away.isUnit_of_dvd (x := orderedRootDiscriminant R m)
    (S := OrderedRootRing R m)
  unfold orderedRootDiscriminant
  apply dvd_mul_of_dvd_left
  exact Finset.dvd_prod_of_mem
    (fun j : Fin m => (MvPolynomial.X (j, ()) : OrderedRootPolynomial R m))
    (Finset.mem_univ i)

theorem orderedRoot_sub_isUnit_of_lt (m : ℕ) (i j : Fin m) (hij : i < j) :
    IsUnit (orderedRoot (R := R) m i - orderedRoot m j) := by
  change IsUnit (algebraMap (OrderedRootPolynomial R m) (OrderedRootRing R m)
    (MvPolynomial.X (i, ())) - algebraMap _ _ (MvPolynomial.X (j, ())))
  rw [← map_sub]
  apply IsLocalization.Away.isUnit_of_dvd (x := orderedRootDiscriminant R m)
    (S := OrderedRootRing R m)
  unfold orderedRootDiscriminant
  apply dvd_mul_of_dvd_right
  exact Finset.dvd_prod_of_mem (M := OrderedRootPolynomial R m)
    (a := (i, j))
    (s := (Finset.univ : Finset (Fin m × Fin m)).filter (fun ij => ij.1 < ij.2))
    (fun ij : Fin m × Fin m =>
      (MvPolynomial.X (ij.1, ()) - MvPolynomial.X (ij.2, ()) : OrderedRootPolynomial R m))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ (i, j), hij⟩)

theorem orderedRoot_pairwise_units (m : ℕ) :
    Pairwise fun i j : Fin m => IsUnit (orderedRoot (R := R) m i - orderedRoot m j) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact orderedRoot_sub_isUnit_of_lt m i j h
  · convert (orderedRoot_sub_isUnit_of_lt (R := R) m j i h).neg using 1 <;> ring

def orderedRootElementaryParameters (m : ℕ) : Fin m → OrderedRootRing R m :=
  fun i => elementaryValue Finset.univ (orderedRoot (R := R) m) (i.val + 1)

noncomputable instance orderedRootParameterAlgebra (n : ℕ) (lam : YoungDiagram) :
    Algebra (ElementaryParameterRing R n lam) (OrderedRootRing R (n - lam.card)) :=
  (MvPolynomial.aeval (orderedRootElementaryParameters (R := R) (n - lam.card))).toRingHom.toAlgebra

noncomputable instance orderedRootParameterTower (n : ℕ) (lam : YoungDiagram) :
    IsScalarTower R (ElementaryParameterRing R n lam) (OrderedRootRing R (n - lam.card)) :=
  IsScalarTower.of_algHom
    (MvPolynomial.aeval (R := R)
      (orderedRootElementaryParameters (R := R) (n - lam.card)))

@[simp] theorem orderedRootParameter_algebraMap_X (n : ℕ) (lam : YoungDiagram)
    (i : Fin (n - lam.card)) :
    algebraMap (ElementaryParameterRing R n lam) (OrderedRootRing R (n - lam.card))
        (MvPolynomial.X i) = orderedRootElementaryParameters (n - lam.card) i :=
  MvPolynomial.aeval_X _ _

theorem parameterPolynomial_elementaryValues [Nontrivial R] {m : ℕ} (x : Fin m → R) :
    parameterPolynomial (fun i : Fin m => elementaryValue Finset.univ x (i.val + 1)) =
      coordinateCharacteristic Finset.univ x := by
  let Q := coordinateCharacteristic Finset.univ x
  have hQ : Q.Monic := coordinateCharacteristic_monic _ _
  have hdeg : Q.natDegree = m := by
    dsimp only [Q]
    rw [coordinateCharacteristic, Polynomial.natDegree_prod_of_monic Finset.univ
      (fun i : Fin m => Polynomial.X - Polynomial.C (x i))
      (fun i _ => Polynomial.monic_X_sub_C (x i))]
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
  have hparams : polynomialParameters Q m =
      (fun i : Fin m => elementaryValue Finset.univ x (i.val + 1)) := by
    funext i
    unfold polynomialParameters
    have hd : i.val + 1 ≤ (Finset.univ : Finset (Fin m)).card := by
      simpa only [Finset.card_univ, Fintype.card_fin] using Nat.succ_le_of_lt i.isLt
    rw [show m - (i.val + 1) = (Finset.univ : Finset (Fin m)).card - (i.val + 1) by simp,
      coordinateCharacteristic_coeff_card_sub _ _ hd, ← mul_assoc, ← mul_pow]
    simp
  rw [← hparams]
  exact parameterPolynomial_polynomialParameters Q hQ hdeg

theorem orderedRootParameter_factorization [IsDomain R] (m : ℕ) :
    parameterPolynomial (orderedRootElementaryParameters (R := R) m) =
      splitRootParameter 0 (orderedRoot m) (fun _ => 1) := by
  change parameterPolynomial
    (fun i : Fin m => elementaryValue Finset.univ (orderedRoot (R := R) m) (i.val + 1)) = _
  rw [parameterPolynomial_elementaryValues]
  simp only [coordinateCharacteristic, splitRootParameter, pow_zero, one_mul, pow_one]

end HigherSpecht
end
end CanonicalSource66

section CanonicalSource67
/- Source: HigherSpecht/DistinctRootAssignments.lean -/



/-! With one coordinate at each nonzero root, the actual root-assignment
index set is exactly the set of injections from the ordered roots into the
coordinate set.  Both directions retain the literal coordinate assignment. -/

noncomputable section

open scoped Classical

namespace HigherSpecht

abbrev DistinctRootAssignments (n k m : ℕ) :=
  PrescribedRootAssignments n (fun i : Option (Fin m) => i.elim k (fun _ => 1))

variable {n k m : ℕ}

def distinctAssignedPoint (f : DistinctRootAssignments n k m) (i : Fin m) :
    {j : Fin n // f.val j = some i} := by
  have hc : Fintype.card {j : Fin n // f.val j = some i} = 1 := by
    simpa only [Fintype.card_eq_nat_card, Option.elim_some] using f.property (some i)
  exact Classical.choice (Fintype.card_pos_iff.mp (by omega))

theorem distinctAssignedPoint_unique (f : DistinctRootAssignments n k m) (i : Fin m)
    (j : Fin n) (hj : f.val j = some i) : j = (distinctAssignedPoint f i).val := by
  have hc : Fintype.card {j : Fin n // f.val j = some i} = 1 := by
    simpa only [Fintype.card_eq_nat_card, Option.elim_some] using f.property (some i)
  letI : Subsingleton {j : Fin n // f.val j = some i} :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  exact congrArg Subtype.val (Subsingleton.elim (⟨j, hj⟩ : {j // f.val j = some i}) _)

def injectionOfDistinctAssignment (f : DistinctRootAssignments n k m) : Fin m ↪ Fin n where
  toFun i := (distinctAssignedPoint f i).val
  inj' i j h := Option.some.inj ((distinctAssignedPoint f i).property.symm.trans
    ((congrArg f.val h).trans (distinctAssignedPoint f j).property))

def assignmentOfInjection (e : Fin m ↪ Fin n) (j : Fin n) : Option (Fin m) :=
  if h : ∃ i : Fin m, e i = j then some (Classical.choose h) else none

theorem assignmentOfInjection_some_iff (e : Fin m ↪ Fin n) (j : Fin n) (i : Fin m) :
    assignmentOfInjection e j = some i ↔ j = e i := by
  by_cases h : ∃ i : Fin m, e i = j
  · simp only [assignmentOfInjection, dif_pos h, Option.some.injEq]
    constructor
    · intro hi
      rw [← Classical.choose_spec h, hi]
    · intro hj
      apply e.injective
      exact (Classical.choose_spec h).trans hj
  · rw [assignmentOfInjection, dif_neg h]
    constructor
    · intro hi
      cases hi
    · intro hj
      exact (h ⟨i, hj.symm⟩).elim

theorem assignmentOfInjection_none_iff (e : Fin m ↪ Fin n) (j : Fin n) :
    assignmentOfInjection e j = none ↔ j ∉ Set.range e := by
  by_cases h : ∃ i : Fin m, e i = j
  · rw [assignmentOfInjection, dif_pos h]
    simp only [Option.some_ne_none, Set.mem_range, h, not_true_eq_false]
  · rw [assignmentOfInjection, dif_neg h]
    simp only [Set.mem_range, h, not_false_eq_true]

def injectionSomeFiberEquiv (e : Fin m ↪ Fin n) (i : Fin m) :
    {j : Fin n // assignmentOfInjection e j = some i} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨e i, (assignmentOfInjection_some_iff e (e i) i).mpr rfl⟩
  left_inv j := Subtype.ext ((assignmentOfInjection_some_iff e j.val i).mp j.property).symm
  right_inv j := by cases j; rfl

theorem assignmentOfInjection_count_some (e : Fin m ↪ Fin n) (i : Fin m) :
    Fintype.card {j : Fin n // assignmentOfInjection e j = some i} = 1 := by
  simpa only [Fintype.card_unit] using Fintype.card_congr (injectionSomeFiberEquiv e i)

theorem assignmentOfInjection_count_none (hsize : k + m = n) (e : Fin m ↪ Fin n) :
    Fintype.card {j : Fin n // assignmentOfInjection e j = none} = k := by
  have hpred : {j : Fin n // assignmentOfInjection e j = none} ≃
      {j : Fin n // j ∉ Set.range e} :=
    Equiv.subtypeEquivRight (assignmentOfInjection_none_iff e)
  rw [Fintype.card_congr hpred, Fintype.card_subtype_compl]
  have hrange : Fintype.card (Set.range e) = m :=
    (Fintype.card_congr (Equiv.ofInjective e e.injective)).symm.trans (Fintype.card_fin m)
  rw [Fintype.card_fin, hrange]
  omega

def distinctAssignmentOfInjection (hsize : k + m = n) (e : Fin m ↪ Fin n) :
    DistinctRootAssignments n k m := by
  refine ⟨assignmentOfInjection e, ?_⟩
  intro i
  cases i with
  | none =>
      simpa only [Fintype.card_eq_nat_card, Option.elim_none] using
        assignmentOfInjection_count_none hsize e
  | some i =>
      simpa only [Fintype.card_eq_nat_card, Option.elim_some] using
        assignmentOfInjection_count_some e i

/-- The literal correspondence required by the ordered-root trivialization. -/
def distinctRootAssignmentsEquivInjections (hsize : k + m = n) :
    DistinctRootAssignments n k m ≃ (Fin m ↪ Fin n) where
  toFun := injectionOfDistinctAssignment
  invFun := distinctAssignmentOfInjection hsize
  left_inv f := by
    apply Subtype.ext
    funext j
    cases hfj : f.val j with
    | none =>
        apply (assignmentOfInjection_none_iff (injectionOfDistinctAssignment f) j).mpr
        rintro ⟨i, hi⟩
        have hpoint := (distinctAssignedPoint f i).property
        change f.val (injectionOfDistinctAssignment f i) = some i at hpoint
        rw [hi, hfj] at hpoint
        cases hpoint
    | some i =>
        apply (assignmentOfInjection_some_iff (injectionOfDistinctAssignment f) j i).mpr
        exact distinctAssignedPoint_unique f i j hfj
  right_inv e := by
    apply Function.Embedding.ext
    intro i
    change (distinctAssignedPoint (distinctAssignmentOfInjection hsize e) i).val = e i
    exact (assignmentOfInjection_some_iff e _ i).mp
      (distinctAssignedPoint (distinctAssignmentOfInjection hsize e) i).property

@[simp] theorem distinctRootAssignmentsEquivInjections_point
    (hsize : k + m = n) (f : DistinctRootAssignments n k m) (i : Fin m) :
    f.val (distinctRootAssignmentsEquivInjections hsize f i) = some i :=
  (distinctAssignedPoint f i).property

end HigherSpecht
end
end CanonicalSource67

section CanonicalSource68
/- Source: HigherSpecht/PrimaryIntersection.lean -/



/-!
# The actual intersection of the Springer components

The ideal equality in Proposition 7.3 is proved directly from integral
monomial spanning and the genuine column witnesses.  The missing-label count
is performed inside the filling's label set, so each witness annihilates its
own embedded Springer component.  Consequently the same monic leaders that
prove independence modulo `J` prove independence modulo the intersection.
The quotient map is therefore injective.  This argument assumes neither
parameter freeness nor the higher Specht tableau count.
-/

noncomputable section

open Finset MvPolynomial TauCeti
open scoped MonomialOrder

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n : ℕ} {mu : YoungDiagram}

theorem card_incomplete_blocks_le_within
    (s : Finset ℕ) (C : ℕ → Finset (Fin n)) (A Y : Finset (Fin n))
    (hC : (s : Set ℕ).PairwiseDisjoint C)
    (hCA : ∀ j ∈ s, C j ⊆ A) (hYA : Y ⊆ A) :
    (s.filter fun j => ¬ C j ⊆ Y).card ≤ A.card - Y.card := by
  classical
  let D := s.filter fun j => ¬ C j ⊆ Y
  have hex : ∀ j : D, ∃ i : Fin n, i ∈ C j.val ∧ i ∉ Y := by
    intro j
    exact Finset.not_subset.mp (Finset.mem_filter.mp j.property).2
  choose f hf hfY using hex
  let g : D → ↥(A \ Y) := fun j => ⟨f j, Finset.mem_sdiff.mpr
    ⟨hCA j.val (Finset.mem_filter.mp j.property).1 (hf j), hfY j⟩⟩
  have hg : Function.Injective g := by
    intro j l heq
    apply Subtype.ext
    by_contra hne
    have hdisj := hC (Finset.mem_filter.mp j.property).1
      (Finset.mem_filter.mp l.property).1 hne
    have hval : f j = f l := congrArg Subtype.val heq
    exact Finset.disjoint_left.mp hdisj (hval ▸ hf j) (hf l)
  have hcard := Fintype.card_le_of_injective g hg
  simpa only [Fintype.card_coe, Finset.card_sdiff_of_subset hYA] using hcard

theorem columnLabels_complete_card_ge_blockTail
    (U : ↥mu.cells ↪ Fin n) {Y : Finset (Fin n)} (hY : Y ⊆ fillingLabels U) :
    columnTail mu (mu.card - Y.card) ≤
      ∑ j ∈ (Finset.range n).filter (fun j => columnLabels U j ⊆ Y),
        (columnLabels U j).card := by
  classical
  have hUcard : (fillingLabels U).card = mu.card := by
    simp only [fillingLabels, Finset.card_map, Finset.card_univ,
      Fintype.card_coe, YoungDiagram.card]
  have hmun : mu.card ≤ n := by
    rw [← hUcard]
    simpa using Finset.card_le_univ (fillingLabels U)
  let D := (Finset.range n).filter fun j => ¬ columnLabels U j ⊆ Y
  have hD : D.card ≤ mu.card - Y.card := by
    rw [← hUcard]
    exact card_incomplete_blocks_le_within _ _ _ _
      ((columnLabels_pairwiseDisjoint U).subset (Set.subset_univ _))
      (fun j hj => columnLabels_subset_fillingLabels U j) hY
  have hbad := sum_antitone_finset_le_range mu.colLen
    (fun i j hij => mu.colLen_anti i j hij) D hD
  have hsplit : (∑ j ∈ Finset.range n, mu.colLen j) =
      (∑ j ∈ (Finset.range n).filter (fun j => columnLabels U j ⊆ Y), mu.colLen j) +
        ∑ j ∈ D, mu.colLen j := by
    symm
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have htotal := columnTail_add_prefix mu n
  rw [columnTail_eq_zero_of_width_le mu ((rowLen_zero_le_card mu).trans hmun),
    zero_add] at htotal
  have htail := columnTail_add_prefix mu (mu.card - Y.card)
  have hcomplete :
      (∑ j ∈ (Finset.range n).filter (fun j => columnLabels U j ⊆ Y),
        (columnLabels U j).card) =
      ∑ j ∈ (Finset.range n).filter (fun j => columnLabels U j ⊆ Y), mu.colLen j := by
    simp only [card_columnLabels]
  rw [hcomplete]
  omega

theorem columnWitness_mem_blockSpringerHarmonics
    (U : ↥mu.cells ↪ Fin n) (s : ℕ) :
    columnWitness (R := R) U s ∈ dividedHarmonics
      (blockSpringerIdeal R (fillingLabels U) mu) := by
  classical
  rw [blockSpringerIdeal, mem_dividedHarmonics_span_iff]
  rintro f ⟨Y, d, hY, hd, hth, rfl⟩
  let J := (Finset.range n).filter fun j => columnLabels U j ⊆ Y
  have hC : (J : Set ℕ).PairwiseDisjoint (columnLabels U) :=
    (columnLabels_pairwiseDisjoint U).subset (Set.subset_univ _)
  have hmem : ∀ j ∈ J, ∀ e : ℕ, 0 < e →
      elementaryOn (R := R) (columnLabels U j) e ∈
        contractionAnnihilator (columnWitness U s) := by
    intro j hj e he
    exact elementaryOn_column_contract_witness U s j e
      (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) he
  have htail := columnLabels_complete_card_ge_blockTail U hY
  have hUcard : (fillingLabels U).card = mu.card := by
    simp only [fillingLabels, Finset.card_map, Finset.card_univ,
      Fintype.card_coe, YoungDiagram.card]
  rw [hUcard] at hth
  have hYcard : Y.card ≤ mu.card := by
    rw [← hUcard]
    exact Finset.card_le_card hY
  have htail_le : columnTail mu (mu.card - Y.card) ≤ Y.card := by
    have h := columnTail_le_card_sub mu (mu.card - Y.card)
    omega
  have hdegree : Y.card - (∑ j ∈ J, (columnLabels U j).card) < d := by
    dsimp [J] at *
    omega
  exact elementaryOn_mem_of_disjoint_complete_blocks
    (contractionAnnihilator (columnWitness U s)) J (columnLabels U) hC hmem Y
    (fun j hj => (Finset.mem_filter.mp hj).2) hdegree

abbrev SpringerCoordinateBlocks (n : ℕ) (mu : YoungDiagram) :=
  {A : Finset (Fin n) // A.card = mu.card}

def springerComponentIntersection (R : Type*) [CommRing R] (n : ℕ)
    (mu : YoungDiagram) : Ideal (PolynomialRing n R) :=
  ⨅ A : SpringerCoordinateBlocks n mu, blockSpringerIdeal R A.val mu

theorem untruncatedIdeal_le_componentIntersection :
    untruncatedIdeal R n mu ≤ springerComponentIntersection R n mu := by
  apply le_iInf
  intro A
  exact untruncatedIdeal_le_blockSpringerIdeal A.val A.property le_rfl

theorem columnWitness_mem_componentIntersectionHarmonics
    (U : ↥mu.cells ↪ Fin n) (s : ℕ) :
    columnWitness (R := R) U s ∈
      dividedHarmonics (springerComponentIntersection R n mu) := by
  let A : SpringerCoordinateBlocks n mu := ⟨fillingLabels U, by
    simp only [fillingLabels, Finset.card_map, Finset.card_univ,
      Fintype.card_coe, YoungDiagram.card]⟩
  apply dividedHarmonics_antitone (iInf_le (fun A : SpringerCoordinateBlocks n mu =>
    blockSpringerIdeal R A.val mu) A)
  exact columnWitness_mem_blockSpringerHarmonics U s

theorem componentIntersection_staircase_monomials_linearIndependent [Nontrivial R] :
    LinearIndependent R (fun c : UntruncatedStaircaseExponents n mu =>
      Ideal.Quotient.mk (springerComponentIntersection R n mu)
        (MvPolynomial.monomial c.val 1)) := by
  apply linearIndependent_quotient_monomials_of_monic_harmonics MonomialOrder.lex
  rintro c ⟨s, U, hU, hc⟩
  let w := columnWitness (R := R) U s
  have hw : MonomialOrder.lex.Monic w := columnWitness_monic U hU s
  have hdeg : MonomialOrder.lex.degree w = staircaseVector U s := columnWitness_degree U hU s
  have hc' : c ≤ MonomialOrder.lex.degree w := by rwa [hdeg]
  have hsub : MonomialOrder.lex.degree w - c ≤ MonomialOrder.lex.degree w := tsub_le_self
  refine ⟨contractMonomial (MonomialOrder.lex.degree w - c) w,
    contractMonomial_mem_dividedHarmonics
      (columnWitness_mem_componentIntersectionHarmonics U s) _, ?_,
    monic_contractMonomial MonomialOrder.lex hw _ hsub⟩
  rw [degree_contractMonomial MonomialOrder.lex hw.ne_zero _ hsub,
    tsub_tsub_cancel_of_le hc']

/-- Proposition 7.3's exact ideal identity.  It holds integrally and over
every nontrivial commutative coefficient ring.  Each component agrees with
the extension of the original Springer ideal by `blockSpringerIdeal_eq_map`. -/
theorem untruncatedIdeal_eq_componentIntersection [Nontrivial R]
    (hn : mu.card ≤ n) :
    untruncatedIdeal R n mu = springerComponentIntersection R n mu := by
  have hle := untruncatedIdeal_le_componentIntersection (R := R) (n := n) (mu := mu)
  let f : UntruncatedRing R n mu →ₗ[R]
      (PolynomialRing n R ⧸ springerComponentIntersection R n mu) :=
    (Ideal.Quotient.factorₐ R hle).toLinearMap
  have hf : Function.Injective f := by
    apply LinearMap.injective_of_linearIndependent
      (untruncated_staircase_monomials_span (R := R) hn)
    exact componentIntersection_staircase_monomials_linearIndependent
  apply le_antisymm hle
  intro p hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hf
  change Ideal.Quotient.mk (springerComponentIntersection R n mu) p = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hp

end HigherSpecht
end
end CanonicalSource68

section CanonicalSource69
/- Source: HigherSpecht/BlockNilpotence.lean -/



/-!
# Nilpotent coordinates and the actual reduced support

Every coordinate in a Springer block satisfies the explicit power relation
`x_i ^ |A| = 0`.  Together with the generator inclusion in the coordinate
ideal this identifies the radical over every coefficient domain.  Combining
it with the actual intersection theorem gives the full reduced support,
including the empty partition.
-/

noncomputable section

open Finset MvPolynomial TauCeti

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n : ℕ}

def coordinateIdeal (R : Type*) [CommRing R] (A : Finset (Fin n)) :
    Ideal (PolynomialRing n R) :=
  Ideal.span (MvPolynomial.X '' (A : Set (Fin n)))

theorem blockSpringer_characteristic (A : Finset (Fin n)) (mu : YoungDiagram)
    (hA : A.card = mu.card) :
    coordinateCharacteristic A
        (fun i => Ideal.Quotient.mk (blockSpringerIdeal R A mu) (MvPolynomial.X i)) =
      Polynomial.X ^ A.card := by
  apply coordinateCharacteristic_eq_X_pow_of_elementary
  intro d hd
  have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr
    (blockSpringer_global_elementary (R := R) A mu hA hd)
  simpa only [elementaryOn, elementaryValue, map_sum, map_prod] using hzero

theorem X_pow_card_mem_blockSpringerIdeal (A : Finset (Fin n)) (mu : YoungDiagram)
    (hA : A.card = mu.card) {i : Fin n} (hi : i ∈ A) :
    (MvPolynomial.X i : PolynomialRing n R) ^ A.card ∈ blockSpringerIdeal R A mu := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_pow]
  have hz := coordinateCharacteristic_eval_root A
    (fun i => Ideal.Quotient.mk (blockSpringerIdeal R A mu) (MvPolynomial.X i)) hi
  rw [blockSpringer_characteristic A mu hA] at hz
  simpa only [Polynomial.eval_pow, Polynomial.eval_X] using hz

theorem coordinateIdeal_le_radical_blockSpringerIdeal
    (A : Finset (Fin n)) (mu : YoungDiagram) (hA : A.card = mu.card) :
    coordinateIdeal R A ≤ (blockSpringerIdeal R A mu).radical := by
  apply Ideal.span_le.mpr
  rintro p ⟨i, hi, rfl⟩
  exact Ideal.mem_radical_iff.mpr ⟨A.card, X_pow_card_mem_blockSpringerIdeal A mu hA hi⟩

theorem blockSpringerIdeal_radical [Nontrivial R] [NoZeroDivisors R]
    (A : Finset (Fin n)) (mu : YoungDiagram) (hA : A.card = mu.card) :
    (blockSpringerIdeal R A mu).radical = coordinateIdeal R A := by
  apply le_antisymm
  · exact (MvPolynomial.span_X_image_isPrime (R := R) (A : Set (Fin n))).radical_le_iff.mpr
      (blockSpringerIdeal_le_coordinateIdeal A mu hA)
  · exact coordinateIdeal_le_radical_blockSpringerIdeal A mu hA

theorem radical_iInf_finite {S : Type*} [CommRing S] {ι : Type*} [Fintype ι]
    (I : ι → Ideal S) : (⨅ i, I i).radical = ⨅ i, (I i).radical := by
  apply le_antisymm (Ideal.radical_iInf_le I)
  intro x hx
  have hx' : ∀ i, ∃ e : ℕ, x ^ e ∈ I i := by
    intro i
    exact Ideal.mem_radical_iff.mp ((Ideal.mem_iInf.mp hx) i)
  choose e he using hx'
  apply Ideal.mem_radical_iff.mpr
  refine ⟨∑ i, e i, Ideal.mem_iInf.mpr fun i => ?_⟩
  exact (I i).pow_mem_of_pow_mem (he i)
    (Finset.single_le_sum (fun j hj => Nat.zero_le _) (Finset.mem_univ i))

/-- The reduced support assertion in Proposition 7.3, as an exact equality
of radical ideals over a field or over the integers. -/
theorem untruncatedIdeal_radical_eq_coordinate_intersection
    [Nontrivial R] [NoZeroDivisors R] {mu : YoungDiagram} (hn : mu.card ≤ n) :
    (untruncatedIdeal R n mu).radical =
      ⨅ A : SpringerCoordinateBlocks n mu, coordinateIdeal R A.val := by
  classical
  rw [untruncatedIdeal_eq_componentIntersection hn, springerComponentIntersection,
    radical_iInf_finite]
  apply iInf_congr
  intro A
  exact blockSpringerIdeal_radical A.val mu A.property

end HigherSpecht
end
end CanonicalSource69

section CanonicalSource70
/- Source: HigherSpecht/SpringerPrimary.lean -/



/-!
# Primaryness of the integral Springer algebra

The actual integral staircase basis supplies torsion-freeness.  The
augmentation kernel is nilpotent elementwise by the explicit coordinate
power relations.  An element with nonzero augmentation is a regular scalar
plus a nilpotent element, hence is regular.  This proves primaryness over
every coefficient domain, including the integers; no characteristic-zero
or factorial-invertibility assumption enters.
-/

noncomputable section

open Finset MvPolynomial TauCeti Module

namespace HigherSpecht

theorem isRegular_add_of_nilpotent {S : Type*} [CommRing S] {a b : S}
    (ha : IsRegular a) (hb : IsNilpotent b) : IsRegular (a + b) := by
  apply (Commute.isRegular_iff (fun z => Commute.all (a + b) z)).mpr
  apply isLeftRegular_of_non_zero_divisor
  intro x hx
  have hax : a * x = (-b) * x := by
    rw [neg_mul]
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_mul] using hx)
  have hpow : ∀ k : ℕ, a ^ k * x = (-b) ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        a ^ (k + 1) * x = a ^ k * (a * x) := by rw [pow_succ, mul_assoc]
        _ = a ^ k * ((-b) * x) := by rw [hax]
        _ = (-b) * (a ^ k * x) := by ring
        _ = (-b) * ((-b) ^ k * x) := by rw [ih]
        _ = (-b) ^ (k + 1) * x := by rw [pow_succ]; ring
  obtain ⟨k, hk⟩ := hb
  have hzero : a ^ k * x = 0 := by
    rw [hpow, neg_pow, hk, mul_zero, zero_mul]
  exact (ha.pow k).left.mul_left_eq_zero_iff.mp hzero

theorem isRegular_algebraMap_of_torsionFree
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [Module.IsTorsionFree R S] {a : R} (ha : a ≠ 0) :
    IsRegular (algebraMap R S a) := by
  apply (Commute.isRegular_iff (fun z => Commute.all (algebraMap R S a) z)).mpr
  intro x y hxy
  apply (IsRegular.of_ne_zero ha).isSMulRegular
  simpa only [Algebra.smul_def] using hxy

variable {R : Type*} [CommRing R]

def springerAugmentation (mu : YoungDiagram) : SpringerRing R mu →ₐ[R] R :=
  Ideal.Quotient.liftₐ (springerIdeal R mu)
    (MvPolynomial.aeval fun _ : Fin mu.card => (0 : R)) (by
      intro p hp
      have hz := untruncatedIdeal_le_constantCoeff_ker (R := R) mu.card mu hp
      simpa only [RingHom.mem_ker, MvPolynomial.aeval_zero', Algebra.algebraMap_self,
        RingHom.id_apply] using hz)

@[simp] theorem springerAugmentation_mk (mu : YoungDiagram) (p : PolynomialRing mu.card R) :
    springerAugmentation (R := R) mu (Ideal.Quotient.mk (springerIdeal R mu) p) =
      p.constantCoeff := by
  change (MvPolynomial.aeval (fun _ : Fin mu.card => (0 : R))) p = _
  simp only [MvPolynomial.aeval_zero', Algebra.algebraMap_self, RingHom.id_apply]

@[simp] theorem springerAugmentation_algebraMap (mu : YoungDiagram) (r : R) :
    springerAugmentation (R := R) mu (algebraMap R (SpringerRing R mu) r) = r :=
  (springerAugmentation mu).commutes r

theorem springerRing_nontrivial [Nontrivial R] (mu : YoungDiagram) :
    Nontrivial (SpringerRing R mu) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have hz := congrArg (springerAugmentation (R := R) mu) h
  exact zero_ne_one (by simpa only [map_zero, map_one] using hz)

theorem coordinateIdeal_univ_eq_ker_constantCoeff {n : ℕ} :
    coordinateIdeal R (Finset.univ : Finset (Fin n)) =
      RingHom.ker (MvPolynomial.constantCoeff : PolynomialRing n R →+* R) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨i, hi, rfl⟩
    change MvPolynomial.constantCoeff (MvPolynomial.X i : PolynomialRing n R) = 0
    exact MvPolynomial.constantCoeff_X R i
  · intro p hp
    apply MvPolynomial.mem_ideal_span_X_image.mpr
    intro a ha
    have ha0 : a ≠ 0 := by
      intro he
      subst a
      exact (MvPolynomial.mem_support_iff.mp ha) hp
    obtain ⟨i, hi⟩ : ∃ i : Fin n, a i ≠ 0 := by
      by_contra h
      push_neg at h
      exact ha0 (Finsupp.ext h)
    exact ⟨i, Finset.mem_univ i, hi⟩

theorem springer_isNilpotent_of_augmentation_eq_zero (mu : YoungDiagram)
    {x : SpringerRing R mu} (hx : springerAugmentation mu x = 0) : IsNilpotent x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [springerAugmentation_mk] at hx
  have hp : p ∈ coordinateIdeal R (Finset.univ : Finset (Fin mu.card)) := by
    rw [coordinateIdeal_univ_eq_ker_constantCoeff]
    exact hx
  have hr := coordinateIdeal_le_radical_blockSpringerIdeal
    (R := R) Finset.univ mu (by simp) hp
  rw [blockSpringerIdeal_univ mu le_rfl] at hr
  obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp hr
  refine ⟨k, ?_⟩
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hk

theorem springerRing_free [Nontrivial R] (mu : YoungDiagram) :
    Module.Free R (SpringerRing R mu) :=
  Module.Free.of_basis (untruncatedStandardMonomialBasis (R := R) (μ := mu) le_rfl)

theorem springer_regular_of_augmentation_ne_zero [IsDomain R]
    (mu : YoungDiagram) {x : SpringerRing R mu}
    (hx : springerAugmentation mu x ≠ 0) : IsRegular x := by
  letI := springerRing_free (R := R) mu
  let a := algebraMap R (SpringerRing R mu) (springerAugmentation mu x)
  have ha : IsRegular a := isRegular_algebraMap_of_torsionFree hx
  have hb : IsNilpotent (x - a) :=
    springer_isNilpotent_of_augmentation_eq_zero mu (by
      simp only [a, map_sub, springerAugmentation_algebraMap, sub_self])
  convert isRegular_add_of_nilpotent ha hb using 1 <;> ring

/-- The zero ideal in the genuine Springer quotient is primary, over every
coefficient domain.  Its freeness was established from the integral monomial
basis, not assumed as a premise. -/
theorem springerRing_bot_isPrimary [IsDomain R] (mu : YoungDiagram) :
    (⊥ : Ideal (SpringerRing R mu)).IsPrimary := by
  letI := springerRing_nontrivial (R := R) mu
  apply Ideal.isPrimary_iff.mpr
  refine ⟨bot_ne_top, ?_⟩
  intro x y hxy
  change x * y = 0 at hxy
  by_cases hy : springerAugmentation mu y = 0
  · right
    obtain ⟨k, hk⟩ := springer_isNilpotent_of_augmentation_eq_zero mu hy
    exact Ideal.mem_radical_iff.mpr ⟨k, hk⟩
  · left
    exact (springer_regular_of_augmentation_ne_zero mu hy).right.mul_right_eq_zero_iff.mp hxy

theorem springerIdeal_isPrimary [IsDomain R] (mu : YoungDiagram) :
    (springerIdeal R mu).IsPrimary := by
  have h := (springerRing_bot_isPrimary (R := R) mu).comap
    (Ideal.Quotient.mk (springerIdeal R mu))
  simpa only [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using h

end HigherSpecht
end
end CanonicalSource70

section CanonicalSource71
/- Source: HigherSpecht/SpringerTrivialFactors.lean -/



/-! The zero extra part and the size-one column factors in the distinct-root
fiber are eliminated by actual shape equality and actual quotient maps. -/

noncomputable section

open TauCeti MvPolynomial Finset

namespace HigherSpecht

@[simp] theorem adjoinOnes_zero (lam : YoungDiagram) : adjoinOnes lam 0 = lam := by
  ext c
  rcases c with ⟨i, j⟩
  simp only [YoungDiagram.mem_cells, mem_adjoinOnes, add_zero]
  constructor
  · rintro (h | ⟨hi, hj⟩)
    · exact h
    · subst j
      exact YoungDiagram.mem_iff_lt_colLen.mpr hi
  · exact Or.inl

variable {R : Type*} [CommRing R]

theorem springerColumnOne_X_mem (i : Fin (columnPartition 1).card) :
    (MvPolynomial.X i : PolynomialRing (columnPartition 1).card R) ∈
      springerIdeal R (columnPartition 1) := by
  have h := X_pow_card_mem_blockSpringerIdeal (R := R)
    (Finset.univ : Finset (Fin (columnPartition 1).card)) (columnPartition 1)
    (by simp) (Finset.mem_univ i)
  rw [blockSpringerIdeal_univ _ (Nat.le_refl _)] at h
  change (MvPolynomial.X i : PolynomialRing (columnPartition 1).card R) ∈
    untruncatedIdeal R (columnPartition 1).card (columnPartition 1)
  simpa only [Finset.card_univ, Fintype.card_fin, columnPartition_card, pow_one] using h

@[simp] theorem springerColumnOne_X_eq_zero (i : Fin (columnPartition 1).card) :
    Ideal.Quotient.mk (springerIdeal R (columnPartition 1)) (MvPolynomial.X i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (springerColumnOne_X_mem i)

/-- The degree-one coinvariant/Springer factor is literally the coefficient
ring, with its augmentation and coefficient inclusion as inverse maps. -/
def springerColumnOneEquiv : SpringerRing R (columnPartition 1) ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom (springerAugmentation (columnPartition 1))
    (Algebra.ofId R (SpringerRing R (columnPartition 1)))
    (by ext)
    (by
      apply Ideal.Quotient.algHom_ext
      ext i
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        springerAugmentation_mk, MvPolynomial.constantCoeff_X, map_zero,
        AlgHom.id_apply, springerColumnOne_X_eq_zero])

end HigherSpecht
end
end CanonicalSource71

section CanonicalSource72
/- Source: HigherSpecht/UnitTensorFactors.lean -/



/-!
# Removing coefficient-ring factors from the genuine finite tensor product

The distinguished factor is retained, and every other factor is the
coefficient ring itself. The equivalence multiplies the scalar factors
into the distinguished algebra. Its inverse is the actual distinguished
factor inclusion.
-/

noncomputable section

open scoped Classical TensorProduct

namespace HigherSpecht

universe u

variable (K A : Type u) {ι : Type*}

def UnitOptionFactor (i : Option ι) : Type u := i.elim A (fun _ => K)

instance unitOptionFactorCommRing [CommRing K] [CommRing A] (i : Option ι) :
    CommRing (UnitOptionFactor K A i) := by
  cases i <;> dsimp [UnitOptionFactor] <;> infer_instance

instance unitOptionFactorAlgebra [CommRing K] [CommRing A] [Algebra K A]
    (i : Option ι) : Algebra K (UnitOptionFactor K A i) := by
  cases i <;> dsimp [UnitOptionFactor] <;> infer_instance

variable [CommRing K] [CommRing A] [Algebra K A] [Fintype ι]

def unitOptionFactorToBase (i : Option ι) : UnitOptionFactor K A i →ₐ[K] A :=
  match i with
  | none => AlgHom.id K A
  | some _ => Algebra.ofId K A

/-- The actual finite tensor product with any number of coefficient-ring
factors is the distinguished algebra. -/
noncomputable def optionUnitTensorEquiv :
    (⨂[K] i : Option ι, UnitOptionFactor K A i) ≃ₐ[K] A := by
  classical
  exact AlgEquiv.ofAlgHom
    (piTensorAlgLift (R := K) (A := UnitOptionFactor K A (ι := ι))
      (unitOptionFactorToBase K A))
    (PiTensorProduct.singleAlgHom (R := K) (A := UnitOptionFactor K A (ι := ι)) none)
    (by
      apply AlgHom.ext
      intro a
      change piTensorAlgLift (unitOptionFactorToBase K A)
        (PiTensorProduct.singleAlgHom (R := K)
          (A := UnitOptionFactor K A (ι := ι)) none a) = a
      exact piTensorAlgLift_single (R := K) (A := UnitOptionFactor K A (ι := ι))
        (unitOptionFactorToBase K A) (none : Option ι) a)
    (by
      apply PiTensorProduct.algHom_ext
      intro i
      cases i with
      | none =>
          apply AlgHom.ext
          intro a
          change PiTensorProduct.singleAlgHom (R := K)
              (A := UnitOptionFactor K A (ι := ι)) none
              (piTensorAlgLift (unitOptionFactorToBase K A)
                (PiTensorProduct.singleAlgHom none a)) =
            PiTensorProduct.singleAlgHom none a
          exact congrArg (PiTensorProduct.singleAlgHom (R := K)
            (A := UnitOptionFactor K A (ι := ι)) none)
            (piTensorAlgLift_single (R := K) (A := UnitOptionFactor K A (ι := ι))
              (unitOptionFactorToBase K A) (none : Option ι) a)
      | some i => ext)

@[simp] theorem optionUnitTensorEquiv_single_none (a : A) :
    optionUnitTensorEquiv K A (ι := ι)
        (PiTensorProduct.singleAlgHom (R := K) (A := UnitOptionFactor K A (ι := ι)) none a) = a := by
  classical
  exact piTensorAlgLift_single (R := K) (A := UnitOptionFactor K A (ι := ι))
    (unitOptionFactorToBase K A) (none : Option ι) a

@[simp] theorem optionUnitTensorEquiv_symm_apply (a : A) :
    (optionUnitTensorEquiv K A (ι := ι)).symm a =
      PiTensorProduct.singleAlgHom (R := K) (A := UnitOptionFactor K A) none a := by
  classical
  rfl

end HigherSpecht
end
end CanonicalSource72

section CanonicalSource73
/- Source: HigherSpecht/OrderedRootTrivialization.lean -/



/-!
# The integral algebra isomorphism on the ordered-root locus

The actual localization makes every root and every pairwise difference
invertible.  The elementary-parameter base-change presentation and the
split-fiber tensor decomposition therefore apply integrally.  The degree-one
column factors are removed by their actual augmentations, and the remaining
index set is the literal set of ordered-root injections.  Equivariance under
coordinate permutations is a separate naturality statement for these maps.
-/

noncomputable section

open TauCeti MvPolynomial
open scoped Polynomial TensorProduct BigOperators Classical

namespace HigherSpecht

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]

@[simp] theorem distinctRootBlockShape_none (lam : YoungDiagram) :
    rootBlockShape lam 0 (splitRootMultiplicities lam 0 (fun _ : ι => 1)) none none = lam := by
  rw [rootBlockShape, if_pos rfl, adjoinOnes_zero]

@[simp] theorem distinctRootBlockShape_some (lam : YoungDiagram) (i : ι) :
    rootBlockShape lam 0 (splitRootMultiplicities lam 0 (fun _ : ι => 1)) none (some i) =
      columnPartition 1 := by
  rw [rootBlockShape, if_neg (Option.some_ne_none i)]
  rfl

/-- Transport the actual Springer quotient algebra along an equality of shapes. -/
def springerShapeEquiv {mu nu : YoungDiagram} (h : mu = nu) :
    SpringerRing R mu ≃ₐ[R] SpringerRing R nu := by
  subst nu
  exact AlgEquiv.refl

def distinctRootFactorEquiv (lam : YoungDiagram) (i : Option ι) :
    SpringerRing R (rootBlockShape lam 0 (splitRootMultiplicities lam 0 (fun _ : ι => 1))
      none i) ≃ₐ[R] UnitOptionFactor R (SpringerRing R lam) i := by
  cases i with
  | none =>
      change SpringerRing R
        (rootBlockShape lam 0 (splitRootMultiplicities lam 0 (fun _ : ι => 1))
          none none) ≃ₐ[R] SpringerRing R lam
      exact springerShapeEquiv (R := R) (distinctRootBlockShape_none (ι := ι) lam)
  | some i =>
      change SpringerRing R
        (rootBlockShape lam 0 (splitRootMultiplicities lam 0 (fun _ : ι => 1))
          none (some i)) ≃ₐ[R] R
      exact (springerShapeEquiv (R := R) (distinctRootBlockShape_some lam i)).trans
        (springerColumnOneEquiv (R := R))

def distinctRootTensorEquiv (lam : YoungDiagram) :
    (⨂[R] i : Option ι,
      SpringerRing R (rootBlockShape lam 0 (splitRootMultiplicities lam 0 (fun _ : ι => 1))
        none i)) ≃ₐ[R] SpringerRing R lam := by
  let E : (⨂[R] i : Option ι,
      SpringerRing R (rootBlockShape lam 0 (splitRootMultiplicities lam 0 (fun _ : ι => 1))
        none i)) ≃ₐ[R]
      ⨂[R] i : Option ι, UnitOptionFactor R (SpringerRing R lam) i :=
    piTensorAlgEquiv (distinctRootFactorEquiv (R := R) (ι := ι) lam)
  exact E.trans (optionUnitTensorEquiv R (SpringerRing R lam))

@[simp] theorem distinctRootTensorEquiv_single (lam : YoungDiagram) (i : Option ι)
    (b : SpringerRing R
      (rootBlockShape lam 0 (splitRootMultiplicities lam 0 (fun _ : ι => 1)) none i)) :
    distinctRootTensorEquiv lam (PiTensorProduct.singleAlgHom i b) =
      unitOptionFactorToBase R (SpringerRing R lam) i (distinctRootFactorEquiv lam i b) := by
  change optionUnitTensorEquiv R (SpringerRing R lam)
      (piTensorAlgEquiv (distinctRootFactorEquiv (R := R) (ι := ι) lam)
        (PiTensorProduct.singleAlgHom i b)) = _
  rw [piTensorAlgEquiv_single]
  exact piTensorAlgLift_single (unitOptionFactorToBase R (SpringerRing R lam)) i _

def springerCoefficientBaseChangeEquiv (S : Type*) [CommRing S] [Algebra R S]
    (lam : YoungDiagram) :
    S ⊗[R] SpringerRing R lam ≃ₐ[S] SpringerRing S lam :=
  polynomialQuotientBaseChangeEquiv _ _
    (map_untruncatedIdeal (algebraMap R S) lam.card lam)

@[simp] theorem springerCoefficientBaseChangeEquiv_tmul
    (S : Type*) [CommRing S] [Algebra R S] (lam : YoungDiagram)
    (s : S) (p : PolynomialRing lam.card R) :
    springerCoefficientBaseChangeEquiv S lam
        (s ⊗ₜ[R] Ideal.Quotient.mk (springerIdeal R lam) p) =
      Ideal.Quotient.mk (springerIdeal S lam) (s • MvPolynomial.map (algebraMap R S) p) :=
  polynomialQuotientBaseChangeEquiv_tmul _ _ _ s p

/-- The elementary-parameter presentation with its parameter family transported
along the specified equality.  The underlying map is the existing presentation. -/
def elementaryParameterBaseChangeEquivOfEq
    (n : ℕ) (lam : YoungDiagram) (S : Type*) [CommRing S]
    [Algebra (ElementaryParameterRing R n lam) S]
    (a : Fin (n - lam.card) → S)
    (ha : (fun i : Fin (n - lam.card) =>
      algebraMap (ElementaryParameterRing R n lam) S (MvPolynomial.X i)) = a) :
    S ⊗[ElementaryParameterRing R n lam] UntruncatedRing R n lam ≃ₐ[S]
      ParameterFiber S n lam (n - lam.card) a := by
  rw [← ha]
  exact elementaryParameterBaseChangeEquiv (R := R) n lam S

/-- Evaluate a composite presentation with a constant factor algebra and
one factor equivalence. The original composite supplies every inverse and
algebra law. The helper uses precisely the semiring structures carried by
`AlgEquiv`, so tensor and quotient algebra instances remain aligned. -/
def componentwiseComposite
    {K : Type*} [CommSemiring K]
    {A : Type*} {B : Type*} {C : Type*} {V : Type*}
    {ι : Type*} {κ : Type*} {D : Type*}
    [Semiring A] [Semiring B] [Semiring C] [Semiring V]
    [Semiring D]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra K V]
    [Algebra K D]
    (P : A ≃ₐ[K] B) (Q : B ≃ₐ[K] C) (F : C ≃ₐ[K] (ι → D))
    (G : D ≃ₐ[K] V) (h : ι ≃ κ) : A ≃ₐ[K] (κ → V) := by
  let T := AlgEquiv.piCongrRight (fun _ : ι => G)
  let J := AlgEquiv.piCongrLeft' K (fun _ : ι => V) h
  let E := (((P.trans Q).trans F).trans T).trans J
  exact { E with toFun := fun x i => G.toEquiv.toFun (F.toEquiv.toFun (Q.toEquiv.toFun (P.toEquiv.toFun x)) (h.invFun i)) }

theorem componentwiseComposite_apply
    {K : Type*} [CommSemiring K]
    {A : Type*} {B : Type*} {C : Type*} {V : Type*}
    {ι : Type*} {κ : Type*} {D : Type*}
    [Semiring A] [Semiring B] [Semiring C] [Semiring V]
    [Semiring D]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra K V]
    [Algebra K D]
    (P : A ≃ₐ[K] B) (Q : B ≃ₐ[K] C) (F : C ≃ₐ[K] (ι → D))
    (G : D ≃ₐ[K] V) (h : ι ≃ κ) (x : A) (i : κ) :
    componentwiseComposite P Q F G h x i =
      G (F (Q (P x)) (h.symm i)) := rfl

/-- The explicit function projections preserve the original composite,
including its inverse and its algebra laws. -/
theorem componentwiseComposite_eq_trans
    {K : Type*} [CommSemiring K]
    {A : Type*} {B : Type*} {C : Type*} {V : Type*}
    {ι : Type*} {κ : Type*} {D : Type*}
    [Semiring A] [Semiring B] [Semiring C] [Semiring V] [Semiring D]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra K V] [Algebra K D]
    (P : A ≃ₐ[K] B) (Q : B ≃ₐ[K] C) (F : C ≃ₐ[K] (ι → D))
    (G : D ≃ₐ[K] V) (h : ι ≃ κ) :
    componentwiseComposite P Q F G h =
      ((((P.trans Q).trans F).trans (AlgEquiv.piCongrRight (fun _ : ι => G))).trans
        (AlgEquiv.piCongrLeft' K (fun _ : ι => V) h)) := rfl

/-- A proved presentation package. Both the whole algebra equivalence and its
pointwise formula are retained; no property is supplied as a hypothesis. -/
structure ComponentwiseCertificate
    {K : Type*} [CommSemiring K]
    {A : Type*} {B : Type*} {C : Type*} {V : Type*}
    {ι : Type*} {κ : Type*} {D : Type*}
    [Semiring A] [Semiring B] [Semiring C] [Semiring V] [Semiring D]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra K V] [Algebra K D]
    (P : A ≃ₐ[K] B) (Q : B ≃ₐ[K] C) (F : C ≃ₐ[K] (ι → D))
    (G : D ≃ₐ[K] V) (h : ι ≃ κ) where
  equiv : A ≃ₐ[K] (κ → V)
  eq_componentwise : equiv = componentwiseComposite P Q F G h
  evaluate : ∀ (x : A) (i : κ),
    equiv.toEquiv.toFun x i =
      G.toEquiv.toFun (F.toEquiv.toFun
        (Q.toEquiv.toFun (P.toEquiv.toFun x)) (h.symm.toFun i))

/-- This safe opaque constant has a complete, fully specified constructor body.
Its opacity prevents repeated unfolding of the composite in specializations;
the two proof fields expose its exact mathematical meaning. -/
opaque certifiedComponentwise
    {K : Type*} [CommSemiring K]
    {A : Type*} {B : Type*} {C : Type*} {V : Type*}
    {ι : Type*} {κ : Type*} {D : Type*}
    [Semiring A] [Semiring B] [Semiring C] [Semiring V] [Semiring D]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra K V] [Algebra K D]
    (P : A ≃ₐ[K] B) (Q : B ≃ₐ[K] C) (F : C ≃ₐ[K] (ι → D))
    (G : D ≃ₐ[K] V) (h : ι ≃ κ) : ComponentwiseCertificate P Q F G h :=
  { equiv := componentwiseComposite P Q F G h
    eq_componentwise := rfl
    evaluate := fun _ _ => rfl }

/-- The certificate gives equality of the entire original algebra equivalence,
including the inverse and every algebra law, with the original trans composite. -/
theorem certifiedComponentwise_eq_trans
    {K : Type*} [CommSemiring K]
    {A : Type*} {B : Type*} {C : Type*} {V : Type*}
    {ι : Type*} {κ : Type*} {D : Type*}
    [Semiring A] [Semiring B] [Semiring C] [Semiring V] [Semiring D]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra K V] [Algebra K D]
    (P : A ≃ₐ[K] B) (Q : B ≃ₐ[K] C) (F : C ≃ₐ[K] (ι → D))
    (G : D ≃ₐ[K] V) (h : ι ≃ κ) :
    (certifiedComponentwise P Q F G h).equiv =
      ((((P.trans Q).trans F).trans (AlgEquiv.piCongrRight (fun _ : ι => G))).trans
        (AlgEquiv.piCongrLeft' K (fun _ : ι => V) h)) :=
  (certifiedComponentwise P Q F G h).eq_componentwise.trans
    (componentwiseComposite_eq_trans P Q F G h)


/-- Convert the raw projections to the usual coercion formula while all maps
and algebra structures are still abstract. -/
theorem componentwise_coercion_of_toEquiv
    {K : Type*} [CommSemiring K]
    {A : Type*} {B : Type*} {C : Type*} {V : Type*}
    {ι : Type*} {κ : Type*} {D : Type*}
    [Semiring A] [Semiring B] [Semiring C] [Semiring V] [Semiring D]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra K V] [Algebra K D]
    (P : A ≃ₐ[K] B) (Q : B ≃ₐ[K] C) (F : C ≃ₐ[K] (ι → D))
    (G : D ≃ₐ[K] V) (h : ι ≃ κ) (T : A ≃ₐ[K] (κ → V))
    (x : A) (i : κ)
    (hraw : T.toEquiv.toFun x i =
      G.toEquiv.toFun (F.toEquiv.toFun
        (Q.toEquiv.toFun (P.toEquiv.toFun x)) (h.symm.toFun i))) :
    T x i = G (F (Q (P x)) (h.symm i)) := by
  exact hraw

/-- Evaluate the componentwise construction through structure projections.
This is the same function as the coercion-based formula, before specialization
to the concrete quotient and tensor algebras. -/
private theorem componentwiseComposite_toEquiv_apply
    {K : Type*} [CommSemiring K]
    {A : Type*} {B : Type*} {C : Type*} {V : Type*}
    {ι : Type*} {κ : Type*} {D : Type*}
    [Semiring A] [Semiring B] [Semiring C] [Semiring V]
    [Semiring D]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra K V]
    [Algebra K D]
    (P : A ≃ₐ[K] B) (Q : B ≃ₐ[K] C) (F : C ≃ₐ[K] (ι → D))
    (G : D ≃ₐ[K] V) (h : ι ≃ κ) (x : A) (i : κ) :
    (componentwiseComposite P Q F G h).toEquiv.toFun x i =
      G.toEquiv.toFun (F.toEquiv.toFun
        (Q.toEquiv.toFun (P.toEquiv.toFun x)) (h.symm.toFun i)) := rfl


/-- The actual elementary-parameter presentation, named once so all later
maps retain the same parameter-family equality transport. -/
def orderedRootParameterPresentation (n : ℕ) (lam : YoungDiagram) :
    OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
        UntruncatedRing R n lam ≃ₐ[OrderedRootRing R (n - lam.card)]
      ParameterFiber (OrderedRootRing R (n - lam.card)) n lam (n - lam.card)
        (orderedRootElementaryParameters (R := R) (n - lam.card)) :=
  elementaryParameterBaseChangeEquivOfEq (R := R) n lam
    (OrderedRootRing R (n - lam.card))
    (orderedRootElementaryParameters (R := R) (n - lam.card))
    (by funext i; exact orderedRootParameter_algebraMap_X n lam i)

/-- The original equality-of-ideals map from elementary parameters to their
monic parameter polynomial, named independently of later compositions. -/
def orderedRootPolynomialPresentation (n : ℕ) (lam : YoungDiagram) :
    ParameterFiber (OrderedRootRing R (n - lam.card)) n lam (n - lam.card)
        (orderedRootElementaryParameters (R := R) (n - lam.card)) ≃ₐ[
          OrderedRootRing R (n - lam.card)]
      PolynomialFiber (OrderedRootRing R (n - lam.card)) n lam (n - lam.card)
        (parameterPolynomial (orderedRootElementaryParameters (R := R) (n - lam.card))) :=
  Ideal.quotientEquivAlgOfEq (OrderedRootRing R (n - lam.card))
    (polynomialFiberIdeal_parameterPolynomial lam
      (orderedRootElementaryParameters (R := R) (n - lam.card))).symm

/-- Explicit zero-block evaluations used in the split presentation. -/
theorem orderedRootSplitValue_none (m : ℕ) :
    splitRootValue (orderedRoot (R := R) m) none = 0 := rfl

theorem orderedRootSplitMultiplicity_none (lam : YoungDiagram) (m : ℕ) :
    splitRootMultiplicities lam 0 (fun _ : Fin m => 1) none = lam.card + 0 := rfl

/-- The original split-fiber tensor presentation. Its factorization and
zero-block proofs are constructed once, rather than copied into applications. -/
def orderedRootSplitPresentation [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    PolynomialFiber (OrderedRootRing R (n - lam.card)) n lam (n - lam.card)
        (parameterPolynomial (orderedRootElementaryParameters (R := R) (n - lam.card))) ≃ₐ[
          OrderedRootRing R (n - lam.card)]
      ∀ _f : PrescribedRootAssignments n
          (splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)),
        ⨂[OrderedRootRing R (n - lam.card)] i : Option (Fin (n - lam.card)),
          SpringerRing (OrderedRootRing R (n - lam.card))
            (rootBlockShape lam 0
              (splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)) none i) := by
  let c := orderedRoot (R := R) (n - lam.card)
  let a := orderedRootElementaryParameters (R := R) (n - lam.card)
  exact polynomialFiberSpringerTensorProductEquiv (Nat.add_sub_of_le hk)
    (parameterPolynomial a) (parameterPolynomial_monic a) (parameterPolynomial_natDegree a)
    0 (splitRootValue c)
    (splitRootValue_unitDifferences c (orderedRoot_isUnit (n - lam.card))
      (orderedRoot_pairwise_units (n - lam.card)))
    none (splitRootMultiplicities lam 0 (fun _ => 1))
    (orderedRootSplitValue_none (R := R) (n - lam.card))
    (orderedRootSplitMultiplicity_none lam (n - lam.card))
    (by
      rw [orderedRootParameter_factorization]
      exact splitRootParameter_factorization lam 0 c (fun _ => 1))

/-- The same assignment-to-injection bijection with the literal domain of
the split-fiber presentation. This avoids unfolding the content function at
later uses of the componentwise algebra equivalence. -/
def orderedRootAssignmentEquiv
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    PrescribedRootAssignments n
        (splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)) ≃
      (Fin (n - lam.card) ↪ Fin n) :=
  distinctRootAssignmentsEquivInjections (k := lam.card) (m := n - lam.card)
    (Nat.add_sub_of_le hk)

/-- Naming the literal domain does not change the original coordinate
assignment, inverse assignment, or injection. -/
theorem orderedRootAssignmentEquiv_eq
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    orderedRootAssignmentEquiv n lam hk =
      distinctRootAssignmentsEquivInjections (k := lam.card) (m := n - lam.card)
        (Nat.add_sub_of_le hk) := rfl

/-- The literal five-presentation construction, with its whole-map equality
and evaluation property supplied by the fully defined generic certificate. -/
def orderedRootTrivializationCertificate [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
  ComponentwiseCertificate (K := OrderedRootRing R (n - lam.card))
    (A := OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam)
    (B := ParameterFiber (OrderedRootRing R (n - lam.card)) n lam (n - lam.card)
      (orderedRootElementaryParameters (R := R) (n - lam.card)))
    (C := PolynomialFiber (OrderedRootRing R (n - lam.card)) n lam (n - lam.card)
      (parameterPolynomial (orderedRootElementaryParameters (R := R) (n - lam.card))))
    (V := SpringerRing (OrderedRootRing R (n - lam.card)) lam)
    (κ := Fin (n - lam.card) ↪ Fin n)
    (ι := PrescribedRootAssignments n
      (splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)))
    (D := ⨂[OrderedRootRing R (n - lam.card)] i : Option (Fin (n - lam.card)),
      SpringerRing (OrderedRootRing R (n - lam.card))
        (rootBlockShape lam 0
          (splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)) none i))
    (orderedRootParameterPresentation (R := R) n lam)
    (orderedRootPolynomialPresentation (R := R) n lam)
    (orderedRootSplitPresentation (R := R) n lam hk)
    (distinctRootTensorEquiv (R := OrderedRootRing R (n - lam.card))
      (ι := Fin (n - lam.card)) lam)
    (orderedRootAssignmentEquiv n lam hk) :=
  certifiedComponentwise (K := OrderedRootRing R (n - lam.card))
    (A := OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam)
    (B := ParameterFiber (OrderedRootRing R (n - lam.card)) n lam (n - lam.card)
      (orderedRootElementaryParameters (R := R) (n - lam.card)))
    (C := PolynomialFiber (OrderedRootRing R (n - lam.card)) n lam (n - lam.card)
      (parameterPolynomial (orderedRootElementaryParameters (R := R) (n - lam.card))))
    (V := SpringerRing (OrderedRootRing R (n - lam.card)) lam)
    (κ := Fin (n - lam.card) ↪ Fin n)
    (ι := PrescribedRootAssignments n
      (splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)))
    (D := ⨂[OrderedRootRing R (n - lam.card)] i : Option (Fin (n - lam.card)),
      SpringerRing (OrderedRootRing R (n - lam.card))
        (rootBlockShape lam 0
          (splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)) none i))
    (orderedRootParameterPresentation (R := R) n lam)
    (orderedRootPolynomialPresentation (R := R) n lam)
    (orderedRootSplitPresentation (R := R) n lam hk)
    (distinctRootTensorEquiv (R := OrderedRootRing R (n - lam.card))
      (ι := Fin (n - lam.card)) lam)
    (orderedRootAssignmentEquiv n lam hk)

/-- The full algebraic ordered-root trivialization over a coefficient domain.
This is independent of characteristic and does not invert a factorial. -/
def orderedRootTrivialization [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
        UntruncatedRing R n lam ≃ₐ[OrderedRootRing R (n - lam.card)]
      ∀ _e : Fin (n - lam.card) ↪ Fin n,
        SpringerRing (OrderedRootRing R (n - lam.card)) lam :=
  (orderedRootTrivializationCertificate (R := R) n lam hk).equiv

/-- Equality to the exact original componentwise algebra equivalence.
Together with `componentwiseComposite_eq_trans`, this identifies the entire
map, inverse and algebra laws with the original composition of presentations. -/
theorem orderedRootTrivialization_eq_componentwise [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    orderedRootTrivialization (R := R) n lam hk =
  componentwiseComposite (K := OrderedRootRing R (n - lam.card))
    (A := OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam)
    (B := ParameterFiber (OrderedRootRing R (n - lam.card)) n lam (n - lam.card)
      (orderedRootElementaryParameters (R := R) (n - lam.card)))
    (C := PolynomialFiber (OrderedRootRing R (n - lam.card)) n lam (n - lam.card)
      (parameterPolynomial (orderedRootElementaryParameters (R := R) (n - lam.card))))
    (V := SpringerRing (OrderedRootRing R (n - lam.card)) lam)
    (κ := Fin (n - lam.card) ↪ Fin n)
    (ι := PrescribedRootAssignments n
      (splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)))
    (D := ⨂[OrderedRootRing R (n - lam.card)] i : Option (Fin (n - lam.card)),
      SpringerRing (OrderedRootRing R (n - lam.card))
        (rootBlockShape lam 0
          (splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)) none i))
    (orderedRootParameterPresentation (R := R) n lam)
    (orderedRootPolynomialPresentation (R := R) n lam)
    (orderedRootSplitPresentation (R := R) n lam hk)
    (distinctRootTensorEquiv (R := OrderedRootRing R (n - lam.card))
      (ι := Fin (n - lam.card)) lam)
    (orderedRootAssignmentEquiv n lam hk) := by
  exact (orderedRootTrivializationCertificate (R := R) n lam hk).eq_componentwise

/-- Evaluate the concrete presentations with explicit function projections.
The following public formula retains the original coercion-based statement. -/
theorem orderedRootTrivialization_toEquiv_apply [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (x : OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam)
    (e : Fin (n - lam.card) ↪ Fin n) :
    (orderedRootTrivialization (R := R) n lam hk).toEquiv.toFun x e =
      (distinctRootTensorEquiv (R := OrderedRootRing R (n - lam.card))
        (ι := Fin (n - lam.card)) lam).toEquiv.toFun
        ((orderedRootSplitPresentation (R := R) n lam hk).toEquiv.toFun
          ((orderedRootPolynomialPresentation (R := R) n lam).toEquiv.toFun
            ((orderedRootParameterPresentation (R := R) n lam).toEquiv.toFun x))
          ((orderedRootAssignmentEquiv n lam hk).symm.toFun e)) := by
  exact (orderedRootTrivializationCertificate (R := R) n lam hk).evaluate x e

/-- Pointwise evaluation through the named actual presentations. Each
presentation is defined by the original quotient or tensor construction. -/
theorem orderedRootTrivialization_apply [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (x : OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam)
    (e : Fin (n - lam.card) ↪ Fin n) :
    orderedRootTrivialization (R := R) n lam hk x e =
      distinctRootTensorEquiv (R := OrderedRootRing R (n - lam.card))
        (ι := Fin (n - lam.card)) lam
        (orderedRootSplitPresentation (R := R) n lam hk
          (orderedRootPolynomialPresentation (R := R) n lam
            (orderedRootParameterPresentation (R := R) n lam x))
          ((orderedRootAssignmentEquiv n lam hk).symm e)) := by
  exact componentwise_coercion_of_toEquiv (K := OrderedRootRing R (n - lam.card))
    (A := OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam)
    (B := ParameterFiber (OrderedRootRing R (n - lam.card)) n lam (n - lam.card)
      (orderedRootElementaryParameters (R := R) (n - lam.card)))
    (C := PolynomialFiber (OrderedRootRing R (n - lam.card)) n lam (n - lam.card)
      (parameterPolynomial (orderedRootElementaryParameters (R := R) (n - lam.card))))
    (V := SpringerRing (OrderedRootRing R (n - lam.card)) lam)
    (κ := Fin (n - lam.card) ↪ Fin n)
    (ι := PrescribedRootAssignments n
      (splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)))
    (D := ⨂[OrderedRootRing R (n - lam.card)] i : Option (Fin (n - lam.card)),
      SpringerRing (OrderedRootRing R (n - lam.card))
        (rootBlockShape lam 0
          (splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)) none i))
    (orderedRootParameterPresentation (R := R) n lam)
    (orderedRootPolynomialPresentation (R := R) n lam)
    (orderedRootSplitPresentation (R := R) n lam hk)
    (distinctRootTensorEquiv (R := OrderedRootRing R (n - lam.card))
      (ι := Fin (n - lam.card)) lam)
    (orderedRootAssignmentEquiv n lam hk)
    (orderedRootTrivialization (R := R) n lam hk) x e
    (orderedRootTrivialization_toEquiv_apply (R := R) n lam hk x e)

/-- The product of the literal coefficient-extension inverses, with all
factor types fixed before forming the product algebra equivalence. -/
def springerCoefficientProductBaseChangeEquiv
    (S : Type*) [CommRing S] [Algebra R S] (lam : YoungDiagram) (κ : Type*) :
    (κ → SpringerRing S lam) ≃ₐ[S] (κ → S ⊗[R] SpringerRing R lam) :=
  AlgEquiv.piCongrRight (R := S) (ι := κ)
    (A₁ := fun _ : κ => SpringerRing S lam)
    (A₂ := fun _ : κ => S ⊗[R] SpringerRing R lam)
    (fun _ : κ => (springerCoefficientBaseChangeEquiv (R := R) S lam).symm)

@[simp] theorem springerCoefficientProductBaseChangeEquiv_apply
    (S : Type*) [CommRing S] [Algebra R S] (lam : YoungDiagram) (κ : Type*)
    (x : κ → SpringerRing S lam) (i : κ) :
    springerCoefficientProductBaseChangeEquiv (R := R) S lam κ x i =
      (springerCoefficientBaseChangeEquiv (R := R) S lam).symm (x i) := rfl

/-- The ordered-root trivialization followed by coefficient extension on each
Springer factor, constructed over a generic coefficient domain. -/
def orderedRootTensorTrivialization [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
        UntruncatedRing R n lam ≃ₐ[OrderedRootRing R (n - lam.card)]
      ∀ _e : Fin (n - lam.card) ↪ Fin n,
        OrderedRootRing R (n - lam.card) ⊗[R] SpringerRing R lam := by
  let S := OrderedRootRing R (n - lam.card)
  let I := Fin (n - lam.card) ↪ Fin n
  let E : S ⊗[ElementaryParameterRing R n lam] UntruncatedRing R n lam ≃ₐ[S]
      (I → SpringerRing S lam) :=
    orderedRootTrivialization (R := R) n lam hk
  let T : (I → SpringerRing S lam) ≃ₐ[S] (I → S ⊗[R] SpringerRing R lam) :=
    springerCoefficientProductBaseChangeEquiv (R := R) S lam I
  exact E.trans T

/-- The generic tensor target retains exactly the componentwise
coefficient-extension inverse of the original ordered-root map. -/
theorem orderedRootTensorTrivialization_apply [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (x : OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam)
    (e : Fin (n - lam.card) ↪ Fin n) :
    orderedRootTensorTrivialization (R := R) n lam hk x e =
      (springerCoefficientBaseChangeEquiv (R := R)
        (OrderedRootRing R (n - lam.card)) lam).symm
        (orderedRootTrivialization (R := R) n lam hk x e) := by
  rw [orderedRootTensorTrivialization, AlgEquiv.trans_apply,
    springerCoefficientProductBaseChangeEquiv_apply]

/-- Capture the original coefficient action on the Springer quotient before
specializing the coefficient ring.  The quotient algebra map is the composite
of the polynomial coefficient embedding with the quotient map. -/
abbrev springerCoefficientModule (K : Type*) [CommRing K] (lam : YoungDiagram) :
    Module K (SpringerRing K lam) :=
  @Algebra.toModule K (SpringerRing K lam) _ _
    (Ideal.Quotient.algebra K (I := springerIdeal K lam))

/-- Select that same coefficient action for the integral Springer factor in
tensor products, matching the generic coefficient-extension equivalence. -/
@[reducible] noncomputable instance springerIntModule (lam : YoungDiagram) :
    Module ℤ (SpringerRing ℤ lam) :=
  springerCoefficientModule ℤ lam

/-- The selected action is the unique integer-module structure; no additional
action or mathematical assumption is introduced by its explicit selection. -/
theorem springerIntModule_eq (lam : YoungDiagram) :
    springerIntModule lam =
      (AddCommGroup.toIntModule (SpringerRing ℤ lam) : Module ℤ (SpringerRing ℤ lam)) :=
  Subsingleton.elim _ _

/-- Proposition 7.2's integral algebra isomorphism, including its literal
coefficient extension of the original integral Springer ring.  The tensor
factors are written with the coefficient ring on the left. -/
def proposition_7_2_integral_trivialization
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    OrderedRootRing ℤ (n - lam.card) ⊗[ElementaryParameterRing ℤ n lam]
        UntruncatedRing ℤ n lam ≃ₐ[OrderedRootRing ℤ (n - lam.card)]
      ∀ _e : Fin (n - lam.card) ↪ Fin n,
        OrderedRootRing ℤ (n - lam.card) ⊗[ℤ] SpringerRing ℤ lam :=
  orderedRootTensorTrivialization (R := ℤ) n lam hk

/-- Pointwise evaluation of the final coefficient-extension transport. -/
theorem proposition_7_2_integral_trivialization_apply
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (x : OrderedRootRing ℤ (n - lam.card) ⊗[ElementaryParameterRing ℤ n lam]
      UntruncatedRing ℤ n lam)
    (e : Fin (n - lam.card) ↪ Fin n) :
    proposition_7_2_integral_trivialization n lam hk x e =
      (springerCoefficientBaseChangeEquiv (R := ℤ)
        (OrderedRootRing ℤ (n - lam.card)) lam).symm
        (orderedRootTrivialization (R := ℤ) n lam hk x e) := by
  exact orderedRootTensorTrivialization_apply (R := ℤ) n lam hk x e

end HigherSpecht
end
end CanonicalSource73

section CanonicalSource74
/- Source: HigherSpecht/FiberPermutation.lean -/



/-!
# The actual coordinate-permutation action on split fibers

Coordinate permutations preserve the parameter ideal, carry each root
assignment to its literal reindexing, and rename the corresponding local
block ideal.  The resulting quotient maps and product maps are the natural
ones induced by polynomial renaming, independently of a chosen
trivialization or a higher-Specht basis.
-/

noncomputable section

open TauCeti MvPolynomial Finset
open scoped Classical

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n m : ℕ} {lam : YoungDiagram}
variable {ι : Type*} [Fintype ι]

theorem map_ideal_of_permutationStable {I : Ideal (PolynomialRing n R)}
    (hI : PermutationStable I) (e : Equiv.Perm (Fin n)) :
    I.map (MvPolynomial.rename e).toRingHom = I := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    exact hI e
  · intro p hp
    have hm := Ideal.mem_map_of_mem (MvPolynomial.rename e).toRingHom (hI e.symm p hp)
    change MvPolynomial.rename e (MvPolynomial.rename e.symm p) ∈
      I.map (MvPolynomial.rename e).toRingHom at hm
    simpa only [MvPolynomial.rename_rename, Equiv.self_comp_symm, MvPolynomial.rename_id_apply] using hm

theorem rename_elementaryOn_univ (e : Equiv.Perm (Fin n)) (d : ℕ) :
    MvPolynomial.rename e (elementaryOn (R := R) Finset.univ d) =
      elementaryOn Finset.univ d := by
  rw [rename_elementaryOn]
  congr 1
  exact Finset.map_univ_equiv e

theorem map_parameterFiberIdeal_rename (e : Equiv.Perm (Fin n))
    (a : Fin m → R) :
    (parameterFiberIdeal R n lam m a).map (MvPolynomial.rename e).toRingHom =
      parameterFiberIdeal R n lam m a := by
  unfold parameterFiberIdeal
  rw [Ideal.map_sup, map_ideal_of_permutationStable
    (permutationStable_untruncatedIdeal lam) e, Ideal.map_span, ← Set.range_comp]
  congr 2
  apply congrArg Set.range
  funext i
  change MvPolynomial.rename e (elementaryOn (R := R) Finset.univ (i.val + 1) -
      MvPolynomial.C (a i)) = elementaryOn Finset.univ (i.val + 1) - MvPolynomial.C (a i)
  rw [map_sub, rename_elementaryOn_univ, MvPolynomial.rename_C]

def parameterFiberPermutation (a : Fin m → R) (e : Equiv.Perm (Fin n)) :
    ParameterFiber R n lam m a ≃ₐ[R] ParameterFiber R n lam m a :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv R e)
    (map_parameterFiberIdeal_rename e a).symm

@[simp] theorem parameterFiberPermutation_mk (a : Fin m → R) (e : Equiv.Perm (Fin n))
    (p : PolynomialRing n R) :
    parameterFiberPermutation (lam := lam) a e
        (Ideal.Quotient.mk (parameterFiberIdeal R n lam m a) p) =
      Ideal.Quotient.mk (parameterFiberIdeal R n lam m a) (MvPolynomial.rename e p) :=
  Ideal.quotientEquivAlg_mk _ _ _ _

@[simp] theorem polynomialFiberPermutation_mk (Q : Polynomial R)
    (e : Equiv.Perm (Fin n)) (p : PolynomialRing n R) :
    parameterFiberPermutation (lam := lam) (polynomialParameters Q m) e
        (Ideal.Quotient.mk (polynomialFiberIdeal R n lam m Q) p) =
      Ideal.Quotient.mk (polynomialFiberIdeal R n lam m Q) (MvPolynomial.rename e p) :=
  parameterFiberPermutation_mk (lam := lam) (polynomialParameters Q m) e p

def coordinatePermutedAssignment (e : Equiv.Perm (Fin n)) (f : Fin n → ι) : Fin n → ι :=
  fun j => f (e.symm j)

@[simp] theorem coordinatePermutedAssignment_apply_image
    (e : Equiv.Perm (Fin n)) (f : Fin n → ι) (j : Fin n) :
    coordinatePermutedAssignment e f (e j) = f j := by
  simp only [coordinatePermutedAssignment, Equiv.symm_apply_apply]

def assignmentFiberPermutation (e : Equiv.Perm (Fin n)) (f : Fin n → ι) (i : ι) :
    RootFiberVariables f i ≃ RootFiberVariables (coordinatePermutedAssignment e f) i where
  toFun j := ⟨e j.val, by simpa only [coordinatePermutedAssignment_apply_image] using j.property⟩
  invFun j := ⟨e.symm j.val, j.property⟩
  left_inv j := Subtype.ext (e.symm_apply_apply j.val)
  right_inv j := Subtype.ext (e.apply_symm_apply j.val)

def rootAssignmentPermutation (r : ι → ℕ) (e : Equiv.Perm (Fin n)) :
    PrescribedRootAssignments n r ≃ PrescribedRootAssignments n r where
  toFun f := ⟨coordinatePermutedAssignment e f.val, fun i =>
    (Fintype.card_congr (assignmentFiberPermutation e f.val i)).symm.trans (f.property i)⟩
  invFun f := ⟨coordinatePermutedAssignment e.symm f.val, fun i =>
    (Fintype.card_congr (assignmentFiberPermutation e.symm f.val i)).symm.trans (f.property i)⟩
  left_inv f := by
    apply Subtype.ext
    funext j
    simp only [coordinatePermutedAssignment, Equiv.symm_symm, Equiv.symm_apply_apply]
  right_inv f := by
    apply Subtype.ext
    funext j
    simp only [coordinatePermutedAssignment, Equiv.symm_symm, Equiv.apply_symm_apply]

theorem rootGroupFinset_permutation (e : Equiv.Perm (Fin n)) (f : Fin n → ι) (i : ι) :
    rootGroupFinset (coordinatePermutedAssignment e f) i =
      (rootGroupFinset f i).map e.toEmbedding := by
  ext j
  constructor
  · intro hj
    refine Finset.mem_map.mpr ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    exact (mem_rootGroupFinset f i _).mpr ((mem_rootGroupFinset _ i j).mp hj)
  · intro hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
    apply (mem_rootGroupFinset _ i _).mpr
    change coordinatePermutedAssignment e f (e k) = i
    rw [coordinatePermutedAssignment_apply_image]
    exact (mem_rootGroupFinset f i k).mp hk

theorem map_blockSpringerIdeal_rename (e : Equiv.Perm (Fin n))
    (A : Finset (Fin n)) (mu : YoungDiagram) (hA : A.card = mu.card) :
    (blockSpringerIdeal R A mu).map (MvPolynomial.rename e).toRingHom =
      blockSpringerIdeal R (A.map e.toEmbedding) mu := by
  let u : Fin mu.card ↪ Fin n :=
    { toFun := fun i => ((Finset.equivFinOfCardEq hA).symm i).val
      inj' := fun i j h => (Finset.equivFinOfCardEq hA).symm.injective (Subtype.ext h) }
  let v := u.trans e.toEmbedding
  have hu : Finset.univ.map u = A := by
    ext i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      exact ((Finset.equivFinOfCardEq hA).symm j).property
    · intro hi
      refine Finset.mem_map.mpr ⟨Finset.equivFinOfCardEq hA ⟨i, hi⟩,
        Finset.mem_univ _, ?_⟩
      change ((Finset.equivFinOfCardEq hA).symm
        (Finset.equivFinOfCardEq hA ⟨i, hi⟩)).val = i
      rw [Equiv.symm_apply_apply]
  have hv : Finset.univ.map v = A.map e.toEmbedding := by
    rw [← hu, Finset.map_map]
  have hcomp : (MvPolynomial.rename (R := R) e).comp
      (MvPolynomial.rename (R := R) u) =
      MvPolynomial.rename (R := R) v := by
    apply AlgHom.ext
    intro p
    change MvPolynomial.rename e (MvPolynomial.rename u p) = MvPolynomial.rename v p
    rw [MvPolynomial.rename_rename]
    rfl
  have huI := blockSpringerIdeal_eq_map (R := R) mu u
  have hvI := blockSpringerIdeal_eq_map (R := R) mu v
  rw [hu] at huI
  rw [hv] at hvI
  simp only [AlgHom.toRingHom_eq_coe, Ideal.map_coe] at hcomp ⊢
  rw [huI, Ideal.map_mapₐ, hcomp, ← hvI]

theorem rename_shiftedElementaryOn (e : Equiv.Perm (Fin n))
    (A : Finset (Fin n)) (c : R) (d : ℕ) :
    MvPolynomial.rename e (shiftedElementaryOn A c d) =
      shiftedElementaryOn (A.map e.toEmbedding) c d := by
  simp only [shiftedElementaryOn, elementaryValue, map_sum, map_prod, map_sub,
    MvPolynomial.rename_X, MvPolynomial.rename_C, Finset.powersetCard_map, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro Y hY
  simp only [RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply, Finset.prod_map,
    Equiv.coe_toEmbedding]

theorem map_shiftedGlobalIdeal_rename (e : Equiv.Perm (Fin n))
    (A : Finset (Fin n)) (c : R) :
    (shiftedGlobalIdeal R A c).map (MvPolynomial.rename e).toRingHom =
      shiftedGlobalIdeal R (A.map e.toEmbedding) c := by
  unfold shiftedGlobalIdeal
  rw [Ideal.map_span, ← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext d
  exact rename_shiftedElementaryOn e A c (d + 1)

theorem map_splitRootBlockIdeal_rename (e : Equiv.Perm (Fin n))
    (lam : YoungDiagram) (r0 : ℕ) (c : ι → R) (f : Fin n → ι) (z : ι)
    (hzero : (rootGroupFinset f z).card = lam.card + r0) :
    (splitRootBlockIdeal R lam r0 c f z).map (MvPolynomial.rename e).toRingHom =
      splitRootBlockIdeal R lam r0 c (coordinatePermutedAssignment e f) z := by
  unfold splitRootBlockIdeal
  rw [Ideal.map_sup, map_blockSpringerIdeal_rename e _ _
    (by simpa only [adjoinOnes_card] using hzero), Ideal.map_iSup,
    ← rootGroupFinset_permutation]
  congr 1
  apply iSup_congr
  intro i
  rw [map_shiftedGlobalIdeal_rename, ← rootGroupFinset_permutation]

/-- The map between local factors is the original polynomial variable
permutation, not an action defined by conjugating a desired theorem. -/
def rootBlockPermutation (lam : YoungDiagram) (r0 : ℕ) (c : ι → R)
    (z : ι) (r : ι → ℕ) (hrz : r z = lam.card + r0)
    (e : Equiv.Perm (Fin n)) (f : PrescribedRootAssignments n r) :
    (PolynomialRing n R ⧸ splitRootBlockIdeal R lam r0 c f.val z) ≃ₐ[R]
      (PolynomialRing n R ⧸ splitRootBlockIdeal R lam r0 c
        (rootAssignmentPermutation r e f).val z) :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv R e)
    (map_splitRootBlockIdeal_rename e lam r0 c f.val z
      (by rw [rootGroupFinset_card, f.property z, hrz])).symm

@[simp] theorem rootBlockPermutation_mk (lam : YoungDiagram) (r0 : ℕ) (c : ι → R)
    (z : ι) (r : ι → ℕ) (hrz : r z = lam.card + r0)
    (e : Equiv.Perm (Fin n)) (f : PrescribedRootAssignments n r) (p : PolynomialRing n R) :
    rootBlockPermutation lam r0 c z r hrz e f
        (Ideal.Quotient.mk (splitRootBlockIdeal R lam r0 c f.val z) p) =
      Ideal.Quotient.mk (splitRootBlockIdeal R lam r0 c
        (rootAssignmentPermutation r e f).val z) (MvPolynomial.rename e p) :=
  Ideal.quotientEquivAlg_mk _ _ _ _

end HigherSpecht
end
end CanonicalSource74

section CanonicalSource75
/- Source: HigherSpecht/ParameterPermutationNaturality.lean -/



/-!
# Coordinate permutations and the actual elementary-parameter base change

The source action is literal polynomial variable renaming.  It fixes every
elementary parameter, hence defines an algebra automorphism over the parameter
ring.  Scalar extension acts identically on the new coefficient factor.  The
presentation equivalence intertwines this action with literal renaming in the
parameter fiber; the proof checks the actual quotient generators.
-/

noncomputable section

open TauCeti MvPolynomial
open scoped TensorProduct Classical

namespace HigherSpecht

variable {R S : Type*} [CommRing R] [CommRing S]
variable {n m : ℕ} {lam : YoungDiagram}

def untruncatedPermutationAlgEquiv (lam : YoungDiagram)
    (e : Equiv.Perm (Fin n)) :
    UntruncatedRing R n lam ≃ₐ[R] UntruncatedRing R n lam :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv R e)
    (map_ideal_of_permutationStable (permutationStable_untruncatedIdeal lam) e).symm

@[simp] theorem untruncatedPermutationAlgEquiv_mk (lam : YoungDiagram)
    (e : Equiv.Perm (Fin n)) (p : PolynomialRing n R) :
    untruncatedPermutationAlgEquiv lam e
        (Ideal.Quotient.mk (untruncatedIdeal R n lam) p) =
      Ideal.Quotient.mk (untruncatedIdeal R n lam) (MvPolynomial.rename e p) :=
  Ideal.quotientEquivAlg_mk _ _ _ _

@[simp] theorem untruncatedPermutationAlgEquiv_parameter
    (lam : YoungDiagram) (e : Equiv.Perm (Fin n)) (i : Fin (n - lam.card)) :
    untruncatedPermutationAlgEquiv lam e (elementaryParameterClasses R n lam i) =
      elementaryParameterClasses R n lam i := by
  change untruncatedPermutationAlgEquiv lam e
      (Ideal.Quotient.mk (untruncatedIdeal R n lam)
        (elementaryOn Finset.univ (i.val + 1))) = _
  rw [untruncatedPermutationAlgEquiv_mk, rename_elementaryOn_univ]
  rfl

theorem untruncatedPermutationAlgEquiv_aeval
    (lam : YoungDiagram) (e : Equiv.Perm (Fin n)) :
    (untruncatedPermutationAlgEquiv (R := R) lam e).toAlgHom.comp
        (MvPolynomial.aeval (elementaryParameterClasses R n lam)) =
      MvPolynomial.aeval (elementaryParameterClasses R n lam) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_X,
    AlgEquiv.coe_toAlgHom, untruncatedPermutationAlgEquiv_parameter]

/-- Literal variable renaming, now over the actual elementary-parameter ring. -/
def untruncatedParameterPermutation (lam : YoungDiagram)
    (e : Equiv.Perm (Fin n)) :
    UntruncatedRing R n lam ≃ₐ[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam where
  __ := (untruncatedPermutationAlgEquiv (R := R) lam e).toRingEquiv
  commutes' p := by
    simp only [untruncatedParameter_algebraMap]
    exact AlgHom.congr_fun (untruncatedPermutationAlgEquiv_aeval lam e) p

@[simp] theorem untruncatedParameterPermutation_mk (lam : YoungDiagram)
    (e : Equiv.Perm (Fin n)) (p : PolynomialRing n R) :
    untruncatedParameterPermutation lam e
        (Ideal.Quotient.mk (untruncatedIdeal R n lam) p) =
      Ideal.Quotient.mk (untruncatedIdeal R n lam) (MvPolynomial.rename e p) :=
  untruncatedPermutationAlgEquiv_mk lam e p

theorem untruncatedParameterPermutation_eq_representation
    (lam : YoungDiagram) (e : Equiv.Perm (Fin n)) (x : UntruncatedRing R n lam) :
    untruncatedParameterPermutation lam e x = untruncatedRepresentation R n lam e x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

def elementaryParameterTensorPermutation
    (S : Type*) [CommRing S] [Algebra (ElementaryParameterRing R n lam) S]
    (e : Equiv.Perm (Fin n)) :
    S ⊗[ElementaryParameterRing R n lam] UntruncatedRing R n lam ≃ₐ[S]
      S ⊗[ElementaryParameterRing R n lam] UntruncatedRing R n lam :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
    (untruncatedParameterPermutation lam e)

@[simp] theorem elementaryParameterTensorPermutation_tmul
    (S : Type*) [CommRing S] [Algebra (ElementaryParameterRing R n lam) S]
    (e : Equiv.Perm (Fin n)) (s : S) (x : UntruncatedRing R n lam) :
    elementaryParameterTensorPermutation S e (s ⊗ₜ[ElementaryParameterRing R n lam] x) =
      s ⊗ₜ[ElementaryParameterRing R n lam] untruncatedParameterPermutation lam e x := by
  simp only [elementaryParameterTensorPermutation, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq]

theorem universalParameterPresentationEquiv_symm_permutation
    (lam : YoungDiagram) (e : Equiv.Perm (Fin n)) (x : UntruncatedRing R n lam) :
    (universalParameterPresentationEquiv (R := R) n lam).symm
        (untruncatedParameterPermutation lam e x) =
      parameterFiberPermutation (fun i : Fin (n - lam.card) => MvPolynomial.X i) e
        ((universalParameterPresentationEquiv (R := R) n lam).symm x) := by
  have h : (untruncatedToUniversalParameterR (R := R) n lam).comp
        (untruncatedPermutationAlgEquiv lam e).toAlgHom =
      ((parameterFiberPermutation
        (fun i : Fin (n - lam.card) => (MvPolynomial.X i : ElementaryParameterRing R n lam))
        e).toAlgHom.restrictScalars R).comp
        (untruncatedToUniversalParameterR n lam) := by
    apply Ideal.Quotient.algHom_ext R
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Ideal.Quotient.mkₐ_eq_mk,
      untruncatedPermutationAlgEquiv_mk, MvPolynomial.rename_X,
      untruncatedToUniversalParameterR_X, AlgHom.restrictScalars_apply,
      parameterFiberPermutation_mk]
  exact AlgHom.congr_fun h x

/-- Coefficient extension commutes with literal variable renaming in the fiber. -/
theorem parameterFiberBaseChangeEquiv_permutation [Algebra R S]
    (n : ℕ) (lam : YoungDiagram) (m : ℕ) (a : Fin m → R)
    (e : Equiv.Perm (Fin n)) (x : S ⊗[R] ParameterFiber R n lam m a) :
    parameterFiberBaseChangeEquiv n lam m a
        (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
          (parameterFiberPermutation a e) x) =
      parameterFiberPermutation (fun i => algebraMap R S (a i)) e
        (parameterFiberBaseChangeEquiv n lam m a x) := by
  have h : (parameterFiberBaseChangeEquiv (S := S) n lam m a).toAlgHom.comp
        (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
          (parameterFiberPermutation a e)).toAlgHom =
      (parameterFiberPermutation (fun i => algebraMap R S (a i)) e).toAlgHom.comp
        (parameterFiberBaseChangeEquiv n lam m a).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro s q
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      AlgEquiv.coe_refl, id_eq, parameterFiberPermutation_mk,
      parameterFiberBaseChangeEquiv_tmul, MvPolynomial.map_rename, map_smul]
  exact AlgHom.congr_fun h x

/-- The elementary-parameter presentation respects the independently defined
coordinate action, with the new coefficient ring fixed pointwise. -/
theorem elementaryParameterBaseChangeEquiv_permutation
    (S : Type*) [CommRing S] [Algebra (ElementaryParameterRing R n lam) S]
    (e : Equiv.Perm (Fin n))
    (x : S ⊗[ElementaryParameterRing R n lam] UntruncatedRing R n lam) :
    elementaryParameterBaseChangeEquiv (R := R) n lam S
        (elementaryParameterTensorPermutation S e x) =
      parameterFiberPermutation
        (fun i => algebraMap (ElementaryParameterRing R n lam) S (MvPolynomial.X i)) e
        (elementaryParameterBaseChangeEquiv (R := R) n lam S x) := by
  let P := Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
    (universalParameterPresentationEquiv (R := R) n lam).symm
  let T := Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
    (parameterFiberPermutation (lam := lam)
      (fun i : Fin (n - lam.card) => (MvPolynomial.X i : ElementaryParameterRing R n lam)) e)
  have hp : P.toAlgHom.comp (elementaryParameterTensorPermutation S e).toAlgHom =
      T.toAlgHom.comp P.toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro s q
    simp only [P, T, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      elementaryParameterTensorPermutation_tmul, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul, AlgEquiv.coe_refl, id_eq,
      universalParameterPresentationEquiv_symm_permutation]
  change parameterFiberBaseChangeEquiv n lam (n - lam.card) (fun i => MvPolynomial.X i)
      (P (elementaryParameterTensorPermutation S e x)) = _
  rw [show P (elementaryParameterTensorPermutation S e x) = T (P x) from
    AlgHom.congr_fun hp x]
  exact parameterFiberBaseChangeEquiv_permutation n lam (n - lam.card)
    (fun i => MvPolynomial.X i) e (P x)

end HigherSpecht
end
end CanonicalSource75

section CanonicalSource76
/- Source: HigherSpecht/FiberPermutationNaturality.lean -/



/-!
# Naturality of the actual CRT and local translation maps

The product action here is assembled from coordinate permutation between
literal quotient ideals.  It is specified before, and independently of,
the CRT isomorphism.  The intertwining proof follows from the canonical
quotient-map formula on every polynomial representative.
-/

noncomputable section

open TauCeti MvPolynomial
open scoped Polynomial BigOperators Classical

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n m : ℕ} {ι : Type*} [Fintype ι]

def rootBlockFamilyPermutation (lam : YoungDiagram) (r0 : ℕ) (c : ι → R)
    (z : ι) (r : ι → ℕ) (hrz : r z = lam.card + r0)
    (e : Equiv.Perm (Fin n)) :
    (∀ f : PrescribedRootAssignments n r,
      PolynomialRing n R ⧸ splitRootBlockIdeal R lam r0 c f.val z) ≃ₐ[R]
      ∀ f : PrescribedRootAssignments n r,
        PolynomialRing n R ⧸ splitRootBlockIdeal R lam r0 c f.val z := by
  let P := rootAssignmentPermutation r e
  let B := fun f : PrescribedRootAssignments n r =>
    PolynomialRing n R ⧸ splitRootBlockIdeal R lam r0 c f.val z
  exact (AlgEquiv.piCongrRight fun f =>
    rootBlockPermutation lam r0 c z r hrz e f).trans (AlgEquiv.piCongrLeft R B P)

@[simp] theorem rootBlockFamilyPermutation_apply_image
    (lam : YoungDiagram) (r0 : ℕ) (c : ι → R)
    (z : ι) (r : ι → ℕ) (hrz : r z = lam.card + r0)
    (e : Equiv.Perm (Fin n))
    (v : ∀ f : PrescribedRootAssignments n r,
      PolynomialRing n R ⧸ splitRootBlockIdeal R lam r0 c f.val z)
    (f : PrescribedRootAssignments n r) :
    rootBlockFamilyPermutation lam r0 c z r hrz e v (rootAssignmentPermutation r e f) =
      rootBlockPermutation lam r0 c z r hrz e f (v f) := by
  simp only [rootBlockFamilyPermutation, AlgEquiv.trans_apply,
    AlgEquiv.piCongrLeft_apply, Equiv.piCongrLeft_apply_apply,
    AlgEquiv.piCongrRight_apply]

@[simp] theorem polynomialFiberBlockProductEquivUnits_mk [Nontrivial R]
    {lam : YoungDiagram} (hsize : lam.card + m = n)
    (Q : R[X]) (hQ : Q.Monic) (hdeg : Q.natDegree = m)
    (r0 : ℕ) (c : ι → R) (hc : Pairwise fun i j => IsUnit (c i - c j))
    (z : ι) (r : ι → ℕ) (hcz : c z = 0) (hrz : r z = lam.card + r0)
    (hfactor : Polynomial.X ^ lam.card * Q =
      ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i)
    (p : PolynomialRing n R) (f : PrescribedRootAssignments n r) :
    polynomialFiberBlockProductEquivUnits hsize Q hQ hdeg r0 c hc z r hcz hrz hfactor
        (Ideal.Quotient.mk (polynomialFiberIdeal R n lam m Q) p) f =
      Ideal.Quotient.mk (splitRootBlockIdeal R lam r0 c f.val z) p := by
  rfl

/-- The full actual CRT decomposition intertwines the natural coordinate
permutations with the explicitly renamed local quotient factors. -/
theorem polynomialFiberBlockProductEquivUnits_permutation [Nontrivial R]
    {lam : YoungDiagram} (hsize : lam.card + m = n)
    (Q : R[X]) (hQ : Q.Monic) (hdeg : Q.natDegree = m)
    (r0 : ℕ) (c : ι → R) (hc : Pairwise fun i j => IsUnit (c i - c j))
    (z : ι) (r : ι → ℕ) (hcz : c z = 0) (hrz : r z = lam.card + r0)
    (hfactor : Polynomial.X ^ lam.card * Q =
      ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i)
    (e : Equiv.Perm (Fin n)) (x : PolynomialFiber R n lam m Q) :
    polynomialFiberBlockProductEquivUnits hsize Q hQ hdeg r0 c hc z r hcz hrz hfactor
        (parameterFiberPermutation (polynomialParameters Q m) e x) =
      rootBlockFamilyPermutation lam r0 c z r hrz e
        (polynomialFiberBlockProductEquivUnits hsize Q hQ hdeg r0 c hc z r hcz hrz hfactor x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  funext g
  obtain ⟨f, rfl⟩ := (rootAssignmentPermutation r e).surjective g
  rw [polynomialFiberPermutation_mk, polynomialFiberBlockProductEquivUnits_mk,
    rootBlockFamilyPermutation_apply_image, polynomialFiberBlockProductEquivUnits_mk,
    rootBlockPermutation_mk]

/-- Translation by the root assigned to each coordinate commutes with the
actual simultaneous coordinate/root-assignment permutation. -/
theorem coordinateTranslation_rename_assignment
    (c : ι → R) (f : Fin n → ι) (e : Equiv.Perm (Fin n)) :
    (coordinateTranslation (fun j => c (coordinatePermutedAssignment e f j))).toAlgHom.comp
        (MvPolynomial.rename e) =
      (MvPolynomial.rename e).comp (coordinateTranslation (fun j => c (f j))).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    MvPolynomial.rename_X, coordinateTranslation_X,
    coordinatePermutedAssignment_apply_image, map_add, MvPolynomial.rename_C]

/-- The induced numbered-variable permutation in a Springer tensor factor. -/
def rootNumberedFactorPermutation
    (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ) (z : ι)
    (hrz : r z = lam.card + r0) (e : Equiv.Perm (Fin n))
    (f : PrescribedRootAssignments n r) (i : ι) :
    Equiv.Perm (Fin (rootBlockShape lam r0 r z i).card) :=
  (rootFiberVariableEquiv lam r0 r f.val z hrz f.property i).trans
    ((assignmentFiberPermutation e f.val i).trans
      (rootFiberVariableEquiv lam r0 r (rootAssignmentPermutation r e f).val z hrz
        (rootAssignmentPermutation r e f).property i).symm)

@[simp] theorem rootNumberedFactorPermutation_coordinate
    (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ) (z : ι)
    (hrz : r z = lam.card + r0) (e : Equiv.Perm (Fin n))
    (f : PrescribedRootAssignments n r) (i : ι)
    (j : Fin (rootBlockShape lam r0 r z i).card) :
    rootFiberEmbedding lam r0 r (rootAssignmentPermutation r e f).val z hrz
        (rootAssignmentPermutation r e f).property i
        (rootNumberedFactorPermutation lam r0 r z hrz e f i j) =
      e (rootFiberEmbedding lam r0 r f.val z hrz f.property i j) := by
  let E := rootFiberVariableEquiv lam r0 r f.val z hrz f.property i
  let F := rootFiberVariableEquiv lam r0 r (rootAssignmentPermutation r e f).val z hrz
    (rootAssignmentPermutation r e f).property i
  exact congrArg
    (fun y : RootFiberVariables (rootAssignmentPermutation r e f).val i => y.val)
    (F.apply_symm_apply (show RootFiberVariables (rootAssignmentPermutation r e f).val i from
      assignmentFiberPermutation e f.val i (E j)))

end HigherSpecht
end
end CanonicalSource76

section CanonicalSource77
/- Source: HigherSpecht/FiberTensorNaturality.lean -/



/-!
# Coordinate permutation on the actual Springer tensor factors

The permutation on each numbered Springer factor is determined by the two
explicit enumerations of its coordinate block.  It is defined independently
of the fiber isomorphism.  The naturality square is proved on the actual
polynomial generators of every tensor factor, using the inverse map's
formula `X_j ↦ X_embedding(j) - c_i`.
-/

noncomputable section

open TauCeti MvPolynomial
open scoped Classical TensorProduct BigOperators Polynomial

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n m : ℕ} {ι : Type*} [Fintype ι]

def springerPermutationAlgEquiv (mu : YoungDiagram)
    (e : Equiv.Perm (Fin mu.card)) : SpringerRing R mu ≃ₐ[R] SpringerRing R mu :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv R e)
    (map_ideal_of_permutationStable (permutationStable_untruncatedIdeal mu) e).symm

@[simp] theorem springerPermutationAlgEquiv_mk (mu : YoungDiagram)
    (e : Equiv.Perm (Fin mu.card)) (p : PolynomialRing mu.card R) :
    springerPermutationAlgEquiv mu e (Ideal.Quotient.mk (springerIdeal R mu) p) =
      Ideal.Quotient.mk (springerIdeal R mu) (MvPolynomial.rename e p) :=
  Ideal.quotientEquivAlg_mk _ _ _ _

@[simp] theorem piTensorAlgEquiv_symm_single
    {A B : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (E : ∀ i, A i ≃ₐ[R] B i) (i : ι) (b : B i) :
    (piTensorAlgEquiv (R := R) E).symm
        (PiTensorProduct.singleAlgHom (R := R) (A := B) i b) =
      PiTensorProduct.singleAlgHom (R := R) (A := A) i ((E i).symm b) := by
  change piTensorAlgMap (fun i => (E i).symm.toAlgHom)
    (PiTensorProduct.singleAlgHom i b) = _
  exact piTensorAlgMap_single _ _ _

@[simp] theorem disjointVariableQuotientTensorEquiv_symm_single
    {σ : Type*} (f : σ → ι)
    (I : ∀ i, Ideal (MvPolynomial (VariableFiber f i) R))
    (i : ι) (p : MvPolynomial (VariableFiber f i) R) :
    (disjointVariableQuotientTensorEquiv f I).symm
        (PiTensorProduct.singleAlgHom i (Ideal.Quotient.mk (I i) p)) =
      Ideal.Quotient.mk (disjointVariableIdeal f I)
        (MvPolynomial.rename (fun j : VariableFiber f i => j.val) p) := by
  change blockTensorToGlobal f I
    (PiTensorProduct.singleAlgHom i (Ideal.Quotient.mk (I i) p)) = _
  rw [blockTensorToGlobal_single, blockQuotientToGlobal_mk]

@[simp] theorem rootFiberSpringerQuotientEquiv_symm_mk
    (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ)
    (f : Fin n → ι) (z : ι) (hrz : r z = lam.card + r0)
    (hcount : ∀ i, Fintype.card (RootFiberVariables f i) = r i) (i : ι)
    (p : PolynomialRing (rootBlockShape lam r0 r z i).card R) :
    (rootFiberSpringerQuotientEquiv lam r0 r f z hrz hcount i).symm
        (Ideal.Quotient.mk (springerIdeal R (rootBlockShape lam r0 r z i)) p) =
      Ideal.Quotient.mk (rootFiberSpringerIdeal R lam r0 r f z hrz hcount i)
        (MvPolynomial.rename (rootFiberVariableEquiv lam r0 r f z hrz hcount i) p) :=
  Ideal.quotientEquivAlg_mk _ _ rfl _

@[simp] theorem rootBlockTranslationQuotientEquiv_symm_mk
    (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ)
    (c : ι → R) (f : Fin n → ι) (z : ι) (hcz : c z = 0)
    (hrz : r z = lam.card + r0)
    (hcount : ∀ i, Fintype.card (RootFiberVariables f i) = r i)
    (p : PolynomialRing n R) :
    (rootBlockTranslationQuotientEquiv lam r0 r c f z hcz hrz hcount).symm
        (Ideal.Quotient.mk (unshiftedRootBlockIdeal R lam r0 r f z) p) =
      Ideal.Quotient.mk (splitRootBlockIdeal R lam r0 c f z)
        (coordinateTranslation (fun j => -c (f j)) p) := by
  simpa only [rootBlockTranslationQuotientEquiv, AlgEquiv.symm_symm] using
    (Ideal.quotientEquivAlg_mk
      (I := unshiftedRootBlockIdeal R lam r0 r f z)
      (splitRootBlockIdeal R lam r0 c f z)
      (coordinateTranslation (fun j : Fin n => -c (f j)))
      (map_unshiftedRootBlockIdeal lam r0 r c f z hcz hrz hcount).symm p)

/-- This generator formula fixes the translation sign and the chosen block
enumeration, and is the concrete correspondence needed for equivariance. -/
@[simp] theorem rootBlockTensorQuotientEquiv_symm_single_X
    (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ)
    (c : ι → R) (f : Fin n → ι) (z : ι) (hcz : c z = 0)
    (hrz : r z = lam.card + r0)
    (hcount : ∀ i, Fintype.card (RootFiberVariables f i) = r i)
    (i : ι) (j : Fin (rootBlockShape lam r0 r z i).card) :
    (rootBlockTensorQuotientEquiv lam r0 r c f z hcz hrz hcount).symm
        (PiTensorProduct.singleAlgHom i
          (Ideal.Quotient.mk (springerIdeal R (rootBlockShape lam r0 r z i))
            (MvPolynomial.X j))) =
      Ideal.Quotient.mk (splitRootBlockIdeal R lam r0 c f z)
        (MvPolynomial.X (rootFiberEmbedding lam r0 r f z hrz hcount i j) -
          MvPolynomial.C (c i)) := by
  have hj : f (rootFiberEmbedding lam r0 r f z hrz hcount i j) = i :=
    (rootFiberVariableEquiv lam r0 r f z hrz hcount i j).property
  simp only [rootBlockTensorQuotientEquiv, AlgEquiv.symm_trans_apply,
    piTensorAlgEquiv_symm_single, rootFiberSpringerQuotientEquiv_symm_mk,
    MvPolynomial.rename_X, disjointVariableQuotientTensorEquiv_symm_single,
    Ideal.quotientEquivAlgOfEq_symm, Ideal.quotientEquivAlgOfEq_mk,
    rootBlockTranslationQuotientEquiv_symm_mk, coordinateTranslation_X]
  change Ideal.Quotient.mk _
      (MvPolynomial.X (rootFiberEmbedding lam r0 r f z hrz hcount i j) +
        MvPolynomial.C (-c (f (rootFiberEmbedding lam r0 r f z hrz hcount i j)))) = _
  rw [hj, map_neg, sub_eq_add_neg]

def rootTensorPermutation (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ) (z : ι)
    (hrz : r z = lam.card + r0) (e : Equiv.Perm (Fin n))
    (f : PrescribedRootAssignments n r) :
    (⨂[R] i : ι, SpringerRing R (rootBlockShape lam r0 r z i)) ≃ₐ[R]
      ⨂[R] i : ι, SpringerRing R (rootBlockShape lam r0 r z i) :=
  piTensorAlgEquiv (R := R) fun i => springerPermutationAlgEquiv (R := R)
    (rootBlockShape lam r0 r z i)
    (rootNumberedFactorPermutation lam r0 r z hrz e f i)

/-- The inverse naturality square is checked on the original variable
class in every genuine Springer factor. -/
theorem rootBlockTensorQuotientEquiv_inverse_permutation
    (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ)
    (c : ι → R) (z : ι) (hcz : c z = 0) (hrz : r z = lam.card + r0)
    (e : Equiv.Perm (Fin n)) (f : PrescribedRootAssignments n r) :
    (rootBlockPermutation lam r0 c z r hrz e f).toAlgHom.comp
        (rootBlockTensorQuotientEquiv lam r0 r c f.val z hcz hrz f.property).symm.toAlgHom =
      (rootBlockTensorQuotientEquiv lam r0 r c (rootAssignmentPermutation r e f).val
        z hcz hrz (rootAssignmentPermutation r e f).property).symm.toAlgHom.comp
        (rootTensorPermutation (R := R) lam r0 r z hrz e f).toAlgHom := by
  apply PiTensorProduct.algHom_ext
  intro i
  apply Ideal.Quotient.algHom_ext R
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Ideal.Quotient.mkₐ_eq_mk,
    rootBlockTensorQuotientEquiv_symm_single_X, rootBlockPermutation_mk,
    map_sub, MvPolynomial.rename_X, MvPolynomial.rename_C,
    rootTensorPermutation, piTensorAlgEquiv_single, springerPermutationAlgEquiv_mk,
    rootNumberedFactorPermutation_coordinate]

theorem rootBlockTensorQuotientEquiv_permutation
    (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ)
    (c : ι → R) (z : ι) (hcz : c z = 0) (hrz : r z = lam.card + r0)
    (e : Equiv.Perm (Fin n)) (f : PrescribedRootAssignments n r)
    (x : PolynomialRing n R ⧸ splitRootBlockIdeal R lam r0 c f.val z) :
    rootBlockTensorQuotientEquiv lam r0 r c (rootAssignmentPermutation r e f).val
        z hcz hrz (rootAssignmentPermutation r e f).property
        (rootBlockPermutation lam r0 c z r hrz e f x) =
      rootTensorPermutation (R := R) lam r0 r z hrz e f
        (rootBlockTensorQuotientEquiv lam r0 r c f.val z hcz hrz f.property x) := by
  apply (rootBlockTensorQuotientEquiv lam r0 r c (rootAssignmentPermutation r e f).val
    z hcz hrz (rootAssignmentPermutation r e f).property).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  have h := AlgHom.congr_fun
    (rootBlockTensorQuotientEquiv_inverse_permutation lam r0 r c z hcz hrz e f)
    (rootBlockTensorQuotientEquiv lam r0 r c f.val z hcz hrz f.property x)
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using h

def rootTensorFamilyPermutation (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ)
    (z : ι) (hrz : r z = lam.card + r0) (e : Equiv.Perm (Fin n)) :
    (∀ _f : PrescribedRootAssignments n r,
      ⨂[R] i : ι, SpringerRing R (rootBlockShape lam r0 r z i)) ≃ₐ[R]
      ∀ _f : PrescribedRootAssignments n r,
        ⨂[R] i : ι, SpringerRing R (rootBlockShape lam r0 r z i) :=
  (AlgEquiv.piCongrLeft' R _ (rootAssignmentPermutation r e)).trans
    (AlgEquiv.piCongrRight fun f =>
      rootTensorPermutation lam r0 r z hrz e ((rootAssignmentPermutation r e).symm f))

@[simp] theorem rootTensorFamilyPermutation_apply_image
    (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ) (z : ι)
    (hrz : r z = lam.card + r0) (e : Equiv.Perm (Fin n))
    (v : ∀ _f : PrescribedRootAssignments n r,
      ⨂[R] i : ι, SpringerRing R (rootBlockShape lam r0 r z i))
    (f : PrescribedRootAssignments n r) :
    rootTensorFamilyPermutation lam r0 r z hrz e v (rootAssignmentPermutation r e f) =
      rootTensorPermutation lam r0 r z hrz e f (v f) := by
  simp only [rootTensorFamilyPermutation, AlgEquiv.trans_apply,
    AlgEquiv.piCongrRight_apply, AlgEquiv.piCongrLeft'_apply,
    Equiv.piCongrLeft'_apply, Equiv.symm_apply_apply]

/-- The full split-fiber isomorphism respects the independently specified
assignment permutation and the actual variable permutations of its factors. -/
theorem polynomialFiberSpringerTensorProductEquiv_permutation [Nontrivial R]
    {lam : YoungDiagram} (hsize : lam.card + m = n)
    (Q : R[X]) (hQ : Q.Monic) (hdeg : Q.natDegree = m)
    (r0 : ℕ) (c : ι → R) (hc : Pairwise fun i j => IsUnit (c i - c j))
    (z : ι) (r : ι → ℕ) (hcz : c z = 0) (hrz : r z = lam.card + r0)
    (hfactor : Polynomial.X ^ lam.card * Q =
      ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i)
    (e : Equiv.Perm (Fin n)) (x : PolynomialFiber R n lam m Q) :
    polynomialFiberSpringerTensorProductEquiv hsize Q hQ hdeg r0 c hc z r hcz hrz hfactor
        (parameterFiberPermutation (polynomialParameters Q m) e x) =
      rootTensorFamilyPermutation lam r0 r z hrz e
        (polynomialFiberSpringerTensorProductEquiv hsize Q hQ hdeg
          r0 c hc z r hcz hrz hfactor x) := by
  funext g
  obtain ⟨f, rfl⟩ := (rootAssignmentPermutation r e).surjective g
  let E := polynomialFiberBlockProductEquivUnits hsize Q hQ hdeg r0 c hc z r
    hcz hrz hfactor
  have hE : E (parameterFiberPermutation (polynomialParameters Q m) e x)
        (rootAssignmentPermutation r e f) =
      rootBlockPermutation lam r0 c z r hrz e f (E x f) := by
    have h := congrFun (polynomialFiberBlockProductEquivUnits_permutation hsize Q hQ hdeg
      r0 c hc z r hcz hrz hfactor e x) (rootAssignmentPermutation r e f)
    simpa only [E, rootBlockFamilyPermutation_apply_image] using h
  change rootBlockTensorQuotientEquiv lam r0 r c
      (rootAssignmentPermutation r e f).val z hcz hrz
      (rootAssignmentPermutation r e f).property
      (E (parameterFiberPermutation (polynomialParameters Q m) e x)
        (rootAssignmentPermutation r e f)) =
    rootTensorFamilyPermutation lam r0 r z hrz e
      (fun g => rootBlockTensorQuotientEquiv lam r0 r c g.val z hcz hrz g.property
        (E x g)) (rootAssignmentPermutation r e f)
  rw [hE, rootTensorFamilyPermutation_apply_image]
  exact rootBlockTensorQuotientEquiv_permutation lam r0 r c z hcz hrz e f (E x f)

end HigherSpecht
end
end CanonicalSource77

section CanonicalSource78
/- Source: HigherSpecht/DistinctRootNaturality.lean -/



/-!
# The natural action after removing the degree-one factors

An ambient coordinate permutation permutes the ordered-root injection and
renumbers the complementary variables.  The latter renumbering is the
literal permutation induced by the chosen two block enumerations.  The
degree-one Springer factors disappear through their genuine augmentations,
so no action remains on those coefficient factors.
-/

noncomputable section

open TauCeti MvPolynomial
open scoped Classical TensorProduct Polynomial BigOperators

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n k m : ℕ} {ι : Type*} [Fintype ι]

def injectionCoordinatePermutation (e : Equiv.Perm (Fin n)) :
    (Fin m ↪ Fin n) ≃ (Fin m ↪ Fin n) where
  toFun f := f.trans e.toEmbedding
  invFun f := f.trans e.symm.toEmbedding
  left_inv f := by
    apply Function.Embedding.ext
    intro i
    exact e.symm_apply_apply (f i)
  right_inv f := by
    apply Function.Embedding.ext
    intro i
    exact e.apply_symm_apply (f i)

@[simp] theorem injectionCoordinatePermutation_apply
    (e : Equiv.Perm (Fin n)) (f : Fin m ↪ Fin n) (i : Fin m) :
    injectionCoordinatePermutation e f i = e (f i) := rfl

@[simp] theorem distinctRootAssignmentsEquivInjections_symm_val
    (hsize : k + m = n) (f : Fin m ↪ Fin n) :
    ((distinctRootAssignmentsEquivInjections hsize).symm f).val = assignmentOfInjection f := rfl

theorem distinctRootAssignmentsEquivInjections_permutation
    (hsize : k + m = n) (e : Equiv.Perm (Fin n))
    (f : DistinctRootAssignments n k m) :
    distinctRootAssignmentsEquivInjections hsize
        (rootAssignmentPermutation (fun i : Option (Fin m) => i.elim k (fun _ => 1)) e f) =
      injectionCoordinatePermutation e (distinctRootAssignmentsEquivInjections hsize f) := by
  apply Function.Embedding.ext
  intro i
  apply (distinctAssignedPoint_unique
    (rootAssignmentPermutation (fun i : Option (Fin m) => i.elim k (fun _ => 1)) e f)
    i (e (distinctAssignedPoint f i).val) ?_).symm
  change coordinatePermutedAssignment e f.val (e (distinctAssignedPoint f i).val) = some i
  rw [coordinatePermutedAssignment_apply_image]
  exact (distinctAssignedPoint f i).property

private theorem springerShapeEquiv_permutation {mu nu : YoungDiagram}
    (h : mu = nu) (e : Equiv.Perm (Fin mu.card)) (x : SpringerRing R mu) :
    springerShapeEquiv h (springerPermutationAlgEquiv mu e x) =
      springerPermutationAlgEquiv nu (h ▸ e) (springerShapeEquiv h x) := by
  cases h
  rfl

/-- The actual permutation of the unassigned (zero-root) coordinate block,
expressed in the numbered variables of the retained Springer ring. -/
def distinctZeroFactorPermutation (lam : YoungDiagram)
    (e : Equiv.Perm (Fin n)) (f : DistinctRootAssignments n lam.card m) :
    Equiv.Perm (Fin lam.card) := by
  exact (distinctRootBlockShape_none (ι := Fin m) lam) ▸
    (rootNumberedFactorPermutation lam 0
      (splitRootMultiplicities lam 0 (fun _ : Fin m => 1)) none rfl e f none)

/-- A coefficient factor is unchanged by every permutation of its variables. -/
theorem springerColumnOneEquiv_permutation
    (e : Equiv.Perm (Fin (columnPartition 1).card))
    (a : SpringerRing R (columnPartition 1)) :
    springerColumnOneEquiv (springerPermutationAlgEquiv (columnPartition 1) e a) =
      springerColumnOneEquiv a := by
  have h : (springerColumnOneEquiv (R := R)).toAlgHom.comp
        (springerPermutationAlgEquiv (R := R) (columnPartition 1) e).toAlgHom =
      (springerColumnOneEquiv (R := R)).toAlgHom := by
    apply Ideal.Quotient.algHom_ext R
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Ideal.Quotient.mkₐ_eq_mk,
      springerPermutationAlgEquiv_mk, MvPolynomial.rename_X,
      springerColumnOne_X_eq_zero, map_zero]
  exact AlgHom.congr_fun h a

/-- The chosen decidable equality only changes the presentation of a tensor
factor inclusion. Transport it to the choice in the actual factorwise map
before applying its generator formula. -/
private theorem rootTensorPermutation_single_decidable [d : DecidableEq ι]
    (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ) (z : ι)
    (hrz : r z = lam.card + r0) (e : Equiv.Perm (Fin n))
    (f : PrescribedRootAssignments n r) (i : ι)
    (b : SpringerRing R (rootBlockShape lam r0 r z i)) :
    rootTensorPermutation (R := R) lam r0 r z hrz e f
        (PiTensorProduct.singleAlgHom i b) =
      PiTensorProduct.singleAlgHom i
        (springerPermutationAlgEquiv (R := R) (rootBlockShape lam r0 r z i)
          (rootNumberedFactorPermutation lam r0 r z hrz e f i) b) := by
  cases Subsingleton.elim d (Classical.decEq ι)
  unfold rootTensorPermutation
  exact piTensorAlgEquiv_single (R := R) (fun j =>
    springerPermutationAlgEquiv (R := R) (rootBlockShape lam r0 r z j)
      (rootNumberedFactorPermutation lam r0 r z hrz e f j)) i b

/-- The collapse formula is independent of the decision procedure used
for the option-indexed factor inclusion. -/
private theorem distinctRootTensorEquiv_single_decidable
    [d : DecidableEq (Option ι)] (lam : YoungDiagram) (i : Option ι)
    (b : SpringerRing R
      (rootBlockShape lam 0 (splitRootMultiplicities lam 0 (fun _ : ι => 1)) none i)) :
    distinctRootTensorEquiv (R := R) (ι := ι) lam
        (PiTensorProduct.singleAlgHom i b) =
      unitOptionFactorToBase R (SpringerRing R lam) i (distinctRootFactorEquiv lam i b) := by
  cases Subsingleton.elim d (@Option.instDecidableEq ι (Classical.decEq ι))
  exact distinctRootTensorEquiv_single (R := R) (ι := ι) lam i b

set_option backward.isDefEq.respectTransparency false in
/-- Collapsing the degree-one factors commutes with the independently
defined numbered-factor action. -/
theorem distinctRootTensorEquiv_permutation
    (lam : YoungDiagram) (e : Equiv.Perm (Fin n))
    (f : DistinctRootAssignments n lam.card m)
    (a : ⨂[R] i : Option (Fin m), SpringerRing R
      (rootBlockShape lam 0 (splitRootMultiplicities lam 0 (fun _ : Fin m => 1)) none i)) :
    distinctRootTensorEquiv lam
        (rootTensorPermutation lam 0 (splitRootMultiplicities lam 0 (fun _ => 1))
          none rfl e f a) =
      springerPermutationAlgEquiv lam (distinctZeroFactorPermutation lam e f)
        (distinctRootTensorEquiv lam a) := by
  letI : DecidableEq (Option (Fin m)) := Classical.decEq (Option (Fin m))
  have hmu : splitRootMultiplicities lam 0 (fun _ : Fin m => 1) none =
      lam.card + 0 := rfl
  have h : (distinctRootTensorEquiv (R := R) (ι := Fin m) lam).toAlgHom.comp
        (rootTensorPermutation (R := R) lam 0 (splitRootMultiplicities lam 0 (fun _ => 1))
          none hmu e f).toAlgHom =
      (springerPermutationAlgEquiv (R := R) lam (distinctZeroFactorPermutation lam e f)).toAlgHom.comp
        (distinctRootTensorEquiv (R := R) (ι := Fin m) lam).toAlgHom := by
    apply PiTensorProduct.algHom_ext
    intro i
    apply AlgHom.ext
    intro b
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
    let p := rootNumberedFactorPermutation lam 0
      (splitRootMultiplicities lam 0 (fun _ : Fin m => 1)) none hmu e f i
    let E := springerPermutationAlgEquiv (R := R)
      (rootBlockShape lam 0
        (splitRootMultiplicities lam 0 (fun _ : Fin m => 1)) none i) p
    have hsingle :
        rootTensorPermutation (R := R) lam 0
            (splitRootMultiplicities lam 0 (fun _ : Fin m => 1)) none hmu e f
            (PiTensorProduct.singleAlgHom i b) =
          PiTensorProduct.singleAlgHom i (E b) :=
      rootTensorPermutation_single_decidable (R := R) lam 0
        (splitRootMultiplicities lam 0 (fun _ : Fin m => 1)) none hmu e f i b
    have hfactor :
        unitOptionFactorToBase R (SpringerRing R lam) i
            (distinctRootFactorEquiv lam i (E b)) =
          springerPermutationAlgEquiv lam (distinctZeroFactorPermutation lam e f)
            (unitOptionFactorToBase R (SpringerRing R lam) i
              (distinctRootFactorEquiv lam i b)) := by
      cases i with
      | none =>
          change springerShapeEquiv (R := R) (distinctRootBlockShape_none (ι := Fin m) lam)
              (springerPermutationAlgEquiv _
                (rootNumberedFactorPermutation lam 0
                  (splitRootMultiplicities lam 0 (fun _ : Fin m => 1)) none hmu e f none) b) =
            springerPermutationAlgEquiv lam (distinctZeroFactorPermutation lam e f)
              (springerShapeEquiv (distinctRootBlockShape_none (ι := Fin m) lam) b)
          exact springerShapeEquiv_permutation _ _ b
      | some i =>
          change algebraMap R (SpringerRing R lam)
              (springerColumnOneEquiv
                (springerShapeEquiv (distinctRootBlockShape_some lam i)
                  (springerPermutationAlgEquiv _
                    (rootNumberedFactorPermutation lam 0
                      (splitRootMultiplicities lam 0 (fun _ : Fin m => 1))
                      none hmu e f (some i)) b))) =
            springerPermutationAlgEquiv lam (distinctZeroFactorPermutation lam e f)
              (algebraMap R (SpringerRing R lam)
                (springerColumnOneEquiv
                  (springerShapeEquiv (distinctRootBlockShape_some lam i) b)))
          rw [springerShapeEquiv_permutation, springerColumnOneEquiv_permutation,
            AlgEquiv.commutes]
    exact (congrArg (distinctRootTensorEquiv (R := R) (ι := Fin m) lam) hsingle).trans
      ((distinctRootTensorEquiv_single_decidable (R := R) (ι := Fin m) lam i (E b)).trans
        (hfactor.trans
          (congrArg (springerPermutationAlgEquiv (R := R) lam
            (distinctZeroFactorPermutation lam e f))
            (distinctRootTensorEquiv_single_decidable (R := R) (ι := Fin m) lam i b)).symm))
  exact AlgHom.congr_fun h a

set_option backward.isDefEq.respectTransparency false in
/-- The generic split-fiber component formula after the one-dimensional
coinvariant factors have been removed.  The target index is the actual
renamed root assignment, and the remaining action is its literal
complementary-coordinate permutation. -/
theorem distinctRootCollapsedFiber_permutation [Nontrivial R]
    {lam : YoungDiagram} (hsize : lam.card + m = n)
    (Q : R[X]) (hQ : Q.Monic) (hdeg : Q.natDegree = m)
    (c : Fin m → R) (hu : ∀ i, IsUnit (c i))
    (hc : Pairwise fun i j => IsUnit (c i - c j))
    (hfactor : Polynomial.X ^ lam.card * Q =
      ∏ i : Option (Fin m),
        (Polynomial.X - Polynomial.C (splitRootValue c i)) ^
          splitRootMultiplicities lam 0 (fun _ => 1) i)
    (e : Equiv.Perm (Fin n)) (x : PolynomialFiber R n lam m Q)
    (f : DistinctRootAssignments n lam.card m) :
    distinctRootTensorEquiv lam
      (polynomialFiberSpringerTensorProductEquiv hsize Q hQ hdeg 0
        (splitRootValue c) (splitRootValue_unitDifferences c hu hc) none
        (splitRootMultiplicities lam 0 (fun _ => 1)) rfl rfl hfactor
        (parameterFiberPermutation (polynomialParameters Q m) e x)
        (rootAssignmentPermutation (splitRootMultiplicities lam 0 (fun _ => 1)) e f)) =
      springerPermutationAlgEquiv lam (distinctZeroFactorPermutation lam e f)
        (distinctRootTensorEquiv lam
          (polynomialFiberSpringerTensorProductEquiv hsize Q hQ hdeg 0
            (splitRootValue c) (splitRootValue_unitDifferences c hu hc) none
            (splitRootMultiplicities lam 0 (fun _ => 1)) rfl rfl hfactor x f)) := by
  have h := congrArg (fun v => distinctRootTensorEquiv (R := R) (ι := Fin m) lam
      (v (rootAssignmentPermutation (splitRootMultiplicities lam 0 (fun _ => 1)) e f)))
    (polynomialFiberSpringerTensorProductEquiv_permutation hsize Q hQ hdeg 0
      (splitRootValue c) (splitRootValue_unitDifferences c hu hc) none
      (splitRootMultiplicities lam 0 (fun _ => 1)) rfl rfl hfactor e x)
  rw [rootTensorFamilyPermutation_apply_image, distinctRootTensorEquiv_permutation] at h
  exact h

end HigherSpecht
end
end CanonicalSource78

section CanonicalSource79
/- Source: HigherSpecht/OrderedRootNaturality.lean -/



/-!
# Equivariance of the integral ordered-root trivialization

The source permutation renames the original coordinates and fixes the root
coefficient ring.  On the target it postcomposes the ordered-root injection
and renames the complementary Springer variables by the permutation obtained
from the two actual complement enumerations.  The component formula below
compares these independently specified maps through each presentation map.
-/

noncomputable section

open TauCeti MvPolynomial
open scoped Classical TensorProduct Polynomial BigOperators

namespace HigherSpecht

variable {R S : Type*} [CommRing R] [CommRing S]
variable {n m : ℕ} {lam : YoungDiagram}

theorem parameterPolynomialPresentation_permutation
    (a : Fin m → R) (e : Equiv.Perm (Fin n))
    (x : ParameterFiber R n lam m a) :
    Ideal.quotientEquivAlgOfEq R (polynomialFiberIdeal_parameterPolynomial lam a).symm
        (parameterFiberPermutation a e x) =
      parameterFiberPermutation (polynomialParameters (parameterPolynomial a) m) e
        (Ideal.quotientEquivAlgOfEq R
          (polynomialFiberIdeal_parameterPolynomial lam a).symm x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [parameterFiberPermutation_mk, Ideal.quotientEquivAlgOfEq_mk,
    polynomialFiberPermutation_mk]

/-- Scalar extension of the actual Springer variable permutation. -/
def springerTensorPermutation [Algebra R S] (lam : YoungDiagram)
    (e : Equiv.Perm (Fin lam.card)) :
    S ⊗[R] SpringerRing R lam ≃ₐ[S] S ⊗[R] SpringerRing R lam :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
    (springerPermutationAlgEquiv lam e)

@[simp] theorem springerTensorPermutation_tmul [Algebra R S]
    (lam : YoungDiagram) (e : Equiv.Perm (Fin lam.card)) (s : S) (x : SpringerRing R lam) :
    springerTensorPermutation lam e (s ⊗ₜ[R] x) =
      s ⊗ₜ[R] springerPermutationAlgEquiv lam e x := by
  change Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
    (springerPermutationAlgEquiv lam e) (s ⊗ₜ[R] x) = _
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  rfl

theorem springerCoefficientBaseChangeEquiv_permutation [Algebra R S]
    (lam : YoungDiagram) (e : Equiv.Perm (Fin lam.card))
    (x : S ⊗[R] SpringerRing R lam) :
    springerCoefficientBaseChangeEquiv S lam (springerTensorPermutation lam e x) =
      springerPermutationAlgEquiv lam e (springerCoefficientBaseChangeEquiv S lam x) := by
  have h : (springerCoefficientBaseChangeEquiv (R := R) S lam).toAlgHom.comp
        (springerTensorPermutation lam e).toAlgHom =
      (springerPermutationAlgEquiv lam e).toAlgHom.comp
        (springerCoefficientBaseChangeEquiv (R := R) S lam).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro s q
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    change springerCoefficientBaseChangeEquiv S lam
        (springerTensorPermutation lam e (s ⊗ₜ[R] Ideal.Quotient.mk (springerIdeal R lam) p)) =
      springerPermutationAlgEquiv lam e
        (springerCoefficientBaseChangeEquiv S lam
          (s ⊗ₜ[R] Ideal.Quotient.mk (springerIdeal R lam) p))
    rw [springerTensorPermutation_tmul, springerPermutationAlgEquiv_mk,
      springerCoefficientBaseChangeEquiv_tmul, springerCoefficientBaseChangeEquiv_tmul,
      springerPermutationAlgEquiv_mk]
    congr 1
    rw [MvPolynomial.map_rename, map_smul]
  exact AlgHom.congr_fun h x

theorem springerCoefficientBaseChangeEquiv_symm_permutation [Algebra R S]
    (lam : YoungDiagram) (e : Equiv.Perm (Fin lam.card)) (x : SpringerRing S lam) :
    (springerCoefficientBaseChangeEquiv (R := R) S lam).symm
        (springerPermutationAlgEquiv lam e x) =
      springerTensorPermutation lam e
        ((springerCoefficientBaseChangeEquiv (R := R) S lam).symm x) := by
  apply (springerCoefficientBaseChangeEquiv (R := R) S lam).injective
  rw [AlgEquiv.apply_symm_apply, springerCoefficientBaseChangeEquiv_permutation,
    AlgEquiv.apply_symm_apply]

end HigherSpecht

namespace HigherSpecht.OrderedParameterCovariance

variable {R : Type*} [CommRing R]

/-- Eliminate the parameter-family transport before comparing the function
fields. This proof uses the original untransported covariance theorem directly. -/
theorem rawParameterBaseChange_permutation
    (n : ℕ) (lam : YoungDiagram) (S : Type*) [CommRing S]
    [Algebra (ElementaryParameterRing R n lam) S]
    (a : Fin (n - lam.card) → S)
    (ha : (fun i : Fin (n - lam.card) =>
      algebraMap (ElementaryParameterRing R n lam) S (MvPolynomial.X i)) = a)
    (e : Equiv.Perm (Fin n))
    (x : S ⊗[ElementaryParameterRing R n lam] UntruncatedRing R n lam) :
    (elementaryParameterBaseChangeEquivOfEq (R := R) n lam S a ha).toEquiv.toFun
        ((elementaryParameterTensorPermutation
          (R := R) (n := n) (lam := lam) S e).toEquiv.toFun x) =
      (parameterFiberPermutation (lam := lam) a e).toEquiv.toFun
        ((elementaryParameterBaseChangeEquivOfEq (R := R) n lam S a ha).toEquiv.toFun x) := by
  subst a
  exact elementaryParameterBaseChangeEquiv_permutation (R := R) (n := n) (lam := lam) S e x

/-- The original equivalence and its already established covariance are
stored together; the whole-map equality identifies the construction exactly. -/
structure ParameterCovarianceCertificate
    (n : ℕ) (lam : YoungDiagram) (S : Type*) [CommRing S]
    [Algebra (ElementaryParameterRing R n lam) S]
    (a : Fin (n - lam.card) → S)
    (ha : (fun i : Fin (n - lam.card) =>
      algebraMap (ElementaryParameterRing R n lam) S (MvPolynomial.X i)) = a) where
  equiv : S ⊗[ElementaryParameterRing R n lam] UntruncatedRing R n lam ≃ₐ[S]
    ParameterFiber S n lam (n - lam.card) a
  eq_original : equiv = elementaryParameterBaseChangeEquivOfEq (R := R) n lam S a ha
  covariance : ∀ (e : Equiv.Perm (Fin n))
      (x : S ⊗[ElementaryParameterRing R n lam] UntruncatedRing R n lam),
    equiv.toEquiv.toFun
        ((elementaryParameterTensorPermutation
          (R := R) (n := n) (lam := lam) S e).toEquiv.toFun x) =
      (parameterFiberPermutation (lam := lam) a e).toEquiv.toFun (equiv.toEquiv.toFun x)

/-- Safe opacity with a fully specified constructor body. No covariance is
assumed: its field is the preceding proved theorem for the original map. -/
opaque certifiedParameter
    (n : ℕ) (lam : YoungDiagram) (S : Type*) [CommRing S]
    [Algebra (ElementaryParameterRing R n lam) S]
    (a : Fin (n - lam.card) → S)
    (ha : (fun i : Fin (n - lam.card) =>
      algebraMap (ElementaryParameterRing R n lam) S (MvPolynomial.X i)) = a) :
    ParameterCovarianceCertificate (R := R) n lam S a ha :=
  { equiv := elementaryParameterBaseChangeEquivOfEq (R := R) n lam S a ha
    eq_original := rfl
    covariance := fun e x => rawParameterBaseChange_permutation (R := R) n lam S a ha e x }

/-- The certificate exposes covariance directly, without a map-equality
transport or a raw/coercion conversion at use sites. -/
theorem certifiedParameter_permutation
    (n : ℕ) (lam : YoungDiagram) (S : Type*) [CommRing S]
    [Algebra (ElementaryParameterRing R n lam) S]
    (a : Fin (n - lam.card) → S)
    (ha : (fun i : Fin (n - lam.card) =>
      algebraMap (ElementaryParameterRing R n lam) S (MvPolynomial.X i)) = a)
    (e : Equiv.Perm (Fin n))
    (x : S ⊗[ElementaryParameterRing R n lam] UntruncatedRing R n lam) :
    (certifiedParameter (R := R) n lam S a ha).equiv.toEquiv.toFun
        ((elementaryParameterTensorPermutation
          (R := R) (n := n) (lam := lam) S e).toEquiv.toFun x) =
      (parameterFiberPermutation (lam := lam) a e).toEquiv.toFun
        ((certifiedParameter (R := R) n lam S a ha).equiv.toEquiv.toFun x) :=
  (certifiedParameter (R := R) n lam S a ha).covariance e x

theorem orderedRootParameter_family_eq (n : ℕ) (lam : YoungDiagram) :
    (fun i : Fin (n - lam.card) =>
      algebraMap (ElementaryParameterRing R n lam) (OrderedRootRing R (n - lam.card))
        (MvPolynomial.X i)) =
      orderedRootElementaryParameters (R := R) (n - lam.card) := by
  funext i
  exact orderedRootParameter_algebraMap_X n lam i

/-- This diagnostic presentation has the original source and target, and its
entire equivalence is proved equal to the unchanged production presentation. -/
def orderedRootParameterPresentation (n : ℕ) (lam : YoungDiagram) :
    OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
        UntruncatedRing R n lam ≃ₐ[OrderedRootRing R (n - lam.card)]
      ParameterFiber (OrderedRootRing R (n - lam.card)) n lam (n - lam.card)
        (orderedRootElementaryParameters (R := R) (n - lam.card)) :=
  (certifiedParameter (R := R) n lam (OrderedRootRing R (n - lam.card))
    (orderedRootElementaryParameters (R := R) (n - lam.card))
    (orderedRootParameter_family_eq (R := R) n lam)).equiv

theorem orderedRootParameterPresentation_eq_original (n : ℕ) (lam : YoungDiagram) :
    orderedRootParameterPresentation (R := R) n lam =
      elementaryParameterBaseChangeEquivOfEq (R := R) n lam
        (OrderedRootRing R (n - lam.card))
        (orderedRootElementaryParameters (R := R) (n - lam.card))
        (orderedRootParameter_family_eq (R := R) n lam) :=
  (certifiedParameter (R := R) n lam (OrderedRootRing R (n - lam.card))
    (orderedRootElementaryParameters (R := R) (n - lam.card))
    (orderedRootParameter_family_eq (R := R) n lam)).eq_original

theorem orderedRootParameterPresentation_eq_previous (n : ℕ) (lam : YoungDiagram) :
    orderedRootParameterPresentation (R := R) n lam =
      HigherSpecht.orderedRootParameterPresentation (R := R) n lam := by
  exact (orderedRootParameterPresentation_eq_original (R := R) n lam).trans (by rfl)

/-- Concrete covariance projects the stored proof directly; it does not
transfer a pointwise equation involving the unsealed implementation. -/
theorem orderedRootParameterPresentation_permutation
    (n : ℕ) (lam : YoungDiagram) (e : Equiv.Perm (Fin n))
    (x : OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam) :
    (orderedRootParameterPresentation (R := R) n lam).toEquiv.toFun
        ((elementaryParameterTensorPermutation
          (R := R) (n := n) (lam := lam)
          (OrderedRootRing R (n - lam.card)) e).toEquiv.toFun x) =
      (parameterFiberPermutation (lam := lam)
        (orderedRootElementaryParameters (R := R) (n - lam.card)) e).toEquiv.toFun
        ((orderedRootParameterPresentation (R := R) n lam).toEquiv.toFun x) :=
  (certifiedParameter (R := R) n lam (OrderedRootRing R (n - lam.card))
    (orderedRootElementaryParameters (R := R) (n - lam.card))
    (orderedRootParameter_family_eq (R := R) n lam)).covariance e x

end HigherSpecht.OrderedParameterCovariance

namespace HigherSpecht.OrderedParameterNaturality

variable {R : Type*} [CommRing R]

abbrev parameterPresentation (n : ℕ) (lam : YoungDiagram) :=
  OrderedParameterCovariance.orderedRootParameterPresentation
    (R := R) n lam

def orderedRootTrivializationCertificate [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
  ComponentwiseCertificate (K := OrderedRootRing R (n - lam.card))
    (A := OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam)
    (B := ParameterFiber (OrderedRootRing R (n - lam.card)) n lam (n - lam.card)
      (orderedRootElementaryParameters (R := R) (n - lam.card)))
    (C := PolynomialFiber (OrderedRootRing R (n - lam.card)) n lam (n - lam.card)
      (parameterPolynomial (orderedRootElementaryParameters (R := R) (n - lam.card))))
    (V := SpringerRing (OrderedRootRing R (n - lam.card)) lam)
    (κ := Fin (n - lam.card) ↪ Fin n)
    (ι := PrescribedRootAssignments n
      (splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)))
    (D := ⨂[OrderedRootRing R (n - lam.card)] i : Option (Fin (n - lam.card)),
      SpringerRing (OrderedRootRing R (n - lam.card))
        (rootBlockShape lam 0
          (splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)) none i))
    (parameterPresentation (R := R) n lam)
    (orderedRootPolynomialPresentation (R := R) n lam)
    (orderedRootSplitPresentation (R := R) n lam hk)
    (distinctRootTensorEquiv (R := OrderedRootRing R (n - lam.card))
      (ι := Fin (n - lam.card)) lam)
    (orderedRootAssignmentEquiv n lam hk) :=
  certifiedComponentwise (K := OrderedRootRing R (n - lam.card))
    (A := OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam)
    (B := ParameterFiber (OrderedRootRing R (n - lam.card)) n lam (n - lam.card)
      (orderedRootElementaryParameters (R := R) (n - lam.card)))
    (C := PolynomialFiber (OrderedRootRing R (n - lam.card)) n lam (n - lam.card)
      (parameterPolynomial (orderedRootElementaryParameters (R := R) (n - lam.card))))
    (V := SpringerRing (OrderedRootRing R (n - lam.card)) lam)
    (κ := Fin (n - lam.card) ↪ Fin n)
    (ι := PrescribedRootAssignments n
      (splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)))
    (D := ⨂[OrderedRootRing R (n - lam.card)] i : Option (Fin (n - lam.card)),
      SpringerRing (OrderedRootRing R (n - lam.card))
        (rootBlockShape lam 0
          (splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)) none i))
    (parameterPresentation (R := R) n lam)
    (orderedRootPolynomialPresentation (R := R) n lam)
    (orderedRootSplitPresentation (R := R) n lam hk)
    (distinctRootTensorEquiv (R := OrderedRootRing R (n - lam.card))
      (ι := Fin (n - lam.card)) lam)
    (orderedRootAssignmentEquiv n lam hk)

def orderedRootTrivialization [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
        UntruncatedRing R n lam ≃ₐ[OrderedRootRing R (n - lam.card)]
      ∀ _e : Fin (n - lam.card) ↪ Fin n,
        SpringerRing (OrderedRootRing R (n - lam.card)) lam :=
  (orderedRootTrivializationCertificate (R := R) n lam hk).equiv

/-- Equality of the complete diagnostic trivialization and the unchanged
production equivalence, obtained by congruence from the complete P equality. -/
theorem orderedRootTrivialization_eq_previous [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    orderedRootTrivialization (R := R) n lam hk =
      HigherSpecht.orderedRootTrivialization (R := R) n lam hk := by
  exact congrArg
    (fun P :
      (OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
        UntruncatedRing R n lam) ≃ₐ[OrderedRootRing R (n - lam.card)]
          ParameterFiber (OrderedRootRing R (n - lam.card)) n lam (n - lam.card)
            (orderedRootElementaryParameters (R := R) (n - lam.card)) =>
      (certifiedComponentwise (K := OrderedRootRing R (n - lam.card))
          (A := OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
            UntruncatedRing R n lam)
          (B := ParameterFiber (OrderedRootRing R (n - lam.card)) n lam (n - lam.card)
            (orderedRootElementaryParameters (R := R) (n - lam.card)))
          (C := PolynomialFiber (OrderedRootRing R (n - lam.card)) n lam (n - lam.card)
            (parameterPolynomial (orderedRootElementaryParameters (R := R) (n - lam.card))))
          (V := SpringerRing (OrderedRootRing R (n - lam.card)) lam)
          (κ := Fin (n - lam.card) ↪ Fin n)
          (ι := PrescribedRootAssignments n
            (splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)))
          (D := ⨂[OrderedRootRing R (n - lam.card)] i : Option (Fin (n - lam.card)),
            SpringerRing (OrderedRootRing R (n - lam.card))
              (rootBlockShape lam 0
                (splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)) none i))
          P
          (orderedRootPolynomialPresentation (R := R) n lam)
          (orderedRootSplitPresentation (R := R) n lam hk)
          (distinctRootTensorEquiv (R := OrderedRootRing R (n - lam.card))
            (ι := Fin (n - lam.card)) lam)
          (orderedRootAssignmentEquiv n lam hk)).equiv)
    (OrderedParameterCovariance.orderedRootParameterPresentation_eq_previous
      (R := R) n lam)

theorem orderedRootTrivialization_toEquiv_apply [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (x : OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam)
    (e : Fin (n - lam.card) ↪ Fin n) :
    (orderedRootTrivialization (R := R) n lam hk).toEquiv.toFun x e =
      (distinctRootTensorEquiv (R := OrderedRootRing R (n - lam.card))
        (ι := Fin (n - lam.card)) lam).toEquiv.toFun
        ((orderedRootSplitPresentation (R := R) n lam hk).toEquiv.toFun
          ((orderedRootPolynomialPresentation (R := R) n lam).toEquiv.toFun
            ((parameterPresentation (R := R) n lam).toEquiv.toFun x))
          ((orderedRootAssignmentEquiv n lam hk).symm.toFun e)) := by
  exact (orderedRootTrivializationCertificate (R := R) n lam hk).evaluate x e

/-- Transfer a componentwise naturality equation from explicit projections to
ordinary applications with all maps and algebra structures kept abstract. -/
private theorem naturality_coercion_of_toEquiv
    {K : Type*} [CommSemiring K]
    {A : Type*} {V : Type*} {I : Type*} {J : Type*}
    [Semiring A] [Semiring V] [Algebra K A] [Algebra K V]
    (T : A ≃ₐ[K] (J → V)) (u : A ≃ₐ[K] A) (rho : V ≃ₐ[K] V)
    (h : I ≃ J) (tau : J → J) (x : A) (f : I)
    (hraw : T.toEquiv.toFun (u.toEquiv.toFun x) (tau (h.toFun f)) =
      rho.toEquiv.toFun (T.toEquiv.toFun x (h.toFun f))) :
    T (u x) (tau (h f)) = rho (T x (h f)) := by
  exact hraw


/-- Naturality of a componentwise composite, proved for plain functions.
All algebra structure belongs to the separately proved input identities. -/
private theorem componentwise_naturality_of_functions
    {A : Type*} {B : Type*} {C : Type*} {D : Type*}
    {V : Type*} {I : Type*} {J : Type*}
    (P : A → B) (Q : B → C) (F : C → I → D) (G : D → V)
    (T : A → J → V) (h : I → J)
    (u : A → A) (v : B → B) (w : C → C)
    (σ : I → I) (τ : J → J) (ρ : V → V) (x : A) (i : I)
    (hT : ∀ y j, T y (h j) = G (F (Q (P y)) j))
    (hindex : h (σ i) = τ (h i))
    (hP : P (u x) = v (P x))
    (hQ : Q (v (P x)) = w (Q (P x)))
    (hF : G (F (w (Q (P x))) (σ i)) = ρ (G (F (Q (P x)) i))) :
    T (u x) (τ (h i)) = ρ (T x (h i)) := by
  calc
    _ = T (u x) (h (σ i)) := congrArg (T (u x)) hindex.symm
    _ = G (F (Q (P (u x))) (σ i)) := hT _ _
    _ = G (F (w (Q (P x))) (σ i)) :=
      congrArg (fun y => G (F y (σ i))) ((congrArg Q hP).trans hQ)
    _ = ρ (G (F (Q (P x)) i)) := hF
    _ = ρ (T x (h i)) := congrArg ρ (hT x i).symm

private theorem orderedRootTrivialization_toEquiv_permutation [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (e : Equiv.Perm (Fin n))
    (x : OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam)
    (f : DistinctRootAssignments n lam.card (n - lam.card)) :
    (orderedRootTrivialization (R := R) n lam hk).toEquiv.toFun
        ((elementaryParameterTensorPermutation (R := R) (n := n) (lam := lam)
          (OrderedRootRing R (n - lam.card)) e).toEquiv.toFun x)
        (injectionCoordinatePermutation e
          ((distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk)).toFun f)) =
      (springerPermutationAlgEquiv lam (distinctZeroFactorPermutation lam e f)).toEquiv.toFun
        ((orderedRootTrivialization (R := R) n lam hk).toEquiv.toFun x
          ((distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk)).toFun f)) := by
  let S := OrderedRootRing R (n - lam.card)
  let c : Fin (n - lam.card) → S := orderedRoot (n - lam.card)
  let a : Fin (n - lam.card) → S := orderedRootElementaryParameters (n - lam.card)
  have hsize : lam.card + (n - lam.card) = n := Nat.add_sub_of_le hk
  let P : S ⊗[ElementaryParameterRing R n lam] UntruncatedRing R n lam ≃ₐ[S]
      ParameterFiber S n lam (n - lam.card) a :=
    parameterPresentation (R := R) n lam
  let Q : ParameterFiber S n lam (n - lam.card) a ≃ₐ[S]
      PolynomialFiber S n lam (n - lam.card) (parameterPolynomial a) :=
    orderedRootPolynomialPresentation (R := R) n lam
  have hfactor : Polynomial.X ^ lam.card * parameterPolynomial a =
      ∏ i : Option (Fin (n - lam.card)),
        (Polynomial.X - Polynomial.C (splitRootValue c i)) ^
          splitRootMultiplicities lam 0 (fun _ => 1) i := by
    rw [orderedRootParameter_factorization]
    exact splitRootParameter_factorization lam 0 c (fun _ => 1)
  let F := orderedRootSplitPresentation (R := R) n lam hk
  let r := splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)
  let J := orderedRootAssignmentEquiv n lam hk
  let D := distinctRootTensorEquiv (R := S) (ι := Fin (n - lam.card)) lam
  have hP :
      P.toEquiv.toFun
        ((elementaryParameterTensorPermutation (R := R) (n := n) (lam := lam) S e).toEquiv.toFun x) =
      (parameterFiberPermutation (lam := lam) a e).toEquiv.toFun (P.toEquiv.toFun x) := by
    exact OrderedParameterCovariance.orderedRootParameterPresentation_permutation (R := R) n lam e x
  have hQ :
      Q.toEquiv.toFun
        ((parameterFiberPermutation (lam := lam) a e).toEquiv.toFun (P.toEquiv.toFun x)) =
      (parameterFiberPermutation (lam := lam)
        (polynomialParameters (parameterPolynomial a) (n - lam.card)) e).toEquiv.toFun
          (Q.toEquiv.toFun (P.toEquiv.toFun x)) := by
    exact parameterPolynomialPresentation_permutation a e (P.toEquiv.toFun x)
  have happly
      (y : S ⊗[ElementaryParameterRing R n lam] UntruncatedRing R n lam)
      (g : PrescribedRootAssignments n r) :
      (orderedRootTrivialization (R := R) n lam hk).toEquiv.toFun y (J.toFun g) =
        D.toEquiv.toFun (F.toEquiv.toFun
          (Q.toEquiv.toFun (P.toEquiv.toFun y)) g) :=
    (orderedRootTrivialization_toEquiv_apply (R := R) n lam hk y (J.toFun g)).trans
      (congrArg (fun t => D.toEquiv.toFun (F.toEquiv.toFun
        (Q.toEquiv.toFun (P.toEquiv.toFun y)) t)) (J.symm_apply_apply g))
  have hindex : J.toFun (rootAssignmentPermutation r e f) =
      injectionCoordinatePermutation e
        ((distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk)).toFun f) := by
    exact distinctRootAssignmentsEquivInjections_permutation (Nat.add_sub_of_le hk) e f
  have hnatural :
      D.toEquiv.toFun (F.toEquiv.toFun
        ((parameterFiberPermutation (lam := lam)
          (polynomialParameters (parameterPolynomial a) (n - lam.card)) e).toEquiv.toFun
            (Q.toEquiv.toFun (P.toEquiv.toFun x))) (rootAssignmentPermutation r e f)) =
        (springerPermutationAlgEquiv lam (distinctZeroFactorPermutation lam e f)).toEquiv.toFun
          (D.toEquiv.toFun (F.toEquiv.toFun (Q.toEquiv.toFun (P.toEquiv.toFun x)) f)) := by
    exact distinctRootCollapsedFiber_permutation hsize
      (parameterPolynomial a) (parameterPolynomial_monic a) (parameterPolynomial_natDegree a)
      c (orderedRoot_isUnit (n - lam.card)) (orderedRoot_pairwise_units (n - lam.card))
      hfactor e (Q.toEquiv.toFun (P.toEquiv.toFun x)) f
  exact componentwise_naturality_of_functions
    P.toEquiv.toFun Q.toEquiv.toFun F.toEquiv.toFun D.toEquiv.toFun
    (orderedRootTrivialization (R := R) n lam hk).toEquiv.toFun J.toFun
    (elementaryParameterTensorPermutation (R := R) (n := n) (lam := lam) S e).toEquiv.toFun
    (parameterFiberPermutation (lam := lam) a e).toEquiv.toFun
    (parameterFiberPermutation (lam := lam)
      (polynomialParameters (parameterPolynomial a) (n - lam.card)) e).toEquiv.toFun
    (rootAssignmentPermutation r e) (injectionCoordinatePermutation e)
    (springerPermutationAlgEquiv lam (distinctZeroFactorPermutation lam e f)).toEquiv.toFun
    x f happly hindex hP hQ hnatural


set_option backward.isDefEq.respectTransparency false in
/-- The componentwise naturality formula for every ambient coordinate
permutation and every actual ordered-root assignment.  The assignment-to-
injection map is a proved bijection, so this covers every target component. -/
theorem orderedRootTrivialization_permutation [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (e : Equiv.Perm (Fin n))
    (x : OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam)
    (f : DistinctRootAssignments n lam.card (n - lam.card)) :
    orderedRootTrivialization n lam hk
        (elementaryParameterTensorPermutation (OrderedRootRing R (n - lam.card)) e x)
        (injectionCoordinatePermutation e
          (distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk) f)) =
      springerPermutationAlgEquiv lam (distinctZeroFactorPermutation lam e f)
        (orderedRootTrivialization n lam hk x
          (distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk) f)) := by
  exact naturality_coercion_of_toEquiv
    (K := OrderedRootRing R (n - lam.card))
    (A := OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam)
    (V := SpringerRing (OrderedRootRing R (n - lam.card)) lam)
    (I := DistinctRootAssignments n lam.card (n - lam.card))
    (J := Fin (n - lam.card) ↪ Fin n)
    (orderedRootTrivialization (R := R) n lam hk)
    (elementaryParameterTensorPermutation (R := R) (n := n) (lam := lam)
      (OrderedRootRing R (n - lam.card)) e)
    (springerPermutationAlgEquiv (R := OrderedRootRing R (n - lam.card))
      lam (distinctZeroFactorPermutation lam e f))
    (distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk))
    (injectionCoordinatePermutation e) x f
    (orderedRootTrivialization_toEquiv_permutation (R := R) n lam hk e x f)

/-- The exact covariance statement for the unchanged production map. This
is derived from a proved equality of whole AlgEquivs, not a semantic convention. -/
theorem originalTrivialization_permutation [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (e : Equiv.Perm (Fin n))
    (x : OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam)
    (f : DistinctRootAssignments n lam.card (n - lam.card)) :
    HigherSpecht.orderedRootTrivialization n lam hk
        (elementaryParameterTensorPermutation (OrderedRootRing R (n - lam.card)) e x)
        (injectionCoordinatePermutation e
          (distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk) f)) =
      springerPermutationAlgEquiv lam (distinctZeroFactorPermutation lam e f)
        (HigherSpecht.orderedRootTrivialization n lam hk x
          (distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk) f)) := by
  have h := orderedRootTrivialization_eq_previous (R := R) n lam hk
  exact (congrArg
    (fun E :
      (OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
        UntruncatedRing R n lam) ≃ₐ[OrderedRootRing R (n - lam.card)]
          ((Fin (n - lam.card) ↪ Fin n) →
            SpringerRing (OrderedRootRing R (n - lam.card)) lam) =>
      E (elementaryParameterTensorPermutation (OrderedRootRing R (n - lam.card)) e x)
        (injectionCoordinatePermutation e
          (distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk) f))) h).symm.trans
    ((orderedRootTrivialization_permutation (R := R) n lam hk e x f).trans
      (congrArg (springerPermutationAlgEquiv lam (distinctZeroFactorPermutation lam e f))
        (congrArg
          (fun E :
            (OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
              UntruncatedRing R n lam) ≃ₐ[OrderedRootRing R (n - lam.card)]
                ((Fin (n - lam.card) ↪ Fin n) →
                  SpringerRing (OrderedRootRing R (n - lam.card)) lam) =>
            E x (distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk) f)) h)))

end HigherSpecht.OrderedParameterNaturality

namespace HigherSpecht

variable {R S : Type*} [CommRing R] [CommRing S]
variable {n m : ℕ} {lam : YoungDiagram}

set_option backward.isDefEq.respectTransparency false in
/-- The componentwise naturality formula for every ambient coordinate
permutation and every actual ordered-root assignment.  The assignment-to-
injection map is a proved bijection, so this covers every target component. -/
theorem orderedRootTrivialization_permutation [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (e : Equiv.Perm (Fin n))
    (x : OrderedRootRing R (n - lam.card) ⊗[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam)
    (f : DistinctRootAssignments n lam.card (n - lam.card)) :
    orderedRootTrivialization n lam hk
        (elementaryParameterTensorPermutation (OrderedRootRing R (n - lam.card)) e x)
        (injectionCoordinatePermutation e
          (distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk) f)) =
      springerPermutationAlgEquiv lam (distinctZeroFactorPermutation lam e f)
        (orderedRootTrivialization n lam hk x
          (distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk) f)) := by
  exact OrderedParameterNaturality.originalTrivialization_permutation (R := R) n lam hk e x f

/-- Proposition 7.2, with the target written as the literal scalar extension
of the integral Springer ring.  The right-hand action fixes the root ring
and renames the complementary Springer variables. -/
theorem proposition_7_2_integral_trivialization_permutation
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (e : Equiv.Perm (Fin n))
    (x : OrderedRootRing ℤ (n - lam.card) ⊗[ElementaryParameterRing ℤ n lam]
      UntruncatedRing ℤ n lam)
    (f : DistinctRootAssignments n lam.card (n - lam.card)) :
    proposition_7_2_integral_trivialization n lam hk
        (elementaryParameterTensorPermutation (OrderedRootRing ℤ (n - lam.card)) e x)
        (injectionCoordinatePermutation e
          (distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk) f)) =
      springerTensorPermutation (R := ℤ) (S := OrderedRootRing ℤ (n - lam.card))
        lam (distinctZeroFactorPermutation lam e f)
        (proposition_7_2_integral_trivialization n lam hk x
          (distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk) f)) := by
  simp only [proposition_7_2_integral_trivialization_apply]
  rw [orderedRootTrivialization_permutation,
    springerCoefficientBaseChangeEquiv_symm_permutation]

end HigherSpecht
end
end CanonicalSource79

section CanonicalSource80
/- Source: HigherSpecht/InjectionStabilizer.lean -/



/-!
# The actual transitive ordered-root index action and its stabilizer

Coordinate permutations act on injections by postcomposition.  The stabilizer
fixes every assigned coordinate, and restriction identifies it with the full
symmetric group of the complementary coordinates.  Both directions are the
literal restriction/extension of permutations, not a transported action
chosen to make a representation isomorphism hold.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht

variable {n m k : ℕ}

@[simp] theorem injectionCoordinatePermutation_eq_smul
    (g : Equiv.Perm (Fin n)) (f : Fin m ↪ Fin n) :
    injectionCoordinatePermutation g f = g • f := rfl

theorem mem_injectionStabilizer_iff (f : Fin m ↪ Fin n)
    (g : Equiv.Perm (Fin n)) :
    g ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) f ↔
      ∀ i : Fin m, g (f i) = f i := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h i
    exact congrArg (fun e : Fin m ↪ Fin n => e i) h
  · intro h
    apply Function.Embedding.ext
    intro i
    exact h i

theorem injectionStabilizer_complement_iff (f : Fin m ↪ Fin n)
    (g : MulAction.stabilizer (Equiv.Perm (Fin n)) f) (x : Fin n) :
    g.val x ∉ Set.range f ↔ x ∉ Set.range f := by
  apply not_congr
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, g.val.injective ?_⟩
    rw [(mem_injectionStabilizer_iff f g.val).mp g.property i]
    exact hi
  · rintro ⟨i, rfl⟩
    exact ⟨i, ((mem_injectionStabilizer_iff f g.val).mp g.property i).symm⟩

/-- Restrict the stabilizer to the actual complement and extend it back by
fixing the assigned coordinates. -/
def injectionComplementStabilizerEquiv (f : Fin m ↪ Fin n) :
    MulAction.stabilizer (Equiv.Perm (Fin n)) f ≃*
      Equiv.Perm {x : Fin n // x ∉ Set.range f} where
  toFun g := g.val.subtypePerm (injectionStabilizer_complement_iff f g)
  invFun p := ⟨Equiv.Perm.ofSubtype p, by
    apply (mem_injectionStabilizer_iff f _).mpr
    intro i
    exact Equiv.Perm.ofSubtype_apply_of_not_mem p
      (by intro h; exact h ⟨i, rfl⟩)⟩
  left_inv g := by
    apply Subtype.ext
    apply Equiv.Perm.ofSubtype_subtypePerm
    intro x hx
    rintro ⟨i, rfl⟩
    exact hx ((mem_injectionStabilizer_iff f g.val).mp g.property i)
  right_inv p := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact Equiv.Perm.ofSubtype_apply_coe p x
  map_mul' g h := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rfl

@[simp] theorem injectionComplementStabilizerEquiv_apply
    (f : Fin m ↪ Fin n)
    (g : MulAction.stabilizer (Equiv.Perm (Fin n)) f)
    (x : {x : Fin n // x ∉ Set.range f}) :
    (injectionComplementStabilizerEquiv f g x).val = g.val x.val := rfl

@[simp] theorem injectionComplementStabilizerEquiv_symm_apply
    (f : Fin m ↪ Fin n) (p : Equiv.Perm {x : Fin n // x ∉ Set.range f}) :
    (injectionComplementStabilizerEquiv f).symm p =
      ⟨Equiv.Perm.ofSubtype p, by
        apply (mem_injectionStabilizer_iff f _).mpr
        intro i
        exact Equiv.Perm.ofSubtype_apply_of_not_mem p
          (by intro h; exact h ⟨i, rfl⟩)⟩ := rfl

theorem card_injection_complement (hsize : k + m = n) (f : Fin m ↪ Fin n) :
    Fintype.card {x : Fin n // x ∉ Set.range f} = k := by
  rw [Fintype.card_subtype_compl]
  have hr : Fintype.card (Set.range f) = m :=
    (Fintype.card_congr (Equiv.ofInjective f f.injective)).symm.trans
      (Fintype.card_fin m)
  rw [Fintype.card_fin, hr]
  omega

def injectionComplementNumbering (hsize : k + m = n) (f : Fin m ↪ Fin n) :
    Fin k ≃ {x : Fin n // x ∉ Set.range f} :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, card_injection_complement hsize f])

/-- The complementary symmetric group, with its actual coordinate action. -/
def injectionStabilizerEquivSymmetric (hsize : k + m = n) (f : Fin m ↪ Fin n) :
    MulAction.stabilizer (Equiv.Perm (Fin n)) f ≃* Equiv.Perm (Fin k) :=
  (injectionComplementStabilizerEquiv f).trans
    (injectionComplementNumbering hsize f).symm.permCongrHom

theorem injectionStabilizerEquivSymmetric_coordinate (hsize : k + m = n)
    (f : Fin m ↪ Fin n) (g : MulAction.stabilizer (Equiv.Perm (Fin n)) f)
    (i : Fin k) :
    (injectionComplementNumbering hsize f
      (injectionStabilizerEquivSymmetric hsize f g i)).val =
        g.val (injectionComplementNumbering hsize f i).val := by
  simp only [injectionStabilizerEquivSymmetric, MulEquiv.trans_apply,
    Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply, injectionComplementStabilizerEquiv_apply]

/-- Literal transitivity of the coordinate action on injections. -/
theorem exists_injectionCoordinatePermutation (f g : Fin m ↪ Fin n) :
    ∃ e : Equiv.Perm (Fin n), e • f = g := by
  let ef : Fin m ≃ Set.range f := Equiv.ofInjective f f.injective
  let eg : Fin m ≃ Set.range g := Equiv.ofInjective g g.injective
  let erange : Set.range f ≃ Set.range g := ef.symm.trans eg
  have hc : Fintype.card {x : Fin n // x ∉ Set.range f} =
      Fintype.card {x : Fin n // x ∉ Set.range g} := by
    apply Fintype.card_compl_eq_card_compl
    exact Fintype.card_congr erange
  let ecompl : {x : Fin n // x ∉ Set.range f} ≃
      {x : Fin n // x ∉ Set.range g} := Fintype.equivOfCardEq hc
  let e := (Equiv.Set.compl erange).symm ecompl
  refine ⟨e.val, ?_⟩
  apply Function.Embedding.ext
  intro i
  change e.val (f i) = g i
  have he := e.property (ef i)
  change e.val (ef i).val = (eg (ef.symm (ef i))).val at he
  rw [Equiv.symm_apply_apply] at he
  simpa only [ef, eg, Equiv.ofInjective_apply] using he

/-- A fixed genuine injection for the ordered-root factor projection. -/
def standardRootInjection (hsize : k + m = n) : Fin m ↪ Fin n where
  toFun i := ⟨k + i.val, by omega⟩
  inj' i j h := by
    apply Fin.ext
    have hh := congrArg Fin.val h
    dsimp only at hh
    omega

end HigherSpecht
end
end CanonicalSource80

section CanonicalSource81
/- Source: HigherSpecht/OrderedRootComplementAction.lean -/



/-!
# The complementary-coordinate cocycle of the ordered-root action

The numbered complement is exactly the enumeration used by the polynomial
fiber trivialization.  Its coordinate formula proves the cocycle and
identifies the stabilizer action with the genuine complementary symmetric
group.  No representation is defined by conjugating the desired isomorphism.
-/

noncomputable section
open TauCeti
open scoped Classical

namespace HigherSpecht

variable {n : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n)

abbrev RootInjection := Fin (n - lam.card) ↪ Fin n

def injectionZeroNumbering (f : RootInjection lam (n := n)) :
    Fin lam.card ≃ {j : Fin n // j ∉ Set.range f} := by
  let F := (distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk)).symm f
  let E := rootFiberVariableEquiv lam 0
    (splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1))
    F.val none rfl F.property none
  have E' : Fin lam.card ≃ {j : Fin n // assignmentOfInjection f j = none} := by
    simpa only [F, distinctRootBlockShape_none,
      distinctRootAssignmentsEquivInjections_symm_val] using E
  exact E'.trans (Equiv.subtypeEquivRight (assignmentOfInjection_none_iff f))

def injectionZeroEmbedding (f : RootInjection lam (n := n)) : Fin lam.card ↪ Fin n :=
  (injectionZeroNumbering lam hk f).toEmbedding.trans (Function.Embedding.subtype _)

def injectionZeroPermutation (g : Equiv.Perm (Fin n))
    (f : RootInjection lam (n := n)) : Equiv.Perm (Fin lam.card) :=
  distinctZeroFactorPermutation lam g
    ((distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk)).symm f)

theorem assignmentOfInjection_smul (g : Equiv.Perm (Fin n))
    (f : RootInjection lam (n := n)) :
    (distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk)).symm (g • f) =
      rootAssignmentPermutation
        (splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)) g
        ((distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk)).symm f) := by
  let J := distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk)
  have h := distinctRootAssignmentsEquivInjections_permutation
    (Nat.add_sub_of_le hk) g (J.symm f)
  have h' : J (rootAssignmentPermutation
      (splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)) g (J.symm f)) =
      g • f := by
    change J (rootAssignmentPermutation
      (fun i : Option (Fin (n - lam.card)) => i.elim lam.card (fun _ => 1))
      g (J.symm f)) = g • f
    simpa only [J, Equiv.apply_symm_apply,
      injectionCoordinatePermutation_eq_smul] using h
  apply J.injective
  exact (J.apply_symm_apply (g • f)).trans h'.symm

/-- Transport the two actual numberings and their permutation together.
The statement keeps the casts used by the numbered fiber equivalences explicit. -/
private theorem transportedNumberings_coordinate
    {mu nu : YoungDiagram} (hshape : mu = nu) {A B : Type*}
    (E : Fin mu.card ≃ A) (F : Fin mu.card ≃ B)
    (p : Equiv.Perm (Fin mu.card)) (g : Equiv.Perm (Fin n))
    (a : A → Fin n) (b : B → Fin n)
    (h : ∀ j, b (F (p j)) = g (a (E j))) (i : Fin nu.card) :
    b ((Eq.mp (congrArg (fun t : YoungDiagram => Fin t.card ≃ B) hshape) F)
        ((hshape ▸ p) i)) =
      g (a ((Eq.mp (congrArg (fun t : YoungDiagram => Fin t.card ≃ A) hshape) E) i)) := by
  cases hshape
  exact h i

theorem injectionZeroPermutation_coordinate (g : Equiv.Perm (Fin n))
    (f : RootInjection lam (n := n)) (i : Fin lam.card) :
    injectionZeroEmbedding lam hk (g • f) (injectionZeroPermutation lam hk g f i) =
      g (injectionZeroEmbedding lam hk f i) := by
  let r : Option (Fin (n - lam.card)) → ℕ :=
    splitRootMultiplicities lam 0 (fun _ : Fin (n - lam.card) => 1)
  have hmu : r none = lam.card + 0 := rfl
  let F : PrescribedRootAssignments n r :=
    (distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk)).symm f
  let G : PrescribedRootAssignments n r :=
    (distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk)).symm (g • f)
  let mu := rootBlockShape lam 0 r none none
  let E : Fin mu.card ≃ RootFiberVariables F.val none :=
    rootFiberVariableEquiv lam 0 r F.val none hmu F.property none
  let E' : Fin mu.card ≃ RootFiberVariables G.val none :=
    rootFiberVariableEquiv lam 0 r G.val none hmu G.property none
  let p : Equiv.Perm (Fin mu.card) :=
    rootNumberedFactorPermutation lam 0 r none hmu g F none
  have hG : G = rootAssignmentPermutation r g F :=
    assignmentOfInjection_smul lam hk g f
  have hEmbedding : rootFiberEmbedding lam 0 r G.val none hmu G.property none =
      rootFiberEmbedding lam 0 r (rootAssignmentPermutation r g F).val none hmu
        (rootAssignmentPermutation r g F).property none :=
    congrArg (fun H : PrescribedRootAssignments n r =>
      rootFiberEmbedding lam 0 r H.val none hmu H.property none) hG
  have hcoordinate (j : Fin mu.card) : (E' (p j)).val = g (E j).val := by
    exact (congrArg (fun H : Fin mu.card ↪ Fin n => H (p j)) hEmbedding).trans
      (rootNumberedFactorPermutation_coordinate lam 0 r none hmu g F none j)
  have hshape : mu = lam := distinctRootBlockShape_none (ι := Fin (n - lam.card)) lam
  change
    ((Eq.mp (congrArg
        (fun t : YoungDiagram => Fin t.card ≃ RootFiberVariables G.val none) hshape) E')
      ((hshape ▸ p) i)).val =
      g ((Eq.mp (congrArg
        (fun t : YoungDiagram => Fin t.card ≃ RootFiberVariables F.val none) hshape) E) i).val
  exact transportedNumberings_coordinate hshape E E' p g
    (fun x : RootFiberVariables F.val none => x.val)
    (fun x : RootFiberVariables G.val none => x.val) hcoordinate i

@[simp] theorem injectionZeroPermutation_one (f : RootInjection lam (n := n)) :
    injectionZeroPermutation lam hk 1 f = 1 := by
  apply Equiv.ext
  intro i
  apply (injectionZeroEmbedding lam hk f).injective
  simpa only [one_smul, Equiv.Perm.one_apply] using
    injectionZeroPermutation_coordinate lam hk 1 f i

theorem injectionZeroPermutation_mul (g h : Equiv.Perm (Fin n))
    (f : RootInjection lam (n := n)) :
    injectionZeroPermutation lam hk (g * h) f =
      injectionZeroPermutation lam hk g (h • f) * injectionZeroPermutation lam hk h f := by
  apply Equiv.ext
  intro i
  apply (injectionZeroEmbedding lam hk ((g * h) • f)).injective
  rw [injectionZeroPermutation_coordinate, Equiv.Perm.mul_apply]
  change g (h (injectionZeroEmbedding lam hk f i)) = _
  rw [mul_smul, Equiv.Perm.mul_apply, injectionZeroPermutation_coordinate,
    injectionZeroPermutation_coordinate]

def rootInjectionStabilizer (f : RootInjection lam (n := n)) :=
  MulAction.stabilizer (Equiv.Perm (Fin n)) f

def rootInjectionStabilizerEquivSymmetric (f : RootInjection lam (n := n)) :
    rootInjectionStabilizer lam f ≃* Equiv.Perm (Fin lam.card) :=
  (injectionComplementStabilizerEquiv f).trans
    (injectionZeroNumbering lam hk f).symm.permCongrHom

theorem rootInjectionStabilizerEquivSymmetric_eq (f : RootInjection lam (n := n))
    (g : rootInjectionStabilizer lam f) :
    rootInjectionStabilizerEquivSymmetric lam hk f g =
      injectionZeroPermutation lam hk g.val f := by
  apply Equiv.ext
  intro i
  apply (injectionZeroEmbedding lam hk f).injective
  have hg : g.val • f = f := MulAction.mem_stabilizer_iff.mp g.property
  have hcoord := injectionZeroPermutation_coordinate lam hk g.val f i
  rw [hg] at hcoord
  rw [hcoord]
  change (injectionZeroNumbering lam hk f
      ((injectionZeroNumbering lam hk f).symm
        (injectionComplementStabilizerEquiv f g (injectionZeroNumbering lam hk f i)))).val =
    g.val (injectionZeroNumbering lam hk f i).val
  rw [Equiv.apply_symm_apply]
  exact injectionComplementStabilizerEquiv_apply f
    (show MulAction.stabilizer (Equiv.Perm (Fin n)) f from g)
    (injectionZeroNumbering lam hk f i)

end HigherSpecht
end
end CanonicalSource81

section CanonicalSource82
/- Source: HigherSpecht/TransitiveProductInduction.lean -/



/-!
# A genuine transitive product is an induced representation

This supporting result composes the literal restriction/coinduction adjunction
map with the proved finite-index induction--coinduction isomorphism. Its
transport hypotheses concern independently specified representations and
factor maps. The ordered-root application must supply those data from actual
coordinate permutations; they are not premises of a paper theorem.
-/

noncomputable section
open CategoryTheory

namespace HigherSpecht

universe u v

def transitiveProductInducedIso
    {R : Type u} {G P I : Type v} [CommRing R] [Group G] [MulAction G P]
    {p : I → P} {M : I → Type (max u v)} {w : I}
    [(MulAction.stabilizer G (p w)).FiniteIndex]
    (T : ∀ (g : G) {i j : I}, p j = g • p i → M i ≃ M j)
    (B : Rep.{max u v} R G) (A : Rep.{max u v} R (MulAction.stabilizer G (p w)))
    (f : Rep.res (MulAction.stabilizer G (p w)).subtype B ⟶ A)
    (e : B ≃ ∀ i, M i)
    (he : ∀ (g : G) (x : B) {i j : I} (h : p j = g • p i),
      e (B.ρ g x) j = T g h (e x i))
    (eA : A ≃ M w) (hf : ∀ x, eA (f.hom x) = e x w)
    (hA : ∀ (d : MulAction.stabilizer G (p w)) (a : A),
      eA (A.ρ d a) = T d (MulAction.mem_stabilizer_iff.mp d.2).symm (eA a))
    (hT : ∀ (g g' : G) {i j k : I} (h : p j = g • p i)
      (h' : p k = g' • p j) (a : M i),
      T g' h' (T g h a) = T (g' * g) (by rw [h', h, mul_smul]) a)
    (htrans : ∀ i, ∃ g : G, p w = g • p i)
    (hsurj : ∀ g : G, ∃ i, p w = g • p i) :
    B ≅ Rep.ind (MulAction.stabilizer G (p w)).subtype A := by
  classical
  exact (Rep.mkIso ((Rep.resCoindToHom _ B A f).hom.ofBijective
    (TauCeti.resCoindToHom_bijective_of_transport T f e he eA hf hA hT htrans hsurj))) ≪≫
      (Rep.indCoindIso A).symm

end HigherSpecht
end
end CanonicalSource82

section CanonicalSource83
/- Source: HigherSpecht/OrderedRootRepresentations.lean -/



/-!
# The induced-module assertion over the ordered-root ring

The source action fixes the root coefficients and renames the original
coordinates.  The stabilizer fixes each assigned root coordinate and acts on
the genuine Springer ring by the independently numbered complementary
coordinates.  The literal projection to one factor is an intertwiner.  Actual
transitivity, the complementary-coordinate cocycle, and finite-index
induction/coinduction then give the induced-module isomorphism.

The subgroup in the final induced object is identified with `S_k` by the
explicit restriction/extension equivalence, not by an assumed representation
transport.  No freeness, rank, characteristic-zero, or semisimplicity premise
is used in this component of Proposition 7.2.
-/

noncomputable section

open TauCeti CategoryTheory
open scoped Classical TensorProduct

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n : ℕ} {lam : YoungDiagram}

@[simp] theorem springerPermutationAlgEquiv_eq_representation
    (lam : YoungDiagram) (g : Equiv.Perm (Fin lam.card)) (x : SpringerRing R lam) :
    springerPermutationAlgEquiv lam g x = springerRepresentation R lam g x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

@[simp] theorem untruncatedParameterPermutation_one
    (lam : YoungDiagram) (x : UntruncatedRing R n lam) :
    untruncatedParameterPermutation lam 1 x = x := by
  rw [untruncatedParameterPermutation_eq_representation, map_one]
  rfl

theorem untruncatedParameterPermutation_mul
    (lam : YoungDiagram) (g h : Equiv.Perm (Fin n)) (x : UntruncatedRing R n lam) :
    untruncatedParameterPermutation lam (g * h) x =
      untruncatedParameterPermutation lam g (untruncatedParameterPermutation lam h x) := by
  simp only [untruncatedParameterPermutation_eq_representation, map_mul,
    Module.End.mul_apply]

def elementaryParameterTensorRepresentation
    (S : Type*) [CommRing S] [Algebra (ElementaryParameterRing R n lam) S] :
    Representation S (Equiv.Perm (Fin n))
      (S ⊗[ElementaryParameterRing R n lam] UntruncatedRing R n lam) where
  toFun g := (elementaryParameterTensorPermutation S g).toLinearMap
  map_one' := by
    apply TensorProduct.AlgebraTensorModule.ext (R := ElementaryParameterRing R n lam)
    intro s x
    change elementaryParameterTensorPermutation S 1
      (s ⊗ₜ[ElementaryParameterRing R n lam] x) = s ⊗ₜ[ElementaryParameterRing R n lam] x
    rw [elementaryParameterTensorPermutation_tmul, untruncatedParameterPermutation_one]
  map_mul' g h := by
    apply TensorProduct.AlgebraTensorModule.ext (R := ElementaryParameterRing R n lam)
    intro s x
    change elementaryParameterTensorPermutation S (g * h)
        (s ⊗ₜ[ElementaryParameterRing R n lam] x) =
      elementaryParameterTensorPermutation S g
        (elementaryParameterTensorPermutation S h (s ⊗ₜ[ElementaryParameterRing R n lam] x))
    simp only [elementaryParameterTensorPermutation_tmul, untruncatedParameterPermutation_mul]

@[simp] theorem elementaryParameterTensorRepresentation_apply
    (S : Type*) [CommRing S] [Algebra (ElementaryParameterRing R n lam) S]
    (g : Equiv.Perm (Fin n))
    (x : S ⊗[ElementaryParameterRing R n lam] UntruncatedRing R n lam) :
    elementaryParameterTensorRepresentation S g x =
      elementaryParameterTensorPermutation S g x := rfl

abbrev orderedRootSourceRep (R : Type*) [CommRing R]
    (n : ℕ) (lam : YoungDiagram) :
    Rep (OrderedRootRing R (n - lam.card)) (Equiv.Perm (Fin n)) :=
  Rep.of (elementaryParameterTensorRepresentation (R := R)
    (n := n) (lam := lam) (OrderedRootRing R (n - lam.card)))

abbrev orderedRootComplementRep (R : Type*) [CommRing R]
    (lam : YoungDiagram) (hk : lam.card ≤ n) (f : RootInjection lam (n := n)) :
    Rep (OrderedRootRing R (n - lam.card)) (rootInjectionStabilizer lam f) :=
  Rep.of ((springerRepresentation (OrderedRootRing R (n - lam.card)) lam).comp
    (rootInjectionStabilizerEquivSymmetric lam hk f).toMonoidHom)

/-- The actual coordinate embedding of the complementary symmetric group. -/
def complementarySymmetricEmbedding (lam : YoungDiagram) (hk : lam.card ≤ n)
    (f : RootInjection lam (n := n)) :
    Equiv.Perm (Fin lam.card) →* Equiv.Perm (Fin n) :=
  (rootInjectionStabilizer lam f).subtype.comp
    (rootInjectionStabilizerEquivSymmetric lam hk f).symm.toMonoidHom

theorem complementarySymmetricEmbedding_injective (lam : YoungDiagram)
    (hk : lam.card ≤ n) (f : RootInjection lam (n := n)) :
    Function.Injective (complementarySymmetricEmbedding lam hk f) :=
  Subtype.val_injective.comp (rootInjectionStabilizerEquivSymmetric lam hk f).symm.injective

theorem complementarySymmetricEmbedding_fixes_assigned (lam : YoungDiagram)
    (hk : lam.card ≤ n) (f : RootInjection lam (n := n))
    (g : Equiv.Perm (Fin lam.card)) (i : Fin (n - lam.card)) :
    complementarySymmetricEmbedding lam hk f g (f i) = f i :=
  (mem_injectionStabilizer_iff f _).mp
    ((rootInjectionStabilizerEquivSymmetric lam hk f).symm g).property i

theorem orderedRootTrivialization_smul [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (g : Equiv.Perm (Fin n)) (x : orderedRootSourceRep R n lam)
    (f : RootInjection lam (n := n)) :
    orderedRootTrivialization (R := R) n lam hk ((orderedRootSourceRep R n lam).ρ g x) (g • f) =
      springerPermutationAlgEquiv lam (injectionZeroPermutation lam hk g f)
        (orderedRootTrivialization (R := R) n lam hk x f) := by
  have h := orderedRootTrivialization_permutation (R := R) n lam hk g x
    ((distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk)).symm f)
  simpa only [Equiv.apply_symm_apply, injectionCoordinatePermutation_eq_smul,
    injectionZeroPermutation, orderedRootSourceRep,
    elementaryParameterTensorRepresentation_apply] using h

/-- The literal factor projection, with the stabilizer action proved from
the coordinate naturality formula. -/
def orderedRootFactorProjection [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (f : RootInjection lam (n := n)) :
    Rep.res (rootInjectionStabilizer lam f).subtype (orderedRootSourceRep R n lam) ⟶
      orderedRootComplementRep R lam hk f := by
  let L : orderedRootSourceRep R n lam →ₗ[OrderedRootRing R (n - lam.card)]
      SpringerRing (OrderedRootRing R (n - lam.card)) lam :=
    (LinearMap.proj f).comp (orderedRootTrivialization (R := R) n lam hk).toLinearMap
  refine Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (Rep.res (rootInjectionStabilizer lam f).subtype (orderedRootSourceRep R n lam)).ρ
    (orderedRootComplementRep R lam hk f).ρ L ?_)
  intro g x
  simp only [L, LinearMap.comp_apply, LinearMap.proj_apply, AlgEquiv.toLinearMap_apply,
    Rep.coe_res_obj_ρ']
  change orderedRootTrivialization (R := R) n lam hk
      ((orderedRootSourceRep R n lam).ρ g.val x) f =
    springerRepresentation (OrderedRootRing R (n - lam.card)) lam
      (rootInjectionStabilizerEquivSymmetric lam hk f g)
      (orderedRootTrivialization (R := R) n lam hk x f)
  have hg : g.val • f = f := MulAction.mem_stabilizer_iff.mp g.property
  have h := orderedRootTrivialization_smul (R := R) n lam hk g.val x f
  rw [hg] at h
  exact h.trans ((springerPermutationAlgEquiv_eq_representation lam _ _).trans
    (congrArg (fun q : Equiv.Perm (Fin lam.card) =>
      springerRepresentation (OrderedRootRing R (n - lam.card)) lam q
        (orderedRootTrivialization (R := R) n lam hk x f))
      (rootInjectionStabilizerEquivSymmetric_eq lam hk f g).symm))

@[simp] theorem orderedRootFactorProjection_apply [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (f : RootInjection lam (n := n)) (x : orderedRootSourceRep R n lam) :
    (orderedRootFactorProjection n lam hk f).hom x =
      orderedRootTrivialization (R := R) n lam hk x f := rfl

/-- Proposition 7.2's induced-module assertion over the ordered-root ring.
The subgroup is literally the pointwise stabilizer of the ordered root
injection and its Springer action is the complementary `S_k` action. -/
def proposition_7_2_orderedRoot_induced [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (f : RootInjection lam (n := n)) :
    orderedRootSourceRep R n lam ≅
      Rep.ind (rootInjectionStabilizer lam f).subtype
        (orderedRootComplementRep R lam hk f) := by
  let S := OrderedRootRing R (n - lam.card)
  let T : ∀ (g : Equiv.Perm (Fin n))
      {i j : RootInjection lam (n := n)}, j = g • i →
      SpringerRing S lam ≃ SpringerRing S lam :=
    fun g {i j} _ => (springerPermutationAlgEquiv lam
      (injectionZeroPermutation lam hk g i)).toEquiv
  refine transitiveProductInducedIso
    (p := fun i : RootInjection lam (n := n) => i)
    (M := fun _ => SpringerRing S lam) (w := f) T
    (orderedRootSourceRep R n lam) (orderedRootComplementRep R lam hk f)
    (orderedRootFactorProjection n lam hk f)
    (orderedRootTrivialization (R := R) n lam hk).toEquiv ?_
    (Equiv.refl _) (fun _ => rfl) ?_ ?_ ?_ ?_
  · intro g x i j hij
    subst j
    exact orderedRootTrivialization_smul n lam hk g x i
  · intro g x
    change springerRepresentation S lam
        (rootInjectionStabilizerEquivSymmetric lam hk f g) x =
      springerPermutationAlgEquiv (R := S) lam (injectionZeroPermutation lam hk g.val f) x
    exact (congrArg (fun q : Equiv.Perm (Fin lam.card) =>
      springerRepresentation S lam q x)
      (rootInjectionStabilizerEquivSymmetric_eq lam hk f g)).trans
        (springerPermutationAlgEquiv_eq_representation (R := S) lam _ x).symm
  · intro g h i j k hij hjk x
    subst j
    subst k
    change springerPermutationAlgEquiv lam (injectionZeroPermutation lam hk h (g • i))
        (springerPermutationAlgEquiv lam (injectionZeroPermutation lam hk g i) x) =
      springerPermutationAlgEquiv lam (injectionZeroPermutation lam hk (h * g) i) x
    simp only [springerPermutationAlgEquiv_eq_representation,
      injectionZeroPermutation_mul, map_mul, Module.End.mul_apply]
  · intro i
    obtain ⟨g, hg⟩ := exists_injectionCoordinatePermutation i f
    exact ⟨g, hg.symm⟩
  · intro g
    exact ⟨g⁻¹ • f, by simp only [smul_inv_smul]⟩

/-- The integral statement, with one genuine distinguished injection.  The
coefficient-extension equivalence identifies its Springer factor with
`OrderedRootRing ℤ m ⊗[ℤ] SpringerRing ℤ lam` equivariantly. -/
def proposition_7_2_integral_induced (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) :
    orderedRootSourceRep ℤ n lam ≅
      Rep.ind (rootInjectionStabilizer lam
        (standardRootInjection (Nat.add_sub_of_le hk))).subtype
        (orderedRootComplementRep ℤ lam hk
          (standardRootInjection (Nat.add_sub_of_le hk))) :=
  proposition_7_2_orderedRoot_induced n lam hk _

/-- Coefficient extension of the literal Springer action; the new coefficient
factor is fixed pointwise. -/
def springerTensorRepresentation (S : Type*) [CommRing S] [Algebra R S]
    (lam : YoungDiagram) :
    Representation S (Equiv.Perm (Fin lam.card)) (S ⊗[R] SpringerRing R lam) where
  toFun g := (springerTensorPermutation (R := R) (S := S) lam g).toLinearMap
  map_one' := by
    apply TensorProduct.AlgebraTensorModule.ext (R := R)
    intro s x
    change springerTensorPermutation lam 1 (s ⊗ₜ[R] x) = s ⊗ₜ[R] x
    rw [springerTensorPermutation_tmul, springerPermutationAlgEquiv_eq_representation, map_one]
    rfl
  map_mul' g h := by
    apply TensorProduct.AlgebraTensorModule.ext (R := R)
    intro s x
    change springerTensorPermutation lam (g * h) (s ⊗ₜ[R] x) =
      springerTensorPermutation lam g (springerTensorPermutation lam h (s ⊗ₜ[R] x))
    simp only [springerTensorPermutation_tmul,
      springerPermutationAlgEquiv_eq_representation, map_mul, Module.End.mul_apply]

/-- Coefficient extension is an equivalence of the literal representations.
The source and target carriers may live in different universes; this
heterogeneous formulation retains arbitrary coefficient rings `R` and `S`.
The ordered-root specialization below packages it as a categorical iso. -/
def springerCoefficientRepresentationEquiv (S : Type*) [CommRing S] [Algebra R S]
    (lam : YoungDiagram) :
    Representation.Equiv (springerTensorRepresentation (R := R) S lam)
      (springerRepresentation S lam) :=
  Representation.Equiv.mk
    (springerCoefficientBaseChangeEquiv (R := R) S lam).toLinearEquiv
    (fun g => by
      apply LinearMap.ext
      intro x
      change springerCoefficientBaseChangeEquiv (R := R) S lam
          (springerTensorPermutation (R := R) (S := S) lam g x) =
        springerRepresentation S lam g
          (springerCoefficientBaseChangeEquiv (R := R) S lam x)
      rw [springerCoefficientBaseChangeEquiv_permutation,
        springerPermutationAlgEquiv_eq_representation])

abbrev orderedRootTensorComplementRep (R : Type*) [CommRing R]
    (lam : YoungDiagram) (hk : lam.card ≤ n) (f : RootInjection lam (n := n)) :
    Rep (OrderedRootRing R (n - lam.card)) (rootInjectionStabilizer lam f) :=
  Rep.res (rootInjectionStabilizerEquivSymmetric lam hk f).toMonoidHom
    (Rep.of (springerTensorRepresentation (R := R)
      (OrderedRootRing R (n - lam.card)) lam))

def orderedRootTensorComplementIso (R : Type*) [CommRing R]
    (lam : YoungDiagram) (hk : lam.card ≤ n) (f : RootInjection lam (n := n)) :
    orderedRootTensorComplementRep R lam hk f ≅ orderedRootComplementRep R lam hk f :=
  (Rep.resFunctor (rootInjectionStabilizerEquivSymmetric lam hk f).toMonoidHom).mapIso
    (Rep.mkIso (springerCoefficientRepresentationEquiv (R := R)
      (OrderedRootRing R (n - lam.card)) lam))

/-- The induced module with the factor written as the literal coefficient
extension of the original coefficient-ring Springer algebra. -/
def proposition_7_2_orderedRoot_induced_tensor [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (f : RootInjection lam (n := n)) :
    orderedRootSourceRep R n lam ≅
      Rep.ind (rootInjectionStabilizer lam f).subtype
        (orderedRootTensorComplementRep R lam hk f) :=
  proposition_7_2_orderedRoot_induced n lam hk f ≪≫
    (Rep.indFunctor (OrderedRootRing R (n - lam.card))
      (rootInjectionStabilizer lam f).subtype).mapIso
        (orderedRootTensorComplementIso R lam hk f).symm

/-- The complete induced-module formula over the integral ordered-root ring.
Its source and Springer factor are the displayed scalar extensions in the
paper, with the tensor factors placed coefficient-first. -/
def proposition_7_2_integral_induced_tensor (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) :
    orderedRootSourceRep ℤ n lam ≅
      Rep.ind (rootInjectionStabilizer lam
        (standardRootInjection (Nat.add_sub_of_le hk))).subtype
        (orderedRootTensorComplementRep ℤ lam hk
          (standardRootInjection (Nat.add_sub_of_le hk))) :=
  proposition_7_2_orderedRoot_induced_tensor n lam hk _

end HigherSpecht
end
end CanonicalSource83

section CanonicalSource84
/- Source: HigherSpecht/OrderedRootBaseChange.lean -/



/-!
# Ordered roots after coefficient extension and in the zero-parameter case

The root polynomial algebra and its displayed localization commute with
coefficient extension.  The images of the individual roots are checked, so
the ordered-root variables keep their intended meaning.  The integral
elementary-parameter algebra can consequently be specialized directly to
the ordered-root algebra of any coefficient field, with the same actual
Springer factors and no characteristic restriction.
-/

noncomputable section

open TauCeti MvPolynomial
open scoped Classical TensorProduct BigOperators

namespace HigherSpecht

variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_orderedRootDiscriminant (f : R →+* S) (m : ℕ) :
    MvPolynomial.map f (orderedRootDiscriminant R m) = orderedRootDiscriminant S m := by
  simp only [orderedRootDiscriminant, map_mul, map_prod, map_sub, MvPolynomial.map_X]

def orderedRootCoefficientBaseChangeEquiv [Algebra R S] (m : ℕ) :
    S ⊗[R] OrderedRootRing R m ≃ₐ[S] OrderedRootRing S m := by
  let E := MvPolynomial.algebraTensorAlgEquiv (σ := Fin m × Unit) R S
  have hD : E ((1 : S) ⊗ₜ[R] orderedRootDiscriminant R m) =
      orderedRootDiscriminant S m := by
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul,
      map_orderedRootDiscriminant]
  have hpowers : Submonoid.map E
      (Submonoid.powers ((1 : S) ⊗ₜ[R] orderedRootDiscriminant R m)) =
      Submonoid.powers (orderedRootDiscriminant S m) := by
    rw [Submonoid.map_powers, hD]
  exact (IsLocalization.Away.tensorProductEquivTMulRight R S
    (orderedRootDiscriminant R m) (OrderedRootRing R m)).trans
    (IsLocalization.algEquivOfAlgEquiv
      (Localization.Away ((1 : S) ⊗ₜ[R] orderedRootDiscriminant R m))
      (OrderedRootRing S m) E hpowers)

@[simp] theorem orderedRootCoefficientBaseChangeEquiv_root [Algebra R S]
    (m : ℕ) (i : Fin m) :
    orderedRootCoefficientBaseChangeEquiv (R := R) (S := S) m
        ((1 : S) ⊗ₜ[R] orderedRoot (R := R) m i) = orderedRoot (R := S) m i := by
  simp only [orderedRootCoefficientBaseChangeEquiv, AlgEquiv.trans_apply, orderedRoot,
    IsLocalization.Away.tensorProductEquivTMulRight_tmul,
    IsLocalization.algEquivOfAlgEquiv_eq, MvPolynomial.algebraTensorAlgEquiv_tmul,
    one_smul, MvPolynomial.map_X]

@[simp] theorem orderedRootDiscriminant_zero (R : Type*) [CommRing R] :
    orderedRootDiscriminant R 0 = 1 := by
  simp [orderedRootDiscriminant]

/-- With no roots the inverted product is literally one, and the coefficient
map identifies the ordered-root ring with its original coefficient ring. -/
def orderedRootRingZeroEquiv (R : Type*) [CommRing R] :
    OrderedRootRing R 0 ≃ₐ[R] R := by
  letI : IsLocalization.Away (1 : OrderedRootPolynomial R 0) (OrderedRootRing R 0) := by
    rw [← orderedRootDiscriminant_zero R]
    infer_instance
  exact ((IsLocalization.atOne (OrderedRootPolynomial R 0)
    (OrderedRootRing R 0)).restrictScalars R).symm.trans
      (MvPolynomial.isEmptyAlgEquiv R (Fin 0 × Unit))

@[simp] theorem orderedRootRingZeroEquiv_algebraMap (R : Type*) [CommRing R] (r : R) :
    orderedRootRingZeroEquiv R (algebraMap R (OrderedRootRing R 0) r) = r := by
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
    (orderedRootRingZeroEquiv R).commutes r

/-- The integral elementary parameters sent to the elementary functions of
the actual ordered roots over `K`.  This is an explicit local algebra
structure, not a replacement for the original parameter action. -/
def orderedIntegralParameterAlgebra (K : Type*) [CommRing K]
    (n : ℕ) (lam : YoungDiagram) :
    Algebra (ElementaryParameterRing ℤ n lam) (OrderedRootRing K (n - lam.card)) :=
  (MvPolynomial.aeval
    (orderedRootElementaryParameters (R := K) (n - lam.card))).toRingHom.toAlgebra

@[simp] theorem orderedIntegralParameter_algebraMap_X
    (K : Type*) [CommRing K] (n : ℕ) (lam : YoungDiagram)
    (i : Fin (n - lam.card)) :
    letI := orderedIntegralParameterAlgebra K n lam
    algebraMap (ElementaryParameterRing ℤ n lam) (OrderedRootRing K (n - lam.card))
      (MvPolynomial.X i) = orderedRootElementaryParameters (R := K) (n - lam.card) i :=
  MvPolynomial.aeval_X _ _

/-- The integral elementary-parameter presentation at the actual ordered roots.
Naming the equality-transported presentation keeps later comparisons abstract. -/
def orderedRootIntegralParameterPresentation (K : Type*) [CommRing K]
    (n : ℕ) (lam : YoungDiagram) :
    letI := orderedIntegralParameterAlgebra K n lam
    OrderedRootRing K (n - lam.card) ⊗[ElementaryParameterRing ℤ n lam]
        UntruncatedRing ℤ n lam ≃ₐ[OrderedRootRing K (n - lam.card)]
      ParameterFiber (OrderedRootRing K (n - lam.card)) n lam (n - lam.card)
        (orderedRootElementaryParameters (R := K) (n - lam.card)) := by
  letI := orderedIntegralParameterAlgebra K n lam
  exact elementaryParameterBaseChangeEquivOfEq (R := ℤ) n lam
    (OrderedRootRing K (n - lam.card))
    (orderedRootElementaryParameters (R := K) (n - lam.card))
    (by funext i; exact orderedIntegralParameter_algebraMap_X K n lam i)

namespace IntegralBaseChangeComparison

/-- A comparison whose complete original map, evaluation and covariance
are all exposed as checked proof fields. -/
structure ComparisonCertificate
    {K : Type*} [CommSemiring K]
    {A : Type*} {B : Type*} {C : Type*} {G : Type*}
    [Semiring A] [Semiring B] [Semiring C]
    [Algebra K A] [Algebra K B] [Algebra K C]
    (P₀ : A ≃ₐ[K] C) (Q₀ : B ≃ₐ[K] C)
    (u : G → A ≃ₐ[K] A) (v : G → B ≃ₐ[K] B) where
  equiv : A ≃ₐ[K] B
  eq_original : equiv = P₀.trans Q₀.symm
  evaluate_raw : ∀ x, equiv.toEquiv.toFun x =
    Q₀.symm.toEquiv.toFun (P₀.toEquiv.toFun x)
  evaluate : ∀ x, equiv x = Q₀.symm (P₀ x)
  covariance : ∀ g x, equiv (u g x) = v g (equiv x)

/-- The constructor is fully defined. It uses the two certified maps and
proves equality to the original comparison before any concrete ring is inserted.
The input covariance proofs concern the certified maps only. -/
opaque certifiedComparison
    {K : Type*} [CommSemiring K]
    {A : Type*} {B : Type*} {C : Type*} {G : Type*}
    [Semiring A] [Semiring B] [Semiring C]
    [Algebra K A] [Algebra K B] [Algebra K C]
    (P₀ : A ≃ₐ[K] C) (Q₀ : B ≃ₐ[K] C)
    (P : A ≃ₐ[K] C) (Q : B ≃ₐ[K] C)
    (u : G → A ≃ₐ[K] A) (v : G → B ≃ₐ[K] B) (w : G → C ≃ₐ[K] C)
    (hP : P = P₀) (hQ : Q = Q₀)
    (hPc : ∀ g x, P.toEquiv.toFun ((u g).toEquiv.toFun x) =
      (w g).toEquiv.toFun (P.toEquiv.toFun x))
    (hQc : ∀ g y, Q.toEquiv.toFun ((v g).toEquiv.toFun y) =
      (w g).toEquiv.toFun (Q.toEquiv.toFun y)) :
    ComparisonCertificate P₀ Q₀ u v :=
  { equiv := P.trans Q.symm
    eq_original := by cases hP; cases hQ; rfl
    evaluate_raw := by intro x; cases hP; cases hQ; rfl
    evaluate := by intro x; cases hP; cases hQ; rfl
    covariance := by
      intro g x
      have hp : P (u g x) = w g (P x) := hPc g x
      have hq : ∀ y, Q (v g y) = w g (Q y) := fun y => hQc g y
      apply Q.injective
      simpa only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply, hq] using hp }

/-- The two actual coefficient presentations use the parameter certificates
already proved in Naturality, with the same explicit integral parameter action. -/
def integralComparisonCertificate (K : Type*) [CommRing K]
    (n : ℕ) (lam : YoungDiagram) :
    letI := orderedIntegralParameterAlgebra K n lam
    ComparisonCertificate
      (orderedRootIntegralParameterPresentation K n lam)
      (orderedRootParameterPresentation (R := K) n lam)
      (fun e : Equiv.Perm (Fin n) => elementaryParameterTensorPermutation
        (R := ℤ) (n := n) (lam := lam) (OrderedRootRing K (n - lam.card)) e)
      (fun e : Equiv.Perm (Fin n) => elementaryParameterTensorPermutation
        (R := K) (n := n) (lam := lam) (OrderedRootRing K (n - lam.card)) e) := by
  letI := orderedIntegralParameterAlgebra K n lam
  let S := OrderedRootRing K (n - lam.card)
  let a : Fin (n - lam.card) → S := orderedRootElementaryParameters (R := K) _
  have hz : (fun i : Fin (n - lam.card) =>
      algebraMap (ElementaryParameterRing ℤ n lam) S (MvPolynomial.X i)) = a := by
    funext i
    exact orderedIntegralParameter_algebraMap_X K n lam i
  have hk : (fun i : Fin (n - lam.card) =>
      algebraMap (ElementaryParameterRing K n lam) S (MvPolynomial.X i)) = a := by
    funext i
    exact orderedRootParameter_algebraMap_X n lam i
  let CP := OrderedParameterCovariance.certifiedParameter
    (R := ℤ) n lam S a hz
  let CQ := OrderedParameterCovariance.certifiedParameter
    (R := K) n lam S a hk
  have hP : CP.equiv = orderedRootIntegralParameterPresentation K n lam := by
    exact CP.eq_original
  have hQ : CQ.equiv = orderedRootParameterPresentation (R := K) n lam := by
    exact CQ.eq_original
  exact certifiedComparison (K := S)
    (A := S ⊗[ElementaryParameterRing ℤ n lam] UntruncatedRing ℤ n lam)
    (B := S ⊗[ElementaryParameterRing K n lam] UntruncatedRing K n lam)
    (C := ParameterFiber S n lam (n - lam.card) a)
    (G := Equiv.Perm (Fin n))
    (orderedRootIntegralParameterPresentation K n lam)
    (orderedRootParameterPresentation (R := K) n lam)
    CP.equiv CQ.equiv
    (fun e => elementaryParameterTensorPermutation (R := ℤ) (n := n) (lam := lam) S e)
    (fun e => elementaryParameterTensorPermutation (R := K) (n := n) (lam := lam) S e)
    (fun e => parameterFiberPermutation (n := n) (lam := lam) a e)
    hP hQ (fun e x => CP.covariance e x) (fun e y => CQ.covariance e y)

end IntegralBaseChangeComparison

/-- The actual integral source specialized to the ordered-root ring of `K`
agrees with the same construction made over `K`. -/
def orderedRootIntegralSourceBaseChangeEquiv (K : Type*) [CommRing K]
    (n : ℕ) (lam : YoungDiagram) :
    letI := orderedIntegralParameterAlgebra K n lam
    OrderedRootRing K (n - lam.card) ⊗[ElementaryParameterRing ℤ n lam]
        UntruncatedRing ℤ n lam ≃ₐ[OrderedRootRing K (n - lam.card)]
      OrderedRootRing K (n - lam.card) ⊗[ElementaryParameterRing K n lam]
        UntruncatedRing K n lam := by
  letI := orderedIntegralParameterAlgebra K n lam
  exact (IntegralBaseChangeComparison.integralComparisonCertificate K n lam).equiv

/-- The comparison is the inverse coefficient presentation after the integral
presentation. This formula unfolds no quotient or tensor construction. -/
theorem orderedRootIntegralSourceBaseChangeEquiv_apply
    (K : Type*) [CommRing K] (n : ℕ) (lam : YoungDiagram) :
    letI := orderedIntegralParameterAlgebra K n lam
    ∀ x : OrderedRootRing K (n - lam.card) ⊗[ElementaryParameterRing ℤ n lam]
        UntruncatedRing ℤ n lam,
      orderedRootIntegralSourceBaseChangeEquiv K n lam x =
        (orderedRootParameterPresentation (R := K) n lam).symm
          (orderedRootIntegralParameterPresentation K n lam x) := by
  letI := orderedIntegralParameterAlgebra K n lam
  intro x
  exact (IntegralBaseChangeComparison.integralComparisonCertificate K n lam).evaluate x

/-- Naming the presentations preserves the original anonymous quotient/tensor
composite exactly, including its equality transports and inverse. -/
private theorem orderedRootIntegralSourceBaseChangeEquiv_eq_original
    (K : Type*) [CommRing K] (n : ℕ) (lam : YoungDiagram) :
    letI := orderedIntegralParameterAlgebra K n lam
    orderedRootIntegralSourceBaseChangeEquiv K n lam = (by
      let S := OrderedRootRing K (n - lam.card)
      letI := orderedIntegralParameterAlgebra K n lam
      let a : Fin (n - lam.card) → S := orderedRootElementaryParameters (R := K) _
      have hz : (fun i : Fin (n - lam.card) =>
          algebraMap (ElementaryParameterRing ℤ n lam) S (MvPolynomial.X i)) = a := by
        funext i
        exact MvPolynomial.aeval_X _ _
      have hk : (fun i : Fin (n - lam.card) =>
          algebraMap (ElementaryParameterRing K n lam) S (MvPolynomial.X i)) = a := by
        funext i
        exact orderedRootParameter_algebraMap_X n lam i
      let EZ : S ⊗[ElementaryParameterRing ℤ n lam] UntruncatedRing ℤ n lam ≃ₐ[S]
          ParameterFiber S n lam (n - lam.card) a := by
        rw [← hz]
        exact elementaryParameterBaseChangeEquiv (R := ℤ) n lam S
      let EK : S ⊗[ElementaryParameterRing K n lam] UntruncatedRing K n lam ≃ₐ[S]
          ParameterFiber S n lam (n - lam.card) a := by
        rw [← hk]
        exact elementaryParameterBaseChangeEquiv (R := K) n lam S
      exact EZ.trans EK.symm) := by
  letI := orderedIntegralParameterAlgebra K n lam
  exact (IntegralBaseChangeComparison.integralComparisonCertificate K n lam).eq_original.trans
    (by rfl)

/-- Naturality survives the literal equality transport of the parameter
family. The named presentation remains abstract in its applications. -/
private theorem transportedParameterBaseChange_permutation
    {R : Type*} [CommRing R] (S : Type*) [CommRing S] (n : ℕ) (lam : YoungDiagram)
    [Algebra (ElementaryParameterRing R n lam) S]
    (a : Fin (n - lam.card) → S)
    (ha : (fun i : Fin (n - lam.card) =>
      algebraMap (ElementaryParameterRing R n lam) S (MvPolynomial.X i)) = a)
    (e : Equiv.Perm (Fin n))
    (x : S ⊗[ElementaryParameterRing R n lam] UntruncatedRing R n lam) :
    elementaryParameterBaseChangeEquivOfEq (R := R) n lam S a ha
        (elementaryParameterTensorPermutation (R := R) (n := n) (lam := lam) S e x) =
      parameterFiberPermutation a e
        (elementaryParameterBaseChangeEquivOfEq (R := R) n lam S a ha x) := by
  subst a
  exact elementaryParameterBaseChangeEquiv_permutation (R := R) (n := n) (lam := lam) S e x

/-- The same transported presentation sends each original coordinate to the
same quotient coordinate, for arbitrary coefficient rings and parameter families. -/
theorem elementaryParameterBaseChangeEquivOfEq_one_tmul_X
    {R : Type*} [CommRing R] (n : ℕ) (lam : YoungDiagram) (S : Type*) [CommRing S]
    [Algebra (ElementaryParameterRing R n lam) S]
    (a : Fin (n - lam.card) → S)
    (ha : (fun j : Fin (n - lam.card) =>
      algebraMap (ElementaryParameterRing R n lam) S (MvPolynomial.X j)) = a)
    (i : Fin n) :
    elementaryParameterBaseChangeEquivOfEq (R := R) n lam S a ha
        ((1 : S) ⊗ₜ[ElementaryParameterRing R n lam]
          Ideal.Quotient.mk (untruncatedIdeal R n lam) (MvPolynomial.X i)) =
      Ideal.Quotient.mk (parameterFiberIdeal S n lam (n - lam.card) a)
        (MvPolynomial.X i) := by
  subst a
  exact elementaryParameterBaseChangeEquiv_one_tmul_X (R := R) n lam S i

/-- Two presentations into the same algebra induce an intertwining comparison
whenever they each intertwine their source action with the same target action. -/
private theorem commonTargetAlgEquiv_intertwines
    {K : Type*} {A : Type*} {B : Type*} {C : Type*}
    [CommSemiring K] [Semiring A] [Semiring B] [Semiring C]
    [Algebra K A] [Algebra K B] [Algebra K C]
    (P : A ≃ₐ[K] C) (Q : B ≃ₐ[K] C)
    (u : A → A) (v : B → B) (w : C → C)
    (hP : ∀ x, P (u x) = w (P x)) (hQ : ∀ y, Q (v y) = w (Q y)) (x : A) :
    (P.trans Q.symm) (u x) = v ((P.trans Q.symm) x) := by
  apply Q.injective
  simpa only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply, hQ] using hP x

/-- The comparison of the integral and coefficient-extended sources
intertwines the two literal variable-renaming actions. -/
theorem orderedRootIntegralSourceBaseChangeEquiv_permutation
    (K : Type*) [CommRing K] (n : ℕ) (lam : YoungDiagram)
    (e : Equiv.Perm (Fin n)) :
    letI := orderedIntegralParameterAlgebra K n lam
    ∀ x : OrderedRootRing K (n - lam.card) ⊗[ElementaryParameterRing ℤ n lam]
        UntruncatedRing ℤ n lam,
      orderedRootIntegralSourceBaseChangeEquiv K n lam
          (elementaryParameterTensorPermutation (R := ℤ) (n := n) (lam := lam)
            (OrderedRootRing K (n - lam.card)) e x) =
        elementaryParameterTensorPermutation (R := K) (n := n) (lam := lam)
          (OrderedRootRing K (n - lam.card)) e
          (orderedRootIntegralSourceBaseChangeEquiv K n lam x) := by
  letI := orderedIntegralParameterAlgebra K n lam
  intro x
  exact (IntegralBaseChangeComparison.integralComparisonCertificate K n lam).covariance e x

/-- Proposition 7.2 after the literal base change of its integral source to
the ordered-root ring over any coefficient field. -/
def proposition_7_2_after_field_baseChange (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    letI := orderedIntegralParameterAlgebra K n lam
    OrderedRootRing K (n - lam.card) ⊗[ElementaryParameterRing ℤ n lam]
        UntruncatedRing ℤ n lam ≃ₐ[OrderedRootRing K (n - lam.card)]
      ∀ _e : Fin (n - lam.card) ↪ Fin n,
        OrderedRootRing K (n - lam.card) ⊗[K] SpringerRing K lam := by
  letI := orderedIntegralParameterAlgebra K n lam
  exact (orderedRootIntegralSourceBaseChangeEquiv K n lam).trans
    ((orderedRootTrivialization (R := K) n lam hk).trans
      (AlgEquiv.piCongrRight fun _ =>
        (springerCoefficientBaseChangeEquiv (R := K)
          (OrderedRootRing K (n - lam.card)) lam).symm))

/-- The actual coefficient-field version retains the independently defined
coordinate action and the complementary Springer action. -/
theorem proposition_7_2_after_field_baseChange_permutation
    (K : Type*) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (e : Equiv.Perm (Fin n))
    (f : DistinctRootAssignments n lam.card (n - lam.card)) :
    letI := orderedIntegralParameterAlgebra K n lam
    ∀ x : OrderedRootRing K (n - lam.card) ⊗[ElementaryParameterRing ℤ n lam]
        UntruncatedRing ℤ n lam,
      proposition_7_2_after_field_baseChange K n lam hk
          (elementaryParameterTensorPermutation (R := ℤ) (n := n) (lam := lam)
            (OrderedRootRing K (n - lam.card)) e x)
          (injectionCoordinatePermutation e
            (distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk) f)) =
        springerTensorPermutation (R := K) lam (distinctZeroFactorPermutation lam e f)
          (proposition_7_2_after_field_baseChange K n lam hk x
            (distinctRootAssignmentsEquivInjections (Nat.add_sub_of_le hk) f)) := by
  letI := orderedIntegralParameterAlgebra K n lam
  intro x
  simp only [proposition_7_2_after_field_baseChange, AlgEquiv.trans_apply,
    AlgEquiv.piCongrRight_apply]
  rw [orderedRootIntegralSourceBaseChangeEquiv_permutation,
    orderedRootTrivialization_permutation,
    springerCoefficientBaseChangeEquiv_symm_permutation]

def orderedIntegralFieldSourceRep (K : Type*) [CommRing K]
    (n : ℕ) (lam : YoungDiagram) :
    Rep (OrderedRootRing K (n - lam.card)) (Equiv.Perm (Fin n)) := by
  letI := orderedIntegralParameterAlgebra K n lam
  exact Rep.of (elementaryParameterTensorRepresentation (R := ℤ) (n := n) (lam := lam)
    (OrderedRootRing K (n - lam.card)))

def orderedRootIntegralSourceRepIso (K : Type*) [CommRing K]
    (n : ℕ) (lam : YoungDiagram) :
    orderedIntegralFieldSourceRep K n lam ≅ orderedRootSourceRep K n lam := by
  letI := orderedIntegralParameterAlgebra K n lam
  apply Rep.mkIso
  refine Representation.Equiv.mk
    (orderedRootIntegralSourceBaseChangeEquiv K n lam).toLinearEquiv ?_
  intro e
  apply LinearMap.ext
  intro x
  exact orderedRootIntegralSourceBaseChangeEquiv_permutation K n lam e x

/-- The induced-module clause after the same literal integral base change.
Its complementary action is the scalar extension of the actual Springer
action over the chosen coefficient field. -/
def proposition_7_2_after_field_baseChange_induced
    (K : Type*) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (f : RootInjection lam (n := n)) :
    orderedIntegralFieldSourceRep K n lam ≅
      Rep.ind (rootInjectionStabilizer lam f).subtype
        (orderedRootTensorComplementRep K lam hk f) :=
  (orderedRootIntegralSourceRepIso K n lam).trans
    (proposition_7_2_orderedRoot_induced_tensor (R := K) n lam hk f)

/-- The full-size Springer quotient carries the already defined elementary
parameter action on the identical untruncated quotient. -/
noncomputable instance springerFullSizeParameterAlgebra (R : Type*) [CommRing R]
    (lam : YoungDiagram) :
    Algebra (ElementaryParameterRing R lam.card lam) (SpringerRing R lam) :=
  inferInstanceAs
    (Algebra (ElementaryParameterRing R lam.card lam) (UntruncatedRing R lam.card lam))

noncomputable instance springerFullSizeParameterScalarTower (R : Type*) [CommRing R]
    (lam : YoungDiagram) :
    IsScalarTower R (ElementaryParameterRing R lam.card lam) (SpringerRing R lam) :=
  inferInstanceAs
    (IsScalarTower R (ElementaryParameterRing R lam.card lam) (UntruncatedRing R lam.card lam))

theorem parameterFiberIdeal_empty (S : Type*) [CommRing S]
    (n : ℕ) (lam : YoungDiagram) (a : Fin 0 → S) :
    parameterFiberIdeal S n lam 0 a = untruncatedIdeal S n lam := by
  simp only [parameterFiberIdeal, Set.range_eq_empty, Ideal.span_empty, sup_bot_eq]

/-- At full partition size there are no elementary parameters to impose.
The resulting map is the literal coordinate-identical quotient map. -/
def fullSizeParameterBaseChangeEquiv (lam : YoungDiagram)
    (S : Type*) [CommRing S]
    [Algebra (ElementaryParameterRing R lam.card lam) S] :
    S ⊗[ElementaryParameterRing R lam.card lam] SpringerRing R lam ≃ₐ[S]
      SpringerRing S lam := by
  have hI : parameterFiberIdeal S lam.card lam (lam.card - lam.card)
      (fun j => algebraMap (ElementaryParameterRing R lam.card lam) S
        (MvPolynomial.X j)) = untruncatedIdeal S lam.card lam := by
    letI : IsEmpty (Fin (lam.card - lam.card)) := by
      rw [Nat.sub_self]
      infer_instance
    simp only [parameterFiberIdeal, Set.range_eq_empty, Ideal.span_empty, sup_bot_eq]
  exact (elementaryParameterBaseChangeEquiv (R := R) lam.card lam S).trans
    (Ideal.quotientEquivAlgOfEq S hI)

@[simp] theorem fullSizeParameterBaseChangeEquiv_one_tmul_X
    (lam : YoungDiagram) (S : Type*) [CommRing S]
    [Algebra (ElementaryParameterRing R lam.card lam) S] (i : Fin lam.card) :
    fullSizeParameterBaseChangeEquiv (R := R) lam S
        ((1 : S) ⊗ₜ[ElementaryParameterRing R lam.card lam]
          Ideal.Quotient.mk (untruncatedIdeal R lam.card lam) (MvPolynomial.X i)) =
      Ideal.Quotient.mk (untruncatedIdeal S lam.card lam) (MvPolynomial.X i) := by
  have hI : parameterFiberIdeal S lam.card lam (lam.card - lam.card)
      (fun j => algebraMap (ElementaryParameterRing R lam.card lam) S
        (MvPolynomial.X j)) = untruncatedIdeal S lam.card lam := by
    letI : IsEmpty (Fin (lam.card - lam.card)) := by
      rw [Nat.sub_self]
      infer_instance
    simp only [parameterFiberIdeal, Set.range_eq_empty, Ideal.span_empty, sup_bot_eq]
  have hEval : elementaryParameterBaseChangeEquiv (R := R) lam.card lam S
      ((1 : S) ⊗ₜ[ElementaryParameterRing R lam.card lam]
        Ideal.Quotient.mk (untruncatedIdeal R lam.card lam) (MvPolynomial.X i)) =
      Ideal.Quotient.mk (parameterFiberIdeal S lam.card lam (lam.card - lam.card)
        (fun j => algebraMap (ElementaryParameterRing R lam.card lam) S
          (MvPolynomial.X j))) (MvPolynomial.X i) :=
    elementaryParameterBaseChangeEquiv_one_tmul_X (R := R) lam.card lam S i
  exact (congrArg (fun z : ParameterFiber S lam.card lam (lam.card - lam.card)
      (fun j => algebraMap (ElementaryParameterRing R lam.card lam) S (MvPolynomial.X j)) =>
        Ideal.quotientEquivAlgOfEq S hI z) hEval).trans
    (Ideal.quotientEquivAlgOfEq_mk S hI (MvPolynomial.X i))

def orderedRootFullSizeCoefficientEquiv (R : Type*) [CommRing R]
    (lam : YoungDiagram) :
    OrderedRootRing R (lam.card - lam.card) ≃ₐ[R] R := by
  have hzero : ∀ m : ℕ, m = 0 → OrderedRootRing R m ≃ₐ[R] R := by
    intro m hm
    subst m
    exact orderedRootRingZeroEquiv R
  exact hzero (lam.card - lam.card) (Nat.sub_self _)

/-- Proposition 7.2 for `m = 0`, after the canonical coefficient
identification.  This construction uses no enumeration of a complementary
coordinate set, and the next two lemmas verify the asserted identity on
the original Springer ring itself. -/
def proposition_7_2_no_parameters (R : Type*) [CommRing R]
    (lam : YoungDiagram) :
    OrderedRootRing R (lam.card - lam.card) ⊗[ElementaryParameterRing R lam.card lam]
        SpringerRing R lam ≃ₐ[R] SpringerRing R lam :=
  ((fullSizeParameterBaseChangeEquiv (R := R) lam
      (OrderedRootRing R (lam.card - lam.card))).restrictScalars R).trans
    (((springerCoefficientBaseChangeEquiv (R := R)
        (OrderedRootRing R (lam.card - lam.card)) lam).symm.restrictScalars R).trans
      ((Algebra.TensorProduct.congr (orderedRootFullSizeCoefficientEquiv R lam)
        (AlgEquiv.refl : SpringerRing R lam ≃ₐ[R] SpringerRing R lam)).trans
          (Algebra.TensorProduct.lid R (SpringerRing R lam))))

/-- Evaluate four composable algebra equivalences before specializing their
algebra structures. This fixes the exact association of the original composite. -/
private theorem algEquiv_fourfold_apply
    {K : Type*} [CommSemiring K]
    {A : Type*} {B : Type*} {C : Type*} {D : Type*} {E : Type*}
    [Semiring A] [Semiring B] [Semiring C] [Semiring D] [Semiring E]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra K D] [Algebra K E]
    (F₁ : A ≃ₐ[K] B) (F₂ : B ≃ₐ[K] C)
    (F₃ : C ≃ₐ[K] D) (F₄ : D ≃ₐ[K] E) (x : A) :
    (F₁.trans (F₂.trans (F₃.trans F₄))) x = F₄ (F₃ (F₂ (F₁ x))) := rfl

/-- The inverse coefficient-extension formula is established over an
abstract coefficient algebra, before a localization is substituted. -/
private theorem springerCoefficientBaseChangeEquiv_symm_mk_X
    (S : Type*) [CommRing S] [Algebra R S]
    (lam : YoungDiagram) (i : Fin lam.card) :
    (springerCoefficientBaseChangeEquiv (R := R) S lam).symm
        (Ideal.Quotient.mk (untruncatedIdeal S lam.card lam) (MvPolynomial.X i)) =
      (1 : S) ⊗ₜ[R]
        Ideal.Quotient.mk (untruncatedIdeal R lam.card lam) (MvPolynomial.X i) := by
  apply (springerCoefficientBaseChangeEquiv (R := R) S lam).symm_apply_eq.mpr
  have hp : (1 : S) • MvPolynomial.map (algebraMap R S)
      (MvPolynomial.X i : PolynomialRing lam.card R) =
        (MvPolynomial.X i : PolynomialRing lam.card S) := by
    simp only [MvPolynomial.map_X, one_smul]
  exact (congrArg (Ideal.Quotient.mk (springerIdeal S lam)) hp).symm.trans
    (springerCoefficientBaseChangeEquiv_tmul (R := R) S lam (1 : S)
      (MvPolynomial.X i)).symm

@[simp] theorem proposition_7_2_no_parameters_coordinate
    (R : Type*) [CommRing R] (lam : YoungDiagram) (i : Fin lam.card) :
    proposition_7_2_no_parameters R lam
        ((1 : OrderedRootRing R (lam.card - lam.card))
          ⊗ₜ[ElementaryParameterRing R lam.card lam]
          Ideal.Quotient.mk (untruncatedIdeal R lam.card lam) (MvPolynomial.X i)) =
      Ideal.Quotient.mk (untruncatedIdeal R lam.card lam) (MvPolynomial.X i) := by
  let S := OrderedRootRing R (lam.card - lam.card)
  let v : SpringerRing R lam :=
    Ideal.Quotient.mk (untruncatedIdeal R lam.card lam) (MvPolynomial.X i)
  let w : SpringerRing S lam :=
    Ideal.Quotient.mk (untruncatedIdeal S lam.card lam) (MvPolynomial.X i)
  have hF : (fullSizeParameterBaseChangeEquiv (R := R) lam S).restrictScalars R
      ((1 : S) ⊗ₜ[ElementaryParameterRing R lam.card lam] v) = w :=
    (AlgEquiv.restrictScalars_apply R
      (fullSizeParameterBaseChangeEquiv (R := R) lam S)
      ((1 : S) ⊗ₜ[ElementaryParameterRing R lam.card lam] v)).trans
        (fullSizeParameterBaseChangeEquiv_one_tmul_X (R := R) lam S i)
  have hE : ((springerCoefficientBaseChangeEquiv (R := R) S lam).symm.restrictScalars R)
      w = (1 : S) ⊗ₜ[R] v :=
    (AlgEquiv.restrictScalars_apply R
      (springerCoefficientBaseChangeEquiv (R := R) S lam).symm w).trans
        (springerCoefficientBaseChangeEquiv_symm_mk_X (R := R) S lam i)
  rw [proposition_7_2_no_parameters, AlgEquiv.trans_apply,
    AlgEquiv.trans_apply, AlgEquiv.trans_apply, hF, hE]
  simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    map_one, AlgEquiv.coe_refl, id_eq, Algebra.TensorProduct.lid_tmul, one_smul]
  rfl

/-- The zero-parameter specialization is the identity on every actual
Springer class, not just an abstract isomorphism between rings of the same
dimension. -/
theorem proposition_7_2_no_parameters_identity
    (R : Type*) [CommRing R] (lam : YoungDiagram) (x : SpringerRing R lam) :
    proposition_7_2_no_parameters R lam
      ((1 : OrderedRootRing R (lam.card - lam.card))
        ⊗ₜ[ElementaryParameterRing R lam.card lam] x) = x := by
  let J : SpringerRing R lam →ₐ[R]
      OrderedRootRing R (lam.card - lam.card) ⊗[ElementaryParameterRing R lam.card lam]
        SpringerRing R lam :=
    (Algebra.TensorProduct.includeRight : SpringerRing R lam →ₐ[
      ElementaryParameterRing R lam.card lam]
      OrderedRootRing R (lam.card - lam.card) ⊗[ElementaryParameterRing R lam.card lam]
        SpringerRing R lam).restrictScalars R
  have h : (proposition_7_2_no_parameters R lam).toAlgHom.comp J =
      AlgHom.id R (SpringerRing R lam) := by
    apply Ideal.Quotient.algHom_ext R
    apply MvPolynomial.algHom_ext
    intro i
    change proposition_7_2_no_parameters R lam
        ((1 : OrderedRootRing R (lam.card - lam.card))
          ⊗ₜ[ElementaryParameterRing R lam.card lam]
          Ideal.Quotient.mk (untruncatedIdeal R lam.card lam) (MvPolynomial.X i)) =
      Ideal.Quotient.mk (untruncatedIdeal R lam.card lam) (MvPolynomial.X i)
    exact proposition_7_2_no_parameters_coordinate R lam i
  exact AlgHom.congr_fun h x

end HigherSpecht
end
end CanonicalSource84

section CanonicalSource85
/- Source: HigherSpecht/OrderedRootCoordinates.lean -/



/-!
# The assigned coordinates in the final ordered-root trivialization

The component maps below are the existing CRT, translation and tensor maps.
The singleton root group supplies the literal relation `X_j - c = 0` in its
actual component ideal.  Transporting that relation through the constructed
algebra equivalences proves the coordinate clause of Proposition 7.2 for the
final integral map, and again after every coefficient-field base change.
No new map, action, presentation or coordinate-value premise is introduced.
-/

noncomputable section

open TauCeti MvPolynomial Finset
open scoped Classical Polynomial TensorProduct BigOperators

namespace HigherSpecht.OrderedParameterCoordinates

variable {R : Type*} [CommRing R]

/-- The actual equality-transported parameter presentation, together with its
whole-map identity and the images of all original coordinate classes. -/
structure ParameterCoordinateCertificate
    (n : ℕ) (lam : YoungDiagram) (S : Type*) [CommRing S]
    [Algebra (ElementaryParameterRing R n lam) S]
    (a : Fin (n - lam.card) → S)
    (ha : (fun i : Fin (n - lam.card) =>
      algebraMap (ElementaryParameterRing R n lam) S (MvPolynomial.X i)) = a) where
  equiv : S ⊗[ElementaryParameterRing R n lam] UntruncatedRing R n lam ≃ₐ[S]
    ParameterFiber S n lam (n - lam.card) a
  eq_original : equiv = elementaryParameterBaseChangeEquivOfEq (R := R) n lam S a ha
  coordinate : ∀ i : Fin n,
    equiv ((1 : S) ⊗ₜ[ElementaryParameterRing R n lam]
      Ideal.Quotient.mk (untruncatedIdeal R n lam) (MvPolynomial.X i)) =
      Ideal.Quotient.mk (parameterFiberIdeal S n lam (n - lam.card) a) (MvPolynomial.X i)

/-- A fully specified safe constructor. The coordinate proof is supplied
while the scalar ring and its algebra structures remain abstract. -/
opaque certifiedParameter
    (n : ℕ) (lam : YoungDiagram) (S : Type*) [CommRing S]
    [Algebra (ElementaryParameterRing R n lam) S]
    (a : Fin (n - lam.card) → S)
    (ha : (fun i : Fin (n - lam.card) =>
      algebraMap (ElementaryParameterRing R n lam) S (MvPolynomial.X i)) = a) :
    ParameterCoordinateCertificate (R := R) n lam S a ha :=
  { equiv := elementaryParameterBaseChangeEquivOfEq (R := R) n lam S a ha
    eq_original := rfl
    coordinate := fun i =>
      elementaryParameterBaseChangeEquivOfEq_one_tmul_X (R := R) n lam S a ha i }


end HigherSpecht.OrderedParameterCoordinates

namespace HigherSpecht.IntegralBaseChangeCoordinates

/-- If two presentations send two elements to the same element, their
comparison identifies those elements. All equality transports occur here
before specializing the scalar ring or any of the presentations. -/
private theorem comparison_coordinate
    {K : Type*} [CommSemiring K]
    {A : Type*} {B : Type*} {C : Type*}
    [Semiring A] [Semiring B] [Semiring C]
    [Algebra K A] [Algebra K B] [Algebra K C]
    (E : A ≃ₐ[K] B) (P₀ : A ≃ₐ[K] C) (Q₀ : B ≃ₐ[K] C)
    (P : A ≃ₐ[K] C) (Q : B ≃ₐ[K] C)
    (hE : E = P₀.trans Q₀.symm) (hP : P = P₀) (hQ : Q = Q₀)
    (x : A) (y : B) (z : C) (hx : P x = z) (hy : Q y = z) : E x = y := by
  cases hP
  cases hQ
  rw [hE, AlgEquiv.trans_apply, hx, ← hy, AlgEquiv.symm_apply_apply]

/-- This is the unchanged coordinate assertion for the actual integral
comparison already defined in `higher_specht`, not a new comparison map. -/
@[simp] theorem orderedRootIntegralSourceBaseChangeEquiv_one_tmul_X
    (K : Type*) [CommRing K] (n : ℕ) (lam : YoungDiagram) (i : Fin n) :
    letI := orderedIntegralParameterAlgebra K n lam
    orderedRootIntegralSourceBaseChangeEquiv K n lam
        ((1 : OrderedRootRing K (n - lam.card)) ⊗ₜ[ElementaryParameterRing ℤ n lam]
          Ideal.Quotient.mk (untruncatedIdeal ℤ n lam) (MvPolynomial.X i)) =
      (1 : OrderedRootRing K (n - lam.card)) ⊗ₜ[ElementaryParameterRing K n lam]
        Ideal.Quotient.mk (untruncatedIdeal K n lam) (MvPolynomial.X i) := by
  let S := OrderedRootRing K (n - lam.card)
  letI := orderedIntegralParameterAlgebra K n lam
  let a : Fin (n - lam.card) → S := orderedRootElementaryParameters (R := K) _
  have hz : (fun j : Fin (n - lam.card) =>
      algebraMap (ElementaryParameterRing ℤ n lam) S (MvPolynomial.X j)) = a := by
    funext j
    exact orderedIntegralParameter_algebraMap_X K n lam j
  have hk : (fun j : Fin (n - lam.card) =>
      algebraMap (ElementaryParameterRing K n lam) S (MvPolynomial.X j)) = a := by
    funext j
    exact orderedRootParameter_algebraMap_X n lam j
  let CP := OrderedParameterCoordinates.certifiedParameter (R := ℤ) n lam S a hz
  let CQ := OrderedParameterCoordinates.certifiedParameter (R := K) n lam S a hk
  have hP : CP.equiv = orderedRootIntegralParameterPresentation K n lam :=
    CP.eq_original
  have hQ : CQ.equiv = orderedRootParameterPresentation (R := K) n lam :=
    CQ.eq_original
  exact comparison_coordinate (K := S)
    (A := S ⊗[ElementaryParameterRing ℤ n lam] UntruncatedRing ℤ n lam)
    (B := S ⊗[ElementaryParameterRing K n lam] UntruncatedRing K n lam)
    (C := ParameterFiber S n lam (n - lam.card) a)
    (orderedRootIntegralSourceBaseChangeEquiv K n lam)
    (orderedRootIntegralParameterPresentation K n lam)
    (orderedRootParameterPresentation (R := K) n lam)
    CP.equiv CQ.equiv
    (IntegralBaseChangeComparison.integralComparisonCertificate K n lam).eq_original
    hP hQ
    ((1 : S) ⊗ₜ[ElementaryParameterRing ℤ n lam]
      Ideal.Quotient.mk (untruncatedIdeal ℤ n lam) (MvPolynomial.X i))
    ((1 : S) ⊗ₜ[ElementaryParameterRing K n lam]
      Ideal.Quotient.mk (untruncatedIdeal K n lam) (MvPolynomial.X i))
    (Ideal.Quotient.mk (parameterFiberIdeal S n lam (n - lam.card) a) (MvPolynomial.X i))
    (CP.coordinate i) (CQ.coordinate i)


end HigherSpecht.IntegralBaseChangeCoordinates

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n m k : ℕ}

theorem shiftedElementaryOn_singleton_one (j : Fin n) (c : R) :
    shiftedElementaryOn ({j} : Finset (Fin n)) c 1 =
      MvPolynomial.X j - MvPolynomial.C c := by
  simp [shiftedElementaryOn, elementaryValue, Finset.powersetCard_one]

/-- A singleton assigned group forces its coordinate to be its actual root
already in the displayed component quotient. -/
theorem splitRootBlock_mk_X_eq_root_of_singleton
    {ι : Type*} [Fintype ι]
    (lam : YoungDiagram) (r0 : ℕ) (c : ι → R) (f : Fin n → ι)
    (z i : ι) (j : Fin n) (hgroup : rootGroupFinset f i = {j}) :
    Ideal.Quotient.mk (splitRootBlockIdeal R lam r0 c f z) (MvPolynomial.X j) =
      algebraMap R (PolynomialRing n R ⧸ splitRootBlockIdeal R lam r0 c f z) (c i) := by
  have hle : shiftedGlobalIdeal R (rootGroupFinset f i) (c i) ≤
      splitRootBlockIdeal R lam r0 c f z :=
    le_trans (le_iSup (fun k => shiftedGlobalIdeal R (rootGroupFinset f k) (c k)) i)
      le_sup_right
  have hgen : shiftedElementaryOn (rootGroupFinset f i) (c i) (0 + 1) ∈
      splitRootBlockIdeal R lam r0 c f z :=
    hle (Ideal.subset_span ⟨0, rfl⟩)
  have hrel : MvPolynomial.X j - MvPolynomial.C (c i) ∈
      splitRootBlockIdeal R lam r0 c f z := by
    simpa only [hgroup, zero_add, shiftedElementaryOn_singleton_one] using hgen
  change Ideal.Quotient.mk _ (MvPolynomial.X j) =
    Ideal.Quotient.mk _ (MvPolynomial.C (c i))
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hrel

theorem rootGroupFinset_distinctAssignedPoint
    (f : DistinctRootAssignments n k m) (i : Fin m) :
    rootGroupFinset f.val (some i) = {injectionOfDistinctAssignment f i} := by
  ext j
  rw [mem_rootGroupFinset, Finset.mem_singleton]
  constructor
  · exact distinctAssignedPoint_unique f i j
  · intro hj
    rw [hj]
    exact (distinctAssignedPoint f i).property

namespace CoordinateEvaluation

/-- A component formula proved while every input algebra map is abstract. -/
theorem trans_pi_apply_raw
    {S : Type*} [CommSemiring S] {A D I : Type*} {B : I → Type*}
    [Semiring A] [Semiring D] [∀ i, Semiring (B i)]
    [Algebra S A] [Algebra S D] [∀ i, Algebra S (B i)]
    (E : A ≃ₐ[S] ∀ i, B i) (F : ∀ i, B i ≃ₐ[S] D) (x : A) (i : I) :
    (E.trans (AlgEquiv.piCongrRight F)).toEquiv.toFun x i =
      (F i).toEquiv.toFun (E.toEquiv.toFun x i) := rfl

theorem raw_pi_apply_of_coe
    {S : Type*} [CommSemiring S] {A I : Type*} {B : I → Type*}
    [Semiring A] [∀ i, Semiring (B i)]
    [Algebra S A] [∀ i, Algebra S (B i)]
    (E : A ≃ₐ[S] ∀ i, B i) (x : A) (i : I) (y : B i)
    (h : E x i = y) : E.toEquiv.toFun x i = y := h

theorem raw_commutes
    {S : Type*} [CommSemiring S] {A B : Type*}
    [Semiring A] [Semiring B] [Algebra S A] [Algebra S B]
    (E : A ≃ₐ[S] B) (s : S) :
    E.toEquiv.toFun (algebraMap S A s) = algebraMap S B s := E.commutes s

theorem collapse_coe_of_raw
    {S : Type*} [CommSemiring S] {A B C I : Type*}
    [Semiring A] [Semiring B] [Semiring C]
    [Algebra S A] [Algebra S B] [Algebra S C]
    (F : A ≃ₐ[S] (I → B)) (D : B ≃ₐ[S] C) (x : A) (i : I) (y : C)
    (h : D.toEquiv.toFun (F.toEquiv.toFun x i) = y) : D (F x i) = y := h

end CoordinateEvaluation

/-- The actual collapsed split-fiber map has the required root value on
each coordinate of a multiplicity-one nonzero-root group. -/
theorem distinctRootCollapsedFiber_mk_assigned_coordinate [Nontrivial R]
    {lam : YoungDiagram} (hsize : lam.card + m = n)
    (Q : R[X]) (hQ : Q.Monic) (hdeg : Q.natDegree = m)
    (c : Fin m → R) (hc : ∀ i, IsUnit (c i))
    (hcc : Pairwise fun i j => IsUnit (c i - c j))
    (hfactor : Polynomial.X ^ lam.card * Q =
      ∏ i : Option (Fin m),
        (Polynomial.X - Polynomial.C (splitRootValue c i)) ^
          splitRootMultiplicities lam 0 (fun _ => 1) i)
    (f : DistinctRootAssignments n lam.card m) (j : Fin m) :
    distinctRootTensorEquiv (R := R) (ι := Fin m) lam
        (polynomialFiberSpringerTensorProductEquiv hsize Q hQ hdeg 0
          (splitRootValue c) (splitRootValue_unitDifferences c hc hcc)
          none (splitRootMultiplicities lam 0 (fun _ => 1)) rfl rfl hfactor
          (Ideal.Quotient.mk (polynomialFiberIdeal R n lam m Q)
            (MvPolynomial.X (injectionOfDistinctAssignment f j))) f) =
      algebraMap R (SpringerRing R lam) (c j) := by
  have hcoord :
      Ideal.Quotient.mk
          (splitRootBlockIdeal R lam 0 (splitRootValue c) f.val none)
          (MvPolynomial.X (injectionOfDistinctAssignment f j)) =
        algebraMap R
          (PolynomialRing n R ⧸ splitRootBlockIdeal R lam 0 (splitRootValue c) f.val none)
          (c j) := by
    simpa only [splitRootValue, Option.elim_some] using
      splitRootBlock_mk_X_eq_root_of_singleton lam 0 (splitRootValue c)
        f.val none (some j) (injectionOfDistinctAssignment f j)
        (rootGroupFinset_distinctAssignedPoint f j)
  let E := polynomialFiberBlockProductEquivUnits hsize Q hQ hdeg 0
    (splitRootValue c) (splitRootValue_unitDifferences c hc hcc)
    none (splitRootMultiplicities lam 0 (fun _ => 1)) rfl rfl hfactor
  let B := fun g : DistinctRootAssignments n lam.card m =>
    rootBlockTensorQuotientEquiv lam 0 (splitRootMultiplicities lam 0 (fun _ => 1))
      (splitRootValue c) g.val none rfl rfl g.property
  let D := distinctRootTensorEquiv (R := R) (ι := Fin m) lam
  let F := polynomialFiberSpringerTensorProductEquiv hsize Q hQ hdeg 0
    (splitRootValue c) (splitRootValue_unitDifferences c hc hcc)
    none (splitRootMultiplicities lam 0 (fun _ => 1)) rfl rfl hfactor
  let p : PolynomialRing n R := MvPolynomial.X (injectionOfDistinctAssignment f j)
  let x : PolynomialFiber R n lam m Q :=
    Ideal.Quotient.mk (polynomialFiberIdeal R n lam m Q) p
  have hE : E.toEquiv.toFun x f =
      Ideal.Quotient.mk (splitRootBlockIdeal R lam 0 (splitRootValue c) f.val none) p :=
    CoordinateEvaluation.raw_pi_apply_of_coe E x f _
      (polynomialFiberBlockProductEquivUnits_mk hsize Q hQ hdeg 0
        (splitRootValue c) (splitRootValue_unitDifferences c hc hcc)
        none (splitRootMultiplicities lam 0 (fun _ => 1)) rfl rfl hfactor p f)
  have hF : F.toEquiv.toFun x f = (B f).toEquiv.toFun (E.toEquiv.toFun x f) :=
    CoordinateEvaluation.trans_pi_apply_raw E B x f
  have hB : (B f).toEquiv.toFun (E.toEquiv.toFun x f) =
      algebraMap R _ (c j) :=
    (congrArg (B f).toEquiv.toFun (hE.trans hcoord)).trans
      (CoordinateEvaluation.raw_commutes (B f) (c j))
  have hraw : D.toEquiv.toFun (F.toEquiv.toFun x f) =
      algebraMap R (SpringerRing R lam) (c j) :=
    (congrArg D.toEquiv.toFun (hF.trans hB)).trans
      (CoordinateEvaluation.raw_commutes D (c j))
  exact CoordinateEvaluation.collapse_coe_of_raw F D x f _ hraw


/-- Evaluate the unchanged componentwise composite using a presentation
proved equal to its original parameter map. The entire equivalence equality
is used before specializing any coefficient algebra. -/
theorem componentwise_coordinate
    {K : Type*} [CommSemiring K]
    {A B C V I J D : Type*}
    [Semiring A] [Semiring B] [Semiring C] [Semiring V] [Semiring D]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra K V] [Algebra K D]
    (T : A ≃ₐ[K] (J → V)) (P₀ P : A ≃ₐ[K] B)
    (Q : B ≃ₐ[K] C) (F : C ≃ₐ[K] (I → D)) (G : D ≃ₐ[K] V) (h : I ≃ J)
    (hT : T = componentwiseComposite P₀ Q F G h) (hP : P = P₀)
    (x : A) (b : B) (c : C) (i : I) (v : V)
    (hx : P x = b) (hb : Q b = c) (hc : G (F c i) = v) : T x (h i) = v := by
  cases hP
  rw [hT, componentwiseComposite_apply, h.symm_apply_apply, hx, hb, hc]

/-- The original coordinate assigned by the injection equals the named
ordered root under the final, previously constructed algebra map. -/
theorem orderedRootTrivialization_assigned_coordinate [IsDomain R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (e : Fin (n - lam.card) ↪ Fin n) (j : Fin (n - lam.card)) :
    orderedRootTrivialization (R := R) n lam hk
        ((1 : OrderedRootRing R (n - lam.card)) ⊗ₜ[ElementaryParameterRing R n lam]
          Ideal.Quotient.mk (untruncatedIdeal R n lam) (MvPolynomial.X (e j))) e =
      algebraMap (OrderedRootRing R (n - lam.card))
        (SpringerRing (OrderedRootRing R (n - lam.card)) lam)
        (orderedRoot (R := R) (n - lam.card) j) := by
  let S := OrderedRootRing R (n - lam.card)
  let c : Fin (n - lam.card) → S := orderedRoot (n - lam.card)
  let a : Fin (n - lam.card) → S := orderedRootElementaryParameters (n - lam.card)
  have hsize : lam.card + (n - lam.card) = n := Nat.add_sub_of_le hk
  have hfamily : (fun i : Fin (n - lam.card) =>
      algebraMap (ElementaryParameterRing R n lam) S (MvPolynomial.X i)) = a := by
    funext i
    exact orderedRootParameter_algebraMap_X n lam i
  let CP := OrderedParameterCoordinates.certifiedParameter (R := R) n lam S a hfamily
  let P : S ⊗[ElementaryParameterRing R n lam] UntruncatedRing R n lam ≃ₐ[S]
      ParameterFiber S n lam (n - lam.card) a := CP.equiv
  have hPfull : P = orderedRootParameterPresentation (R := R) n lam := CP.eq_original
  let Q : ParameterFiber S n lam (n - lam.card) a ≃ₐ[S]
      PolynomialFiber S n lam (n - lam.card) (parameterPolynomial a) :=
    orderedRootPolynomialPresentation (R := R) n lam
  let F := orderedRootSplitPresentation (R := R) n lam hk
  let J := orderedRootAssignmentEquiv n lam hk
  let D := distinctRootTensorEquiv (R := S) (ι := Fin (n - lam.card)) lam
  obtain ⟨f, rfl⟩ := J.surjective e
  let x : S ⊗[ElementaryParameterRing R n lam] UntruncatedRing R n lam :=
    (1 : S) ⊗ₜ[ElementaryParameterRing R n lam]
      Ideal.Quotient.mk (untruncatedIdeal R n lam) (MvPolynomial.X (J f j))
  let p : PolynomialRing n S := MvPolynomial.X (J f j)
  let q : ParameterFiber S n lam (n - lam.card) a :=
    Ideal.Quotient.mk (parameterFiberIdeal S n lam (n - lam.card) a) p
  have hP : P x = q := CP.coordinate (J f j)
  have hQ : Q q =
      Ideal.Quotient.mk (polynomialFiberIdeal S n lam (n - lam.card)
        (parameterPolynomial a)) p :=
    Ideal.quotientEquivAlgOfEq_mk S
      (polynomialFiberIdeal_parameterPolynomial lam a).symm p
  have hfactor : Polynomial.X ^ lam.card * parameterPolynomial a =
      ∏ i : Option (Fin (n - lam.card)),
        (Polynomial.X - Polynomial.C (splitRootValue c i)) ^
          splitRootMultiplicities lam 0 (fun _ => 1) i := by
    rw [orderedRootParameter_factorization]
    exact splitRootParameter_factorization lam 0 c (fun _ => 1)
  have hF : D (F
      (Ideal.Quotient.mk (polynomialFiberIdeal S n lam (n - lam.card)
        (parameterPolynomial a)) p) f) =
      algebraMap S (SpringerRing S lam) (c j) := by
    exact distinctRootCollapsedFiber_mk_assigned_coordinate hsize
      (parameterPolynomial a) (parameterPolynomial_monic a) (parameterPolynomial_natDegree a)
      c (orderedRoot_isUnit (n - lam.card)) (orderedRoot_pairwise_units (n - lam.card))
      hfactor f j
  exact componentwise_coordinate
    (orderedRootTrivialization (R := R) n lam hk)
    (orderedRootParameterPresentation (R := R) n lam) P Q F D J
    (orderedRootTrivialization_eq_componentwise (R := R) n lam hk)
    hPfull x q
    (Ideal.Quotient.mk (polynomialFiberIdeal S n lam (n - lam.card)
      (parameterPolynomial a)) p) f
    (algebraMap S (SpringerRing S lam) (c j)) hP hQ hF

/-- The explicit coordinate clause of Proposition 7.2, for its literal
integral scalar-extension target. -/
theorem proposition_7_2_integral_trivialization_coordinate
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (e : Fin (n - lam.card) ↪ Fin n) (j : Fin (n - lam.card)) :
    proposition_7_2_integral_trivialization n lam hk
        ((1 : OrderedRootRing ℤ (n - lam.card)) ⊗ₜ[ElementaryParameterRing ℤ n lam]
          Ideal.Quotient.mk (untruncatedIdeal ℤ n lam) (MvPolynomial.X (e j))) e =
      @algebraMap (OrderedRootRing ℤ (n - lam.card))
        (OrderedRootRing ℤ (n - lam.card) ⊗[ℤ] SpringerRing ℤ lam)
        (inferInstance : CommSemiring (OrderedRootRing ℤ (n - lam.card)))
        (inferInstance : Semiring
          (OrderedRootRing ℤ (n - lam.card) ⊗[ℤ] SpringerRing ℤ lam))
        (inferInstance : Algebra (OrderedRootRing ℤ (n - lam.card))
          (OrderedRootRing ℤ (n - lam.card) ⊗[ℤ] SpringerRing ℤ lam))
        (orderedRoot (R := ℤ) (n - lam.card) j) := by
  change (springerCoefficientBaseChangeEquiv (R := ℤ)
      (OrderedRootRing ℤ (n - lam.card)) lam).symm
      (orderedRootTrivialization (R := ℤ) n lam hk
        ((1 : OrderedRootRing ℤ (n - lam.card)) ⊗ₜ[ElementaryParameterRing ℤ n lam]
          Ideal.Quotient.mk (untruncatedIdeal ℤ n lam) (MvPolynomial.X (e j))) e) = _
  rw [orderedRootTrivialization_assigned_coordinate]
  exact (springerCoefficientBaseChangeEquiv (R := ℤ)
    (OrderedRootRing ℤ (n - lam.card)) lam).symm.commutes
      (orderedRoot (R := ℤ) (n - lam.card) j)

@[simp] theorem orderedRootIntegralSourceBaseChangeEquiv_one_tmul_X
    (K : Type*) [CommRing K] (n : ℕ) (lam : YoungDiagram) (i : Fin n) :
    letI := orderedIntegralParameterAlgebra K n lam
    orderedRootIntegralSourceBaseChangeEquiv K n lam
        ((1 : OrderedRootRing K (n - lam.card)) ⊗ₜ[ElementaryParameterRing ℤ n lam]
          Ideal.Quotient.mk (untruncatedIdeal ℤ n lam) (MvPolynomial.X i)) =
      (1 : OrderedRootRing K (n - lam.card)) ⊗ₜ[ElementaryParameterRing K n lam]
        Ideal.Quotient.mk (untruncatedIdeal K n lam) (MvPolynomial.X i) := by
  exact IntegralBaseChangeCoordinates.orderedRootIntegralSourceBaseChangeEquiv_one_tmul_X
    K n lam i

/-- The same explicit assigned-root clause after every coefficient-field
base change of the integral source. -/
theorem proposition_7_2_after_field_baseChange_coordinate
    (K : Type*) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (e : Fin (n - lam.card) ↪ Fin n) (j : Fin (n - lam.card)) :
    letI := orderedIntegralParameterAlgebra K n lam
    proposition_7_2_after_field_baseChange K n lam hk
        ((1 : OrderedRootRing K (n - lam.card)) ⊗ₜ[ElementaryParameterRing ℤ n lam]
          Ideal.Quotient.mk (untruncatedIdeal ℤ n lam) (MvPolynomial.X (e j))) e =
      @algebraMap (OrderedRootRing K (n - lam.card))
        (OrderedRootRing K (n - lam.card) ⊗[K] SpringerRing K lam)
        (inferInstance : CommSemiring (OrderedRootRing K (n - lam.card)))
        (inferInstance : Semiring
          (OrderedRootRing K (n - lam.card) ⊗[K] SpringerRing K lam))
        (inferInstance : Algebra (OrderedRootRing K (n - lam.card))
          (OrderedRootRing K (n - lam.card) ⊗[K] SpringerRing K lam))
        (orderedRoot (R := K) (n - lam.card) j) := by
  letI := orderedIntegralParameterAlgebra K n lam
  change (springerCoefficientBaseChangeEquiv (R := K)
      (OrderedRootRing K (n - lam.card)) lam).symm
      (orderedRootTrivialization (R := K) n lam hk
        (orderedRootIntegralSourceBaseChangeEquiv K n lam
          ((1 : OrderedRootRing K (n - lam.card)) ⊗ₜ[ElementaryParameterRing ℤ n lam]
            Ideal.Quotient.mk (untruncatedIdeal ℤ n lam) (MvPolynomial.X (e j)))) e) = _
  rw [orderedRootIntegralSourceBaseChangeEquiv_one_tmul_X,
    orderedRootTrivialization_assigned_coordinate]
  exact (springerCoefficientBaseChangeEquiv (R := K)
    (OrderedRootRing K (n - lam.card)) lam).symm.commutes
      (orderedRoot (R := K) (n - lam.card) j)

end HigherSpecht
end
end CanonicalSource85

section CanonicalSource86
/- Source: HigherSpecht/OrderedRootZeroNaturality.lean -/



/-!
# Equivariance of the canonical zero-parameter identification

The zero-parameter map is the identity on the original Springer classes.
Its injectivity therefore identifies every source tensor with an included
Springer class. This proves that the same map intertwines the coordinate
permutations directly, without a complementary-coordinate enumeration.

The coefficient ring is any commutative ring, including the zero ring;
the empty diagram is retained.
-/

noncomputable section

open TauCeti
open scoped Classical TensorProduct

namespace HigherSpecht

variable {R : Type*} [CommRing R]

/-- At full partition size both actions are the literal renaming action on
the same quotient, with different displayed scalar rings. -/
theorem untruncatedParameterPermutation_fullSize
    (lam : YoungDiagram) (g : Equiv.Perm (Fin lam.card))
    (x : SpringerRing R lam) :
    untruncatedParameterPermutation lam g x = springerPermutationAlgEquiv lam g x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The inverse of the canonical zero-parameter map is the actual inclusion
of the original Springer algebra. -/
theorem proposition_7_2_no_parameters_includeRight
    (R : Type*) [CommRing R] (lam : YoungDiagram)
    (x : OrderedRootRing R (lam.card - lam.card)
      ⊗[ElementaryParameterRing R lam.card lam] SpringerRing R lam) :
    (1 : OrderedRootRing R (lam.card - lam.card))
        ⊗ₜ[ElementaryParameterRing R lam.card lam]
        proposition_7_2_no_parameters R lam x = x := by
  apply (proposition_7_2_no_parameters R lam).injective
  exact proposition_7_2_no_parameters_identity R lam
    (proposition_7_2_no_parameters R lam x)

/-- The canonical identity map for Proposition 7.2 at `m = 0` commutes with
the actual ambient coordinate action, which fixes all coefficient scalars. -/
theorem proposition_7_2_no_parameters_permutation
    (R : Type*) [CommRing R] (lam : YoungDiagram)
    (g : Equiv.Perm (Fin lam.card))
    (x : OrderedRootRing R (lam.card - lam.card)
      ⊗[ElementaryParameterRing R lam.card lam] SpringerRing R lam) :
    proposition_7_2_no_parameters R lam
        (elementaryParameterTensorPermutation
          (OrderedRootRing R (lam.card - lam.card)) g x) =
      springerPermutationAlgEquiv lam g
        (proposition_7_2_no_parameters R lam x) := by
  have hTensor :
      elementaryParameterTensorPermutation (R := R) (n := lam.card) (lam := lam)
          (OrderedRootRing R (lam.card - lam.card)) g x =
        (1 : OrderedRootRing R (lam.card - lam.card))
          ⊗ₜ[ElementaryParameterRing R lam.card lam]
            untruncatedParameterPermutation (R := R) (n := lam.card) lam g
              (proposition_7_2_no_parameters R lam x) :=
    (congrArg
      (fun z : OrderedRootRing R (lam.card - lam.card)
          ⊗[ElementaryParameterRing R lam.card lam] SpringerRing R lam =>
        elementaryParameterTensorPermutation (R := R) (n := lam.card) (lam := lam)
          (OrderedRootRing R (lam.card - lam.card)) g z)
      (proposition_7_2_no_parameters_includeRight R lam x).symm).trans
      (elementaryParameterTensorPermutation_tmul (R := R) (n := lam.card) (lam := lam)
        (OrderedRootRing R (lam.card - lam.card)) g
        (1 : OrderedRootRing R (lam.card - lam.card))
        (proposition_7_2_no_parameters R lam x))
  exact (congrArg
    (fun z : OrderedRootRing R (lam.card - lam.card)
        ⊗[ElementaryParameterRing R lam.card lam] SpringerRing R lam =>
      proposition_7_2_no_parameters R lam z) hTensor).trans
    ((proposition_7_2_no_parameters_identity R lam
      (untruncatedParameterPermutation (R := R) (n := lam.card) lam g
        (proposition_7_2_no_parameters R lam x))).trans
      (untruncatedParameterPermutation_fullSize (R := R) lam g
        (proposition_7_2_no_parameters R lam x)))

end HigherSpecht
end
end CanonicalSource86
