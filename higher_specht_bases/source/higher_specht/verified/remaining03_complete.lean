module

public import higher_specht.verified.remaining03_ordered
public import Mathlib.Algebra.Order.Chebyshev

/- Generated ordinary source-preserving proof stage. See audit/staged_specht_remaining/Remaining03Complete/manifest.json. -/

@[expose] public section

section CanonicalSource87
/- Source: HigherSpecht/Theorem32SelectedFamily.lean -/



/-!
# Theorem 3.2 for a selected family

Each matrix entry pairs the prescribed higher Specht polynomial with the
column-insertion Vandermonde witness through the ordinary polynomial
differential action. The proof uses the coefficient formula and exact
lexicographic norm/column-prefix order from the preceding modules.

An arbitrary finite set of left tableaux, including the empty set, is
enumerated in that order, with stable ties in a chosen finite enumeration.
This ordinary differential-operator statement assumes characteristic zero;
the separate coefficient-pairing theory also treats the admissible
positive-characteristic range.
-/

noncomputable section

open Module MvPolynomial TauCeti TauCeti.YoungTableau
open scoped Classical

namespace HigherSpecht

variable {μ : YoungDiagram}

def selectedFamilyEnumeration (A : Finset (StandardYoungTableau μ))
    (T : StandardYoungTableau μ) : Fin A.card ≃ A :=
  (Tuple.sort (fun i : Fin A.card =>
    higherSpechtPrefixKey (A.equivFin.symm i).val T.toTableau)).trans A.equivFin.symm

theorem selectedFamilyEnumeration_monotone
    (A : Finset (StandardYoungTableau μ)) (T : StandardYoungTableau μ) :
    Monotone (fun i : Fin A.card =>
      higherSpechtPrefixKey (selectedFamilyEnumeration A T i).val T.toTableau) := by
  exact Tuple.monotone_sort
    (fun i : Fin A.card => higherSpechtPrefixKey (A.equivFin.symm i).val T.toTableau)

/-- Ties are resolved by the original finite enumeration; no injectivity of
the prefix key is assumed. -/
theorem selectedFamilyEnumeration_ties
    (A : Finset (StandardYoungTableau μ)) (T : StandardYoungTableau μ)
    {i j : Fin A.card} (hij : i ≤ j)
    (hkey : higherSpechtPrefixKey (selectedFamilyEnumeration A T i).val T.toTableau =
      higherSpechtPrefixKey (selectedFamilyEnumeration A T j).val T.toTableau) :
    A.equivFin (selectedFamilyEnumeration A T i) ≤
      A.equivFin (selectedFamilyEnumeration A T j) := by
  let key : Fin A.card → Lex (Fin (μ.card + 1) → ℤ) :=
    fun i => higherSpechtPrefixKey (A.equivFin.symm i).val T.toTableau
  have hstable := (Tuple.eq_sort_iff (f := key) (σ := Tuple.sort key)).mp rfl
  simpa only [selectedFamilyEnumeration, Equiv.trans_apply, Equiv.apply_symm_apply]
    using hstable.2 hij hkey

def higherSpechtSelectedMatrix {K : Type*} [Field K] [CharZero K]
    (A : Finset (StandardYoungTableau μ)) (T : StandardYoungTableau μ)
    (e : Fin A.card ≃ A) : Matrix (Fin A.card) (Fin A.card) K :=
  fun i j => higherSpechtApolarFunctional (K := K) (e i).val T.toTableau
    (higherSpechtPolynomial (e j).val T)

/-- Every matrix entry is the stated coefficient of the actual ordinary
differential operator applied to the literal product of column alternants.
The explicit WitnessVandermonde import is part of this correspondence. -/
theorem theorem_3_2_selected_entry {K : Type*} [Field K] [CharZero K]
    (A : Finset (StandardYoungTableau μ)) (T : StandardYoungTableau μ)
    (e : Fin A.card ≃ A) (i j : Fin A.card) :
    higherSpechtSelectedMatrix (K := K) A T e i j =
      (ordinaryAction (higherSpechtPolynomial (R := K) (e j).val T)
        (columnWitness (insertionFilling (e i).val T.toTableau).toEmbedding 1)).coeff
          (insertionRejectionExponent (e i).val T.toTableau) := by
  rw [higherSpechtSelectedMatrix, higherSpechtApolarFunctional_apply,
    higherSpechtWitness_eq_columnWitness]

theorem higherSpechtApolarFunctional_self_ne_zero
    {K : Type*} [Field K] [CharZero K] (S T : StandardYoungTableau μ) :
    higherSpechtApolarFunctional (K := K) S T.toTableau
      (higherSpechtPolynomial S T) ≠ 0 := by
  change
    (((exponentFactorial (insertionAlpha S T.toTableau) : K) /
      exponentFactorial (insertionRejectionExponent S T.toTableau)) *
      higherSpechtCoefficientFunctional S T.toTableau (higherSpechtPolynomial S T)) ≠ 0
  apply mul_ne_zero
  · apply div_ne_zero
    · exact_mod_cast (exponentFactorial_pos (insertionAlpha S T.toTableau)).ne'
    · exact_mod_cast
        (exponentFactorial_pos (insertionRejectionExponent S T.toTableau)).ne'
  · exact higherSpecht_coefficient_pairing_diagonal_ne_zero S T

/-- The actual selected matrix is upper triangular in a compatible
enumeration, including tied keys. Its diagonal has the exact stabilizer and
factorial value, is nonzero over every characteristic-zero field, and is
strictly positive over the rationals. -/
theorem theorem_3_2_selected_family
    (K : Type*) [Field K] [CharZero K]
    (A : Finset (StandardYoungTableau μ)) (T : StandardYoungTableau μ) :
    ∃ e : Fin A.card ≃ A,
      Monotone (fun i => higherSpechtPrefixKey (e i).val T.toTableau) ∧
      (∀ i j : Fin A.card, i ≤ j →
        higherSpechtPrefixKey (e i).val T.toTableau =
          higherSpechtPrefixKey (e j).val T.toTableau →
        A.equivFin (e i) ≤ A.equivFin (e j)) ∧
      (∀ i j : Fin A.card, j < i →
        higherSpechtSelectedMatrix (K := K) A T e i j = 0) ∧
      (∀ i : Fin A.card,
        higherSpechtSelectedMatrix (K := K) A T e i i =
          ((rowFillingStabilizers T.toTableau
            (transportedCocharge (e i).val T.toTableau)).card : K) *
          ((insertionFixedPermutations (e i).val T.toTableau).card : K) *
          ((exponentFactorial (insertionAlpha (e i).val T.toTableau) : K) /
            exponentFactorial (insertionRejectionExponent (e i).val T.toTableau))) ∧
      (∀ i : Fin A.card, higherSpechtSelectedMatrix (K := K) A T e i i ≠ 0) ∧
      (∀ i : Fin A.card, 0 < higherSpechtSelectedMatrix (K := ℚ) A T e i i) := by
  let e := selectedFamilyEnumeration A T
  refine ⟨e, selectedFamilyEnumeration_monotone A T, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij hkey
    exact selectedFamilyEnumeration_ties A T hij hkey
  · intro i j hij
    apply theorem_3_2_prefix_offDiagonal (e i).val (e j).val T
    · intro heq
      have hsub : e i = e j := Subtype.ext heq
      exact (ne_of_gt hij) (e.injective hsub)
    · exact selectedFamilyEnumeration_monotone A T hij.le
  · intro i
    exact theorem_3_2_diagonal (e i).val T
  · intro i
    exact higherSpechtApolarFunctional_self_ne_zero (e i).val T
  · intro i
    exact theorem_3_2_diagonal_pos (e i).val T

end HigherSpecht
end
end CanonicalSource87

section CanonicalSource88
/- Source: HigherSpecht/MultiplierMajorization.lean -/



/-!
# The strict norm comparison for alternative symmetric multipliers

The square norm is strictly increasing under genuine strict partition
dominance.  This is proved from the pinned, constructive box-move theorem.
Abel's finite inequality supplies the separate weighted comparison with the
increasing cocharge sequence.  Their sum is the strict inequality used in
Corollary 4.3; it is not an extra support hypothesis on that corollary.
-/

noncomputable section
open Finset TauCeti Function
open scoped Classical

namespace HigherSpecht

def partitionSquareNorm {d : ℕ} (eta : d.Partition) : ℤ :=
  (eta.parts.map fun a : ℕ => (a : ℤ) ^ 2).sum

def diagramSquareNorm (eta : YoungDiagram) : ℤ :=
  ((eta.rowLens : Multiset ℕ).map fun a : ℕ => (a : ℤ) ^ 2).sum

@[simp] theorem diagramSquareNorm_ofPartition {d : ℕ} (eta : d.Partition) :
    diagramSquareNorm (YoungDiagram.ofPartition eta) = partitionSquareNorm eta := by
  simp only [diagramSquareNorm, YoungDiagram.rowLens_ofPartition_eq_sort_parts,
    Multiset.sort_eq, partitionSquareNorm]

theorem partitionSquareNorm_lt_of_boxMove {d : ℕ} {zeta eta : d.Partition}
    (h : zeta.IsBoxMove eta) : partitionSquareNorm zeta < partitionSquareNorm eta := by
  obtain ⟨a, b, hba, heq⟩ := Nat.Partition.isBoxMove_iff.mp h
  have hsum := congrArg (fun l : Multiset ℕ => (l.map fun x : ℕ => (x : ℤ) ^ 2).sum) heq
  have hfilter : ((({a + 1, b} : Multiset ℕ).filter (· ≠ 0)).map
      fun x : ℕ => (x : ℤ) ^ 2).sum = (a + 1 : ℤ) ^ 2 + (b : ℤ) ^ 2 := by
    by_cases hb : b = 0 <;> simp [hb, Multiset.filter_singleton]
  simp only [Multiset.map_add, Multiset.sum_add, hfilter] at hsum
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton, Nat.cast_add, Nat.cast_one] at hsum
  change partitionSquareNorm eta + ((a : ℤ) ^ 2 + (b + 1 : ℤ) ^ 2) =
    partitionSquareNorm zeta + ((a + 1 : ℤ) ^ 2 + (b : ℤ) ^ 2) at hsum
  have hab : (b : ℤ) < a := by exact_mod_cast hba
  nlinarith

theorem partitionSquareNorm_lt_of_strictlyDominates {d : ℕ}
    {zeta eta : d.Partition} (h : eta.StrictlyDominates zeta) :
    partitionSquareNorm zeta < partitionSquareNorm eta := by
  have hc := Nat.Partition.strictlyDominates_iff_transGen_isBoxMove.mp h
  clear h
  induction hc with
  | single h => exact partitionSquareNorm_lt_of_boxMove h
  | tail _ h ih => exact ih.trans (partitionSquareNorm_lt_of_boxMove h)

@[simp] theorem boostLabel_rev (eta : YoungDiagram) {n : ℕ} (i : Fin n) :
    boostLabel eta n i.rev = eta.rowLen i.val := by
  unfold boostLabel
  congr 1
  simp only [Fin.val_rev]
  omega

theorem squareNorm_boostLabel {n : ℕ} (eta : YoungDiagram)
    (heta : eta.colLen 0 ≤ n) :
    squareNorm (fun i : Fin n => (boostLabel eta n i : ℤ)) =
      diagramSquareNorm eta := by
  rw [← squareNorm_comp_perm _ Fin.revPerm]
  simp only [Function.comp_def, Fin.revPerm_apply, boostLabel_rev]
  rw [squareNorm,
    Fin.sum_univ_eq_sum_range (fun i : ℕ => (eta.rowLen i : ℤ) ^ 2) n]
  rw [diagramSquareNorm, YoungDiagram.sum_map_coe_rowLens]
  symm
  apply Finset.sum_subset (Finset.range_mono heta)
  intro i hi hnot
  have hz := YoungDiagram.rowLen_eq_zero_of_colLen_le
    (show eta.colLen 0 ≤ i from Nat.le_of_not_gt (by simpa using hnot))
  simp only [hz, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0)]

theorem weighted_boost_le_of_dominates {n : ℕ} (a : Fin n → ℤ)
    (ha : Monotone a) (ha0 : ∀ i, 0 ≤ a i)
    {eta zeta : YoungDiagram} (hdom : Dominates eta zeta) :
    (∑ i, a i * (boostLabel zeta n i : ℤ)) ≤
      ∑ i, a i * (boostLabel eta n i : ℤ) := by
  let w : ℕ → ℤ := fun k => if hk : k < n then a (Fin.rev ⟨k, hk⟩) else 0
  have hw0 : 0 ≤ w := by
    intro k
    dsimp [w]
    split_ifs <;> simp_all [ha0]
  have hw : AntitoneOn w (Set.Iio n) := by
    intro i hi j hj hij
    simp only [Set.mem_Iio] at hi hj
    simp only [w, dif_pos hi, dif_pos hj]
    apply ha
    exact Fin.rev_le_rev.mpr hij
  have h := Finset.sum_mul_le_sum_mul_of_sum_range_le
    (f := fun i => (zeta.rowLen i : ℤ))
    (c := fun i => (eta.rowLen i : ℤ)) (g := w) (n := n)
    (fun k hk => by exact_mod_cast hdom k) hw0 hw
  have hreverse (theta : YoungDiagram) :
      (∑ i : Fin n, a i * (boostLabel theta n i : ℤ)) =
        ∑ k ∈ Finset.range n, (theta.rowLen k : ℤ) * w k := by
    rw [← Equiv.sum_comp Fin.revPerm]
    simp only [Fin.revPerm_apply, boostLabel_rev]
    rw [← Fin.sum_univ_eq_sum_range (fun k => (theta.rowLen k : ℤ) * w k) n]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [w, dif_pos i.isLt]
    ring
  rwa [hreverse zeta, hreverse eta]

theorem shifted_boost_norm_lt_of_strictlyDominates {n d : ℕ}
    (a : Fin n → ℤ) (ha : Monotone a) (ha0 : ∀ i, 0 ≤ a i)
    {zeta eta : d.Partition} (h : eta.StrictlyDominates zeta)
    (hz : (YoungDiagram.ofPartition zeta).colLen 0 ≤ n)
    (he : (YoungDiagram.ofPartition eta).colLen 0 ≤ n) :
    squareNorm (fun i => a i + (boostLabel (YoungDiagram.ofPartition zeta) n i : ℤ)) <
      squareNorm (fun i => a i + (boostLabel (YoungDiagram.ofPartition eta) n i : ℤ)) := by
  have hd : Dominates (YoungDiagram.ofPartition eta) (YoungDiagram.ofPartition zeta) := by
    intro k
    have hp := Nat.Partition.dominates_iff.mp
      (Nat.Partition.strictlyDominates_iff.mp h).1 k
    rw [← YoungDiagram.rowLens_ofPartition_eq_sort_parts,
      ← YoungDiagram.rowLens_ofPartition_eq_sort_parts,
      YoungDiagram.sum_take_rowLens_eq_card_filter_fst,
      YoungDiagram.sum_take_rowLens_eq_card_filter_fst,
      ← YoungDiagram.sum_range_rowLen_eq_card_filter_fst,
      ← YoungDiagram.sum_range_rowLen_eq_card_filter_fst] at hp
    exact_mod_cast hp
  have hweight := weighted_boost_le_of_dominates a ha ha0 hd
  have hsq := partitionSquareNorm_lt_of_strictlyDominates h
  rw [squareNorm_add, squareNorm_add, squareNorm_boostLabel _ hz,
    squareNorm_boostLabel _ he, diagramSquareNorm_ofPartition,
    diagramSquareNorm_ofPartition]
  linarith

end HigherSpecht
end
end CanonicalSource88

section CanonicalSource89
/- Source: HigherSpecht/MonomialMultipliers.lean -/



/-!
# The genuine monomial symmetric multiplier and its extremal coefficients

This uses Mathlib's `MvPolynomial.msymm`, including its coefficient-one
convention.  A supported exponent is an actual permutation of the padded
partition.  In the top norm layer its product with a higher Specht polynomial
has exactly the same coefficients as the elementary product from Lemma 4.2.
-/

noncomputable section
open Finset TauCeti TauCeti.YoungTableau MvPolynomial Function Equiv
open scoped Classical

namespace HigherSpecht

variable {R : Type*} [CommRing R]

theorem symmetric_coeff_permuted {n : ℕ} (f : PolynomialRing n R)
    (hf : f.IsSymmetric) (delta : Fin n →₀ ℕ) (e : Equiv.Perm (Fin n)) :
    f.coeff (permutedExponent delta e) = f.coeff delta := by
  rw [← coeff_rename_perm, hf e]

def monomialMultiplier (n : ℕ) (R : Type*) [CommRing R] (eta : YoungDiagram) :
    PolynomialRing n R := MvPolynomial.msymm (Fin n) R (eta.toPartition rfl)

theorem monomialMultiplier_toPartition (n : ℕ) (eta : YoungDiagram)
    {d : ℕ} (h : eta.card = d) :
    monomialMultiplier n R eta = MvPolynomial.msymm (Fin n) R (eta.toPartition h) := by
  subst d
  rfl

@[simp] theorem monomialMultiplier_ofPartition (n : ℕ) {d : ℕ} (eta : d.Partition) :
    monomialMultiplier n R (YoungDiagram.ofPartition eta) =
      MvPolynomial.msymm (Fin n) R eta := by
  rw [monomialMultiplier_toPartition n _ (YoungDiagram.card_ofPartition eta),
    YoungDiagram.toPartition_ofPartition]

theorem partWeight_eq_permuted_boost {n d : ℕ} (eta : d.Partition) :
    partWeight (Fin n) eta = permutedExponent
      (boostExponent (YoungDiagram.ofPartition eta) n)
      (((Fintype.equivFin (Fin n)).trans (finCongr (Fintype.card_fin n))).trans Fin.revPerm) := by
  ext i
  simp only [partWeight_apply, permutedExponent_apply, boostExponent,
    Finsupp.equivFunOnFinite_symm_apply_apply, Equiv.trans_apply,
    Fin.revPerm_apply, boostLabel_rev, finCongr_apply_coe]

theorem msymm_boostCoefficient {n d : ℕ} (eta : d.Partition)
    (heta : (YoungDiagram.ofPartition eta).colLen 0 ≤ n) :
    (MvPolynomial.msymm (Fin n) R eta).coeff
      (boostExponent (YoungDiagram.ofPartition eta) n) = 1 := by
  have h := TauCeti.coeff_msymm_partWeight (σ := Fin n) R eta eta
    (by simpa only [YoungDiagram.colLen_zero_ofPartition, Fintype.card_fin] using heta)
  rw [partWeight_eq_permuted_boost,
    symmetric_coeff_permuted _ (MvPolynomial.msymm_isSymmetric _ _ eta)] at h
  simpa only [if_pos rfl, ite_true] using h

theorem msymm_coeff_ne_zero_orbit {n d : ℕ} (eta : d.Partition)
    (delta : Fin n →₀ ℕ)
    (hdelta : (MvPolynomial.msymm (Fin n) R eta).coeff delta ≠ 0) :
    (YoungDiagram.ofPartition eta).colLen 0 ≤ n ∧
      ∃ e : Equiv.Perm (Fin n),
        delta = permutedExponent (boostExponent (YoungDiagram.ofPartition eta) n) e := by
  have hd : delta.degree = d := by
    by_contra hn
    exact hdelta (TauCeti.coeff_msymm_eq_zero_of_degree_ne R eta hn)
  have hp : TauCeti.weightPartition delta hd = eta := by
    by_contra hn
    exact hdelta (by rw [TauCeti.coeff_msymm R eta hd, if_neg hn])
  have hheight : (YoungDiagram.ofPartition eta).colLen 0 ≤ n := by
    rw [YoungDiagram.colLen_zero_ofPartition, ← hp]
    simpa only [Fintype.card_fin] using TauCeti.card_parts_weightPartition_le delta hd
  obtain ⟨e, he⟩ := TauCeti.exists_perm_mapDomain_eq_partWeight delta hd
  rw [hp, partWeight_eq_permuted_boost] at he
  let c := ((Fintype.equivFin (Fin n)).trans (finCongr (Fintype.card_fin n))).trans Fin.revPerm
  refine ⟨hheight, e.trans c, ?_⟩
  ext i
  have hi := congrArg (fun a : Fin n →₀ ℕ => a (e i)) he
  rw [Finsupp.mapDomain_apply_of_injective e.injective] at hi
  exact hi

theorem monomialMultiplier_coeff_ne_zero_orbit {n : ℕ} (eta : YoungDiagram)
    (delta : Fin n →₀ ℕ) (hd : (monomialMultiplier n R eta).coeff delta ≠ 0) :
    eta.colLen 0 ≤ n ∧ ∃ e : Equiv.Perm (Fin n),
      delta = permutedExponent (boostExponent eta n) e := by
  simpa only [monomialMultiplier, YoungDiagram.ofPartition_toPartition] using
    msymm_coeff_ne_zero_orbit (eta.toPartition rfl) delta hd

theorem monomialMultiplier_boostCoefficient {n : ℕ} (eta : YoungDiagram)
    (heta : eta.colLen 0 ≤ n) :
    (monomialMultiplier n R eta).coeff (boostExponent eta n) = 1 := by
  simpa only [monomialMultiplier, YoungDiagram.ofPartition_toPartition] using
    msymm_boostCoefficient (R := R) (eta.toPartition rfl)
      (by simpa only [YoungDiagram.ofPartition_toPartition] using heta)

theorem monomialMultiplier_isSymmetric (n : ℕ) (eta : YoungDiagram) :
    (monomialMultiplier n R eta).IsSymmetric := MvPolynomial.msymm_isSymmetric _ _ _

theorem monomialMultiplier_coefficient_of_orbit {n : ℕ} (eta : YoungDiagram)
    (heta : eta.colLen 0 ≤ n) (e : Equiv.Perm (Fin n)) :
    (monomialMultiplier n R eta).coeff (permutedExponent (boostExponent eta n) e) = 1 := by
  rw [symmetric_coeff_permuted _ (monomialMultiplier_isSymmetric n eta),
    monomialMultiplier_boostCoefficient eta heta]

theorem elementary_coefficient_of_monomial_supported {n : ℕ}
    (eta : YoungDiagram) (delta : Fin n →₀ ℕ)
    (hd : (monomialMultiplier n R eta).coeff delta ≠ 0) :
    (elementaryMultiplier (R := R) n n eta.rowLen).coeff delta = 1 := by
  obtain ⟨heta, e, rfl⟩ := monomialMultiplier_coeff_ne_zero_orbit eta delta hd
  rw [elementaryMultiplier_coeff_permuted,
    elementaryMultiplier_boostCoefficient le_rfl eta heta]

theorem youngExponent_elementary_norm_bound {mu : YoungDiagram}
    (S T : StandardYoungTableau mu) (eta : YoungDiagram)
    (heta : eta.colLen 0 ≤ mu.card)
    (sigma : colSubgroup T.toTableau) (rho : rowSubgroup T.toTableau)
    (delta : Fin mu.card →₀ ℕ)
    (hd : (elementaryMultiplier (R := R) mu.card mu.card eta.rowLen).coeff delta ≠ 0) :
    squareNorm (intExponent
      (youngExponent T.toTableau (transportedCocharge S T.toTableau) sigma rho + delta)) ≤
      squareNorm (intExponent (transportedBoosted S T.toTableau eta)) := by
  let e := tableauLabelEquiv S T.toTableau
  let tau := e.symm.trans (sigma.val.symm.trans (rho.val.symm.trans e))
  have hd' : (elementaryMultiplier (R := R) mu.card mu.card eta.rowLen).coeff
      (permutedExponent delta e.symm) ≠ 0 := by
    rwa [elementaryMultiplier_coeff_permuted]
  have h := elementaryMultiplier_supported_norm_bound le_rfl eta heta
    (fun i => (cochargeLabel S i : ℤ))
    (fun i j hij => by
      change (cochargeLabel S i : ℤ) ≤ (cochargeLabel S j : ℤ)
      exact_mod_cast cochargeLabel_mono S hij) tau
    (permutedExponent delta e.symm) hd'
  have hl : (fun i => (cochargeLabel S (tau i) : ℤ) +
      (permutedExponent delta e.symm i : ℤ)) =
      intExponent (youngExponent T.toTableau (transportedCocharge S T.toTableau) sigma rho +
        delta) ∘ e.symm := by
    funext i
    simp only [Function.comp_apply, intExponent, Finsupp.add_apply, Nat.cast_add,
      youngExponent, permutedExponent_apply, transportedCocharge_apply_labelEquiv,
      tau, Equiv.trans_apply, e]
  have hr : intExponent (transportedBoosted S T.toTableau eta) =
      (fun i => (cochargeLabel S i : ℤ) + (boostLabel eta mu.card i : ℤ)) ∘ e := by
    funext i
    simp only [intExponent, transportedBoosted_apply_labelEquiv, boostedLabel,
      Nat.cast_add, Function.comp_apply, e]
  rw [hl, squareNorm_comp_perm] at h
  rw [hr, squareNorm_comp_perm]
  exact h

theorem youngExponent_elementary_norm_tie_delta {mu : YoungDiagram}
    (S T : StandardYoungTableau mu) (eta : YoungDiagram)
    (heta : eta.colLen 0 ≤ mu.card)
    (sigma : colSubgroup T.toTableau) (rho : rowSubgroup T.toTableau)
    (delta : Fin mu.card →₀ ℕ)
    (hd : (elementaryMultiplier (R := R) mu.card mu.card eta.rowLen).coeff delta ≠ 0)
    (hn : squareNorm (intExponent
      (youngExponent T.toTableau (transportedCocharge S T.toTableau) sigma rho + delta)) =
      squareNorm (intExponent (transportedBoosted S T.toTableau eta))) :
    ∃ e : Equiv.Perm (Fin mu.card), delta = permutedExponent (boostExponent eta mu.card) e := by
  obtain ⟨pi, hp, hb⟩ := youngExponent_boosted_norm_tie_data S T le_rfl eta heta
    sigma rho delta hd hn
  refine ⟨sigma.val.symm.trans (pi.trans (tableauLabelEquiv S T.toTableau)), ?_⟩
  ext i
  have hi := congrFun hp i
  have hb' := congrFun hb (sigma.val.symm i)
  simp only [Function.comp_apply, intExponent, Finsupp.add_apply, Nat.cast_add,
    youngExponent, permutedExponent_apply, transportedCocharge_apply_labelEquiv,
    transportedBoosted_apply_labelEquiv, boostedLabel] at hi hb'
  simp only [permutedExponent_apply, boostExponent,
    Finsupp.equivFunOnFinite_symm_apply_apply, Equiv.trans_apply]
  omega

theorem higherSpecht_monomial_norm_bound [Nontrivial R] {mu : YoungDiagram}
    (S T : StandardYoungTableau mu) (eta : YoungDiagram)
    (heta : eta.colLen 0 ≤ mu.card) (beta : Fin mu.card →₀ ℕ)
    (hb : (higherSpechtPolynomial (R := R) S T *
      monomialMultiplier mu.card R eta).coeff beta ≠ 0) :
    squareNorm (intExponent beta) ≤
      squareNorm (intExponent (transportedBoosted S T.toTableau eta)) := by
  obtain ⟨a, delta, ha, hd, rfl⟩ := coeff_mul_ne_zero_exists _ _ beta hb
  obtain ⟨sigma, rho, rfl⟩ := youngApply_coeff_ne_zero T.toTableau _ a ha
  apply youngExponent_elementary_norm_bound (R := R) S T eta heta sigma rho delta
  rw [elementary_coefficient_of_monomial_supported eta delta hd]
  exact one_ne_zero

/-- Equality of literal coefficients in the maximal norm layer; this also
fixes the diagonal normalization of every alternative multiplier. -/
theorem higherSpecht_monomial_topCoefficient [Nontrivial R] {mu : YoungDiagram}
    (S T : StandardYoungTableau mu) (eta : YoungDiagram)
    (heta : eta.colLen 0 ≤ mu.card) (beta : Fin mu.card →₀ ℕ)
    (hn : squareNorm (intExponent beta) =
      squareNorm (intExponent (transportedBoosted S T.toTableau eta))) :
    (higherSpechtPolynomial (R := R) S T * monomialMultiplier mu.card R eta).coeff beta =
      (higherSpechtPolynomial S T * elementaryMultiplier mu.card mu.card eta.rowLen).coeff beta := by
  rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨a, delta⟩ hz
  have hsum := Finset.mem_antidiagonal.mp hz
  by_cases ha : (higherSpechtPolynomial (R := R) S T).coeff a = 0
  · simp only [ha, zero_mul]
  by_cases hd : (elementaryMultiplier (R := R) mu.card mu.card eta.rowLen).coeff delta = 0
  · have hm : (monomialMultiplier mu.card R eta).coeff delta = 0 := by
      by_contra hm
      have he := elementary_coefficient_of_monomial_supported eta delta hm
      exact one_ne_zero (he.symm.trans hd)
    simp only [hd, hm, mul_zero]
  obtain ⟨sigma, rho, hbase⟩ := youngApply_coeff_ne_zero T.toTableau _ a ha
  obtain ⟨e, he⟩ := youngExponent_elementary_norm_tie_delta S T eta heta sigma rho delta hd
    (by rw [hbase, hsum]; exact hn)
  rw [he, monomialMultiplier_coefficient_of_orbit eta heta,
    elementaryMultiplier_coeff_permuted, elementaryMultiplier_boostCoefficient le_rfl eta heta]

end HigherSpecht
end
end CanonicalSource89

section CanonicalSource90
/- Source: HigherSpecht/DominanceTriangularMultipliers.lean -/



/-!
# Exactly the symmetric-polynomial hypothesis of Corollary 4.3

`IsDominanceTriangularMultiplier` is the literal finite monomial-symmetric
expansion from the paper, with nonzero leading coefficient and no restriction
on the coefficients below dominance.  Its symmetry, homogeneity, strict
lower-layer norm bound, and top coefficient are all proved here.
-/

noncomputable section
open Finset TauCeti TauCeti.YoungTableau MvPolynomial Function
open scoped Classical

namespace HigherSpecht

variable {R : Type*} [CommRing R]

def IsDominanceTriangularMultiplier (n : ℕ) (eta : YoungDiagram)
    (f : PolynomialRing n R) : Prop :=
  ∃ c : eta.card.Partition → R,
    c (eta.toPartition rfl) ≠ 0 ∧
    (∀ zeta, c zeta ≠ 0 → (eta.toPartition rfl).Dominates zeta) ∧
    f = ∑ zeta, c zeta • MvPolynomial.msymm (Fin n) R zeta

/-- Equivalence with the manuscript's displayed leading term plus terms
strictly below it in dominance.  The definition above uses a single finite
sum only to make coefficient calculations convenient. -/
theorem isDominanceTriangularMultiplier_iff_strictExpansion {n : ℕ}
    (eta : YoungDiagram) (f : PolynomialRing n R) :
    IsDominanceTriangularMultiplier n eta f ↔
      ∃ c : R, c ≠ 0 ∧ ∃ b : eta.card.Partition → R,
        f = c • monomialMultiplier n R eta +
          ∑ zeta ∈ Finset.univ.filter ((eta.toPartition rfl).StrictlyDominates),
            b zeta • MvPolynomial.msymm (Fin n) R zeta := by
  constructor
  · rintro ⟨b, hb, hdom, hf⟩
    refine ⟨b (eta.toPartition rfl), hb, b, ?_⟩
    rw [hf, ← Finset.sum_erase_add Finset.univ
      (fun zeta => b zeta • MvPolynomial.msymm (Fin n) R zeta)
      (Finset.mem_univ (eta.toPartition rfl))]
    rw [add_comm]
    congr 1
    symm
    apply Finset.sum_subset
    · intro zeta hz
      obtain ⟨hz, hstrict⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_erase.mpr
        ⟨Ne.symm (Nat.Partition.strictlyDominates_iff.mp hstrict).2, hz⟩
    · intro zeta hz hnot
      obtain ⟨hne, _⟩ := Finset.mem_erase.mp hz
      have hz0 : b zeta = 0 := by
        by_contra hz0
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Nat.Partition.strictlyDominates_iff.mpr ⟨hdom zeta hz0, Ne.symm hne⟩⟩)
      simp only [hz0, zero_smul]
  · rintro ⟨c, hc, b, hf⟩
    let a : eta.card.Partition → R := fun zeta =>
      if zeta = eta.toPartition rfl then c
      else if (eta.toPartition rfl).StrictlyDominates zeta then b zeta else 0
    refine ⟨a, by simpa only [a, if_pos rfl] using hc, ?_, ?_⟩
    · intro zeta hz
      by_cases he : zeta = eta.toPartition rfl
      · subst zeta
        exact Nat.Partition.dominates_refl _
      · by_cases hs : (eta.toPartition rfl).StrictlyDominates zeta
        · exact (Nat.Partition.strictlyDominates_iff.mp hs).1
        · exact (hz (by simp only [a, if_neg he, if_neg hs])).elim
    · rw [hf, ← Finset.sum_erase_add Finset.univ
        (fun zeta => a zeta • MvPolynomial.msymm (Fin n) R zeta)
        (Finset.mem_univ (eta.toPartition rfl))]
      simp only [a, if_pos rfl]
      rw [add_comm]
      congr 1
      rw [Finset.sum_filter]
      apply Finset.sum_congr_of_eq_on_inter
      · intro zeta hz hnot
        have he : zeta = eta.toPartition rfl := by
          simpa only [Finset.mem_erase, Finset.mem_univ, and_true, not_not] using hnot
        subst zeta
        simp [Nat.Partition.strictlyDominates_iff]
      · intro zeta hz hnot
        exact (hnot (Finset.mem_univ _)).elim
      · intro zeta hz hz'
        have he := (Finset.mem_erase.mp hz').1
        simp only [if_neg he]
        split_ifs <;> simp

theorem IsDominanceTriangularMultiplier.isSymmetric {n : ℕ} {eta : YoungDiagram}
    {f : PolynomialRing n R} (hf : IsDominanceTriangularMultiplier n eta f) :
    f.IsSymmetric := by
  obtain ⟨c, hc, hdom, rfl⟩ := hf
  intro e
  simp only [map_sum, map_smul, MvPolynomial.rename_msymm]

theorem IsDominanceTriangularMultiplier.isHomogeneous {n : ℕ} {eta : YoungDiagram}
    {f : PolynomialRing n R} (hf : IsDominanceTriangularMultiplier n eta f) :
    f.IsHomogeneous eta.card := by
  obtain ⟨c, hc, hdom, rfl⟩ := hf
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun zeta _ =>
    (MvPolynomial.homogeneousSubmodule (Fin n) R eta.card).smul_mem (c zeta)
      (TauCeti.isHomogeneous_msymm (σ := Fin n) R zeta)

theorem monomialMultiplier_isDominanceTriangular [Nontrivial R]
    (n : ℕ) (eta : YoungDiagram) :
    IsDominanceTriangularMultiplier n eta (monomialMultiplier n R eta) := by
  refine ⟨fun zeta => if zeta = eta.toPartition rfl then 1 else 0, by simp, ?_, ?_⟩
  · intro zeta hz
    have he : zeta = eta.toPartition rfl := by
      by_contra he
      exact hz (if_neg he)
    subst zeta
    exact Nat.Partition.dominates_refl _
  · simp [monomialMultiplier]

theorem schurMultiplier_isDominanceTriangular [Nontrivial R]
    (n : ℕ) (eta : YoungDiagram) :
    IsDominanceTriangularMultiplier n eta
      (TauCeti.schurPoly (Fin n) R (eta.toPartition rfl)) := by
  refine ⟨fun zeta => (TauCeti.kostkaNumber (eta.toPartition rfl) zeta : R),
    by simp, ?_, TauCeti.schurPoly_eq_sum_kostkaNumber_smul_msymm _ _⟩
  intro zeta hz
  apply TauCeti.dominates_of_kostkaNumber_ne_zero
  intro hzero
  exact hz (by
    change (TauCeti.kostkaNumber (eta.toPartition rfl) zeta : R) = 0
    rw [hzero, Nat.cast_zero])

theorem msymm_boostCoefficient_other {n d : ℕ} (eta zeta : d.Partition)
    (heta : (YoungDiagram.ofPartition eta).colLen 0 ≤ n) :
    (MvPolynomial.msymm (Fin n) R zeta).coeff
      (boostExponent (YoungDiagram.ofPartition eta) n) = if eta = zeta then 1 else 0 := by
  have h := TauCeti.coeff_msymm_partWeight (σ := Fin n) R zeta eta
    (by simpa only [YoungDiagram.colLen_zero_ofPartition, Fintype.card_fin] using heta)
  rw [partWeight_eq_permuted_boost,
    symmetric_coeff_permuted _ (MvPolynomial.msymm_isSymmetric _ _ zeta)] at h
  exact h

theorem dominanceTriangular_leadingCoefficient {n : ℕ} (eta : YoungDiagram)
    (heta : eta.colLen 0 ≤ n) (c : eta.card.Partition → R) :
    (∑ zeta, c zeta • MvPolynomial.msymm (Fin n) R zeta).coeff
      (boostExponent eta n) = c (eta.toPartition rfl) := by
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_smul, smul_eq_mul]
  have hcoeff (zeta : eta.card.Partition) :
      (MvPolynomial.msymm (Fin n) R zeta).coeff (boostExponent eta n) =
        if eta.toPartition rfl = zeta then 1 else 0 := by
    simpa only [YoungDiagram.ofPartition_toPartition] using
      msymm_boostCoefficient_other (R := R) (eta.toPartition rfl) zeta
        (by simpa only [YoungDiagram.ofPartition_toPartition] using heta)
  simp only [hcoeff, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem IsDominanceTriangularMultiplier.leadingCoefficient_ne_zero {n : ℕ}
    {eta : YoungDiagram} {f : PolynomialRing n R}
    (hf : IsDominanceTriangularMultiplier n eta f) (heta : eta.colLen 0 ≤ n) :
    f.coeff (boostExponent eta n) ≠ 0 := by
  obtain ⟨c, hc, hdom, rfl⟩ := hf
  rwa [dominanceTriangular_leadingCoefficient eta heta]

theorem transportedBoosted_norm_eq {mu : YoungDiagram}
    (S : StandardYoungTableau mu) (T : YoungTableau mu) (eta : YoungDiagram) :
    squareNorm (intExponent (transportedBoosted S T eta)) =
      squareNorm (fun i => (cochargeLabel S i : ℤ) + (boostLabel eta mu.card i : ℤ)) := by
  have h : intExponent (transportedBoosted S T eta) =
      (fun i => (cochargeLabel S i : ℤ) + (boostLabel eta mu.card i : ℤ)) ∘
        tableauLabelEquiv S T := by
    funext i
    simp only [intExponent, transportedBoosted_apply_labelEquiv, boostedLabel,
      Nat.cast_add, Function.comp_apply]
  rw [h, squareNorm_comp_perm]

theorem higherSpecht_strictly_dominated_monomial_norm [Nontrivial R]
    {mu : YoungDiagram} (S T : StandardYoungTableau mu) (eta : YoungDiagram)
    (heta : eta.colLen 0 ≤ mu.card) (zeta : eta.card.Partition)
    (hdom : (eta.toPartition rfl).StrictlyDominates zeta)
    (beta : Fin mu.card →₀ ℕ)
    (hb : (higherSpechtPolynomial (R := R) S T *
      MvPolynomial.msymm (Fin mu.card) R zeta).coeff beta ≠ 0) :
    squareNorm (intExponent beta) <
      squareNorm (intExponent (transportedBoosted S T.toTableau eta)) := by
  obtain ⟨a, delta, ha, hd, heq⟩ := coeff_mul_ne_zero_exists _ _ beta hb
  have hz := (msymm_coeff_ne_zero_orbit zeta delta hd).1
  have hle := higherSpecht_monomial_norm_bound S T (YoungDiagram.ofPartition zeta)
    hz beta (by simpa only [monomialMultiplier_ofPartition] using hb)
  have hlt := shifted_boost_norm_lt_of_strictlyDominates
    (fun i => (cochargeLabel S i : ℤ))
    (fun i j hij => by
      change (cochargeLabel S i : ℤ) ≤ (cochargeLabel S j : ℤ)
      exact_mod_cast cochargeLabel_mono S hij)
    (fun i => Int.natCast_nonneg _) hdom hz
    (by simpa only [YoungDiagram.ofPartition_toPartition] using heta)
  rw [transportedBoosted_norm_eq] at hle ⊢
  exact hle.trans_lt (by simpa only [YoungDiagram.ofPartition_toPartition] using hlt)

theorem dominanceTriangular_product_norm [Nontrivial R] {mu : YoungDiagram}
    (S T : StandardYoungTableau mu) (eta : YoungDiagram)
    (heta : eta.colLen 0 ≤ mu.card) {f : PolynomialRing mu.card R}
    (hf : IsDominanceTriangularMultiplier mu.card eta f)
    (beta : Fin mu.card →₀ ℕ)
    (hb : (higherSpechtPolynomial S T * f).coeff beta ≠ 0) :
    squareNorm (intExponent beta) ≤
      squareNorm (intExponent (transportedBoosted S T.toTableau eta)) := by
  obtain ⟨c, hc, hdom, rfl⟩ := hf
  rw [Finset.mul_sum, MvPolynomial.coeff_sum] at hb
  obtain ⟨zeta, hzeta, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  simp only [mul_smul_comm, MvPolynomial.coeff_smul, smul_eq_mul] at hz
  have hcz := left_ne_zero_of_mul hz
  have hpz := right_ne_zero_of_mul hz
  by_cases he : zeta = eta.toPartition rfl
  · subst zeta
    exact higherSpecht_monomial_norm_bound S T eta heta beta hpz
  · exact (higherSpecht_strictly_dominated_monomial_norm S T eta heta zeta
      (Nat.Partition.strictlyDominates_iff.mpr ⟨hdom zeta hcz, Ne.symm he⟩) beta hpz).le

theorem dominanceTriangular_product_topCoefficient [Nontrivial R]
    {mu : YoungDiagram} (S T : StandardYoungTableau mu) (eta : YoungDiagram)
    (heta : eta.colLen 0 ≤ mu.card) {f : PolynomialRing mu.card R}
    (hf : IsDominanceTriangularMultiplier mu.card eta f)
    (beta : Fin mu.card →₀ ℕ)
    (hn : squareNorm (intExponent beta) =
      squareNorm (intExponent (transportedBoosted S T.toTableau eta))) :
    (higherSpechtPolynomial S T * f).coeff beta =
      f.coeff (boostExponent eta mu.card) *
        (higherSpechtPolynomial S T * elementaryMultiplier mu.card mu.card eta.rowLen).coeff beta := by
  obtain ⟨c, hc, hdom, rfl⟩ := hf
  rw [dominanceTriangular_leadingCoefficient eta heta,
    Finset.mul_sum, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single (eta.toPartition rfl)]
  · rw [mul_smul_comm, MvPolynomial.coeff_smul, smul_eq_mul]
    exact congrArg (c (eta.toPartition rfl) * ·)
      (higherSpecht_monomial_topCoefficient S T eta heta beta hn)
  · intro zeta hz he
    rw [mul_smul_comm, MvPolynomial.coeff_smul, smul_eq_mul]
    by_cases hcz : c zeta = 0
    · simp only [hcz, zero_mul]
    have hz0 : (higherSpechtPolynomial (R := R) S T *
        MvPolynomial.msymm (Fin mu.card) R zeta).coeff beta = 0 := by
      by_contra hz0
      have hlt := higherSpecht_strictly_dominated_monomial_norm S T eta heta zeta
        (Nat.Partition.strictlyDominates_iff.mpr ⟨hdom zeta hcz, Ne.symm he⟩) beta hz0
      exact (ne_of_lt hlt) hn
    rw [hz0, mul_zero]
  · exact fun h => (h (Finset.mem_univ _)).elim

/-- The actual polynomial-side certificate used by the old witness, derived
from the paper's expansion rather than supplied as an extra hypothesis. -/
theorem dominanceTriangular_product_support [Nontrivial R] {mu : YoungDiagram}
    (S T : StandardYoungTableau mu) (eta : YoungDiagram)
    (heta : eta.colLen 0 ≤ mu.card) {f : PolynomialRing mu.card R}
    (hf : IsDominanceTriangularMultiplier mu.card eta f) :
    TriangularSupport (fun i => (colIndex T.toTableau i : ℤ))
      (transportedBoosted S T.toTableau eta) (higherSpechtPolynomial S T * f) := by
  let hE := boosted_higherSpecht_triangularSupport (R := R) S T le_rfl eta heta
  refine ⟨dominanceTriangular_product_norm S T eta heta hf, ?_, ?_⟩
  · intro beta hb hn
    have htop := dominanceTriangular_product_topCoefficient S T eta heta hf beta hn
    rw [htop] at hb
    exact hE.weight beta (right_ne_zero_of_mul hb) hn
  · intro beta hb hn hw
    have htop := dominanceTriangular_product_topCoefficient S T eta heta hf beta hn
    rw [htop] at hb
    exact hE.orbit beta (right_ne_zero_of_mul hb) hn hw

end HigherSpecht
end
end CanonicalSource90

section CanonicalSource91
/- Source: HigherSpecht/AlternativeMultiplierPairing.lean -/



/-!
# The unchanged common witnesses for arbitrary triangular multipliers

The true adjoint Young operator is paired with a symmetric multiplier.  Its
pairing is the same coefficient functional as before.  The support theorem
and exact top coefficient then give the zero entries and nonzero diagonal;
no complete-copy independence is inferred merely from these scalar entries.
-/

noncomputable section
open Finset TauCeti TauCeti.YoungTableau MvPolynomial Function
open scoped Classical

namespace HigherSpecht

theorem youngApply_mul_symmetric {mu : YoungDiagram} (T : YoungTableau mu)
    (P f : PolynomialRing mu.card ℂ) (hf : f.IsSymmetric) :
    youngApply T (P * f) = youngApply T P * f := by
  have hsym (e : Equiv.Perm (Fin mu.card)) : rename e f = f := hf e
  simp only [youngApply, columnAlternate, rowSymmetrize, map_mul,
    hsym, ← Finset.sum_mul, map_sum, smul_mul_assoc]
  simp only [← smul_mul_assoc, ← Finset.sum_mul]

theorem ordinaryApolar_commonWitness_symmetric {mu : YoungDiagram}
    (S T : StandardYoungTableau mu) (f : PolynomialRing mu.card ℂ)
    (hf : f.IsSymmetric) (r : Fin mu.card →₀ ℕ) (G : PolynomialRing mu.card ℂ) :
    ordinaryApolarFunctional (adjointYoungApply T.toTableau (normalizedOrdinaryDerivative r G))
      (higherSpechtPolynomial S T * f) = algebraMap ℚ ℂ (youngScalar T.toTableau) *
        (ordinaryAction (higherSpechtPolynomial S T * f) G).coeff r := by
  rw [ordinaryApolar_adjointYoung, youngApply_mul_symmetric _ _ _ hf,
    higherSpechtPolynomial, youngApply_youngApply, smul_mul_assoc, map_smul,
    smul_eq_mul, ordinaryApolar_normalizedDerivative]

theorem ordinaryApolar_fixedCommon_symmetric {mu : YoungDiagram} {s : ℕ}
    (T : StandardYoungTableau mu) (i : FixedFiniteHarmonicIndex mu s)
    (S : StandardYoungTableau mu) (f : PolynomialRing mu.card ℂ)
    (hf : f.IsSymmetric) :
    ordinaryApolarFunctional (fixedCommonHarmonicVector T i) (higherSpechtPolynomial S T * f) =
      fixedCommonPairingScalar T i *
        fixedCommonWitnessFunctional T i (higherSpechtPolynomial S T * f) := by
  rw [fixedCommonHarmonicVector, ordinaryApolar_commonWitness_symmetric S T f hf,
    griffinApolarWitness_eq_coefficientWitness, ordinaryAction_coefficientWitness_coeff]
  rw [fixedCommonPairingScalar, fixedCommonWitnessFunctional, griffinCoefficientFunctional_eq]
  exact (mul_assoc _ _ _).symm

theorem symmetricProduct_columnAlternating {mu : YoungDiagram}
    (S T : StandardYoungTableau mu) (f : PolynomialRing mu.card ℂ)
    (hf : f.IsSymmetric) (tau : Equiv.Perm (Fin mu.card))
    (htau : ∀ i, colIndex T.toTableau (tau i) = colIndex T.toTableau i) :
    rename tau (higherSpechtPolynomial S T * f) =
      coefficientSign (R := ℂ) tau • (higherSpechtPolynomial S T * f) := by
  rw [map_mul, hf, higherSpechtPolynomial,
    youngApply_columnAlternating T.toTableau _ ⟨tau, mem_colSubgroup.mpr htau⟩,
    smul_mul_assoc]

theorem alternativeCommonWitness_offDiagonal {mu : YoungDiagram} {s : ℕ}
    (T : StandardYoungTableau mu) (i j : FixedFiniteHarmonicIndex mu s)
    (f : PolynomialRing mu.card ℂ)
    (hf : IsDominanceTriangularMultiplier mu.card j.multiplier f)
    (hne : i ≠ j) (hkey : fixedGriffinKey T j ≤ fixedGriffinKey T i) :
    fixedCommonWitnessFunctional T i (higherSpechtPolynomial j.left T * f) = 0 := by
  rw [fixedCommonWitnessFunctional, griffinCoefficientFunctional_eq]
  exact witnessCoefficient_eq_zero_of_key_finiteRange
    (row := fun i => (rowIndex T.toTableau i : ℤ))
    (griffinWitness_rearrangement i.left T.toTableau i.multiplier
      (fixedCommonCut i) (fixedCommonCut_le i) s
      (fixedCommonCut_multiplier_length i) i.descents_lt i.multiplier_width)
    (griffinWitnessGroup i.left T.toTableau (fixedCommonCut i) (fixedCommonCut_le i))
    (griffinWitnessGroup_preserves i.left T.toTableau (fixedCommonCut i) (fixedCommonCut_le i))
    (higherSpechtPolynomial j.left T * f)
    (dominanceTriangular_product_support j.left T j.multiplier
      (j.multiplier_length.trans (Nat.sub_le _ _)) hf)
    hkey (fun h => hne (fixedGriffinBoost_injective T h))
    (rowIndex_injective_on_intColumn T.toTableau)
    (transportedBoosted_intColumnMonovary i.left T.toTableau i.multiplier)
    (transportedBoosted_intColumnMonovary j.left T.toTableau j.multiplier)

theorem alternativeCommonWitness_diagonal {mu : YoungDiagram} {s : ℕ}
    (T : StandardYoungTableau mu) (i : FixedFiniteHarmonicIndex mu s)
    (f : PolynomialRing mu.card ℂ)
    (hf : IsDominanceTriangularMultiplier mu.card i.multiplier f) :
    fixedCommonWitnessFunctional T i (higherSpechtPolynomial i.left T * f) =
      f.coeff (boostExponent i.multiplier mu.card) *
        fixedCommonWitnessFunctional T i (fixedGriffinPolynomial T i) := by
  have heta : i.multiplier.colLen 0 ≤ mu.card :=
    i.multiplier_length.trans (Nat.sub_le _ _)
  conv_lhs => rw [fixedCommonWitnessFunctional, griffinCoefficientFunctional_eq]
  rw [witnessCoefficient_diagonal_finiteRange
    (griffinWitness_rearrangement i.left T.toTableau i.multiplier
      (fixedCommonCut i) (fixedCommonCut_le i) s
      (fixedCommonCut_multiplier_length i) i.descents_lt i.multiplier_width)
    (griffinWitnessGroup i.left T.toTableau (fixedCommonCut i) (fixedCommonCut_le i))
    (griffinWitnessGroup_preserves i.left T.toTableau (fixedCommonCut i) (fixedCommonCut_le i))
    (higherSpechtPolynomial i.left T * f)
    (dominanceTriangular_product_support i.left T i.multiplier heta hf)]
  · rw [dominanceTriangular_product_topCoefficient i.left T i.multiplier heta hf _ rfl,
      lemma_4_2_distinguishedCoefficient i.left T le_rfl i.multiplier heta,
      fixedCommonWitnessFunctional_diagonal]
    ring
  · intro tau htau
    rw [← coeff_rename_perm,
      symmetricProduct_columnAlternating i.left T f hf.isSymmetric tau
        (fun j => Int.ofNat_inj.mp (congrFun htau j)), MvPolynomial.coeff_smul, smul_eq_mul]

theorem alternativeCommonWitness_diagonal_ne_zero {mu : YoungDiagram} {s : ℕ}
    (T : StandardYoungTableau mu) (i : FixedFiniteHarmonicIndex mu s)
    (f : PolynomialRing mu.card ℂ)
    (hf : IsDominanceTriangularMultiplier mu.card i.multiplier f) :
    fixedCommonWitnessFunctional T i (higherSpechtPolynomial i.left T * f) ≠ 0 := by
  rw [alternativeCommonWitness_diagonal T i f hf]
  exact mul_ne_zero
    (hf.leadingCoefficient_ne_zero (i.multiplier_length.trans (Nat.sub_le _ _)))
    (fixedCommonWitnessFunctional_diagonal_ne_zero T i)

theorem IsDominanceTriangularMultiplier.rename_finCongr {n m : ℕ}
    {eta : YoungDiagram} {f : PolynomialRing n ℂ}
    (hf : IsDominanceTriangularMultiplier n eta f) (h : n = m) :
    IsDominanceTriangularMultiplier m eta (rename (finCongr h) f) := by
  subst m
  simpa only [finCongr_refl, Equiv.coe_refl, rename_id_apply] using hf

end HigherSpecht
end
end CanonicalSource91

section CanonicalSource92
/- Source: HigherSpecht/ApolarIdealLattice.lean -/



/-!
# The actual finite apolar ideal lattice

For ideals containing a fixed coordinate-power ideal, every linear
annihilator has the explicit bounded polynomial representative constructed
in `OrdinaryHarmonicDuality`.  This identifies the *actual* ideal with the
annihilator of its ordinary harmonic space and proves both lattice
identities.  No dimension, simultaneous-basis, or ideal-operation assertion
is assumed.
-/

noncomputable section
open Module MvPolynomial

namespace HigherSpecht

theorem ordinaryHarmonics_map_apolar {n s : ℕ}
    (I : Ideal (PolynomialRing n ℂ)) (hI : powerIdeal ℂ n s ≤ I) :
    (ordinaryHarmonics I).map (ordinaryApolarRepresenter n) =
      (I.restrictScalars ℂ).dualAnnihilator := by
  apply le_antisymm
  · rintro L ⟨p, hp, rfl⟩
    exact (Submodule.mem_dualAnnihilator _).mpr
      ((mem_ordinaryHarmonics_iff_apolar I p).mp hp)
  · intro L hL
    have hz : ∀ f ∈ I, L f = 0 := (Submodule.mem_dualAnnihilator L).mp hL
    let p := boundedApolarRepresentative s L
    have hp : p ∈ ordinaryHarmonics I := by
      apply (mem_ordinaryHarmonics_iff_apolar I p).mpr
      intro f hf
      rw [boundedApolarRepresentative_pairing I hI L hz, hz f hf]
    refine ⟨p, hp, ?_⟩
    apply LinearMap.ext
    intro f
    exact boundedApolarRepresentative_pairing I hI L hz f

theorem mem_ideal_iff_all_harmonic_pairings_zero {n s : ℕ}
    (I : Ideal (PolynomialRing n ℂ)) (hI : powerIdeal ℂ n s ≤ I)
    (f : PolynomialRing n ℂ) :
    f ∈ I ↔ ∀ p ∈ ordinaryHarmonics I, ordinaryApolarFunctional p f = 0 := by
  have h := Subspace.dualAnnihilator_dualCoannihilator_eq
    (W := I.restrictScalars ℂ)
  rw [← ordinaryHarmonics_map_apolar I hI] at h
  change f ∈ I.restrictScalars ℂ ↔ _
  rw [← h, Submodule.mem_dualCoannihilator]
  constructor
  · intro hf p hp
    exact hf _ ⟨p, hp, rfl⟩
  · rintro hf L ⟨p, hp, rfl⟩
    exact hf p hp

theorem ordinaryHarmonics_injective_on_powerIdeals {n s : ℕ}
    {I J : Ideal (PolynomialRing n ℂ)}
    (hI : powerIdeal ℂ n s ≤ I) (hJ : powerIdeal ℂ n s ≤ J)
    (h : ordinaryHarmonics I = ordinaryHarmonics J) : I = J := by
  ext f
  rw [mem_ideal_iff_all_harmonic_pairings_zero I hI,
    mem_ideal_iff_all_harmonic_pairings_zero J hJ, h]

theorem ordinaryHarmonics_inf {n s : ℕ}
    (I J : Ideal (PolynomialRing n ℂ))
    (hI : powerIdeal ℂ n s ≤ I) (hJ : powerIdeal ℂ n s ≤ J) :
    ordinaryHarmonics (I ⊓ J) = ordinaryHarmonics I ⊔ ordinaryHarmonics J := by
  apply Submodule.map_injective_of_injective (ordinaryApolarRepresenter_injective n)
  rw [ordinaryHarmonics_map_apolar (I ⊓ J) (le_inf hI hJ),
    Submodule.map_sup, ordinaryHarmonics_map_apolar I hI,
    ordinaryHarmonics_map_apolar J hJ]
  exact Subspace.dualAnnihilator_inf_eq (I.restrictScalars ℂ) (J.restrictScalars ℂ)

theorem finiteDimensional_quotient_of_power_le {n s : ℕ}
    (I : Ideal (PolynomialRing n ℂ)) (hs : 0 < s)
    (hI : powerIdeal ℂ n s ≤ I) :
    FiniteDimensional ℂ (PolynomialRing n ℂ ⧸ I) := by
  letI := finiteDimensional_ordinaryHarmonics_of_power_le hs hI
  letI := Module.Finite.equiv (ordinaryHarmonicQuotientDualEquiv I hI)
  exact (Module.finite_dual_iff ℂ).mp inferInstance

theorem finrank_ordinaryHarmonics_of_power_le {n s : ℕ}
    (I : Ideal (PolynomialRing n ℂ)) (hI : powerIdeal ℂ n s ≤ I) :
    Module.finrank ℂ (ordinaryHarmonics I) =
      Module.finrank ℂ (PolynomialRing n ℂ ⧸ I) := by
  rw [(ordinaryHarmonicQuotientDualEquiv I hI).finrank_eq,
    Subspace.dual_finrank_eq]

end HigherSpecht
end
end CanonicalSource92

section CanonicalSource93
/- Source: HigherSpecht/IndependentSubsumLattice.lean -/



/-!
# Unions and intersections of genuine independent sums

The intersection identity is proved by splitting one index set into its
intersection and difference, using independence to kill the difference,
and applying the modular law.  It applies to arbitrary finite independent
families of submodules, without a selected-coordinate hypothesis.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht

variable {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M] [Finite ι]

def independentSubsum (p : ι → Submodule K M) (S : Set ι) : Submodule K M :=
  ⨆ i ∈ S, p i

theorem independentSubsum_mono (p : ι → Submodule K M) {S T : Set ι}
    (h : S ⊆ T) : independentSubsum p S ≤ independentSubsum p T :=
  iSup₂_le fun i hi => le_iSup_of_le i (le_iSup_of_le (h hi) le_rfl)

@[simp] theorem independentSubsum_union (p : ι → Submodule K M) (S T : Set ι) :
    independentSubsum p (S ∪ T) = independentSubsum p S ⊔ independentSubsum p T := by
  exact iSup_union

theorem independentSubsum_inter (p : ι → Submodule K M) (hp : iSupIndep p)
    (S T : Set ι) :
    independentSubsum p (S ∩ T) = independentSubsum p S ⊓ independentSubsum p T := by
  have hsplit : S = (S ∩ T) ∪ (S \ T) := by ext i; simp
  have hle : independentSubsum p (S ∩ T) ≤ independentSubsum p T :=
    independentSubsum_mono p Set.inter_subset_right
  have hdis : Disjoint (independentSubsum p (S \ T)) (independentSubsum p T) :=
    hp.disjoint_biSup_biSup' (by exact Set.disjoint_sdiff_left) (Set.toFinite _)
  conv_rhs => rw [hsplit, independentSubsum_union]
  rw [sup_inf_assoc_of_le _ hle, hdis.eq_bot, sup_bot_eq]

theorem independentSubsum_injective (p : ι → Submodule K M) (hp : iSupIndep p)
    (hne : ∀ i, p i ≠ ⊥) : Function.Injective (independentSubsum p) := by
  intro S T hST
  apply Set.Subset.antisymm
  · intro i hi
    by_contra hit
    have hle : p i ≤ independentSubsum p S := le_iSup_of_le i (le_iSup_of_le hi le_rfl)
    rw [hST] at hle
    have hd := hp.disjoint_biSup hit
    exact hne i (le_bot_iff.mp ((le_inf le_rfl hle).trans hd.le_bot))
  · intro i hi
    by_contra his
    have hle : p i ≤ independentSubsum p T := le_iSup_of_le i (le_iSup_of_le hi le_rfl)
    rw [← hST] at hle
    have hd := hp.disjoint_biSup his
    exact hne i (le_bot_iff.mp ((le_inf le_rfl hle).trans hd.le_bot))

end HigherSpecht
end
end CanonicalSource93

section CanonicalSource94
/- Source: HigherSpecht/GriffinIdealExpressions.lean -/



/-!
# Actual finite expressions in Griffin ideals

An expression records an allowed partition at each leaf and literal ideal
sums/intersections at each internal node.  Its eligibility set is obtained
by the reversed set operations.  The harmonic equality below is proved
inductively from the actual simultaneous decomposition and finite apolar
duality, and the distributive identities are equalities of ideals.
-/

noncomputable section
open TauCeti Module
open scoped Classical

namespace HigherSpecht

structure BoundedGriffinShape (n s : ℕ) where
  diagram : YoungDiagram
  card_le : diagram.card ≤ n
  height_le : diagram.colLen 0 ≤ s

inductive GriffinIdealExpression (n s : ℕ) where
  | atom : BoundedGriffinShape n s → GriffinIdealExpression n s
  | sum : GriffinIdealExpression n s → GriffinIdealExpression n s → GriffinIdealExpression n s
  | intersection : GriffinIdealExpression n s → GriffinIdealExpression n s → GriffinIdealExpression n s

namespace GriffinIdealExpression

variable {n s : ℕ}

def ideal (R : Type*) [CommRing R] : GriffinIdealExpression n s → Ideal (PolynomialRing n R)
  | .atom a => griffinIdeal R n a.diagram s
  | .sum e f => ideal R e ⊔ ideal R f
  | .intersection e f => ideal R e ⊓ ideal R f

def eligible : GriffinIdealExpression n s → Set (FiniteHarmonicIndex n s)
  | .atom a => {i | i.toUnboundedHarmonicIndex.eligible a.diagram a.card_le}
  | .sum e f => eligible e ∩ eligible f
  | .intersection e f => eligible e ∪ eligible f

theorem powerIdeal_le (R : Type*) [CommRing R] (e : GriffinIdealExpression n s) :
    powerIdeal R n s ≤ e.ideal R := by
  induction e with
  | atom a => exact le_sup_right
  | sum e f he hf => exact he.trans le_sup_left
  | intersection e f he hf => exact le_inf he hf

theorem permutationStable (R : Type*) [CommRing R] (e : GriffinIdealExpression n s) :
    PermutationStable (e.ideal R) := by
  induction e with
  | atom a => exact permutationStable_griffinIdeal a.diagram s
  | sum e f he hf => exact he.sup hf
  | intersection e f he hf => exact he.inf hf

theorem harmonic_decomposition (e : GriffinIdealExpression n s) (hs : 0 < s) :
    ordinaryHarmonics (e.ideal ℂ) =
      independentSubsum (finiteCommonHarmonicCopy (n := n) (s := s)) e.eligible := by
  induction e with
  | atom a =>
      rw [ideal, finiteCommonHarmonic_decomposition_of_specifiedBasis n s
        a.diagram a.card_le hs a.height_le
        (griffin_specifiedBasis ℂ n a.diagram a.card_le s hs a.height_le)]
      exact iSup_subtype
  | sum e f he hf =>
      rw [ideal, ordinaryHarmonics_sup, he, hf]
      exact (independentSubsum_inter _ (finiteCommonHarmonicCopies_iSupIndep hs) _ _).symm
  | intersection e f he hf =>
      rw [ideal, ordinaryHarmonics_inf _ _ (e.powerIdeal_le ℂ) (f.powerIdeal_le ℂ), he, hf]
      exact (independentSubsum_union _ _ _).symm

theorem finiteDimensional (e : GriffinIdealExpression n s) (hs : 0 < s) :
    FiniteDimensional ℂ (PolynomialRing n ℂ ⧸ e.ideal ℂ) :=
  finiteDimensional_quotient_of_power_le (e.ideal ℂ) hs (e.powerIdeal_le ℂ)

abbrev VectorIndex (e : GriffinIdealExpression n s) :=
  Σ i : {i // i ∈ e.eligible}, StandardYoungTableau (YoungDiagram.ofPartition i.val.part)

instance finiteVectorIndex (e : GriffinIdealExpression n s) : Finite e.VectorIndex := by
  unfold VectorIndex
  infer_instance

noncomputable instance fintypeVectorIndex (e : GriffinIdealExpression n s) : Fintype e.VectorIndex :=
  Fintype.ofFinite _

theorem finrank_quotient (e : GriffinIdealExpression n s) (hs : 0 < s) :
    Module.finrank ℂ (PolynomialRing n ℂ ⧸ e.ideal ℂ) = Nat.card e.VectorIndex := by
  letI : ∀ i : {i // i ∈ e.eligible},
      Module.Finite ℂ (finiteCommonHarmonicCopy i.val) :=
    fun i => finite_finiteCommonHarmonicCopy i.val hs
  rw [← finrank_ordinaryHarmonics_of_power_le _ (e.powerIdeal_le ℂ),
    e.harmonic_decomposition hs]
  rw [independentSubsum, ← iSup_subtype'' e.eligible
    (finiteCommonHarmonicCopy (n := n) (s := s))]
  have hi : iSupIndep (fun i : {i // i ∈ e.eligible} =>
      finiteCommonHarmonicCopy (n := n) (s := s) i.val) := by
    simpa only [Function.comp_def] using
      ((finiteCommonHarmonicCopies_iSupIndep (n := n) (s := s) hs).comp
        (f := fun i : {i // i ∈ e.eligible} => i.val) Subtype.val_injective)
  rw [finrank_iSup_of_independent
    (fun i : {i // i ∈ e.eligible} => finiteCommonHarmonicCopy i.val) hi]
  simp_rw [finrank_finiteCommonHarmonicCopy _ hs]
  change (∑ i : {i // i ∈ e.eligible},
      standardCount (YoungDiagram.ofPartition i.val.part)) =
    Nat.card (Σ i : {i // i ∈ e.eligible},
      StandardYoungTableau (YoungDiagram.ofPartition i.val.part))
  rw [Nat.card_sigma]
  simp only [Nat.card_eq_fintype_card, standardCount_def]

theorem ideal_eq_of_eligible_eq (e f : GriffinIdealExpression n s) (hs : 0 < s)
    (h : e.eligible = f.eligible) : e.ideal ℂ = f.ideal ℂ := by
  apply ordinaryHarmonics_injective_on_powerIdeals (e.powerIdeal_le ℂ) (f.powerIdeal_le ℂ)
  rw [e.harmonic_decomposition hs, f.harmonic_decomposition hs, h]

theorem sum_intersection_distributive (a b c : GriffinIdealExpression n s) (hs : 0 < s) :
    a.ideal ℂ ⊔ (b.ideal ℂ ⊓ c.ideal ℂ) =
      (a.ideal ℂ ⊔ b.ideal ℂ) ⊓ (a.ideal ℂ ⊔ c.ideal ℂ) := by
  apply ideal_eq_of_eligible_eq (.sum a (.intersection b c))
    (.intersection (.sum a b) (.sum a c)) hs
  ext i
  simp only [eligible, Set.mem_inter_iff, Set.mem_union]
  tauto

theorem intersection_sum_distributive (a b c : GriffinIdealExpression n s) (hs : 0 < s) :
    a.ideal ℂ ⊓ (b.ideal ℂ ⊔ c.ideal ℂ) =
      (a.ideal ℂ ⊓ b.ideal ℂ) ⊔ (a.ideal ℂ ⊓ c.ideal ℂ) := by
  apply ideal_eq_of_eligible_eq (.intersection a (.sum b c))
    (.sum (.intersection a b) (.intersection a c)) hs
  ext i
  simp only [eligible, Set.mem_inter_iff, Set.mem_union]
  tauto

end GriffinIdealExpression

/-- The generated lattice means the literal range of all finite nonempty
sum/intersection expressions; no ideal is replaced by an index-set object. -/
def generatedGriffinIdealLattice (n s : ℕ) : Set (Ideal (PolynomialRing n ℂ)) :=
  Set.range (GriffinIdealExpression.ideal ℂ (n := n) (s := s))

theorem corollary_5_3_distributive {n s : ℕ} (hs : 0 < s)
    {A B C : Ideal (PolynomialRing n ℂ)}
    (hA : A ∈ generatedGriffinIdealLattice n s)
    (hB : B ∈ generatedGriffinIdealLattice n s)
    (hC : C ∈ generatedGriffinIdealLattice n s) :
    A ⊔ (B ⊓ C) = (A ⊔ B) ⊓ (A ⊔ C) ∧
      A ⊓ (B ⊔ C) = (A ⊓ B) ⊔ (A ⊓ C) := by
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨c, rfl⟩ := hC
  exact ⟨a.sum_intersection_distributive b c hs,
    a.intersection_sum_distributive b c hs⟩

end HigherSpecht
end
end CanonicalSource94

section CanonicalSource95
/- Source: HigherSpecht/GriffinExpressionBases.lean -/



/-!
# The original higher Specht basis for every ideal expression

The vectors here are the original products `F_T^S E_eta`.  A principal
submatrix of the actual common-witness pairing proves fixed-tableau
independence in the literal expression quotient.  Genuine simple-module
evaluation then gives every right tableau and every shape.  Finally the
already proved harmonic decomposition supplies the exact dimension.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial
open scoped Classical

namespace HigherSpecht

def finiteMasterPolynomial {R : Type*} [CommRing R] {n s : ℕ}
    (i : FiniteHarmonicIndex n s)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) : PolynomialRing n R :=
  rename (finCongr (YoungDiagram.card_ofPartition i.part)) (higherSpechtPolynomial i.left T) *
    elementaryMultiplier n n i.multiplier.rowLen

theorem rename_fixedFinitePolynomial {R : Type*} [CommRing R]
    {mu : YoungDiagram} {n s : ℕ} (hn : mu.card = n)
    (T : StandardYoungTableau mu) (i : FixedFiniteHarmonicIndex mu s) :
    rename (finCongr hn) (fixedGriffinPolynomial (R := R) T i) =
      rename (finCongr hn) (higherSpechtPolynomial i.left T) *
        elementaryMultiplier n n i.multiplier.rowLen := by
  subst n
  simp [finCongr_refl, Equiv.coe_refl, rename_id_apply, fixedGriffinPolynomial, YoungDiagram.card]

theorem finiteMasterPolynomial_toFixed {R : Type*} [CommRing R]
    {n s : ℕ} (part : n.Partition)
    (i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s)
    (T : StandardYoungTableau (YoungDiagram.ofPartition part)) :
    finiteMasterPolynomial (R := R) (fixedFiniteToHarmonic part i) T =
      rename (finCongr (YoungDiagram.card_ofPartition part)) (fixedGriffinPolynomial T i) :=
  (rename_fixedFinitePolynomial (YoungDiagram.card_ofPartition part) T i).symm

theorem ordinaryApolar_rename_finCongr {n m : ℕ} (h : n = m)
    (p q : PolynomialRing n ℂ) :
    ordinaryApolarFunctional (rename (finCongr h) p) (rename (finCongr h) q) =
      ordinaryApolarFunctional p q := by
  subst m
  simp only [finCongr_refl, Equiv.coe_refl, rename_id_apply]

theorem finiteMasterPolynomial_isHomogeneous {R : Type*} [CommRing R]
    {n s : ℕ} (i : FiniteHarmonicIndex n s)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    (finiteMasterPolynomial (R := R) i T).IsHomogeneous i.toUnboundedHarmonicIndex.degree :=
  (higherSpechtPolynomial_isHomogeneous i.left T).rename_isHomogeneous.mul
    (elementaryMultiplier_isHomogeneous n n i.multiplier i.multiplier_length)

def finiteMasterIntertwiner {R : Type*} [CommRing R] {n s : ℕ}
    (i : FiniteHarmonicIndex n s) :
    Representation.IntertwiningMap (partitionSpechtRepresentationOver R i.part)
      (polynomialRepresentation R n) :=
  (symmetricMultiplicationIntertwiner (elementaryMultiplier n n i.multiplier.rowLen)
    (elementaryMultiplier_isSymmetric n n i.multiplier.rowLen)).comp
      (partitionHigherSpechtIntertwinerOver i.part i.left)

@[simp] theorem finiteMasterIntertwiner_standard {R : Type*} [CommRing R] {n s : ℕ}
    (i : FiniteHarmonicIndex n s)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    finiteMasterIntertwiner (R := R) i (standardPolytabloidOver T) =
      finiteMasterPolynomial (R := R) i T := by
  change rename (finCongr (YoungDiagram.card_ofPartition i.part))
      (higherSpechtIntertwinerOver (R := R) i.left (standardPolytabloidOver T)) *
        elementaryMultiplier n n i.multiplier.rowLen =
    rename (finCongr (YoungDiagram.card_ofPartition i.part))
      (higherSpechtPolynomial i.left T) * elementaryMultiplier n n i.multiplier.rowLen
  rw [higherSpechtIntertwinerOver_standard]

namespace GriffinIdealExpression

variable {n s : ℕ} (e : GriffinIdealExpression n s)

abbrev FixedIndex (part : n.Partition) :=
  {i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s //
    fixedFiniteToHarmonic part i ∈ e.eligible}

abbrev PartitionVectorIndex :=
  Σ part : n.Partition,
    StandardYoungTableau (YoungDiagram.ofPartition part) × e.FixedIndex part

def partitionVectorEquiv : e.PartitionVectorIndex ≃ e.VectorIndex where
  toFun z := ⟨⟨fixedFiniteToHarmonic z.1 z.2.2.val, z.2.2.property⟩, z.2.1⟩
  invFun z := ⟨z.1.val.part, z.2, ⟨finiteHarmonicToFixed z.1.val, by
    simpa only [show fixedFiniteToHarmonic z.1.val.part (finiteHarmonicToFixed z.1.val) =
      z.1.val from (finiteHarmonicIndexEquiv n s).left_inv z.1.val] using z.1.property⟩⟩
  left_inv z := by rcases z with ⟨part, T, i, hi⟩; cases i; rfl
  right_inv z := by rcases z with ⟨⟨i, hi⟩, T⟩; cases i; rfl

def polynomial (R : Type*) [CommRing R] (z : e.VectorIndex) : PolynomialRing n R :=
  finiteMasterPolynomial z.1.val z.2

def family (R : Type*) [CommRing R] (z : e.VectorIndex) : PolynomialRing n R ⧸ e.ideal R :=
  Ideal.Quotient.mk (e.ideal R) (e.polynomial R z)

def intertwiner (R : Type*) [CommRing R] (i : {i // i ∈ e.eligible}) :
    Representation.IntertwiningMap (partitionSpechtRepresentationOver R i.val.part)
      (quotientRepresentation (e.ideal R) (e.permutationStable R)) :=
  (quotientProjectionIntertwiner (e.ideal R) (e.permutationStable R)).comp
    (finiteMasterIntertwiner i.val)

@[simp] theorem intertwiner_standard (R : Type*) [CommRing R]
    (i : {i // i ∈ e.eligible}) (T : StandardYoungTableau (YoungDiagram.ofPartition i.val.part)) :
    e.intertwiner R i (standardPolytabloidOver T) = e.family R ⟨i, T⟩ := by
  change Ideal.Quotient.mk (e.ideal R)
      (finiteMasterIntertwiner (R := R) i.val (standardPolytabloidOver T)) =
    Ideal.Quotient.mk (e.ideal R) (finiteMasterPolynomial (R := R) i.val T)
  rw [finiteMasterIntertwiner_standard]

theorem commonVector_mem (hs : 0 < s) (i : {i // i ∈ e.eligible}) :
    finiteCommonHarmonicVector i.val ∈ ordinaryHarmonics (e.ideal ℂ) := by
  rw [e.harmonic_decomposition hs]
  have hle : finiteCommonHarmonicCopy i.val ≤
      independentSubsum finiteCommonHarmonicCopy e.eligible :=
    le_iSup_of_le i.val (le_iSup_of_le i.property le_rfl)
  apply hle
  exact Submodule.subset_span ⟨1, by simp [polynomialRepresentation_apply]⟩

def fixedPairing (hs : 0 < s) (part : n.Partition) (i : e.FixedIndex part) :
    Module.Dual ℂ (PolynomialRing n ℂ ⧸ e.ideal ℂ) :=
  ((e.ideal ℂ).restrictScalars ℂ).liftQ
    (ordinaryApolarFunctional (finiteCommonHarmonicVector (fixedFiniteToHarmonic part i.val)))
    ((mem_ordinaryHarmonics_iff_apolar _ _).mp
      (e.commonVector_mem hs ⟨fixedFiniteToHarmonic part i.val, i.property⟩))

theorem fixedPairing_apply (hs : 0 < s) (part : n.Partition)
    (i j : e.FixedIndex part) :
    e.fixedPairing hs part i
      (e.family ℂ ⟨⟨fixedFiniteToHarmonic part j.val, j.property⟩,
        StandardYoungTableau.rowSuperstandard _⟩) =
      fixedCommonPairingScalar (StandardYoungTableau.rowSuperstandard _) i.val *
        fixedCommonWitnessFunctional (StandardYoungTableau.rowSuperstandard _) i.val
          (fixedGriffinPolynomial (StandardYoungTableau.rowSuperstandard _) j.val) := by
  change ordinaryApolarFunctional
      (finiteCommonHarmonicVector (fixedFiniteToHarmonic part i.val))
      (finiteMasterPolynomial (fixedFiniteToHarmonic part j.val)
        (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition part))) = _
  rw [finiteCommonHarmonicVector_toFixed, finiteMasterPolynomial_toFixed,
    ordinaryApolar_rename_finCongr, ordinaryApolar_fixedCommonHarmonicVector]

theorem fixedFamily_linearIndependent (hs : 0 < s) (part : n.Partition) :
    LinearIndependent ℂ (fun i : e.FixedIndex part =>
      e.family ℂ ⟨⟨fixedFiniteToHarmonic part i.val, i.property⟩,
        StandardYoungTableau.rowSuperstandard _⟩) := by
  apply linearIndependent_of_pairing_key
    (fun i => fixedGriffinKey (StandardYoungTableau.rowSuperstandard _) i.val)
    (e.fixedPairing hs part)
  · intro i j hne hkey
    rw [e.fixedPairing_apply,
      fixedCommonWitnessFunctional_offDiagonal _ _ _
        (fun h => hne (Subtype.ext h)) hkey, mul_zero]
  · intro i
    rw [e.fixedPairing_apply]
    exact mul_ne_zero (fixedCommonPairingScalar_ne_zero _ i.val)
      (fixedCommonWitnessFunctional_diagonal_ne_zero _ i.val)

theorem family_linearIndependent (hs : 0 < s) : LinearIndependent ℂ (e.family ℂ) := by
  let sigma (part : n.Partition) := partitionSpechtRepresentationOver ℂ part
  have hfac : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  letI (part : n.Partition) : Representation.IsIrreducible (sigma part) :=
    partitionSpechtRepresentationOver_isIrreducible hfac part
  let a (part : n.Partition) (T : StandardYoungTableau (YoungDiagram.ofPartition part)) :=
    standardPolytabloidOver (R := ℂ) T
  let f (part : n.Partition) (i : e.FixedIndex part) :=
    e.intertwiner ℂ ⟨fixedFiniteToHarmonic part i.val, i.property⟩
  let T0 (part : n.Partition) := StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition part)
  have hstandard (part : n.Partition) (i : e.FixedIndex part)
      (T : StandardYoungTableau (YoungDiagram.ofPartition part)) :
      f part i (a part T) =
        e.family ℂ ⟨⟨fixedFiniteToHarmonic part i.val, i.property⟩, T⟩ :=
    e.intertwiner_standard ℂ ⟨fixedFiniteToHarmonic part i.val, i.property⟩ T
  have hf (part : n.Partition) : LinearIndependent ℂ
      (fun i : e.FixedIndex part => f part i (a part (T0 part))) := by
    have heval :
        (fun i : e.FixedIndex part => f part i (a part (T0 part))) =
        (fun i : e.FixedIndex part =>
          e.family ℂ ⟨⟨fixedFiniteToHarmonic part i.val, i.property⟩, T0 part⟩) :=
      funext (fun i => hstandard part i (T0 part))
    exact Eq.mpr (congrArg
      (fun v : e.FixedIndex part → PolynomialRing n ℂ ⧸ e.ideal ℂ =>
        LinearIndependent ℂ v) heval) (e.fixedFamily_linearIndependent hs part)
  have hall := independent_simple_intertwiner_copies sigma
    (fun i j ⟨h⟩ => partitionSpecht_eq_of_equiv hfac h)
    (quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ)) a f
    (fun part => a part (T0 part))
    (fun part => linearIndependent_standardPolytabloidOver _) hf
  have hfamily :
      (fun z : e.PartitionVectorIndex => f z.1 z.2.2 (a z.1 z.2.1)) =
        e.family ℂ ∘ e.partitionVectorEquiv := by
    funext z
    exact hstandard z.1 z.2.2 z.2.1
  have hindex : LinearIndependent ℂ (e.family ℂ ∘ e.partitionVectorEquiv) :=
    Eq.mp (congrArg
      (fun v : e.PartitionVectorIndex → PolynomialRing n ℂ ⧸ e.ideal ℂ =>
        LinearIndependent ℂ v) hfamily) hall
  exact (linearIndependent_equiv (R := ℂ) e.partitionVectorEquiv).mp hindex

def prescribedBasis (hs : 0 < s) :
    Basis e.VectorIndex ℂ (PolynomialRing n ℂ ⧸ e.ideal ℂ) := by
  letI := e.finiteDimensional hs
  exact basisOfLinearIndependentOfCardEqFinrank' (e.family ℂ)
    (e.family_linearIndependent hs) (by
      rw [e.finrank_quotient hs, Nat.card_eq_fintype_card])

@[simp] theorem prescribedBasis_apply (hs : 0 < s) (z : e.VectorIndex) :
    e.prescribedBasis hs z = e.family ℂ z := by
  simp only [prescribedBasis, coe_basisOfLinearIndependentOfCardEqFinrank']

/-- Original prescribed polynomial basis for every finite nonempty
sum/intersection expression, with exactly its recursively computed index set. -/
theorem corollary_5_3_basis (hs : 0 < s) : IsSpecifiedBasis (R := ℂ) (e.family ℂ) :=
  ⟨e.prescribedBasis hs, e.prescribedBasis_apply hs⟩

end GriffinIdealExpression
end HigherSpecht
end
end CanonicalSource95

section CanonicalSource96
/- Source: HigherSpecht/AlternativeMultiplierBases.lean -/



/-!
# Corollary 4.3 and its simultaneous-ideal version

The scalar witness calculation is promoted through the actual irreducible
Specht representations, including every right tableau.  The dimension used
to finish the basis is the already established dimension of the literal
ideal quotient.  Both the original Griffin index and every sum/intersection
expression retain their exact eligibility conditions.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial Function
open scoped Classical

namespace HigherSpecht

def alternativeMasterPolynomial {n s : ℕ}
    (f : YoungDiagram → PolynomialRing n ℂ) (i : FiniteHarmonicIndex n s)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) : PolynomialRing n ℂ :=
  rename (finCongr (YoungDiagram.card_ofPartition i.part))
    (higherSpechtPolynomial i.left T) * f i.multiplier

def pullMultiplier {n m : ℕ} (h : m = n)
    (f : YoungDiagram → PolynomialRing n ℂ) : YoungDiagram → PolynomialRing m ℂ :=
  fun eta => rename (finCongr h.symm) (f eta)

theorem alternativeMasterPolynomial_toFixed {n s : ℕ}
    (f : YoungDiagram → PolynomialRing n ℂ) (part : n.Partition)
    (i : FixedFiniteHarmonicIndex (YoungDiagram.ofPartition part) s)
    (T : StandardYoungTableau (YoungDiagram.ofPartition part)) :
    alternativeMasterPolynomial f (fixedFiniteToHarmonic part i) T =
      rename (finCongr (YoungDiagram.card_ofPartition part))
        (higherSpechtPolynomial i.left T *
          pullMultiplier (YoungDiagram.card_ofPartition part) f i.multiplier) := by
  change rename (finCongr (YoungDiagram.card_ofPartition part))
      (higherSpechtPolynomial i.left T) * f i.multiplier =
    rename (finCongr (YoungDiagram.card_ofPartition part))
      (higherSpechtPolynomial i.left T *
        pullMultiplier (YoungDiagram.card_ofPartition part) f i.multiplier)
  rw [map_mul]
  apply congrArg (fun p : PolynomialRing n ℂ =>
    rename (finCongr (YoungDiagram.card_ofPartition part))
      (higherSpechtPolynomial i.left T) * p)
  have hcancel {m l : ℕ} (h : m = l) (p : PolynomialRing l ℂ) :
      p = rename (finCongr h) (rename (finCongr h.symm) p) := by
    cases h
    simp only [finCongr_refl, Equiv.coe_refl, rename_id_apply]
  exact hcancel (YoungDiagram.card_ofPartition part) (f i.multiplier)

theorem pullMultiplier_triangular {n m : ℕ} (h : m = n)
    (f : YoungDiagram → PolynomialRing n ℂ)
    (hf : ∀ eta, eta.colLen 0 ≤ n → IsDominanceTriangularMultiplier n eta (f eta))
    (eta : YoungDiagram) (heta : eta.colLen 0 ≤ m) :
    IsDominanceTriangularMultiplier m eta (pullMultiplier h f eta) :=
  (hf eta (heta.trans_eq h)).rename_finCongr h.symm

def alternativeMasterIntertwiner {n s : ℕ}
    (f : YoungDiagram → PolynomialRing n ℂ)
    (hf : ∀ eta, eta.colLen 0 ≤ n → IsDominanceTriangularMultiplier n eta (f eta))
    (i : FiniteHarmonicIndex n s) :
    Representation.IntertwiningMap (partitionSpechtRepresentationOver ℂ i.part)
      (polynomialRepresentation ℂ n) :=
  (symmetricMultiplicationIntertwiner (f i.multiplier)
    (hf i.multiplier i.multiplier_length).isSymmetric).comp
      (partitionHigherSpechtIntertwinerOver i.part i.left)

@[simp] theorem alternativeMasterIntertwiner_standard {n s : ℕ}
    (f : YoungDiagram → PolynomialRing n ℂ)
    (hf : ∀ eta, eta.colLen 0 ≤ n → IsDominanceTriangularMultiplier n eta (f eta))
    (i : FiniteHarmonicIndex n s)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    alternativeMasterIntertwiner f hf i (standardPolytabloidOver T) =
      alternativeMasterPolynomial f i T := by
  change rename (finCongr (YoungDiagram.card_ofPartition i.part))
      (higherSpechtIntertwinerOver (R := ℂ) i.left (standardPolytabloidOver T)) *
        f i.multiplier =
    rename (finCongr (YoungDiagram.card_ofPartition i.part))
      (higherSpechtPolynomial i.left T) * f i.multiplier
  rw [higherSpechtIntertwinerOver_standard]

namespace GriffinIdealExpression

variable {n s : ℕ} (e : GriffinIdealExpression n s)
    (f : YoungDiagram → PolynomialRing n ℂ)
    (hf : ∀ eta, eta.colLen 0 ≤ n → IsDominanceTriangularMultiplier n eta (f eta))

def alternativeFamily (z : e.VectorIndex) : PolynomialRing n ℂ ⧸ e.ideal ℂ :=
  Ideal.Quotient.mk (e.ideal ℂ) (alternativeMasterPolynomial f z.1.val z.2)

def alternativeIntertwiner (i : {i // i ∈ e.eligible}) :
    Representation.IntertwiningMap (partitionSpechtRepresentationOver ℂ i.val.part)
      (quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ)) :=
  (quotientProjectionIntertwiner (e.ideal ℂ) (e.permutationStable ℂ)).comp
    (alternativeMasterIntertwiner f hf i.val)

@[simp] theorem alternativeIntertwiner_standard (i : {i // i ∈ e.eligible})
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.val.part)) :
    e.alternativeIntertwiner f hf i (standardPolytabloidOver T) =
      e.alternativeFamily f ⟨i, T⟩ := by
  change Ideal.Quotient.mk (e.ideal ℂ)
      (alternativeMasterIntertwiner f hf i.val (standardPolytabloidOver T)) =
    Ideal.Quotient.mk (e.ideal ℂ) (alternativeMasterPolynomial f i.val T)
  rw [alternativeMasterIntertwiner_standard]

include hf in
theorem fixedPairing_alternative_apply (hs : 0 < s) (part : n.Partition)
    (i j : e.FixedIndex part) :
    e.fixedPairing hs part i
      (e.alternativeFamily f ⟨⟨fixedFiniteToHarmonic part j.val, j.property⟩,
        StandardYoungTableau.rowSuperstandard _⟩) =
      fixedCommonPairingScalar (StandardYoungTableau.rowSuperstandard _) i.val *
        fixedCommonWitnessFunctional (StandardYoungTableau.rowSuperstandard _) i.val
          (higherSpechtPolynomial j.val.left (StandardYoungTableau.rowSuperstandard _) *
            pullMultiplier (YoungDiagram.card_ofPartition part) f j.val.multiplier) := by
  change ordinaryApolarFunctional
      (finiteCommonHarmonicVector (fixedFiniteToHarmonic part i.val))
      (alternativeMasterPolynomial f (fixedFiniteToHarmonic part j.val)
        (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition part))) = _
  rw [finiteCommonHarmonicVector_toFixed, alternativeMasterPolynomial_toFixed,
    ordinaryApolar_rename_finCongr]
  exact ordinaryApolar_fixedCommon_symmetric _ i.val j.val.left _
    (pullMultiplier_triangular _ f hf _
      (j.val.multiplier_length.trans (Nat.sub_le _ _))).isSymmetric

include hf in
theorem alternativeFixedFamily_linearIndependent (hs : 0 < s) (part : n.Partition) :
    LinearIndependent ℂ (fun i : e.FixedIndex part =>
      e.alternativeFamily f ⟨⟨fixedFiniteToHarmonic part i.val, i.property⟩,
        StandardYoungTableau.rowSuperstandard _⟩) := by
  apply linearIndependent_of_pairing_key
    (fun i => fixedGriffinKey (StandardYoungTableau.rowSuperstandard _) i.val)
    (e.fixedPairing hs part)
  · intro i j hne hkey
    rw [e.fixedPairing_alternative_apply f hf hs part i j,
      alternativeCommonWitness_offDiagonal _ i.val j.val _
        (pullMultiplier_triangular _ f hf _
          (j.val.multiplier_length.trans (Nat.sub_le _ _)))
        (fun h => hne (Subtype.ext h)) hkey, mul_zero]
  · intro i
    rw [e.fixedPairing_alternative_apply f hf hs part i i]
    exact mul_ne_zero (fixedCommonPairingScalar_ne_zero _ i.val)
      (alternativeCommonWitness_diagonal_ne_zero _ i.val _
        (pullMultiplier_triangular _ f hf _
          (i.val.multiplier_length.trans (Nat.sub_le _ _))))

include hf in
theorem alternativeFamily_linearIndependent (hs : 0 < s) :
    LinearIndependent ℂ (e.alternativeFamily f) := by
  let sigma (part : n.Partition) := partitionSpechtRepresentationOver ℂ part
  have hfac : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  letI (part : n.Partition) : Representation.IsIrreducible (sigma part) :=
    partitionSpechtRepresentationOver_isIrreducible hfac part
  let a (part : n.Partition) (T : StandardYoungTableau (YoungDiagram.ofPartition part)) :=
    standardPolytabloidOver (R := ℂ) T
  let F (part : n.Partition) (i : e.FixedIndex part) :=
    e.alternativeIntertwiner f hf ⟨fixedFiniteToHarmonic part i.val, i.property⟩
  let T0 (part : n.Partition) := StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition part)
  have hstandard (part : n.Partition) (i : e.FixedIndex part)
      (T : StandardYoungTableau (YoungDiagram.ofPartition part)) :
      F part i (a part T) =
        e.alternativeFamily f ⟨⟨fixedFiniteToHarmonic part i.val, i.property⟩, T⟩ :=
    e.alternativeIntertwiner_standard f hf ⟨fixedFiniteToHarmonic part i.val, i.property⟩ T
  have hF (part : n.Partition) : LinearIndependent ℂ
      (fun i : e.FixedIndex part => F part i (a part (T0 part))) := by
    have heval :
        (fun i : e.FixedIndex part => F part i (a part (T0 part))) =
        (fun i : e.FixedIndex part =>
          e.alternativeFamily f ⟨⟨fixedFiniteToHarmonic part i.val, i.property⟩, T0 part⟩) :=
      funext (fun i => hstandard part i (T0 part))
    exact Eq.mpr (congrArg
      (fun v : e.FixedIndex part → PolynomialRing n ℂ ⧸ e.ideal ℂ =>
        LinearIndependent ℂ v) heval) (e.alternativeFixedFamily_linearIndependent f hf hs part)
  have hall := independent_simple_intertwiner_copies sigma
    (fun i j ⟨h⟩ => partitionSpecht_eq_of_equiv hfac h)
    (quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ)) a F
    (fun part => a part (T0 part))
    (fun part => linearIndependent_standardPolytabloidOver _) hF
  have hfamily :
      (fun z : e.PartitionVectorIndex => F z.1 z.2.2 (a z.1 z.2.1)) =
        e.alternativeFamily f ∘ e.partitionVectorEquiv := by
    funext z
    exact hstandard z.1 z.2.2 z.2.1
  have hindex : LinearIndependent ℂ (e.alternativeFamily f ∘ e.partitionVectorEquiv) :=
    Eq.mp (congrArg
      (fun v : e.PartitionVectorIndex → PolynomialRing n ℂ ⧸ e.ideal ℂ =>
        LinearIndependent ℂ v) hfamily) hall
  exact (linearIndependent_equiv (R := ℂ) e.partitionVectorEquiv).mp hindex

def alternativeBasis (hs : 0 < s) :
    Basis e.VectorIndex ℂ (PolynomialRing n ℂ ⧸ e.ideal ℂ) := by
  letI := e.finiteDimensional hs
  exact basisOfLinearIndependentOfCardEqFinrank' (e.alternativeFamily f)
    (e.alternativeFamily_linearIndependent f hf hs) (by
      rw [e.finrank_quotient hs, Nat.card_eq_fintype_card])

@[simp] theorem alternativeBasis_apply (hs : 0 < s) (z : e.VectorIndex) :
    e.alternativeBasis f hf hs z = e.alternativeFamily f z := by
  simp only [alternativeBasis, coe_basisOfLinearIndependentOfCardEqFinrank']

include hf in
/-- The alternative multiplier clause for the exact recursively computed
indices of Corollary 5.3. -/
theorem corollary_5_3_alternative_basis (hs : 0 < s) :
    IsSpecifiedBasis (R := ℂ) (e.alternativeFamily f) :=
  ⟨e.alternativeBasis f hf hs, e.alternativeBasis_apply f hf hs⟩

def alternativeCopy (i : {i // i ∈ e.eligible}) :
    Subrepresentation (quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ)) :=
  (e.alternativeIntertwiner f hf i).range

theorem alternativeCopy_eq_span (i : {i // i ∈ e.eligible}) :
    (e.alternativeCopy f hf i).toSubmodule =
      Submodule.span ℂ (Set.range fun T : StandardYoungTableau (YoungDiagram.ofPartition i.val.part) =>
        e.alternativeFamily f ⟨i, T⟩) := by
  change LinearMap.range (e.alternativeIntertwiner f hf i).toLinearMap = _
  rw [linearMap_range_eq_span_standard]
  simp only [Representation.IntertwiningMap.coe_toLinearMap, alternativeIntertwiner_standard]

theorem alternativeIntertwiner_injective (hs : 0 < s) (i : {i // i ∈ e.eligible}) :
    Function.Injective (e.alternativeIntertwiner f hf i) := by
  let B := standardPolytabloidBasisOver ℂ (YoungDiagram.ofPartition i.val.part)
  have h := (e.alternativeBasis f hf hs).linearIndependent.comp
    (fun T : StandardYoungTableau (YoungDiagram.ofPartition i.val.part) =>
      (⟨i, T⟩ : e.VectorIndex)) (fun T U h => eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  have hB : LinearIndependent ℂ (fun T => e.alternativeIntertwiner f hf i (B T)) := by
    simpa only [B, standardPolytabloidBasisOver_apply, alternativeIntertwiner_standard,
      Function.comp_def, alternativeBasis_apply] using h
  intro x y hxy
  apply B.repr.injective
  apply hB.finsuppLinearCombination_injective
  change Finsupp.linearCombination ℂ ((e.alternativeIntertwiner f hf i).toLinearMap ∘ B)
      (B.repr x) = Finsupp.linearCombination ℂ
        ((e.alternativeIntertwiner f hf i).toLinearMap ∘ B) (B.repr y)
  rw [Finsupp.linearCombination_linear_comp, LinearMap.comp_apply,
    LinearMap.comp_apply, B.linearCombination_repr, B.linearCombination_repr]
  exact hxy

/-- The chosen vectors form actual Specht copies, not merely vector-space
bases of the right cardinality. -/
def alternativeSpechtEquiv (hs : 0 < s) (i : {i // i ∈ e.eligible}) :
    Representation.Equiv (partitionSpechtRepresentationOver ℂ i.val.part)
      (e.alternativeCopy f hf i).toRepresentation :=
  (e.alternativeIntertwiner f hf i).equivOfRange
    (e.alternativeIntertwiner_injective f hf hs i) rfl

end GriffinIdealExpression

def alternativeGriffinFamily {n s : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n)
    (f : YoungDiagram → PolynomialRing n ℂ) (i : GriffinIndex n lam hk s) :
    GriffinRing ℂ n lam s :=
  Ideal.Quotient.mk (griffinIdeal ℂ n lam s) (pairPolynomial i.pair * f i.multiplier)

/-- Corollary 4.3 with every original Griffin index and the full literal
dominance-triangular expansion, including non-monic leading coefficients. -/
theorem corollary_4_3 (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s)
    (f : YoungDiagram → PolynomialRing n ℂ)
    (hf : ∀ eta, eta.colLen 0 ≤ n → IsDominanceTriangularMultiplier n eta (f eta)) :
    IsSpecifiedBasis (R := ℂ) (alternativeGriffinFamily (s := s) lam hk f) := by
  let e : GriffinIdealExpression n s := .atom ⟨lam, hk, hheight⟩
  let E : e.VectorIndex ≃ GriffinIndex n lam hk s :=
    eligibleHarmonicTableauEquiv n s lam hk
  let b := (e.alternativeBasis f hf hs).reindex E
  refine ⟨b, ?_⟩
  intro i
  change ((e.alternativeBasis f hf hs).reindex E) i =
    (alternativeGriffinFamily (s := s) lam hk f i : PolynomialRing n ℂ ⧸ e.ideal ℂ)
  refine ((e.alternativeBasis f hf hs).reindex_apply E i).trans
    ((e.alternativeBasis_apply f hf hs (E.symm i)).trans ?_)
  change Ideal.Quotient.mk (griffinIdeal ℂ n lam s)
      (alternativeMasterPolynomial f
        ((eligibleHarmonicTableauEquiv n s lam hk).symm i).1.val
        ((eligibleHarmonicTableauEquiv n s lam hk).symm i).2) = _
  obtain ⟨z, rfl⟩ := (eligibleHarmonicTableauEquiv n s lam hk).surjective i
  have hcancel := congrArg
    (fun w : EligibleHarmonicTableauIndex n s lam hk =>
      Ideal.Quotient.mk (griffinIdeal ℂ n lam s)
        (alternativeMasterPolynomial f w.1.val w.2))
    ((eligibleHarmonicTableauEquiv n s lam hk).symm_apply_apply z)
  exact hcancel.trans (by rfl)

theorem corollary_4_3_monomial (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    IsSpecifiedBasis (R := ℂ) (alternativeGriffinFamily (s := s) lam hk (monomialMultiplier n ℂ)) :=
  corollary_4_3 n lam hk s hs hheight _
    (fun eta _ => monomialMultiplier_isDominanceTriangular n eta)

theorem corollary_4_3_schur (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    IsSpecifiedBasis (R := ℂ) (alternativeGriffinFamily (s := s) lam hk
      (fun eta => TauCeti.schurPoly (Fin n) ℂ (eta.toPartition rfl))) :=
  corollary_4_3 n lam hk s hs hheight _
    (fun eta _ => schurMultiplier_isDominanceTriangular n eta)

end HigherSpecht
end
end CanonicalSource96

section CanonicalSource97
/- Source: HigherSpecht/AlternativeMultiplierEligibility.lean -/



/-!
# Triangularity only at multipliers that actually occur

The manuscript chooses the auxiliary symmetric factors at its admissible
indices.  The earlier simultaneous construction accepts a global family.
This file proves that no condition on unused choices is needed: complete
the family by monomial symmetric polynomials off the literal finite set of
used multipliers, and compare every actual quotient vector pointwise.
-/

noncomputable section
open TauCeti Module MvPolynomial
open scoped Classical

namespace HigherSpecht

def completeTriangularMultipliers {n : ℕ} (A : Set YoungDiagram)
    (f : YoungDiagram → PolynomialRing n ℂ) : YoungDiagram → PolynomialRing n ℂ :=
  fun eta => if eta ∈ A then f eta else monomialMultiplier n ℂ eta

@[simp] theorem completeTriangularMultipliers_apply_of_mem {n : ℕ}
    (A : Set YoungDiagram) (f : YoungDiagram → PolynomialRing n ℂ)
    {eta : YoungDiagram} (heta : eta ∈ A) :
    completeTriangularMultipliers A f eta = f eta := by
  simp only [completeTriangularMultipliers, if_pos heta]

theorem completeTriangularMultipliers_triangular {n : ℕ}
    (A : Set YoungDiagram) (f : YoungDiagram → PolynomialRing n ℂ)
    (hf : ∀ eta ∈ A, IsDominanceTriangularMultiplier n eta (f eta))
    (eta : YoungDiagram) :
    IsDominanceTriangularMultiplier n eta (completeTriangularMultipliers A f eta) := by
  by_cases heta : eta ∈ A
  · rw [completeTriangularMultipliers_apply_of_mem A f heta]
    exact hf eta heta
  · rw [completeTriangularMultipliers, if_neg heta]
    exact monomialMultiplier_isDominanceTriangular n eta

namespace GriffinIdealExpression

variable {n s : ℕ} (e : GriffinIdealExpression n s)

def usedMultipliers : Set YoungDiagram :=
  {eta | ∃ i : FiniteHarmonicIndex n s, i ∈ e.eligible ∧ i.multiplier = eta}

theorem alternativeFamily_complete
    (f : YoungDiagram → PolynomialRing n ℂ) :
    e.alternativeFamily (completeTriangularMultipliers e.usedMultipliers f) =
      e.alternativeFamily f := by
  funext z
  have hz : z.1.val.multiplier ∈ e.usedMultipliers :=
    ⟨z.1.val, z.1.property, rfl⟩
  simp only [alternativeFamily, alternativeMasterPolynomial,
    completeTriangularMultipliers_apply_of_mem _ _ hz]

/-- The simultaneous alternative-multiplier basis needs triangularity only
at the literal eligible indices of the ideal expression. -/
theorem corollary_5_3_alternative_basis_onEligible (hs : 0 < s)
    (f : YoungDiagram → PolynomialRing n ℂ)
    (hf : ∀ i : {i : FiniteHarmonicIndex n s // i ∈ e.eligible},
      IsDominanceTriangularMultiplier n i.val.multiplier (f i.val.multiplier)) :
    IsSpecifiedBasis (R := ℂ) (e.alternativeFamily f) := by
  have hused (eta : YoungDiagram) (heta : eta ∈ e.usedMultipliers) :
      IsDominanceTriangularMultiplier n eta (f eta) := by
    obtain ⟨i, hi, rfl⟩ := heta
    exact hf ⟨i, hi⟩
  have h := e.corollary_5_3_alternative_basis
    (completeTriangularMultipliers e.usedMultipliers f)
    (fun eta _ => completeTriangularMultipliers_triangular e.usedMultipliers f hused eta) hs
  rw [e.alternativeFamily_complete f] at h
  exact h

end GriffinIdealExpression

/-- Corollary 4.3 without hypotheses on any auxiliary polynomial unused by
the actual Griffin family.  All original indices and representatives remain
unchanged, including their exact rectangle and prefix conditions. -/
theorem corollary_4_3_on_admissible_multipliers
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s)
    (f : YoungDiagram → PolynomialRing n ℂ)
    (hf : ∀ i : GriffinIndex n lam hk s,
      IsDominanceTriangularMultiplier n i.multiplier (f i.multiplier)) :
    IsSpecifiedBasis (R := ℂ) (alternativeGriffinFamily (s := s) lam hk f) := by
  let A : Set YoungDiagram := {eta | ∃ i : GriffinIndex n lam hk s, i.multiplier = eta}
  have hused (eta : YoungDiagram) (heta : eta ∈ A) :
      IsDominanceTriangularMultiplier n eta (f eta) := by
    obtain ⟨i, rfl⟩ := heta
    exact hf i
  have h := corollary_4_3 n lam hk s hs hheight (completeTriangularMultipliers A f)
    (fun eta _ => completeTriangularMultipliers_triangular A f hused eta)
  have hfamily :
      alternativeGriffinFamily (s := s) lam hk (completeTriangularMultipliers A f) =
        alternativeGriffinFamily (s := s) lam hk f := by
    funext i
    have hi : i.multiplier ∈ A := ⟨i, rfl⟩
    simp only [alternativeGriffinFamily, completeTriangularMultipliers_apply_of_mem A f hi]
  rw [hfamily] at h
  exact h

end HigherSpecht
end
end CanonicalSource97

section CanonicalSource98
/- Source: HigherSpecht/AlternativeMultiplierCopies.lean -/



/-!
# Literal alternative-multiplier Specht copies

The only multiplier hypotheses are those at the actual eligible indices.
Complete the unused factors by monomial symmetric polynomials, use the
already constructed equivariant maps, and prove that their ranges are the
spans of the original, unchanged vectors. Every final conclusion includes
that literal span equality together with an actual Specht equivalence and
irreducibility.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial
open scoped Classical

namespace HigherSpecht
namespace GriffinIdealExpression

variable {n s : ℕ} (e : GriffinIdealExpression n s)
    (f : YoungDiagram → PolynomialRing n ℂ)
    (hf : ∀ i : {i : FiniteHarmonicIndex n s // i ∈ e.eligible},
      IsDominanceTriangularMultiplier n i.val.multiplier (f i.val.multiplier))

include hf in
theorem usedMultiplierCompletion_triangular (eta : YoungDiagram) (_heta : eta.colLen 0 ≤ n) :
    IsDominanceTriangularMultiplier n eta
      (completeTriangularMultipliers e.usedMultipliers f eta) := by
  apply completeTriangularMultipliers_triangular
  intro z hz
  obtain ⟨i, hi, rfl⟩ := hz
  exact hf ⟨i, hi⟩

/-- The actual range of the completed-family map. Its literal original-vector
span is proved below, so the completion imposes no condition on unused values. -/
def alternativeCopyOnEligible
    (i : {i : FiniteHarmonicIndex n s // i ∈ e.eligible}) :
    Subrepresentation (quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ)) :=
  e.alternativeCopy (completeTriangularMultipliers e.usedMultipliers f)
    (e.usedMultiplierCompletion_triangular f hf) i

theorem alternativeCopyOnEligible_eq_span
    (i : {i : FiniteHarmonicIndex n s // i ∈ e.eligible}) :
    (e.alternativeCopyOnEligible f hf i).toSubmodule =
      Submodule.span ℂ (Set.range fun T : StandardYoungTableau (YoungDiagram.ofPartition i.val.part) =>
        e.alternativeFamily f ⟨i, T⟩) := by
  change (e.alternativeCopy (completeTriangularMultipliers e.usedMultipliers f)
    (e.usedMultiplierCompletion_triangular f hf) i).toSubmodule = _
  rw [e.alternativeCopy_eq_span, e.alternativeFamily_complete]

def alternativeCopyOnEligibleSpechtEquiv (hs : 0 < s)
    (i : {i : FiniteHarmonicIndex n s // i ∈ e.eligible}) :
    Representation.Equiv (partitionSpechtRepresentationOver ℂ i.val.part)
      (e.alternativeCopyOnEligible f hf i).toRepresentation :=
  e.alternativeSpechtEquiv (completeTriangularMultipliers e.usedMultipliers f)
    (e.usedMultiplierCompletion_triangular f hf) hs i

/-- The higher-Specht-copy clause for the literal alternative vectors in
every finite nonempty ideal expression, with only eligible hypotheses. -/
theorem corollary_5_3_alternative_copy_onEligible (hs : 0 < s)
    (i : {i : FiniteHarmonicIndex n s // i ∈ e.eligible}) :
    (e.alternativeCopyOnEligible f hf i).toSubmodule =
        Submodule.span ℂ (Set.range fun T : StandardYoungTableau (YoungDiagram.ofPartition i.val.part) =>
          e.alternativeFamily f ⟨i, T⟩) ∧
      (e.alternativeCopyOnEligible f hf i).toRepresentation.IsIrreducible ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver ℂ i.val.part)
        (e.alternativeCopyOnEligible f hf i).toRepresentation) := by
  have hfac : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  letI := partitionSpechtRepresentationOver_isIrreducible hfac i.val.part
  let E := e.alternativeCopyOnEligibleSpechtEquiv f hf hs i
  exact ⟨e.alternativeCopyOnEligible_eq_span f hf i,
    irreducible_of_representation_equiv E, ⟨E⟩⟩

end GriffinIdealExpression

/-- The exact fixed-`(S,eta)` copy clause in Corollary 4.3. The subspace in
the conclusion is the span of the manuscript's original alternative products,
and triangularity is required only for the original Griffin indices. -/
theorem corollary_4_3_copy_on_admissible_multipliers
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s)
    (f : YoungDiagram → PolynomialRing n ℂ)
    (hf : ∀ z : GriffinIndex n lam hk s,
      IsDominanceTriangularMultiplier n z.multiplier (f z.multiplier))
    (part : n.Partition) (i : PartitionGriffinCopies n lam hk s part) :
    ∃ W : Subrepresentation (griffinRepresentation ℂ n lam s),
      W.toSubmodule =
        Submodule.span ℂ (Set.range fun T : StandardYoungTableau (YoungDiagram.ofPartition part) =>
          Ideal.Quotient.mk (griffinIdeal ℂ n lam s)
            (rename (finCongr (YoungDiagram.card_ofPartition part))
              (higherSpechtPolynomial i.left T) * f i.multiplier)) ∧
      W.toRepresentation.IsIrreducible ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver ℂ part) W.toRepresentation) := by
  let e : GriffinIdealExpression n s := .atom ⟨lam, hk, hheight⟩
  have hfe : ∀ j : {j : FiniteHarmonicIndex n s // j ∈ e.eligible},
      IsDominanceTriangularMultiplier n j.val.multiplier (f j.val.multiplier) := by
    intro j
    let T := StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition j.val.part)
    let z : GriffinIndex n lam hk s :=
      eligibleHarmonicTableauEquiv n s lam hk ⟨⟨j.val, j.property⟩, T⟩
    have hz : z.multiplier = j.val.multiplier := rfl
    simpa only [hz] using hf z
  let j : FiniteHarmonicIndex n s :=
    { part := part
      left := i.left
      multiplier := i.multiplier
      multiplier_length := by
        have h := i.multiplier_length.trans (Nat.sub_le _ _)
        simpa only [YoungDiagram.card_ofPartition] using h
      descents_lt := i.descents_lt
      multiplier_width := i.multiplier_width }
  have hj : j ∈ e.eligible :=
    ⟨by simpa only [YoungDiagram.card_ofPartition] using i.multiplier_length,
      i.eligible⟩
  have hcopy := e.corollary_5_3_alternative_copy_onEligible f hfe hs ⟨j, hj⟩
  refine ⟨e.alternativeCopyOnEligible f hfe ⟨j, hj⟩, ?_, hcopy.2⟩
  exact hcopy.1

end HigherSpecht
end
end CanonicalSource98
