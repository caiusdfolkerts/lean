module
public import gram_foundation
public import schur_theory

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# A genuine symmetric bitableau basis in every characteristic

Each tableau represents the product of minors formed from adjacent columns.
The Gram leading exponent is precisely its row-count exponent.  These
exponents distinguish all tableaux, so the products are independent over
every field.  The actual paired-insertion bijection counts the degree pieces
and proves that this independent family spans the entire coordinate ring.
-/

noncomputable section
namespace FourPapers.Symmetric.Gram
open Finset Finsupp MvPolynomial
open Schur
open CommAlg.RealWeight
open scoped BigOperators MonomialOrder
universe u

/-- The purely combinatorial minor exponent agrees with the Gram determinant exponent. -/
theorem minorRowExponent_toLex {n : ℕ} (δ : MinorData n) :
    Finsupp.mapDomain toLex (minorRowExponent δ) =
      minorExponent (minorData_size_le δ) δ.rows δ.cols := by
  simp only [minorRowExponent, Finsupp.mapDomain_add, Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_single, minorExponent, diagonalExponent, assignmentExponent,
    firstColumns]

theorem bitableauLexExponent_eq_sum {n : ℕ} (T : EvenSemistandardTableaux n) :
    bitableauLexExponent T = ∑ j : Fin (columnPairCount T),
      minorExponent (minorData_size_le (bitableauMinor T j))
        (bitableauMinor T j).rows (bitableauMinor T j).cols := by
  simp only [bitableauLexExponent, bitableauRowExponent,
    Finsupp.mapDomain_finsetSum, minorRowExponent_toLex]

/-- The Gram image of every actual paired-minor product is monic. -/
theorem hom_bitableau_monic {n : ℕ} (R : Type u) [CommRing R]
    (T : EvenSemistandardTableaux n) :
    (order n).Monic (hom n R (bitableauPolynomial R T)) := by
  classical
  rw [bitableauPolynomial, map_prod]
  apply Finset.prod_induction
  · intro f g hf hg
    exact hf.mul hg
  · exact (order n).monic_one
  · intro j _
    exact hom_minor_monic R (minorData_size_le (bitableauMinor T j))
      (bitableauMinor T j).rows (bitableauMinor T j).cols

/-- Its leading exponent is the independently defined tableau row-count exponent. -/
theorem hom_bitableau_degree {n : ℕ} (K : Type u) [Field K]
    (T : EvenSemistandardTableaux n) :
    (order n).degree (hom n K (bitableauPolynomial K T)) = bitableauLexExponent T := by
  classical
  rw [bitableauPolynomial, map_prod]
  simp only [MinorData.polynomial]
  rw [(order n).degree_prod (fun j _ =>
    (hom_minor_monic K (minorData_size_le (bitableauMinor T j))
      (bitableauMinor T j).rows (bitableauMinor T j).cols).ne_zero)]
  rw [bitableauLexExponent_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact hom_minor_degree K (minorData_size_le (bitableauMinor T j))
    (bitableauMinor T j).rows (bitableauMinor T j).cols

theorem hom_bitableau_degree_injective (n : ℕ) (K : Type u) [Field K] :
    Function.Injective (fun T : EvenSemistandardTableaux n =>
      (order n).degree (hom n K (bitableauPolynomial K T))) := by
  simpa only [hom_bitableau_degree] using @bitableauLexExponent_injective n

/-- Linear independence of actual determinant products over every field. -/
theorem bitableau_linearIndependent (n : ℕ) (K : Type u) [Field K] :
    LinearIndependent K (bitableauPolynomial (n := n) K) := by
  apply LinearIndependent.of_comp (hom n K).toLinearMap
  exact linearIndependent_of_distinct_monic (order n)
    (fun T => hom n K (bitableauPolynomial K T))
    (hom_bitableau_monic K) (hom_bitableau_degree_injective n K)

theorem degreeBitableau_linearIndependent (n d : ℕ) (K : Type u) [Field K] :
    LinearIndependent K (degreeBitableau (n := n) (d := d) K) := by
  apply LinearIndependent.of_comp (homogeneousSubmodule (Entry n) K d).subtype
  exact (bitableau_linearIndependent n K).comp Subtype.val Subtype.val_injective

/-- The complete basis of the homogeneous degree piece. -/
def homogeneousBitableauBasis (n d : ℕ) (K : Type u) [Field K] :
    Module.Basis (DegreeTableaux n d) K (homogeneousSubmodule (Entry n) K d) :=
  degreeTableauBasis n d K (degreeBitableau K) (degreeBitableau_linearIndependent n d K)

@[simp] theorem homogeneousBitableauBasis_apply (n d : ℕ) (K : Type u) [Field K]
    (T : DegreeTableaux n d) :
    homogeneousBitableauBasis n d K T = degreeBitableau K T := by
  simp only [homogeneousBitableauBasis, degreeTableauBasis_apply]

private theorem homogeneous_mem_bitableau_span {n d : ℕ} (K : Type u) [Field K]
    (f : CoordinateRing n K) (hf : f ∈ homogeneousSubmodule (Entry n) K d) :
    f ∈ Submodule.span K (Set.range (bitableauPolynomial (n := n) K)) := by
  classical
  let B := homogeneousBitableauBasis n d K
  let x : homogeneousSubmodule (Entry n) K d := ⟨f,hf⟩
  have hs := congrArg (fun y : homogeneousSubmodule (Entry n) K d => y.val)
    (B.linearCombination_repr x)
  have he : (B.repr x).sum (fun T c => c • bitableauPolynomial K T.val) = f := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul,
      B, homogeneousBitableauBasis_apply, degreeBitableau, x] using hs
  rw [← he]
  apply Submodule.sum_mem
  intro T _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨T.val,rfl⟩

/-- Degreewise counting and homogeneous decomposition prove full spanning. -/
theorem bitableau_span (n : ℕ) (K : Type u) [Field K] :
    Submodule.span K (Set.range (bitableauPolynomial (n := n) K)) = ⊤ := by
  apply top_unique
  intro f _
  rw [← sum_homogeneousComponent f]
  apply Submodule.sum_mem
  intro d _
  exact homogeneous_mem_bitableau_span K _ (homogeneousComponent_mem d f)

/-- A basis of the full symmetric coordinate ring, with genuine minor products as vectors. -/
def bitableauBasis (n : ℕ) (K : Type u) [Field K] :
    Module.Basis (EvenSemistandardTableaux n) K (CoordinateRing n K) :=
  Module.Basis.mk (bitableau_linearIndependent n K) (bitableau_span n K).ge

@[simp] theorem bitableauBasis_apply (n : ℕ) (K : Type u) [Field K]
    (T : EvenSemistandardTableaux n) :
    bitableauBasis n K T = bitableauPolynomial K T :=
  Module.Basis.mk_apply _ _ _

/-- The full symbolic score of the tableau's actual minor-size partition. -/
def tableauScore {n : ℕ} (T : EvenSemistandardTableaux n) (j : Fin n) : ℕ :=
  ((tableauHalfShape T).rowLens.drop j.val).sum

def tableauWeight {n : ℕ} (w : Fin n → ℝ) (T : EvenSemistandardTableaux n) : ℝ :=
  2 * ∑ j, w j * (tableauScore T j : ℕ)

theorem sum_minorWeights {n : ℕ} (w : Fin n → ℝ) (T : EvenSemistandardTableaux n) :
    (∑ i : Fin (columnPairCount T),
      2 * ∑ j : Fin n, w j * ((bitableauMinor T i).size - j.val : ℕ)) = tableauWeight w T := by
  classical
  rw [← Finset.mul_sum, Finset.sum_comm]
  unfold tableauWeight
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum, ← Nat.cast_sum]
  congr 2
  have hs := bitableau_minor_score T (j.val+1) (Nat.succ_pos _)
  simpa only [tableauScore, Nat.add_sub_add_right, Nat.add_sub_cancel] using hs

private theorem gram_bound_prod {V R ι : Type*} [DecidableEq V] [CommRing R]
    (w : V → ℝ) (s : Finset ι) (c : ι → ℝ) (p : ι → MvPolynomial V R)
    (hp : ∀ i ∈ s, Bound w (c i) (p i)) :
    Bound w (∑ i ∈ s, c i) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bound_one w
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem hom_bitableau_bound {n : ℕ} (K : Type u) [Field K]
    (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (T : EvenSemistandardTableaux n) :
    Bound (weight w) (tableauWeight w T) (hom n K (bitableauPolynomial K T)) := by
  classical
  rw [bitableauPolynomial, map_prod, ← sum_minorWeights]
  apply gram_bound_prod
  intro j _
  exact hom_minor_bound K (bitableauMinor T j).rows (bitableauMinor T j).cols w hw

theorem hom_bitableau_leading_weight {n : ℕ} (K : Type u) [Field K]
    (w : Fin n → ℝ) (T : EvenSemistandardTableaux n) :
    Finsupp.weight (weight w) ((order n).degree
      (hom n K (bitableauPolynomial K T))) = tableauWeight w T := by
  rw [hom_bitableau_degree, bitableauLexExponent_eq_sum, map_sum]
  simp_rw [minorExponent_weight]
  exact sum_minorWeights w T

/-- Exact Gram-weight support formula for the actual basis of the original ring. -/
theorem bound_hom_iff_basis_support (n : ℕ) (K : Type u) [Field K]
    (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (f : CoordinateRing n K) (c : ℝ) :
    Bound (weight w) c (hom n K f) ↔
      ∀ T, (bitableauBasis n K).repr f T ≠ 0 → c ≤ tableauWeight w T := by
  classical
  let B := bitableauBasis n K
  have he : hom n K f = ∑ T ∈ (B.repr f).support,
      (B.repr f T) • hom n K (bitableauPolynomial K T) := by
    conv_lhs => rw [← B.linearCombination_repr f]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
      B, bitableauBasis_apply]
  rw [he, bound_sum_iff_of_distinct_monic (order n)
    (fun T => hom n K (bitableauPolynomial K T))
    (hom_bitableau_monic K) (hom_bitableau_degree_injective n K)
    (weight w) (tableauWeight w) (hom_bitableau_bound K w hw)
    (hom_bitableau_leading_weight K w)]
  constructor
  · intro h T hT
    exact h T (Finsupp.mem_support_iff.mpr hT) hT
  · intro h T _ hT
    exact h T hT

end FourPapers.Symmetric.Gram
end

#print axioms FourPapers.Symmetric.Gram.bitableauBasis
#print axioms FourPapers.Symmetric.Gram.bound_hom_iff_basis_support
