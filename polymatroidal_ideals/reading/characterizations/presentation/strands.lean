import Characterizations.Resolution.HomogeneousFree
import Characterizations.ExchangeGraph
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # The actual multigraded strands of the canonical monomial presentation -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Presentation
open Classical Finset MvPolynomial CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k]

abbrev Generators (B : Family V) := {b // b ∈ B}
abbrev Free (B : Family V) := Generators B → MvPolynomial V k

/-- The canonical augmentation of the actual free polynomial module. -/
def augmentation (B : Family V) : Free (k := k) B →ₗ[MvPolynomial V k] MvPolynomial V k :=
  Fintype.linearCombination _ (fun b : Generators B => monomial b.val 1)

@[simp] theorem augmentation_apply (B : Family V) (x : Free (k := k) B) :
    augmentation B x = ∑ b, x b * monomial b.val 1 := by
  simp [augmentation, Fintype.linearCombination_apply, smul_eq_mul]

/-- The coefficient of the generator-labelled basis monomial of multidegree `C`. -/
def strandCoefficient (B : Family V) (C : Exponent V) (x : Free (k := k) B)
    (b : Generators B) : k := if b.val ≤ C then (x b).coeff (C - b.val) else 0

/-- Projection of a genuine polynomial vector onto one multidegree, with the
basis vector labelled `b` carrying its natural degree `b`. -/
def strand (B : Family V) (C : Exponent V) (x : Free (k := k) B) : Free (k := k) B :=
  fun b => monomial (C - b.val) (strandCoefficient B C x b)

@[simp] theorem strandCoefficient_add (B : Family V) (C : Exponent V)
    (x y : Free (k := k) B) :
    strandCoefficient B C (x + y) = strandCoefficient B C x + strandCoefficient B C y := by
  funext b
  by_cases h : b.val ≤ C <;> simp [strandCoefficient, h]

@[simp] theorem strandCoefficient_sub (B : Family V) (C : Exponent V)
    (x y : Free (k := k) B) :
    strandCoefficient B C (x - y) = strandCoefficient B C x - strandCoefficient B C y := by
  funext b
  by_cases h : b.val ≤ C <;> simp [strandCoefficient, h]

@[simp] theorem strandCoefficient_zero (B : Family V) (C : Exponent V) :
    strandCoefficient B C (0 : Free (k := k) B) = 0 := by
  funext b
  simp [strandCoefficient]

@[simp] theorem strandCoefficient_smul (B : Family V) (C : Exponent V) (c : k)
    (x : Free (k := k) B) : strandCoefficient B C (c • x) = c • strandCoefficient B C x := by
  funext b
  by_cases h : b.val ≤ C <;> simp [strandCoefficient, h]

lemma augmentation_coeff (B : Family V) (C : Exponent V) (x : Free (k := k) B) :
    (augmentation B x).coeff C = ∑ b, strandCoefficient B C x b := by
  simp [augmentation_apply, coeff_mul_monomial', strandCoefficient]

lemma strandCoefficient_sum_zero {B : Family V} {x : Free (k := k) B}
    (hx : x ∈ LinearMap.ker (augmentation B)) (C : Exponent V) :
    ∑ b, strandCoefficient B C x b = 0 := by
  rw [← augmentation_coeff, LinearMap.mem_ker.mp hx]
  simp

lemma strand_augmentation (B : Family V) (C : Exponent V) (x : Free (k := k) B) :
    augmentation B (strand B C x) = monomial C (∑ b, strandCoefficient B C x b) := by
  rw [augmentation_apply, map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : b.val ≤ C
  · simp [strand, strandCoefficient, h, monomial_mul_monomial, tsub_add_cancel_of_le h]
  · simp [strand, strandCoefficient, h]

lemma strand_mem_ker {B : Family V} {x : Free (k := k) B}
    (hx : x ∈ LinearMap.ker (augmentation B)) (C : Exponent V) :
    strand B C x ∈ LinearMap.ker (augmentation B) := by
  apply LinearMap.mem_ker.mpr
  rw [strand_augmentation, strandCoefficient_sum_zero hx]
  simp

/-- The finite set of multidegrees occurring in an actual polynomial vector. -/
def support (B : Family V) (x : Free (k := k) B) : Finset (Exponent V) :=
  univ.biUnion (fun b => (x b).support.image (fun a => a + b.val))

lemma degree_mem_support {B : Family V} (x : Free (k := k) B) (b : Generators B)
    (a : Exponent V) (ha : (x b).coeff a ≠ 0) : a + b.val ∈ support B x := by
  exact mem_biUnion.mpr ⟨b, mem_univ _, mem_image.mpr ⟨a, mem_support_iff.mpr ha, rfl⟩⟩

lemma strand_coeff (B : Family V) (C : Exponent V) (x : Free (k := k) B)
    (b : Generators B) (a : Exponent V) :
    (strand B C x b).coeff a = if C = a + b.val then (x b).coeff a else 0 := by
  by_cases h : b.val ≤ C
  · have he : C - b.val = a ↔ C = a + b.val := by
      constructor
      · intro he
        rw [← he, tsub_add_cancel_of_le h]
      · intro he
        rw [he, add_tsub_cancel_right]
    by_cases hC : C = a + b.val
    · subst C; simp [strand, strandCoefficient, add_tsub_cancel_right]
    · simp [strand, strandCoefficient, h, coeff_monomial, he, hC]
  · have he : C ≠ a + b.val := by
      intro he
      exact h (he ▸ le_add_left le_rfl)
    simp [strand, strandCoefficient, h, he]

/-- Finite multigraded decomposition in the original free module. -/
lemma sum_strand (B : Family V) (x : Free (k := k) B) :
    ∑ C ∈ support B x, strand B C x = x := by
  funext b
  apply MvPolynomial.ext
  intro a
  simp only [Finset.sum_apply, coeff_sum, strand_coeff]
  by_cases h : a + b.val ∈ support B x
  · simp [h]
  · have hz : (x b).coeff a = 0 := by
      by_contra hn
      exact h (degree_mem_support x b a hn)
    simp [h, hz]

/-- A genuine binomial syzygy between two canonical generators, at their lcm. -/
def pairSyzygy (B : Family V) (a b : Generators B) : Free (k := k) B :=
  Pi.single a (monomial ((a.val ⊔ b.val) - a.val) 1) -
    Pi.single b (monomial ((a.val ⊔ b.val) - b.val) 1)

lemma augmentation_single (B : Family V) (b : Generators B) (p : MvPolynomial V k) :
    augmentation B (Pi.single b p) = p * monomial b.val 1 := by
  simp [augmentation_apply, Pi.single_apply]

lemma pairSyzygy_mem_ker (B : Family V) (a b : Generators B) :
    pairSyzygy (k := k) B a b ∈ LinearMap.ker (augmentation B) := by
  apply LinearMap.mem_ker.mpr
  rw [pairSyzygy, map_sub, augmentation_single, augmentation_single,
    monomial_mul_monomial, monomial_mul_monomial,
    tsub_add_cancel_of_le le_sup_left, tsub_add_cancel_of_le le_sup_right, sub_self]

/-- The conventional algebraic definition: the first syzygy module of the
canonical minimal generator presentation is generated by linear forms. -/
def HasLinearPresentation (B : Family V) : Prop :=
  LinearMap.ker (augmentation (k := k) B) ≤
    Submodule.span (MvPolynomial V k)
      {x | x ∈ LinearMap.ker (augmentation B) ∧ Resolution.IsHomogeneousVector x 1}

end Characterizations.Presentation
