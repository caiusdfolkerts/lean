module

public import sunlet.dimension_lower_bound
public import sunlet.dimension_upper_bound
public import sunlet.latin_split
public import sunlet.generated_action
public import sunlet.group_coordinates

/-!
# The full dimension theorems in the supplied sunlet paper

The dimension is ordinary Krull dimension of the coordinate ring of the actual
algebraic image closure. Every characteristic is allowed. The final group
statement uses all six independent Fourier parameter families and the original
constraint `a + b + c = 0` on the coordinate indices.
-/

@[expose] public section
noncomputable section

namespace Sunlet

variable {K ι Ω : Type*} [Field K] [Fintype ι] [Fintype Ω]
  [DecidableEq ι] [DecidableEq Ω]

/-- Exact hypotheses of the two transitive color families in Theorem 2.3. -/
structure TransitiveColorSplit (π : ι → Equiv.Perm Ω) (e : ι) where
  positive : Finset ι
  negative : Finset ι
  disjoint : Disjoint positive negative
  partition : positive ∪ negative = Finset.univ.erase e
  positive_card : 2 ≤ positive.card
  negative_card : 2 ≤ negative.card
  positive_transitive : TransitiveFamily π (positive : Set ι)
  negative_transitive : TransitiveFamily π (negative : Set ι)

namespace TransitiveColorSplit

variable {π : ι → Equiv.Perm Ω} {e : ι} (S : TransitiveColorSplit π e)

theorem positive_ne (a : ι) (ha : a ∈ S.positive) : a ≠ e := by
  have hm : a ∈ S.positive ∪ S.negative := Finset.mem_union_left _ ha
  rw [S.partition] at hm
  exact (Finset.mem_erase.mp hm).1

theorem negative_ne (a : ι) (ha : a ∈ S.negative) : a ≠ e := by
  have hm : a ∈ S.positive ∪ S.negative := Finset.mem_union_right _ ha
  rw [S.partition] at hm
  exact (Finset.mem_erase.mp hm).1

theorem positive_two (hπ : Function.Injective π) :
    ∃ a ∈ (S.positive : Set ι), ∃ b ∈ (S.positive : Set ι), π a ≠ π b := by
  have := S.positive_card
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < S.positive.card by omega)
  exact ⟨a, ha, b, hb, fun h => hab (hπ h)⟩

theorem negative_two (hπ : Function.Injective π) :
    ∃ a ∈ (S.negative : Set ι), ∃ b ∈ (S.negative : Set ι), π a ≠ π b := by
  have := S.negative_card
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < S.negative.card by omega)
  exact ⟨a, ha, b, hb, fun h => hab (hπ h)⟩

end TransitiveColorSplit

/-- Theorem 2.3 at the level of polynomial coordinate algebras, valid over every field. -/
theorem coordinateRing_dimension_of_transitive_split
    (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω)
    (he : π e = Equiv.refl Ω) (hπ : Function.Injective π)
    (hder : ∀ a, a ≠ e → ∀ b, π a b ≠ b)
    (S : TransitiveColorSplit π e) :
    ringKrullDim (MvPolynomial (ι × Ω) K ⧸
      PolynomialImage.definingIdeal (coordinatePolynomial (K := K) π)) =
        (3 * Fintype.card Ω + 2 * Fintype.card {a : ι // a ≠ e} - 2 : ℕ) := by
  classical
  have hnonid : Fintype.card {a : ι // a ≠ e} = Fintype.card ι - 1 := by
    simpa only [Fintype.card_subtype_eq] using Fintype.card_subtype_compl (fun a : ι => a = e)
  have hi : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨e⟩
  have hm : 0 < Fintype.card Ω := Fintype.card_pos_iff.mpr ⟨o⟩
  have heP : e ∉ (S.positive : Set ι) := fun h => S.positive_ne e h rfl
  have hdis : Disjoint (S.positive : Set ι) (S.negative : Set ι) := by
    exact_mod_cast S.disjoint
  apply le_antisymm
  · exact Normalization.coordinateRing_dimension_le (o := o) π he
  · have h := DimensionLowerBound.coordinateRing_dimension_ge (K := K)
      π e o S.positive S.negative he heP hdis hder
      S.positive_ne S.negative_ne (S.positive_two hπ) (S.negative_two hπ)
      S.positive_transitive S.negative_transitive
    have hn : 3 * Fintype.card Ω + 2 * Fintype.card ι - 4 =
        3 * Fintype.card Ω + 2 * Fintype.card {a : ι // a ≠ e} - 2 := by omega
    simpa only [hn] using h

/-- Theorem 2.3 for the actual algebraic image closure, with every characteristic allowed. -/
theorem paper_theorem_2_3 [IsAlgClosed K]
    (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω)
    (he : π e = Equiv.refl Ω) (hπ : Function.Injective π)
    (hder : ∀ a, a ≠ e → ∀ b, π a b ≠ b)
    (S : TransitiveColorSplit π e) :
    ringKrullDim (MvPolynomial (ι × Ω) K ⧸
      MvPolynomial.vanishingIdeal K (imageClosure (K := K) π)) =
        (3 * Fintype.card Ω + 2 * Fintype.card {a : ι // a ≠ e} - 2 : ℕ) := by
  rw [imageClosure, PolynomialImage.vanishingIdeal_imageClosure]
  exact coordinateRing_dimension_of_transitive_split π e o he hπ hder S

/-- Theorem 1.1: every normalized Latin system of every order at least five. -/
theorem paper_theorem_1_1 [IsAlgClosed K]
    (L : NormalizedLatinSystem ι Ω) (hm : 5 ≤ Fintype.card Ω) :
    ringKrullDim (MvPolynomial (ι × Ω) K ⧸
      MvPolynomial.vanishingIdeal K (imageClosure (K := K) L.perm)) =
        (5 * Fintype.card Ω - 4 : ℕ) := by
  classical
  have ho : Nonempty Ω := Fintype.card_pos_iff.mp (by omega)
  let o : Ω := Classical.choice ho
  obtain ⟨P, N, hdis, hpart, hPc, hNc, hPt, hNt⟩ := L.exists_transitive_partition o hm
  let S : TransitiveColorSplit L.perm L.identity :=
    ⟨P, N, hdis, hpart, hPc, hNc, hPt, hNt⟩
  have h := paper_theorem_2_3 (K := K) L.perm L.identity o L.normalized
    (L.perm_injective o) L.derangement S
  have hc : Fintype.card {a : ι // a ≠ L.identity} = Fintype.card Ω - 1 := by
    rw [← L.card_eq o]
    simpa only [Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun a : ι => a = L.identity)
  have hn : 3 * Fintype.card Ω + 2 * Fintype.card {a : ι // a ≠ L.identity} - 2 =
      5 * Fintype.card Ω - 4 := by omega
  simpa only [hn] using h

end Sunlet

namespace Sunlet.GroupCoordinates

variable {K G : Type*} [Field K] [IsAlgClosed K] [AddCommGroup G] [Fintype G]

/-- Group translations form the normalized Latin system in the paper. -/
def translationLatinSystem : NormalizedLatinSystem G G where
  perm := addTranslationPerm
  identity := 0
  normalized := by ext b; simp
  column_bijective b := by
    constructor
    · intro a c h
      exact add_right_cancel h
    · intro y
      refine ⟨y - b, ?_⟩
      simp

/-- The group case in the five-family coordinates, over every algebraically closed field. -/
theorem paper_theorem_1_1_group (hm : 5 ≤ Fintype.card G) :
    ringKrullDim (MvPolynomial (G × G) K ⧸
      MvPolynomial.vanishingIdeal K (imageClosure (K := K) (G := G))) =
        (5 * Fintype.card G - 4 : ℕ) := by
  classical
  rw [imageClosure_eq_fiveFamily]
  exact Sunlet.paper_theorem_1_1 (K := K) translationLatinSystem hm

/-- The original six-family, constrained-triple-coordinate statement of Theorem 1.1. -/
theorem paper_theorem_1_1_original_coordinates (hm : 5 ≤ Fintype.card G) :
    ringKrullDim (MvPolynomial (FlowIndex G) K ⧸
      MvPolynomial.vanishingIdeal K (tripleImageClosure (K := K) (G := G))) =
        (5 * Fintype.card G - 4 : ℕ) := by
  rw [ringKrullDim_eq_of_ringEquiv (flowCoordinateRingEquiv (K := K) (G := G)).toRingEquiv]
  exact paper_theorem_1_1_group hm

end Sunlet.GroupCoordinates
