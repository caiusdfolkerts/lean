module

public import PaperVerification.IsotropicAttractingChartRings
public import PaperVerification.OddPathIndependent

/-!
# Counting the actual attracting-chart indices

The geometric charts are indexed by increasing Plücker indices satisfying
the two literal isotropy conditions.  This file identifies that indexing
type with the independent subsets already counted in `OddPathIndependent`.
The equivalence retains the original chart indices; no geometric dimension
or cohomological assertion is built into the counting type.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCharts

open PaperVerification.AlternatingForms
open PaperVerification.IsotropicAttractingCoordinates
open PaperVerification.OddPathIndependent

/-- Increasing Plücker indices are precisely order embeddings. -/
def pluckerIndexOrderEmbeddingEquiv (s n : ℕ) :
    PluckerIndex s n ≃ (Fin s ↪o Fin n) where
  toFun p := OrderEmbedding.ofStrictMono p.val p.property
  invFun e := ⟨e, e.strictMono⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv e := by ext i; rfl

/-- Taking the image gives the underlying subset of an increasing index. -/
def pluckerIndexSubsetEquiv (s n : ℕ) :
    PluckerIndex s n ≃ {S : Finset (Fin n) // S.card = s} :=
  (pluckerIndexOrderEmbeddingEquiv s n).trans
    (SeparatedSubsets.orderEmbeddingEquivSubsets n s)

@[simp] theorem pluckerIndexSubsetEquiv_val (s n : ℕ) (p : PluckerIndex s n) :
    (pluckerIndexSubsetEquiv s n p).val = Finset.univ.map (indexEmbedding p) := rfl

theorem independentPivots_iff_chainIndependent {k s : ℕ}
    (p : PluckerIndex s (2*k+1)) :
    IndependentPivots (indexEmbedding p) ↔
      ChainIndependent k (Finset.univ.map (indexEmbedding p)) := by
  classical
  constructor
  · intro hp a ha b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hb
    by_cases hij : i = j
    · exact Or.inl (congrArg (indexEmbedding p) hij)
    · exact Or.inr (hp i j hij)
  · intro hp i j hij
    have hi : indexEmbedding p i ∈ Finset.univ.map (indexEmbedding p) :=
      Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hj : indexEmbedding p j ∈ Finset.univ.map (indexEmbedding p) :=
      Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩
    rcases hp _ hi _ hj with he | he
    · exact (hij ((indexEmbedding p).injective he)).elim
    · exact he

/-- The indices of the nonempty attracting cells. -/
abbrev IndependentPluckerIndices (k s : ℕ) :=
  {p : PluckerIndex s (2*k+1) // IndependentPivots (indexEmbedding p)}

/-- The chart indexing type and the independently counted subset type agree. -/
def independentPluckerEquivCoordinateSubsets (k s : ℕ) :
    IndependentPluckerIndices k s ≃ CoordinateSubsets k s where
  toFun p := ⟨(pluckerIndexSubsetEquiv s (2*k+1) p.val).val,
    (pluckerIndexSubsetEquiv s (2*k+1) p.val).property,
    (independentPivots_iff_chainIndependent p.val).mp p.property⟩
  invFun S := ⟨(pluckerIndexSubsetEquiv s (2*k+1)).symm ⟨S.val, S.property.1⟩, by
    apply (independentPivots_iff_chainIndependent _).mpr
    change ChainIndependent k
      (pluckerIndexSubsetEquiv s (2*k+1)
        ((pluckerIndexSubsetEquiv s (2*k+1)).symm ⟨S.val, S.property.1⟩)).val
    rw [Equiv.apply_symm_apply]
    exact S.property.2⟩
  left_inv p := by
    apply Subtype.ext
    exact (pluckerIndexSubsetEquiv s (2*k+1)).symm_apply_apply p.val
  right_inv S := by
    apply Subtype.ext
    change ((pluckerIndexSubsetEquiv s (2*k+1))
      ((pluckerIndexSubsetEquiv s (2*k+1)).symm ⟨S.val,S.property.1⟩)).val = S.val
    exact congrArg (fun T : {S : Finset (Fin (2*k+1)) // S.card = s} => T.val)
      ((pluckerIndexSubsetEquiv s (2*k+1)).apply_symm_apply ⟨S.val, S.property.1⟩)

/-- The complete binomial count for the actual attracting cells. -/
theorem card_independentPluckerIndices (k s : ℕ) (hs : s ≤ k+1) :
    Nat.card (IndependentPluckerIndices k s) = Nat.choose (2*k+2-s) s := by
  rw [Nat.card_congr (independentPluckerEquivCoordinateSubsets k s)]
  exact card_coordinateSubsets k s hs

end PaperVerification.IsotropicAttractingCharts
