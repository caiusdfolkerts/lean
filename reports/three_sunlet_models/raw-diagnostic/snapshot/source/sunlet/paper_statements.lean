module

public import sunlet.main_dimension

/-! Quantifier-level wrappers matching the manuscript's choice-free statements. -/

@[expose] public section
noncomputable section

namespace Sunlet

variable {K ι Ω : Type*} [Field K] [IsAlgClosed K]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]

/-- The split hypotheses themselves imply that the underlying set is nonempty;
the distinguished basepoint used in the proof is not an extra hypothesis. -/
theorem nonempty_of_transitive_split (π : ι → Equiv.Perm Ω) (e : ι)
    (hπ : Function.Injective π) (S : TransitiveColorSplit π e) : Nonempty Ω := by
  by_contra h
  obtain ⟨a, _, b, _, hab⟩ := S.positive_two hπ
  apply hab
  ext x
  exact False.elim (h ⟨x⟩)

/-- Theorem 2.3 without an additional chosen point of the underlying set. -/
theorem paper_theorem_2_3_without_basepoint
    (π : ι → Equiv.Perm Ω) (e : ι)
    (he : π e = Equiv.refl Ω) (hπ : Function.Injective π)
    (hder : ∀ a, a ≠ e → ∀ b, π a b ≠ b)
    (S : TransitiveColorSplit π e) :
    ringKrullDim (MvPolynomial (ι × Ω) K ⧸
      MvPolynomial.vanishingIdeal K (imageClosure (K := K) π)) =
        (3 * Fintype.card Ω + 2 * Fintype.card {a : ι // a ≠ e} - 2 : ℕ) := by
  let o := Classical.choice (nonempty_of_transitive_split π e hπ S)
  exact paper_theorem_2_3 π e o he hπ hder S

/-- The literal `c + 1` color indexing and `3m + 2c - 2` formula of Theorem 2.3. -/
theorem paper_theorem_2_3_fin
    (c : ℕ) (π : Fin (c + 1) → Equiv.Perm Ω)
    (he : π 0 = Equiv.refl Ω) (hπ : Function.Injective π)
    (hder : ∀ a, a ≠ 0 → ∀ b, π a b ≠ b)
    (S : TransitiveColorSplit π 0) :
    ringKrullDim (MvPolynomial (Fin (c + 1) × Ω) K ⧸
      MvPolynomial.vanishingIdeal K (imageClosure (K := K) π)) =
        (3 * Fintype.card Ω + 2 * c - 2 : ℕ) := by
  have hc : Fintype.card {a : Fin (c + 1) // a ≠ 0} = c := by
    simpa only [Fintype.card_subtype_eq, Fintype.card_fin, Nat.add_sub_cancel] using
      Fintype.card_subtype_compl (fun a : Fin (c + 1) => a = 0)
  simpa only [hc] using paper_theorem_2_3_without_basepoint (K := K) π 0 he hπ hder S

/-- A finite column of distinct values with the same cardinality as the
underlying set is bijective. Thus the paper's literal injective-column
hypothesis supplies exactly the Latin-system structure used in the proof. -/
def normalizedLatinSystemOfInjectiveColumns
    (π : ι → Equiv.Perm Ω) (e : ι)
    (he : π e = Equiv.refl Ω) (hcard : Fintype.card ι = Fintype.card Ω)
    (hcolumns : ∀ b, Function.Injective (fun a => π a b)) : NormalizedLatinSystem ι Ω where
  perm := π
  identity := e
  normalized := he
  column_bijective b := (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hcolumns b, hcard⟩

/-- Theorem 1.1 with precisely `m` indexed permutations, precisely `m`
underlying points, and distinct values in each column, as in the manuscript.
The distinguished index is the element `0` of `Fin m`; its existence follows
from the stated lower bound and is not a separate nonemptiness assumption. -/
theorem paper_theorem_1_1_fin
    (m : ℕ) (hm : 5 ≤ m) (π : Fin m → Equiv.Perm Ω)
    (hcard : Fintype.card Ω = m)
    (he : π ⟨0, by omega⟩ = Equiv.refl Ω)
    (hcolumns : ∀ b, Function.Injective (fun a => π a b)) :
    ringKrullDim (MvPolynomial (Fin m × Ω) K ⧸
      MvPolynomial.vanishingIdeal K (imageClosure (K := K) π)) =
        (5 * m - 4 : ℕ) := by
  let L := normalizedLatinSystemOfInjectiveColumns π ⟨0, by omega⟩ he
    (by simpa only [Fintype.card_fin] using hcard.symm) hcolumns
  have h := paper_theorem_1_1 (K := K) L (by omega)
  change ringKrullDim (MvPolynomial (Fin m × Ω) K ⧸
    MvPolynomial.vanishingIdeal K (imageClosure (K := K) π)) =
      (5 * Fintype.card Ω - 4 : ℕ) at h
  rw [hcard] at h
  exact h

end Sunlet
