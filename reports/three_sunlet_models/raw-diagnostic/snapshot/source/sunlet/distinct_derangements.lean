module

public import sunlet.paper_statements

/-! The literal distinctness convention of Theorem 2.3: only the listed
nonidentity derangements need be assumed distinct. The identity color is
automatically distinct from them. -/

@[expose] public section
noncomputable section

namespace Sunlet

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
  [DecidableEq ι] [DecidableEq Ω]

theorem injective_iff_distinct_nonidentity
    (π : ι → Equiv.Perm Ω) (e : ι)
    (he : π e = Equiv.refl Ω)
    (hder : ∀ a, a ≠ e → ∀ x, π a x ≠ x)
    (S : TransitiveColorSplit π e) :
    Function.Injective π ↔ Function.Injective (fun a : {a : ι // a ≠ e} => π a) := by
  constructor
  · intro h a b hab
    exact Subtype.ext (h hab)
  · intro h
    have hΩ : Nonempty Ω := by
      by_contra hn
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp
        (show 1 < S.positive.card by have := S.positive_card; omega)
      have hp : π a = π b := by
        ext x
        exact False.elim (hn ⟨x⟩)
      exact hab (congrArg Subtype.val
        (@h ⟨a, S.positive_ne a ha⟩ ⟨b, S.positive_ne b hb⟩ hp))
    let o := Classical.choice hΩ
    intro a b hab
    by_cases ha : a = e
    · subst a
      by_cases hb : b = e
      · exact hb.symm
      · exfalso
        apply hder b hb o
        have hh := congrArg (fun f : Equiv.Perm Ω => f o) hab
        simpa only [he, Equiv.refl_apply] using hh.symm
    · by_cases hb : b = e
      · subst b
        exfalso
        apply hder a ha o
        have hh := congrArg (fun f : Equiv.Perm Ω => f o) hab
        simpa only [he, Equiv.refl_apply] using hh
      · exact congrArg Subtype.val (@h ⟨a, ha⟩ ⟨b, hb⟩ hab)

/-- Theorem 2.3 with distinctness assumed only for the `c` nonidentity
derangements, exactly as in the displayed manuscript statement. -/
theorem paper_theorem_2_3_literal {K : Type*} [Field K] [IsAlgClosed K]
    (c : ℕ) (π : Fin (c + 1) → Equiv.Perm Ω)
    (he : π 0 = Equiv.refl Ω)
    (hπ : Function.Injective (fun a : {a : Fin (c + 1) // a ≠ 0} => π a))
    (hder : ∀ a, a ≠ 0 → ∀ x, π a x ≠ x)
    (S : TransitiveColorSplit π 0) :
    ringKrullDim (MvPolynomial (Fin (c + 1) × Ω) K ⧸
      MvPolynomial.vanishingIdeal K (imageClosure (K := K) π)) =
        (3 * Fintype.card Ω + 2 * c - 2 : ℕ) := by
  exact paper_theorem_2_3_fin c π he
    ((injective_iff_distinct_nonidentity π 0 he hder S).mpr hπ) hder S

end Sunlet
