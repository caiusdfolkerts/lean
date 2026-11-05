import Characterizations.Isolators.Coverage
import Characterizations.Triangular
import Characterizations.SmallCases

/-! # Exact optimal localization families and the smallest isolator degrees -/
noncomputable section
set_option maxHeartbeats 600000
namespace Characterizations.Isolators
open Classical Finset CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- Full fixed-family equivalence in Theorem 4.5, without prior local purity. -/
theorem localizationTestSufficient_iff (Γ : Finset (Finset V)) (d : ℕ) (hd : 2 ≤ d) :
    LocalizationTestSufficient (k := k) Γ d ↔ localizationBand (V := V) (d-1) ⊆ Γ := by
  constructor
  · exact localizationTestSufficient_necessary Γ d hd
  · intro hΓ B hB hdeg htest
    apply (polymatroidal_iff_localization_band (k := k) hB hdeg hd).mpr
    intro U hm hk
    exact htest U (hΓ ((mem_localizationBand _ _).mpr ⟨hm, by simpa only [card_compl] using hk⟩))

/-- Full fixed-family equivalence in Theorem 4.5 with prior local purity. -/
theorem pureLocalizationTestSufficient_iff (Γ : Finset (Finset V)) (d : ℕ) (hd : 2 ≤ d) :
    PureLocalizationTestSufficient (k := k) Γ d ↔ localizationBand (V := V) (d-2) ⊆ Γ := by
  constructor
  · exact pureLocalizationTestSufficient_necessary Γ d hd
  · intro hΓ B hB hdeg hl htest
    apply (polymatroidal_iff_pure_localization_band (k := k) hB hdeg hd hl).mpr
    intro U hm hk
    exact htest U (hΓ ((mem_localizationBand _ _).mpr ⟨hm, by simpa only [card_compl] using hk⟩))

/-- The exact ordinary-band minimum is attained and bounds every valid testing family. -/
theorem localizationTest_minimum (d : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ Fintype.card V) :
    (∃ Γ : Finset (Finset V), LocalizationTestSufficient (k := k) Γ d ∧
      Γ.card = ∑ j ∈ Finset.range (min (d-1) (Fintype.card V-2)+1), Nat.choose (Fintype.card V) j) ∧
    (∀ Γ : Finset (Finset V), LocalizationTestSufficient (k := k) Γ d →
      (∑ j ∈ Finset.range (min (d-1) (Fintype.card V-2)+1), Nat.choose (Fintype.card V) j) ≤ Γ.card) := by
  constructor
  · exact ⟨localizationBand (d-1), (localizationTestSufficient_iff _ d hd).mpr le_rfl,
      localizationBand_card (d-1) hn⟩
  · intro Γ hΓ
    rw [← localizationBand_card (d-1) hn]
    exact Finset.card_le_card ((localizationTestSufficient_iff Γ d hd).mp hΓ)

/-- The exact narrower-band minimum under prior local equigeneration. -/
theorem pureLocalizationTest_minimum (d : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ Fintype.card V) :
    (∃ Γ : Finset (Finset V), PureLocalizationTestSufficient (k := k) Γ d ∧
      Γ.card = ∑ j ∈ Finset.range (min (d-2) (Fintype.card V-2)+1), Nat.choose (Fintype.card V) j) ∧
    (∀ Γ : Finset (Finset V), PureLocalizationTestSufficient (k := k) Γ d →
      (∑ j ∈ Finset.range (min (d-2) (Fintype.card V-2)+1), Nat.choose (Fintype.card V) j) ≤ Γ.card) := by
  constructor
  · exact ⟨localizationBand (d-2), (pureLocalizationTestSufficient_iff _ d hd).mpr le_rfl,
      localizationBand_card (d-2) hn⟩
  · intro Γ hΓ
    rw [← localizationBand_card (d-2) hn]
    exact Finset.card_le_card ((pureLocalizationTestSufficient_iff Γ d hd).mp hΓ)

/-- Any equigenerated ideal with a unique bad localization has degree at least
codimension plus one, and never degree zero or one. -/
theorem unique_bad_degree_lower_bound {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d) (U : Finset V)
    (hbad : ¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U))
    (hgood : ∀ R : Finset V, R ≠ U →
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) R)) :
    2 ≤ d ∧ Uᶜ.card+1 ≤ d := by
  have hd2 : 2 ≤ d := by
    by_contra hn
    exact hbad (polymatroidal_local_linearResolutions
      (equigenerated_polymatroidal_of_degree_le_one hd (by omega)) U)
  refine ⟨hd2, ?_⟩
  by_contra hcost
  have hp : IsPolymatroidal B := (polymatroidal_iff_localization_band (k := k) hB hd hd2).mpr (by
    intro R hm hk
    apply hgood R
    intro he
    subst R
    have hc : Uᶜ.card = Fintype.card V-U.card := card_compl U
    omega)
  exact hbad (polymatroidal_local_linearResolutions hp U)

/-- Proposition 4.7's sharper optimality when all localizations are equigenerated. -/
theorem pure_unique_bad_degree_lower_bound {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d) (hl : LocallyEquigenerated B) (U : Finset V)
    (hbad : ¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U))
    (hgood : ∀ R : Finset V, R ≠ U →
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) R)) :
    Uᶜ.card+2 ≤ d := by
  have hd2 := (unique_bad_degree_lower_bound hB hd U hbad hgood).1
  by_contra hcost
  have hp : IsPolymatroidal B :=
    (polymatroidal_iff_pure_localization_band (k := k) hB hd hd2 hl).mpr (by
      intro R hm hk
      apply hgood R
      intro he
      subst R
      have hc : Uᶜ.card = Fintype.card V-U.card := card_compl U
      omega)
  exact hbad (polymatroidal_local_linearResolutions hp U)

end Characterizations.Isolators
