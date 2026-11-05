import Characterizations.Isolators.Optimality
import Characterizations.MonomialNormalForm

/-! Theorem 4.5 and its universal testing predicates, including the zero ideal. -/
noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem empty_family_polymatroidal : IsPolymatroidal (∅ : Family V) := by
  refine ⟨⟨0,?_⟩,?_⟩
  · intro a ha; simp at ha
  · intro a ha; simp at ha

theorem polymatroidal_iff_localization_band_all {B : Family V}
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) :
    IsPolymatroidal B ↔ ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) U) := by
  by_cases hB : B.Nonempty
  · exact polymatroidal_iff_localization_band hB hd hd2
  · have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    subst B
    exact ⟨fun hp U _ _ => polymatroidal_local_linearResolutions hp U,
      fun _ => empty_family_polymatroidal⟩

theorem polymatroidal_iff_pure_localization_band_all {B : Family V}
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) (hl : LocallyEquigenerated B) :
    IsPolymatroidal B ↔ ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-2 →
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) U) := by
  by_cases hB : B.Nonempty
  · exact polymatroidal_iff_pure_localization_band hB hd hd2 hl
  · have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    subst B
    exact ⟨fun hp U _ _ => polymatroidal_local_linearResolutions hp U,
      fun _ => empty_family_polymatroidal⟩

/-- Literal-ideal Theorem 4.5, with no nonzero hypothesis. The degree refers
to the actual minimal monomial generators characterized in MonomialNormalForm. -/
theorem monomialIdeal_polymatroidal_iff_localization_band
    {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I)
    {d : ℕ} (hd : Equigenerated (monomialGenerators I hI) d) (hd2 : 2 ≤ d) :
    IsPolymatroidalIdeal I ↔ ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
      HasLinearResolution (monomialLocalization k I U) := by
  rw [isPolymatroidalIdeal_iff_generators hI]
  simpa only [monomialGenerators_ideal] using
    (polymatroidal_iff_localization_band_all (k:=k) hd hd2)

theorem monomialIdeal_polymatroidal_iff_pure_localization_band
    {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I)
    {d : ℕ} (hd : Equigenerated (monomialGenerators I hI) d) (hd2 : 2 ≤ d)
    (hl : LocallyEquigenerated (monomialGenerators I hI)) :
    IsPolymatroidalIdeal I ↔ ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-2 →
      HasLinearResolution (monomialLocalization k I U) := by
  rw [isPolymatroidalIdeal_iff_generators hI]
  simpa only [monomialGenerators_ideal] using
    (polymatroidal_iff_pure_localization_band_all (k:=k) hd hd2 hl)

namespace Isolators

def LocalizationTestSufficientAll (Γ : Finset (Finset V)) (d : ℕ) : Prop :=
  ∀ B : Family V, Equigenerated B d →
    (∀ U ∈ Γ, HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) →
      IsPolymatroidal B

def PureLocalizationTestSufficientAll (Γ : Finset (Finset V)) (d : ℕ) : Prop :=
  ∀ B : Family V, Equigenerated B d → LocallyEquigenerated B →
    (∀ U ∈ Γ, HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) →
      IsPolymatroidal B

def UnboundedLocalizationTestSufficientAll (Γ : Finset (Finset V)) : Prop :=
  ∀ B : Family V, Antichain B →
    (∀ U ∈ Γ, HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) →
      IsPolymatroidal B

theorem localizationTestSufficientAll_iff (Γ : Finset (Finset V)) (d : ℕ) :
    LocalizationTestSufficientAll (k:=k) Γ d ↔ LocalizationTestSufficient (k:=k) Γ d := by
  constructor
  · intro h B _ hd ht; exact h B hd ht
  · intro h B hd ht
    by_cases hB : B.Nonempty
    · exact h B hB hd ht
    · simpa only [Finset.not_nonempty_iff_eq_empty.mp hB] using
        (empty_family_polymatroidal (V:=V))

theorem pureLocalizationTestSufficientAll_iff (Γ : Finset (Finset V)) (d : ℕ) :
    PureLocalizationTestSufficientAll (k:=k) Γ d ↔ PureLocalizationTestSufficient (k:=k) Γ d := by
  constructor
  · intro h B _ hd hl ht; exact h B hd hl ht
  · intro h B hd hl ht
    by_cases hB : B.Nonempty
    · exact h B hB hd hl ht
    · simpa only [Finset.not_nonempty_iff_eq_empty.mp hB] using
        (empty_family_polymatroidal (V:=V))

theorem unboundedLocalizationTestSufficientAll_iff (Γ : Finset (Finset V)) :
    UnboundedLocalizationTestSufficientAll (k:=k) Γ ↔ UnboundedLocalizationTestSufficient (k:=k) Γ := by
  constructor
  · intro h B _ ha ht; exact h B ha ht
  · intro h B ha ht
    by_cases hB : B.Nonempty
    · exact h B hB ha ht
    · simpa only [Finset.not_nonempty_iff_eq_empty.mp hB] using
        (empty_family_polymatroidal (V:=V))

theorem localizationTestSufficientAll_coverage (Γ : Finset (Finset V)) (d : ℕ) (hd : 2 ≤ d) :
    LocalizationTestSufficientAll (k:=k) Γ d ↔ localizationBand (V:=V) (d-1) ⊆ Γ :=
  (localizationTestSufficientAll_iff Γ d).trans (localizationTestSufficient_iff Γ d hd)

theorem pureLocalizationTestSufficientAll_coverage (Γ : Finset (Finset V)) (d : ℕ) (hd : 2 ≤ d) :
    PureLocalizationTestSufficientAll (k:=k) Γ d ↔ localizationBand (V:=V) (d-2) ⊆ Γ :=
  (pureLocalizationTestSufficientAll_iff Γ d).trans (pureLocalizationTestSufficient_iff Γ d hd)

end Isolators
end Characterizations
