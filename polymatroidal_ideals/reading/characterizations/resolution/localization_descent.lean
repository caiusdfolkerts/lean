import Characterizations.Resolution.Descent
import Characterizations.Resolution.LocalizationDescentData

/-! Descent from a restored variable when the actual generator family is unchanged. -/
noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid Resolution
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k]

theorem local_linearResolution_of_insert_family_eq (B : Family V) (U : Finset V)
    (i : V) (hi : i ∉ U)
    (he : localize B (insert i U) = localize B U)
    (hL : HasLinearResolution (monomialLocalization k (monomialIdeal k B) (insert i U))) :
    HasLinearResolution (monomialLocalization k (monomialIdeal k B) U) := by
  let hUW : U ⊆ insert i U := Finset.subset_insert i U
  let j : (insert i U : Finset V) := ⟨i,Finset.mem_insert_self _ _⟩
  let f : U → (insert i U : Finset V) := retainedInclusion hUW
  have hf : Function.Injective f := retainedInclusion_injective hUW
  have hrange : ∀ w, w ∈ Set.range f ↔ w ≠ j := by
    intro w
    constructor
    · rintro ⟨u,rfl⟩ heq
      have hv := congrArg Subtype.val heq
      change u.val = i at hv
      exact hi (hv ▸ u.property)
    · intro hne
      have hw : w.val ∈ U := by
        rcases Finset.mem_insert.mp w.property with hw | hw
        · exact False.elim (hne (Subtype.ext hw))
        · exact hw
      exact ⟨⟨w.val,hw⟩,Subtype.ext rfl⟩
  rw [monomialLocalization_eq] at hL
  obtain ⟨d,⟨P⟩⟩ := hL
  have hs : ∀ a ∈ localFamily B (insert i U), a j = 0 := by
    exact localFamily_zero_of_localize_eq B hUW he j hi
  have hI := monomialIdeal_variable_saturated (k:=k) (localFamily B (insert i U)) j hs
  rw [monomialLocalization_eq, ← killCompl_localFamily_ideal (k:=k) B hUW he]
  exact ⟨d,⟨P.descendAlong f hf j hrange hI⟩⟩

end Characterizations
