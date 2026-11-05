import Characterizations.Resolution.Localizations
import Characterizations.Resolution.Socle
import Characterizations.SocleCharacterization

/-! # Theorem 1.1(A): actual local linear resolutions characterize polymatroids -/
noncomputable section
namespace Characterizations
open CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [Field k]

theorem polymatroidal_iff_local_linearResolutions {B : Family V}
    (hB : B.Nonempty) (hanti : Antichain B) :
    IsPolymatroidal B ↔ ∀ U : Finset V,
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) U) := by
  constructor
  · exact fun hp U => polymatroidal_local_linearResolutions hp U
  · intro h
    classical
    have hres : ∀ U, HasLinearResolution (monomialIdeal k (localFamily B U)) := by
      intro U
      simpa only [monomialLocalization_eq] using h U
    have hl : LocallyEquigenerated B := by
      rw [locallyEquigenerated_iff]
      intro U
      obtain ⟨d, ⟨P⟩⟩ := hres U
      exact ⟨d, P.equigenerated_of_monomial (localFamily B U) (localFamily_antichain B U)⟩
    apply (polymatroidal_iff_local_socles k hB hanti).mpr
    refine ⟨hl, ?_⟩
    intro U _
    letI : LinearOrder U := LinearOrder.lift' (Fintype.equivFin U) (Fintype.equivFin U).injective
    obtain ⟨d, ⟨P⟩⟩ := hres U
    obtain ⟨a, ha⟩ := localFamily_nonempty hB U
    have hd : d = lowerRank B U :=
      (P.equigenerated_of_monomial (localFamily B U) (localFamily_antichain B U) a ha).symm.trans
        (localFamily_degree_of_locallyEquigenerated hB hl U a ha)
    simpa only [hd] using P.socleConcentrated (localFamily B U) (localFamily_nonempty hB U)

theorem local_linearResolutions_field_independent {k' : Type u} [Field k']
    {B : Family V} (hB : B.Nonempty) (hanti : Antichain B) :
    (∀ U : Finset V, HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) ↔
    (∀ U : Finset V, HasLinearResolution (monomialLocalization k' (monomialIdeal k' B) U)) :=
  (polymatroidal_iff_local_linearResolutions (k := k) hB hanti).symm.trans
    (polymatroidal_iff_local_linearResolutions (k := k') hB hanti)

end Characterizations
