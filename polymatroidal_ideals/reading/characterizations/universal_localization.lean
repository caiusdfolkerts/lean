import Characterizations.PureDegree
import Characterizations.Projection

/-! # Universal pure reverse-lexicographic quotients survive localization -/

noncomputable section
namespace Characterizations
open CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Corollary 3.11. `localFamily` is the actual minimal generator family of
`Ideal.map (localizationHom U) (monomialIdeal k B)`, as established in
`Localization.monomialIdeal_localFamily`. -/
theorem universal_pure_revlex_localization {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} (hB : Antichain B)
    (h : ∀ o : VariableOrder V, HasLinearQuotients k B (variableRevlex o))
    (U : Finset V) (o : VariableOrder U) :
    HasLinearQuotients k (localFamily B U) (variableRevlex o) := by
  have hp := (polymatroidal_iff_universal_pure_revlex hB).mpr h
  exact polymatroidal_variable_linearQuotients (localFamily_polymatroidal hp U).2 o

end Characterizations
