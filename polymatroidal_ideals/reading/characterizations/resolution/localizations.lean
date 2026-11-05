import Characterizations.Resolution.LinearQuotients
import Characterizations.Projection

/-! # Actual linear resolutions after monomial localization -/

noncomputable section
namespace Characterizations
open CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

/-- The forward implication in Theorem 1.1(A), in the actual polynomial ring on
exactly the retained variables. The conclusion is an exact finite-free complex,
with linear differential matrices, resolving the literal localized ideal. -/
theorem polymatroidal_local_linearResolutions {B : Family V}
    (hB : IsPolymatroidal B) (U : Finset V) :
    HasLinearResolution (monomialLocalization k (monomialIdeal k B) U) := by
  rw [monomialLocalization_eq]
  exact linearResolution_of_polymatroidal (localFamily_polymatroidal hB U)

end Characterizations
