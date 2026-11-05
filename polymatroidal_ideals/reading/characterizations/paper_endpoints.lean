import Characterizations.MonomialNormalForm
import CommAlg.IntegralClosure.OrdinaryRees

/-!
# The integral-closedness characterization, including the zero ideal

The polytope in Theorem 2.11 requires a nonempty generator family, since its
lower rank is a minimum.  The characterization in (2.5) itself also holds at
zero.  This interface states that equivalence for every literal monomial ideal.
It adds no hypothesis and uses the ordinary monic-equation definition of
integral closedness already used by the nonzero theorem.
-/

noncomputable section

namespace Characterizations

open CommAlg CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- Equation (2.5), for an arbitrary monomial ideal, including zero. -/
theorem monomialIdeal_polymatroidal_iff_integrallyClosed_all
    {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I) :
    IsPolymatroidalIdeal I ↔ IsIntegrallyClosedIdeal I ∧
      ∀ U : Finset V, ∃ d,
        Equigenerated (localFamily (monomialGenerators I hI) U) d := by
  by_cases hzero : I = ⊥
  · subst I
    have hp : IsPolymatroidalIdeal (⊥ : Ideal (MvPolynomial V k)) :=
      isPolymatroidalIdeal_bot
    have hgenerators := (isPolymatroidalIdeal_iff_generators hI).mp hp
    constructor
    · intro _
      exact ⟨integrallyClosed_bot, fun U => (localFamily_polymatroidal hgenerators U).1⟩
    · intro _
      exact hp
  · exact monomialIdeal_polymatroidal_iff_integrallyClosed hI hzero

/-- Corollary 2.10 for an arbitrary literal monomial ideal, including zero.
The same minimal monomial exponent family is interpreted over any coefficient field. -/
theorem monomialIdeal_local_linearResolutions_field_independent_all
    {k' : Type u} [Field k']
    {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I)
    (hlinear : ∀ U : Finset V,
      HasLinearResolution (monomialLocalization k I U)) :
    ∀ U : Finset V,
      HasLinearResolution
        (monomialLocalization k' (monomialIdeal k' (monomialGenerators I hI)) U) := by
  have hp := (monomialIdeal_polymatroidal_iff_local_linear hI).mpr hlinear
  have hgenerators := (isPolymatroidalIdeal_iff_generators hI).mp hp
  exact fun U => polymatroidal_local_linearResolutions (k := k') hgenerators U

end Characterizations
