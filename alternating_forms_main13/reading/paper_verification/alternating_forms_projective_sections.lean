module

public import PaperVerification.AlternatingFormsExtremeRegularity
public import PaperVerification.HomogeneousQuotientProjective
public import PaperVerification.RegularPairProjectiveSections

/-! Exact graded and projective comparison maps. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial Hibi AlgebraicGeometry

variable {K : Type*} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "Q" => isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)
local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "φ" => oddGoodMap (K := K) k t hs

/-- The original ordinary homogeneous grading on the original isotropic
Plucker quotient, with its verified internal decomposition. -/
def oddProjectiveGrading : ℕ → Submodule K
    (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸Q) :=
  HomogeneousQuotientProjective.grading Q (isotropicPluckerIdeal_isHomogeneous _)

instance oddProjectiveGradedAlgebra : GradedAlgebra (oddProjectiveGrading (K := K) k t) :=
  HomogeneousQuotientProjective.quotientGradedAlgebra Q _

theorem odd_goodCoordinate_degree_one (I : IntervalIndex α β) :
    φ (X I)∈oddProjectiveGrading (K := K) k t 1 := by
  rw [oddGoodMap_X]
  exact HomogeneousQuotientProjective.quotient_X_mem_one Q _ I.val

theorem odd_goodCoordinate_basicOpen_cover :
    (⨆ I : IntervalIndex α β,
      Proj.basicOpen (oddProjectiveGrading (K := K) k t) (φ (X I)))=⊤ :=
  HomogeneousQuotientProjective.presentation_basicOpen_cover Q _ φ
    (oddGoodMap_surjective k t hs) (odd_goodCoordinate_degree_one k t hs)

theorem odd_goodCoordinate_isRegular (I : IntervalIndex α β) : IsRegular (φ (X I)) := by
  letI : (Q).IsPrime := odd_isotropicPluckerIdeal_isPrime k t hs
  exact isRegular_iff_ne_zero.mpr (oddGoodCoordinate_ne_zero k t hs I)

include hs in
/-- All nonnegative-degree complete sections on the actual Proj are the
original homogeneous coordinate elements, in every distinct-endpoint case. -/
theorem odd_bijective_toTwistingSheaf_top (hstrict : t+2<k+1) (d : ℕ) :
    Function.Bijective
      (Proj.toTwistingSheaf (oddProjectiveGrading (K := K) k t)
        (rfl : (d : ℤ)=d) ⊤) :=
  RegularPairProjectiveSections.bijective_toTwistingSheaf_top
    (oddProjectiveGrading (K := K) k t) (fun I : IntervalIndex α β ↦ φ (X I))
    (odd_goodCoordinate_degree_one k t hs) (odd_goodCoordinate_isRegular k t hs)
    (odd_goodCoordinate_basicOpen_cover k t hs)
    (oddLeastGoodIndex k t hs) (oddGreatestGoodIndex k t hs)
    (odd_extremeCoordinates_regularPair k t hs hstrict).2 d

set_option synthInstance.maxHeartbeats 80000 in
/-- The canonical component isomorphisms preserve literal sheaf-section
multiplication; they are the degreewise comparison for the complete section ring. -/
theorem odd_toTwistingSheaf_top_mul (a b : ℕ)
    (r : oddProjectiveGrading (K := K) k t a)
    (s : oddProjectiveGrading (K := K) k t b) :
    Proj.twistingSheaf.mul (oddProjectiveGrading (K := K) k t) ⊤ (a : ℤ) (b : ℤ)
      (Proj.toTwistingSheaf (oddProjectiveGrading (K := K) k t) rfl ⊤ r)
      (Proj.toTwistingSheaf (oddProjectiveGrading (K := K) k t) rfl ⊤ s)=
    Proj.toTwistingSheaf (oddProjectiveGrading (K := K) k t)
      (by omega : ((a+b : ℕ) : ℤ)=(a : ℤ)+(b : ℤ)) ⊤
      ⟨(r : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸Q)*
        (s : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸Q),SetLike.mul_mem_graded r.2 s.2⟩ :=
  Proj.mul_toTwistingSheaf (𝒜 := oddProjectiveGrading (K := K) k t) rfl rfl ⊤ r s

end PaperVerification.AlternatingForms
