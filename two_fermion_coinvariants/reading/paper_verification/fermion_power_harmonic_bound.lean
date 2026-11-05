module

public import PaperVerification.FermionPowerHarmonicEndpoint
public import PaperVerification.FermionHarmonicGrading
public import PaperVerification.FermionLeadingBound
public import PaperVerification.FermionEndpointLength
public import PaperVerification.FermionOrdinaryCompleteIntersection

/-!
# The unrestricted paired harmonic dimension upper bound

The endpoint annihilator, its complete-intersection length, and the actual
ordinary Frobenius pairing are combined through the leading-coordinate
filtration. The bound retains every exterior word, every covering degree,
and every allowed split of the odd factors.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.Fermion

open scoped BigOperators
open MvPolynomial Exterior Endpoint Colex

variable {K : Type*} [Field K] {n : ℕ}

local instance FermionPowerHarmonicBound_localInst_1 (m : ℕ) : LinearOrder (Fin m ⊕ Fin m) := interleavedOddOrder m
local instance FermionPowerHarmonicBound_localInst_2 (m : ℕ) : PartialOrder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPartialOrder
local instance FermionPowerHarmonicBound_localInst_3 (m : ℕ) : Preorder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPreorder
local instance FermionPowerHarmonicBound_localInst_4 (m : ℕ) : LE (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLE
local instance FermionPowerHarmonicBound_localInst_5 (m : ℕ) : LT (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLT
local instance FermionPowerHarmonicBound_localInst_6 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) := (interleavedOddOrder m).toDecidableEq

abbrev ordinaryPowerRing (r : Fin n → ℕ) (β : Fin n → K) (s : ℕ) :=
  MvPolynomial (Fin n) K ⧸ powerMomentIdeal r β s

abbrev ordinaryPowerExterior (r : Fin n → ℕ) (β : Fin n → K) (s : ℕ) :=
  ExteriorAlgebra (ordinaryPowerRing r β s) (Fin n ⊕ Fin n → ordinaryPowerRing r β s)

def pairedPowerHarmonics (r u v : Fin n → ℕ) (β : Fin n → K) (s : ℕ) :
    Submodule K (ordinaryPowerExterior r β s) :=
  (harmonicSubmodule (Pi.basisFun (ordinaryPowerRing r β s) (Fin n ⊕ Fin n))
    (fun i ↦ Ideal.Quotient.mk (powerMomentIdeal r β s) (X i ^ r i))
    (fun i ↦ Ideal.Quotient.mk (powerMomentIdeal r β s) (C (β i)))
    (fun i ↦ Ideal.Quotient.mk (powerMomentIdeal r β s) (X i ^ u i))
    (fun i ↦ Ideal.Quotient.mk (powerMomentIdeal r β s) (X i ^ v i))).restrictScalars K

def ValidWord (T : Finset (Fin n ⊕ Fin n)) : Prop :=
  ∀ i ≤ n, (T ∩ pairedPrefix n i).card ≤ i

def pairedWordBoxCard (r u v : Fin n → ℕ) (s : ℕ) (T : Finset (Fin n ⊕ Fin n)) : ℕ := by
  classical
  exact if ValidWord T then
    ∏ i : Fin n, pairedBoxBound (r i) (u i) (v i) s (wordHeight T i) (wordMark T i)
  else 0

theorem pairedPower_largest_ungraded_endpoint
    (r u v : Fin n → ℕ) (β : Fin n → K) (s : ℕ)
    (hr : ∀ i, 0 < r i) (huv : ∀ i, u i + v i = r i * s)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hfac : IsUnit (n.factorial : K))
    (w : ordinaryPowerExterior r β s) (hw : w ∈ pairedPowerHarmonics r u v β s)
    (T : Finset (Fin n ⊕ Fin n))
    (hT : (Pi.basisFun (ordinaryPowerRing r β s) (Fin n ⊕ Fin n)).ExteriorAlgebra.repr w T ≠ 0)
    (hmax : ∀ U,
      (Pi.basisFun (ordinaryPowerRing r β s) (Fin n ⊕ Fin n)).ExteriorAlgebra.repr w U ≠ 0 →
        toColex U ≤ toColex T) :
    ValidWord T ∧ (Pi.basisFun (ordinaryPowerRing r β s) (Fin n ⊕ Fin n)).ExteriorAlgebra.repr w T ∈
      coefficientAnnihilator (Ideal.Quotient.mkₐ K (powerMomentIdeal r β s))
        (endpointIdeal (pairedPowerData r u v β (wordMark T)) n (wordHeight T n)) := by
  let b := Pi.basisFun (ordinaryPowerRing r β s) (Fin n ⊕ Fin n)
  let q := Ideal.Quotient.mk (powerMomentIdeal r β s)
  let w' := exteriorDegreeProjection T.card w
  have hw' := IsHarmonic.projection b
    (fun i ↦ q (X i ^ r i)) (fun i ↦ q (C (β i)))
    (fun i ↦ q (X i ^ u i)) (fun i ↦ q (X i ^ v i)) T.card w hw
  have hT' : b.ExteriorAlgebra.repr w' T = b.ExteriorAlgebra.repr w T := by
    simp only [w', exteriorDegreeProjection_coordinate, ite_true]
  have hne : b.ExteriorAlgebra.repr w' T ≠ 0 := by rwa [hT']
  have hmax' : ∀ U, b.ExteriorAlgebra.repr w' U ≠ 0 → toColex U ≤ toColex T := by
    intro U hU
    apply hmax U
    intro hz
    apply hU
    dsimp only [w']
    rw [exteriorDegreeProjection_coordinate, hz]
    split_ifs <;> rfl
  have hfac' : IsUnit (n.factorial : ordinaryPowerRing r β s) := by
    simpa only [map_natCast] using hfac.map (algebraMap K (ordinaryPowerRing r β s))
  constructor
  · exact largest_harmonic_term_prefix_card_le b _ _ _ _ hfac' T.card w'
      (exteriorDegreeProjection_mem _ _) hw' T hne hmax'
  · change ∀ p ∈ endpointIdeal (pairedPowerData r u v β (wordMark T)) n (wordHeight T n),
      q p * b.ExteriorAlgebra.repr w T = 0
    have hh := pairedPower_largest_coefficient_endpoint_annihilates r u v β s hr huv hβ hfac
      T.card w' (exteriorDegreeProjection_mem _ _) hw' T hne hmax'
    change ∀ p ∈ endpointIdeal (pairedPowerData r u v β (wordMark T)) n (wordHeight T n),
      q p * b.ExteriorAlgebra.repr w' T = 0 at hh
    rw [hT'] at hh
    exact hh

/-- The entire harmonic space has the paper's full path-box upper bound.
The ordinary Frobenius functional, valid heights, endpoint support,
regularity, quotient lengths and coefficient filtration are all derived. -/
theorem pairedPowerHarmonics_finrank_le_box_count
    (r u v : Fin n → ℕ) (β : Fin n → K) (s : ℕ) (hs : 0 < s)
    (hr : ∀ i, 0 < r i) (huv : ∀ i, u i + v i = r i * s)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hfac : IsUnit (n.factorial : K)) :
    Module.finrank K (pairedPowerHarmonics r u v β s) ≤
      ∑ T : Finset (Fin n ⊕ Fin n), pairedWordBoxCard r u v s T := by
  classical
  let A := ordinaryPowerRing r β s
  let E := ordinaryPowerExterior r β s
  let q := Ideal.Quotient.mkₐ K (powerMomentIdeal r β s)
  let b := Pi.basisFun A (Fin n ⊕ Fin n)
  letI : Module.Finite K A := powerMoment_quotient_finite r β s hβ
  letI : Module.Finite A E := Module.Finite.of_basis b.ExteriorAlgebra
  letI : Module.Finite K E := Module.Finite.trans A E
  obtain ⟨ε, hε⟩ := powerMoment_quotient_frobenius r β s hr hs hβ
  let J := Colex (Finset (Fin n ⊕ Fin n))
  letI : Fintype J := Fintype.ofEquiv (Finset (Fin n ⊕ Fin n)) toColex
  let coord : J → E →ₗ[K] A := fun T ↦ (b.ExteriorAlgebra.coord (ofColex T)).restrictScalars K
  let B : J → Submodule K A := fun T ↦ if ValidWord (ofColex T) then
    coefficientAnnihilator q
      (endpointIdeal (pairedPowerData r u v β (wordMark (ofColex T))) n (wordHeight (ofColex T) n))
    else ⊥
  have hdim : Module.finrank K (pairedPowerHarmonics r u v β s) ≤
      ∑ T : J, Module.finrank K (B T) := by
    apply finrank_le_sum_leading_constraints coord B Finset.univ (pairedPowerHarmonics r u v β s)
    · intro w hw T hT
      exact (hT (Finset.mem_univ T)).elim
    · intro w hw hz
      apply b.ExteriorAlgebra.repr.injective
      ext T
      simpa only [coord,LinearMap.restrictScalars_apply,Module.Basis.coord_apply,
        ofColex_toColex,map_zero,Finsupp.zero_apply] using hz (toColex T)
    · intro T hT w hw hlater
      change b.ExteriorAlgebra.repr w (ofColex T) ∈ B T
      by_cases hc : b.ExteriorAlgebra.repr w (ofColex T) = 0
      · rw [hc]
        exact zero_mem _
      · have hmax : ∀ U, b.ExteriorAlgebra.repr w U ≠ 0 → toColex U ≤ T := by
          intro U hU
          by_contra hle
          exact hU (hlater (toColex U) (lt_of_not_ge hle))
        obtain ⟨hvalid, hann⟩ := pairedPower_largest_ungraded_endpoint r u v β s hr huv hβ hfac
          w hw (ofColex T) hc (by simpa only [toColex_ofColex] using hmax)
        simpa only [B, if_pos hvalid] using hann
  have hB (T : J) : Module.finrank K (B T) ≤ pairedWordBoxCard r u v s (ofColex T) := by
    by_cases hvalid : ValidWord (ofColex T)
    · have he : B T=coefficientAnnihilator q
          (endpointIdeal (pairedPowerData r u v β (wordMark (ofColex T))) n (wordHeight (ofColex T) n)) :=
        if_pos hvalid
      have hfinrank := (LinearEquiv.ofEq _ _ he).finrank_eq
      rw [hfinrank]
      simp only [pairedWordBoxCard,if_pos hvalid]
      have hsteps : ∀ j (hj : j < n), HeightStep (wordMark (ofColex T) ⟨j, hj⟩)
          (wordHeight (ofColex T) j) (wordHeight (ofColex T) (j + 1)) :=
        wordHeight_steps (ofColex T) hvalid
      letI := pairedPowerEndpoint_quotient_finite r u v β (wordMark (ofColex T))
        (wordHeight (ofColex T)) (wordHeight_zero _) s hs huv hsteps hβ
      have hle := coefficientAnnihilator_finrank_le q (Ideal.Quotient.mk_surjective)
        (endpointIdeal (pairedPowerData r u v β (wordMark (ofColex T))) n (wordHeight (ofColex T) n))
        ε hε.separatingLeft
      rw [pairedPowerEndpoint_finrank r u v β (wordMark (ofColex T))
        (wordHeight (ofColex T)) (wordHeight_zero _) s hs hr huv hsteps hβ] at hle
      exact hle
    · have he : B T=⊥ := if_neg hvalid
      have hfinrank := (LinearEquiv.ofEq _ _ he).finrank_eq
      rw [hfinrank]
      simp only [pairedWordBoxCard,if_neg hvalid,finrank_bot,le_refl]
  calc
    _ ≤ ∑ T : J, Module.finrank K (B T) := hdim
    _ ≤ ∑ T : J, pairedWordBoxCard r u v s (ofColex T) :=
      Finset.sum_le_sum (fun T hT ↦ hB T)
    _ = _ := (ofColex.sum_comp (pairedWordBoxCard r u v s))

end PaperVerification.Fermion
