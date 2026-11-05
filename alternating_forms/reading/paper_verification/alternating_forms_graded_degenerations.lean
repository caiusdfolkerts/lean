module

public import PaperVerification.WeightedReesGradedSpecialization
public import PaperVerification.AlternatingFormsOddPrincipal
public import PaperVerification.AlternatingFormsPluckerHomogeneity

/-!
# Ordinary graded flat degenerations in Theorem 1.3

The families are the original weighted Rees images. The parameter has
degree zero; the original Plücker coordinates have degree one. The maps
already used to identify their special and nonzero fibers preserve every
ordinary homogeneous piece. The one-plane boundary is included.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open MvPolynomial PaperVerification.WeightedInitialFiber

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {s n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A flat degeneration with the actual ordinary coordinate grading.

The family is fixed to the literal weighted Rees image, whose grading over
`K[t]` was constructed coefficient by coefficient in
`reesParameterInternalGrading`. Both endpoint maps must identify every
ordinary homogeneous piece. The source and target may use different
coordinate presentations; this is needed for the good-coordinate Hibi family.
This structure is constructed below, never assumed as a geometric hypothesis. -/
structure CoordinateGradedReesDegeneration {σ τ υ : Type*}
    (Q : Ideal (MvPolynomial σ K))
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ)
    (sourceIdeal : Ideal (MvPolynomial τ K))
    (specialIdeal : Ideal (MvPolynomial υ K)) where
  flat : Module.Flat (Polynomial K) (reesAlgebra Q w)
  specialFiberEquiv : ZeroFiber Q w ≃ₐ[K] MvPolynomial υ K ⧸ specialIdeal
  specialFiber_piece : ∀ d : ℕ,
    ((zeroFiberCoordinateGrading Q hQ w).piece d).map
      specialFiberEquiv.toLinearEquiv.toLinearMap =
        HomogeneousIdealPieces.piece specialIdeal d
  nonzeroFiberEquiv : ∀ (c : K), c ≠ 0 →
    ParameterFiber Q w c ≃ₐ[K] MvPolynomial τ K ⧸ sourceIdeal
  nonzeroFiber_piece : ∀ (c : K) (hc : c ≠ 0) (d : ℕ),
    ((parameterFiberCoordinateGrading Q hQ w c).piece d).map
      (nonzeroFiberEquiv c hc).toLinearEquiv.toLinearMap =
        HomogeneousIdealPieces.piece sourceIdeal d

theorem intervalIdeal_coordinate_homogeneous (α β : Fin s → Fin n) (hs : 0 < s) :
    (intervalPluckerIdeal (K := K) α β).IsHomogeneous
      (homogeneousSubmodule (PluckerIndex s n) K) := by
  unfold intervalPluckerIdeal
  apply (matrixPluckerIdeal_isHomogeneous hs).sup
  apply Ideal.homogeneous_span
  rintro p ⟨I, _, rfl⟩
  exact ⟨1, isHomogeneous_X K I⟩

namespace Hibi

/-- The literal Hibi relations are homogeneous quadrics in the original good coordinates. -/
theorem relationIdeal_coordinate_homogeneous (α β : Fin s → Fin n) :
    (relationIdeal (K := K) α β).IsHomogeneous
      (homogeneousSubmodule (IntervalIndex α β) K) := by
  unfold relationIdeal
  apply Ideal.homogeneous_span
  rintro p ⟨I, J, _, rfl⟩
  refine ⟨2, ?_⟩
  change (X I * X J - X (meet α β I J) * X (join α β I J) :
    MvPolynomial (IntervalIndex α β) K).IsHomogeneous 2
  exact ((isHomogeneous_X K I).mul (isHomogeneous_X K J)).sub
    ((isHomogeneous_X K (meet α β I J)).mul (isHomogeneous_X K (join α β I J)))

/-- The actual ordinary grading on the Hibi endpoint ring. -/
abbrev hibiOrdinaryGrading (α β : Fin s → Fin n) :=
  HomogeneousQuotientProjective.grading (relationIdeal (K := K) α β)
    (relationIdeal_coordinate_homogeneous α β)

end Hibi

/-- The literal odd family, with the original ordinary-coordinate pieces. -/
abbrev oddRichardsonCoordinateGrading (k t : ℕ) :=
  reesCoordinateGrading
    (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
    (isotropicPluckerIdeal_isHomogeneous _) (pluckerVertexWeight (oddNatVertexWeight k))

/-- The same family as a genuinely graded algebra over its original parameter ring. -/
abbrev oddRichardsonParameterPiece (k t : ℕ) :=
  reesParameterPiece
    (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
    (isotropicPluckerIdeal_isHomogeneous _) (pluckerVertexWeight (oddNatVertexWeight k))

section CharacteristicZero

variable [CharZero K]

theorem oddRichardsonSpecialFiberEquiv_coordinate_piece (k t : ℕ) (hs : t + 2 ≤ k + 1)
    (d : ℕ) :
    ((zeroFiberCoordinateGrading
      (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
      (isotropicPluckerIdeal_isHomogeneous _) (pluckerVertexWeight (oddNatVertexWeight k))).piece d).map
        (oddRichardsonSpecialFiberEquiv (K := K) k t hs).toLinearEquiv.toLinearMap =
      HomogeneousIdealPieces.piece
        (intervalPluckerIdeal (oddIntervalLower k (t + 2) hs)
          (oddIntervalUpper k (t + 2) hs)) d :=
  specialFiberEquivOfInitial_coordinate_piece _ _ _ _ (odd_isotropic_initial_eq_interval (K := K) k t hs) d

theorem oddRichardsonNonzeroFiberEquiv_coordinate_piece (k t : ℕ)
    (c : K) (hc : c ≠ 0) (d : ℕ) :
    ((parameterFiberCoordinateGrading
      (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
      (isotropicPluckerIdeal_isHomogeneous _) (pluckerVertexWeight (oddNatVertexWeight k)) c).piece d).map
        (oddRichardsonNonzeroFiberEquiv (K := K) k t c hc).toLinearEquiv.toLinearMap =
      HomogeneousIdealPieces.piece
        (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) d :=
  nonzeroFiberEquiv_coordinate_piece _ _ _ c hc d

/-- The original one-plane special-fiber map with the full odd interval presentation. -/
def onePlaneOddRichardsonSpecialFiberEquiv (k : ℕ) :
    ZeroFiber (matrixPluckerIdeal (K := K) (s := 1) (n := 2 * k + 1))
      (pluckerVertexWeight (oddNatVertexWeight k)) ≃ₐ[K]
      MvPolynomial (PluckerIndex 1 (2 * k + 1)) K ⧸
        intervalPluckerIdeal (oddIntervalLower k 1 (by omega))
          (oddIntervalUpper k 1 (by omega)) :=
  specialFiberEquivOfInitial _ _ _
    ((onePlane_initialIdeal _).trans (onePlane_odd_intervalIdeal k (by omega)).symm)

theorem onePlaneOddRichardsonSpecialFiberEquiv_coordinate_piece (k d : ℕ) :
    ((zeroFiberCoordinateGrading
      (matrixPluckerIdeal (K := K) (s := 1) (n := 2 * k + 1))
      (matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1))
      (pluckerVertexWeight (oddNatVertexWeight k))).piece d).map
        (onePlaneOddRichardsonSpecialFiberEquiv (K := K) k).toLinearEquiv.toLinearMap =
      HomogeneousIdealPieces.piece
        (intervalPluckerIdeal (oddIntervalLower k 1 (by omega))
          (oddIntervalUpper k 1 (by omega))) d :=
  specialFiberEquivOfInitial_coordinate_piece _ _ _ _ _ d

/-- The complete first graded flat family in Theorem 1.3 for every
`2 ≤ s ≤ k+1`, written `s=t+2`, with its original fiber maps. -/
def oddRichardsonGradedFlatDegeneration (k t : ℕ) (hs : t + 2 ≤ k + 1) :
    CoordinateGradedReesDegeneration
      (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
      (isotropicPluckerIdeal_isHomogeneous _)
      (pluckerVertexWeight (oddNatVertexWeight k))
      (isotropicPluckerIdeal (t := t) (oddPluckerForms k))
      (intervalPluckerIdeal (oddIntervalLower k (t + 2) hs)
        (oddIntervalUpper k (t + 2) hs)) where
  flat := inferInstance
  specialFiberEquiv := oddRichardsonSpecialFiberEquiv k t hs
  specialFiber_piece := oddRichardsonSpecialFiberEquiv_coordinate_piece k t hs
  nonzeroFiberEquiv := oddRichardsonNonzeroFiberEquiv k t
  nonzeroFiber_piece := oddRichardsonNonzeroFiberEquiv_coordinate_piece k t

/-- The first graded flat family at `s=1`, including `k=0`. -/
def onePlaneOddRichardsonGradedFlatDegeneration (k : ℕ) :
    CoordinateGradedReesDegeneration
      (matrixPluckerIdeal (K := K) (s := 1) (n := 2 * k + 1))
      (matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1))
      (pluckerVertexWeight (oddNatVertexWeight k))
      (matrixPluckerIdeal (s := 1) (n := 2 * k + 1))
      (intervalPluckerIdeal (oddIntervalLower k 1 (by omega))
        (oddIntervalUpper k 1 (by omega))) where
  flat := inferInstance
  specialFiberEquiv := onePlaneOddRichardsonSpecialFiberEquiv k
  specialFiber_piece := onePlaneOddRichardsonSpecialFiberEquiv_coordinate_piece k
  nonzeroFiberEquiv := nonzeroFiberEquiv _ _
  nonzeroFiber_piece := nonzeroFiberEquiv_coordinate_piece _ _ _

namespace Hibi

variable (α β : Fin s → Fin n)

theorem goodToInterval_coordinate_homogeneous (hs : 0 < s) :
    TauCeti.LinearMap.IsHomogeneous (goodToInterval (K := K) α β).toLinearMap
      (ordinaryPolynomialGrading (K := K) (σ := IntervalIndex α β)).piece
      (HomogeneousIdealPieces.grading (intervalPluckerIdeal α β)
        (intervalIdeal_coordinate_homogeneous α β hs)).piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro d p hp
  rw [add_zero, HomogeneousIdealPieces.grading_piece]
  have hp' : p.IsHomogeneous d := by
    rwa [ordinaryPolynomialGrading_piece] at hp
  exact ⟨rename (fun I : IntervalIndex α β ↦ I.val) p, hp'.rename_isHomogeneous, rfl⟩

theorem goodBandIdeal_coordinate_homogeneous (hα : Monotone α) (hβ : Monotone β)
    (hs : 0 < s) :
    (goodBandIdeal (K := K) α β).IsHomogeneous
      (homogeneousSubmodule (IntervalIndex α β) K) := by
  rw [← goodToInterval_kernel α β hα hβ hs]
  have h := (goodToInterval_coordinate_homogeneous (K := K) α β hs).isHomogeneous_ker
  change DirectSum.SetLike.IsHomogeneous
    (TauCeti.InternalGrading.ofDecomposition (homogeneousSubmodule (IntervalIndex α β) K)).piece
    ((RingHom.ker (goodToInterval (K := K) α β).toRingHom).restrictScalars K) at h
  rwa [TauCeti.InternalGrading.isHomogeneous_ofDecomposition_piece_iff] at h

theorem goodBandQuotientEquiv_coordinate_homogeneous (hα : Monotone α) (hβ : Monotone β)
    (hs : 0 < s) :
    TauCeti.LinearMap.IsHomogeneous
      (goodBandQuotientEquiv (K := K) α β hα hβ hs).toLinearEquiv.toLinearMap
      (HomogeneousIdealPieces.grading (goodBandIdeal α β)
        (goodBandIdeal_coordinate_homogeneous α β hα hβ hs)).piece
      (HomogeneousIdealPieces.grading (intervalPluckerIdeal α β)
        (intervalIdeal_coordinate_homogeneous α β hs)).piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro d a ha
  rw [HomogeneousIdealPieces.grading_piece] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  change goodBandQuotientEquiv α β hα hβ hs (Ideal.Quotient.mk _ p) ∈ _
  rw [goodBandQuotientEquiv_mk]
  have hp' : p ∈ (ordinaryPolynomialGrading (K := K) (σ := IntervalIndex α β)).piece d := by
    rwa [ordinaryPolynomialGrading_piece]
  exact (goodToInterval_coordinate_homogeneous (K := K) α β hs).map_mem hp'

theorem goodBandQuotientEquiv_coordinate_piece (hα : Monotone α) (hβ : Monotone β)
    (hs : 0 < s) (d : ℕ) :
    (HomogeneousIdealPieces.piece (goodBandIdeal (K := K) α β) d).map
      (goodBandQuotientEquiv (K := K) α β hα hβ hs).toLinearEquiv.toLinearMap =
        HomogeneousIdealPieces.piece (intervalPluckerIdeal α β) d := by
  simpa only [HomogeneousIdealPieces.grading_piece] using
    GradedAlgebraQuotient.homogeneousEquiv_map_piece _ _
      (goodBandQuotientEquiv (K := K) α β hα hβ hs).toLinearEquiv
      (goodBandQuotientEquiv_coordinate_homogeneous α β hα hβ hs) d

/-- The literal Richardson-to-Hibi family with the ordinary Plücker grading. -/
abbrev hibiCoordinateGrading (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) :=
  reesCoordinateGrading (goodBandIdeal (K := K) α β)
    (goodBandIdeal_coordinate_homogeneous α β hα hβ hs) (diagonalWeight α β)

abbrev hibiParameterPiece (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) :=
  reesParameterPiece (goodBandIdeal (K := K) α β)
    (goodBandIdeal_coordinate_homogeneous α β hα hβ hs) (diagonalWeight α β)

theorem hibiSpecialFiberEquiv_coordinate_piece (hα : Monotone α) (hβ : Monotone β)
    (hs : 0 < s) (d : ℕ) :
    ((zeroFiberCoordinateGrading (goodBandIdeal (K := K) α β)
      (goodBandIdeal_coordinate_homogeneous α β hα hβ hs) (diagonalWeight α β)).piece d).map
        (hibiSpecialFiberEquiv (K := K) α β hα hβ hs).toLinearEquiv.toLinearMap =
      HomogeneousIdealPieces.piece (relationIdeal α β) d :=
  specialFiberEquivOfInitial_coordinate_piece _ _ _ _
    (goodBandInitial_eq_hibi (K := K) α β hα hβ hs) d

theorem hibiNonzeroFiberEquiv_coordinate_piece (hα : Monotone α) (hβ : Monotone β)
    (hs : 0 < s) (c : K) (hc : c ≠ 0) (d : ℕ) :
    ((parameterFiberCoordinateGrading (goodBandIdeal (K := K) α β)
      (goodBandIdeal_coordinate_homogeneous α β hα hβ hs) (diagonalWeight α β) c).piece d).map
        (hibiNonzeroFiberEquiv (K := K) α β hα hβ hs c hc).toLinearEquiv.toLinearMap =
      HomogeneousIdealPieces.piece (intervalPluckerIdeal α β) d := by
  change ((parameterFiberCoordinateGrading (goodBandIdeal (K := K) α β)
    (goodBandIdeal_coordinate_homogeneous α β hα hβ hs) (diagonalWeight α β) c).piece d).map
      ((goodBandQuotientEquiv (K := K) α β hα hβ hs).toLinearEquiv.toLinearMap.comp
        (nonzeroFiberEquiv (goodBandIdeal α β) (diagonalWeight α β) c hc).toLinearEquiv.toLinearMap) = _
  rw [Submodule.map_comp, nonzeroFiberEquiv_coordinate_piece,
    goodBandQuotientEquiv_coordinate_piece]

/-- The complete second graded flat family in Theorem 1.3. Its nonzero
fibers are the full Richardson coordinate ring, not merely the isomorphic
presentation with good coordinates. This includes every positive rank. -/
def hibiGradedFlatDegeneration (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) :
    CoordinateGradedReesDegeneration (goodBandIdeal (K := K) α β)
      (goodBandIdeal_coordinate_homogeneous α β hα hβ hs) (diagonalWeight α β)
      (intervalPluckerIdeal α β) (relationIdeal α β) where
  flat := inferInstance
  specialFiberEquiv := hibiSpecialFiberEquiv α β hα hβ hs
  specialFiber_piece := hibiSpecialFiberEquiv_coordinate_piece α β hα hβ hs
  nonzeroFiberEquiv := hibiNonzeroFiberEquiv α β hα hβ hs
  nonzeroFiber_piece := hibiNonzeroFiberEquiv_coordinate_piece α β hα hβ hs

end Hibi
end CharacteristicZero
end PaperVerification.AlternatingForms
