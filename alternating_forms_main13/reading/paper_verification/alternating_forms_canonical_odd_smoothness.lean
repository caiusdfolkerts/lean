module

public import PaperVerification.ProjGradedAlgEquivOver
public import PaperVerification.AlternatingFormsCoefficientFrames
public import PaperVerification.AlternatingFormsGenericSmoothness
import Mathlib.Tactic.FinCases

/-!
# Smoothness of the actual canonical odd common-isotropic scheme

An explicit surjective orbit Jacobian makes the invertible odd orbit meet
the proved generic-smoothness open.  The genuine Proj isomorphism transports
smoothness to the canonical pair.  This is independent of a classification
of pencils, a Borel fixed-point theorem, or a reduced-point interpretation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped BigOperators Classical

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [CharZero K] {t n m : ℕ}

theorem isotropicProjLinearIso_hom_over
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n))) :
    (isotropicProjLinearIso (t := t) e forms forms' hforms).hom ≫
      isotropicStructureMap forms = isotropicStructureMap forms' :=
  projIsoOfGradedAlgEquiv_hom_over _ _ _

theorem isotropicProjLinearIso_inv_over
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n))) :
    (isotropicProjLinearIso (t := t) e forms forms' hforms).inv ≫
      isotropicStructureMap forms' = isotropicStructureMap forms :=
  projIsoOfGradedAlgEquiv_inv_over _ _ _

/-- Smoothness transports over the original coefficient field. -/
theorem isotropicStructureMap_smooth_linearEquiv
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n))) :
    Smooth (isotropicStructureMap (t := t) forms) ↔
      Smooth (isotropicStructureMap (t := t) forms') := by
  constructor
  · intro h
    letI := h
    rw [← isotropicProjLinearIso_hom_over e forms forms' hforms]
    infer_instance
  · intro h
    letI := h
    rw [← isotropicProjLinearIso_inv_over e forms forms' hforms]
    infer_instance

theorem isotropicStructureMap_smooth_of_ideal_eq
    (forms forms' : Fin m → StrictPairs n → K)
    (hI : isotropicPluckerIdeal (t := t) forms = isotropicPluckerIdeal forms') :
    Smooth (isotropicStructureMap (t := t) forms) ↔
      Smooth (isotropicStructureMap (t := t) forms') := by
  have h (Q Q' : Ideal (MvPolynomial (PluckerIndex (t+2) n) K))
      (hQ : Q.IsHomogeneous (homogeneousSubmodule _ K))
      (hQ' : Q'.IsHomogeneous (homogeneousSubmodule _ K)) (he : Q = Q') :
      Smooth (HomogeneousQuotientCharts.structureMap Q hQ) ↔
        Smooth (HomogeneousQuotientCharts.structureMap Q' hQ') := by
    subst Q'
    rfl
  exact h _ _ _ _ hI

theorem oddOrbitToPath_first (k : ℕ) :
    exteriorPower.map 2 (oddOrbitToPathEquiv (K := K) k).toLinearMap
      (oddOrbitFirstForm k) =
    twoFormOfCoefficients (oddPluckerForms (k+1) 1)
      (Pi.basisFun K (Fin (2*(k+1)+1))) := by
  rw [oddOrbitFirstForm_eq_path, oddPluckerForms_second]
  rw [oddPathSecondQuadratic_map]
  congr 1
  funext i
  change (standardBasisEquiv (oddOrbitInterleavedBasis (K := K) k)).symm
    (oddOrbitInterleavedBasis k i) = Pi.basisFun K (Fin (2*(k+1)+1)) i
  apply (standardBasisEquiv (oddOrbitInterleavedBasis (K := K) k)).injective
  rw [LinearEquiv.apply_symm_apply, standardBasisEquiv_basisFun]

theorem oddOrbitToPath_second (k : ℕ) :
    exteriorPower.map 2 (oddOrbitToPathEquiv (K := K) k).toLinearMap
      (oddOrbitSecondForm k) =
    -twoFormOfCoefficients (oddPluckerForms (k+1) 0)
      (Pi.basisFun K (Fin (2*(k+1)+1))) := by
  rw [oddOrbitSecondForm_eq_path, map_neg, oddPluckerForms_first]
  congr 1
  rw [oddPathFirstQuadratic_map]
  congr 1
  funext i
  change (standardBasisEquiv (oddOrbitInterleavedBasis (K := K) k)).symm
    (oddOrbitInterleavedBasis k i) = Pi.basisFun K (Fin (2*(k+1)+1)) i
  apply (standardBasisEquiv (oddOrbitInterleavedBasis (K := K) k)).injective
  rw [LinearEquiv.apply_symm_apply, standardBasisEquiv_basisFun]

/-- Conjugating the ambient linear action commutes with every exterior power. -/
theorem exteriorPower_conjugate_apply
    {M N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (e : M ≃ₗ[K] N) (g : M ≃ₗ[K] M) (d : ℕ) (x : ⋀[K]^d M) :
    exteriorPower.map d (e.symm.trans (g.trans e)).toLinearMap
      (exteriorPower.map d e.toLinearMap x) =
      exteriorPower.map d e.toLinearMap (exteriorPower.map d g.toLinearMap x) := by
  have he : (e.symm.trans (g.trans e)).toLinearMap.comp e.toLinearMap =
      e.toLinearMap.comp g.toLinearMap := by
    ext v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply]
  change ((exteriorPower.map d (e.symm.trans (g.trans e)).toLinearMap).comp
    (exteriorPower.map d e.toLinearMap)) x = _
  rw [← exteriorPower.map_comp, he, exteriorPower.map_comp]
  rfl

/-- The actual canonical odd common-isotropic scheme is smooth, in every
ambient odd dimension at least three and for every plane dimension at least two. -/
theorem canonicalOdd_isotropicStructureMap_smooth_succ (k t : ℕ) :
    Smooth (isotropicStructureMap (t := t) (oddPluckerForms (K := K) (k+1))) := by
  letI : Infinite K := Infinite.of_injective Nat.cast Nat.cast_injective
  let n := 2*(k+1)+1
  obtain ⟨Q,hQ,_,hsmooth⟩ := generic_commonIsotropic_smooth (K := K) t n 2
  obtain ⟨x,hx,hQx⟩ := oddOrbit_meets_principal_open k Q hQ
  let p := actualOrbitPolynomials (row := oddOrbitSlotRow k) (col := oddOrbitSlotCol k)
    (oddOrbitFirstForm (K := K) k) (oddOrbitSecondForm k)
  let base := orbitPairCoefficientPoint
    (actualOrbitBasePoint (row := oddOrbitSlotRow k) (col := oddOrbitSlotCol k)
      (oddOrbitFirstForm (K := K) k) (oddOrbitSecondForm k))
  let y := fun i => eval x (orbitPairPolynomialCoordinates p i)
  let a := oddOrbitToPairCoefficients k y
  let b := oddOrbitToPairCoefficients k base
  let forms : Fin 2 → StrictPairs n → K := fun l i => b (l,i)
  let forms' : Fin 2 → StrictPairs n → K := fun l i => a (l,i)
  have hs : Smooth (isotropicStructureMap (t := t) forms') :=
    hsmooth a (by simpa only [aeval_eq_eval] using hQx)
  let X : Matrix (OddOrbitMode k) (OddOrbitMode k) K := Matrix.of (fun i j => x (i,j))
  have hX : X.det ≠ 0 := by simpa only [X, orbitDeterminant_eval] using hx
  let g := orbitTransposeEquiv X hX
  let e := oddOrbitToPathEquiv (K := K) k
  let E := e.symm.trans (g.trans e)
  have hb : (twoFormOfCoefficients (forms 0) (Pi.basisFun K (Fin n)),
      twoFormOfCoefficients (forms 1) (Pi.basisFun K (Fin n))) =
      (exteriorPower.map 2 e.toLinearMap (oddOrbitFirstForm k),
       exteriorPower.map 2 e.toLinearMap (oddOrbitSecondForm k)) := by
    change pairCoefficientExteriorEquiv n b = _
    rw [oddOrbitToPairCoefficients_forms]
    dsimp only [base, oddOrbitExteriorBasis]
    rw [actualOrbitBasePoint_forms]
  have ha : (twoFormOfCoefficients (forms' 0) (Pi.basisFun K (Fin n)),
      twoFormOfCoefficients (forms' 1) (Pi.basisFun K (Fin n))) =
      (exteriorPower.map 2 e.toLinearMap
        (exteriorPower.map 2 g.toLinearMap (oddOrbitFirstForm k)),
       exteriorPower.map 2 e.toLinearMap
        (exteriorPower.map 2 g.toLinearMap (oddOrbitSecondForm k))) := by
    change pairCoefficientExteriorEquiv n a = _
    rw [oddOrbitToPairCoefficients_forms]
    dsimp only [y, p, oddOrbitExteriorBasis]
    rw [actualOrbitPolynomials_forms_eval (oddOrbitPairSlots k)]
    rfl
  have hforms (l : Fin 2) : exteriorPower.map 2 E.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n)) := by
    fin_cases l
    · change exteriorPower.map 2 E.toLinearMap
        (twoFormOfCoefficients (forms 0) (Pi.basisFun K (Fin n))) =
          twoFormOfCoefficients (forms' 0) (Pi.basisFun K (Fin n))
      rw [show twoFormOfCoefficients (forms 0) (Pi.basisFun K (Fin n)) = _ from
        congrArg Prod.fst hb,
        show twoFormOfCoefficients (forms' 0) (Pi.basisFun K (Fin n)) = _ from
          congrArg Prod.fst ha]
      exact exteriorPower_conjugate_apply e g 2 (oddOrbitFirstForm k)
    · change exteriorPower.map 2 E.toLinearMap
        (twoFormOfCoefficients (forms 1) (Pi.basisFun K (Fin n))) =
          twoFormOfCoefficients (forms' 1) (Pi.basisFun K (Fin n))
      rw [show twoFormOfCoefficients (forms 1) (Pi.basisFun K (Fin n)) = _ from
        congrArg Prod.snd hb,
        show twoFormOfCoefficients (forms' 1) (Pi.basisFun K (Fin n)) = _ from
          congrArg Prod.snd ha]
      exact exteriorPower_conjugate_apply e g 2 (oddOrbitSecondForm k)
  have hsbase := (isotropicStructureMap_smooth_linearEquiv
    (t := t) E forms forms' hforms).mpr hs
  have hb₀ := congrArg Prod.fst hb
  have hb₁ := congrArg Prod.snd hb
  change twoFormOfCoefficients (forms 0) (Pi.basisFun K (Fin n)) =
    exteriorPower.map 2 (oddOrbitToPathEquiv k).toLinearMap (oddOrbitFirstForm k) at hb₀
  change twoFormOfCoefficients (forms 1) (Pi.basisFun K (Fin n)) =
    exteriorPower.map 2 (oddOrbitToPathEquiv k).toLinearMap (oddOrbitSecondForm k) at hb₁
  rw [oddOrbitToPath_first] at hb₀
  rw [oddOrbitToPath_second] at hb₁
  have heForms : forms = pairCoefficientForms (forms 0) (forms 1) := by
    funext l
    fin_cases l <;> rfl
  have heCanonical : oddPluckerForms (K := K) (k+1) =
      pairCoefficientForms (oddPluckerForms (k+1) 0) (oddPluckerForms (k+1) 1) := by
    funext l
    fin_cases l <;> rfl
  have hI : isotropicPluckerIdeal (t := t) forms =
      isotropicPluckerIdeal (oddPluckerForms (K := K) (k+1)) := by
    rw [heForms,heCanonical]
    apply pair_isotropicIdeal_eq_of_quadraticSpan_eq
    rw [hb₀,hb₁]
    exact (quadraticSpan_swap_neg _ _).symm
  exact (isotropicStructureMap_smooth_of_ideal_eq forms _ hI).mp hsbase

/-- The dimension-one boundary has a unique coefficient tuple; generic
smoothness therefore applies to that tuple itself. -/
theorem canonicalOdd_isotropicStructureMap_smooth_zero (t : ℕ) :
    Smooth (isotropicStructureMap (t := t) (oddPluckerForms (K := K) 0)) := by
  obtain ⟨Q,hQ,⟨a,ha⟩,hsmooth⟩ := generic_commonIsotropic_smooth (K := K) t 1 2
  have he : (fun l i => a (l,i)) = oddPluckerForms (K := K) 0 := by
    funext l i
    have hi := i.property
    have h₀ := i.val.1.isLt
    have h₁ := i.val.2.isLt
    change i.val.1.val < i.val.2.val at hi
    omega
  exact (congrArg (fun forms : Fin 2 → StrictPairs 1 → K =>
    Smooth (isotropicStructureMap (t := t) forms)) he).mp (hsmooth a ha)

/-- Uniform canonical odd smoothness with no omitted ambient dimension. -/
theorem canonicalOdd_isotropicStructureMap_smooth (k t : ℕ) :
    Smooth (isotropicStructureMap (t := t) (oddPluckerForms (K := K) k)) := by
  cases k with
  | zero => exact canonicalOdd_isotropicStructureMap_smooth_zero t
  | succ k => exact canonicalOdd_isotropicStructureMap_smooth_succ k t

/-- An actual isotropic row chart over the coefficient field supplies a point
of the original projective scheme. -/
theorem isotropicProj_nonempty_of_chart_point
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (A : IsotropicChartPoint p forms K) :
    Nonempty (Proj (isotropicProjectiveGrading (t := t) forms)) := by
  let x : Spec (CommRingCat.of K) := Classical.arbitrary _
  let z := (Spec.map (CommRingCat.ofHom A.toAlgHom.toRingHom)) x
  let y := (isotropicProjBasicOpenIso p forms).inv z
  exact ⟨y.val⟩

/-- The canonical odd scheme is nonempty throughout the paper's entire
plane range. Its witness is the original coordinate plane on even path vertices. -/
theorem canonicalOdd_isotropicProj_nonempty (k t : ℕ) (h : t+2 ≤ k+1) :
    Nonempty (Proj (isotropicProjectiveGrading (t := t) (oddPluckerForms (K := K) k))) := by
  let p := oddCoordinatePivot k t h
  apply isotropicProj_nonempty_of_chart_point p (oddPluckerForms k)
  refine ⟨pluckerCoordinatePlane p, ?_, oddCoordinatePlane_isotropic k t h⟩
  ext i j
  simp only [Matrix.submatrix_apply, id_eq, pluckerCoordinatePlane, Matrix.one_apply,
    p.property.injective.eq_iff, eq_comm]

/-- Smoothness and nonemptiness for every canonical odd case of plane
dimension at least two occurring in Section 4. -/
theorem canonicalOdd_isotropicProj_nonempty_smooth
    (k t : ℕ) (h : t+2 ≤ k+1) :
    Nonempty (Proj (isotropicProjectiveGrading (t := t) (oddPluckerForms (K := K) k))) ∧
      Smooth (isotropicStructureMap (t := t) (oddPluckerForms (K := K) k)) :=
  ⟨canonicalOdd_isotropicProj_nonempty k t h,
    canonicalOdd_isotropicStructureMap_smooth k t⟩

end PaperVerification.AlternatingForms
