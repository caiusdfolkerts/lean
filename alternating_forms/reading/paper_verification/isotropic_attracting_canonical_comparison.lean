module

public import PaperVerification.IsotropicAttractingChartRings
public import PaperVerification.OddPathIndependent
public import PaperVerification.AlternatingFormsSectionFourGeometry

/-!
# The attracting-chart coordinates are the paper's actual canonical pencil

The elimination files use the chain order `b₀,…,bₖ,aₖ,…,a₁`.  The original
geometric proof uses `b₀,a₁,b₁,…,aₖ,bₖ`.  The explicit permutation below
identifies both literal exterior two-forms, hence their original homogeneous
ideals and projective zero schemes.  Smoothness is transported over the
ground field, with no extra geometric hypothesis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.IsotropicAttractingCharts

open AlgebraicGeometry CategoryTheory
open PaperVerification.AlternatingForms
open PaperVerification.IsotropicAttractingCoordinates
open PaperVerification.OddPathIndependent
open scoped BigOperators

variable {K : Type} [Field K]

/-- The exact coordinate permutation on vectors. -/
def pathChainLinearEquiv (k : ℕ) : (Fin (2*k+1) → K) ≃ₗ[K] (Fin (2*k+1) → K) where
  toFun x i := x ((pathChainEquiv k).symm i)
  invFun x i := x (pathChainEquiv k i)
  left_inv x := by funext i; exact congrArg x ((pathChainEquiv k).symm_apply_apply i)
  right_inv x := by funext i; exact congrArg x ((pathChainEquiv k).apply_symm_apply i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem orbitExteriorCoefficient_pathChain (k : ℕ) (i j : Fin (2*k+1))
    (f : ⋀[K]^2 (Fin (2*k+1) → K)) :
    orbitExteriorCoefficientMatrix
      (exteriorPower.map 2 (pathChainLinearEquiv (K := K) k).toLinearMap f)
      (pathChainEquiv k i) (pathChainEquiv k j) =
      orbitExteriorCoefficientMatrix f i j := by
  have h : (orbitExteriorCoefficient (K := K) (pathChainEquiv k i) (pathChainEquiv k j)).comp
      (exteriorPower.map 2 (pathChainLinearEquiv k).toLinearMap) =
        orbitExteriorCoefficient i j := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, orbitExteriorCoefficient_word,
      Function.comp_apply, LinearEquiv.coe_coe, pathChainLinearEquiv,
      Equiv.symm_apply_apply]
    change w 0 ((pathChainEquiv k).symm (pathChainEquiv k i)) *
        w 1 ((pathChainEquiv k).symm (pathChainEquiv k j)) -
      w 0 ((pathChainEquiv k).symm (pathChainEquiv k j)) *
        w 1 ((pathChainEquiv k).symm (pathChainEquiv k i)) = _
    simp only [Equiv.symm_apply_apply]
  exact congrArg (fun L : (⋀[K]^2 (Fin (2*k+1) → K)) →ₗ[K] K => L f) h

theorem coefficientMatrix_twoForm_upper {n : ℕ} (f : StrictPairs n → K)
    (i j : Fin n) (hij : i < j) :
    orbitExteriorCoefficientMatrix (twoFormOfCoefficients f (Pi.basisFun K (Fin n))) i j =
      f ⟨(i,j),hij⟩ :=
  orbitTwoFormOfSlots_coefficient (strictPairSlots n) f ⟨(i,j),hij⟩

/-- The chain coefficient convention is the literal alternating matrix
used by the polynomial equations. -/
theorem coefficientMatrix_canonicalCoefficient {n : ℕ} (c : ℕ) (i j : Fin n) :
    orbitExteriorCoefficientMatrix
      (twoFormOfCoefficients (canonicalCoefficient (K := K) c) (Pi.basisFun K (Fin n))) i j =
        formMatrix c i j := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact coefficientMatrix_twoForm_upper _ i j h
  · rw [orbitExteriorCoefficientMatrix_diagonal, formMatrix_self]
  · rw [orbitExteriorCoefficientMatrix_skew,
      coefficientMatrix_twoForm_upper _ j i h, formMatrix_swap]
    rfl

/-- A path coefficient is nonzero exactly on its correctly colored edge. -/
theorem oddPluckerForms_edge_value (k : ℕ) (l : Fin 2) (a : StrictPairs (2*k+1)) :
    oddPluckerForms (K := K) k l a =
      if a.val.1.val % 2 = l.val ∧ a.val.2.val = a.val.1.val + 1 then 1 else 0 := by
  classical
  have ha := a.property
  have hb := a.val.2.isLt
  have hl := l.isLt
  unfold oddPluckerForms
  by_cases h : a.val.1.val % 2 = l.val ∧ a.val.2.val = a.val.1.val + 1
  · rw [if_pos h]
    let i : Fin k := ⟨a.val.1.val / 2, by omega⟩
    have hai : a = oddPluckerEdge k l i := by
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> dsimp [oddPluckerEdge, i] <;> omega
    rw [Finset.sum_eq_single i]
    · simp [hai]
    · intro j _ hji
      have hne : a ≠ oddPluckerEdge k l j := by
        intro he
        have hv := congrArg (fun q : StrictPairs (2*k+1) => q.val.1.val) (hai.symm.trans he)
        have hj : j = i := by apply Fin.ext; dsimp [oddPluckerEdge] at hv; omega
        exact hji hj
      simp [hne]
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i _
    have hne : a ≠ oddPluckerEdge k l i := by
      intro he
      apply h
      rw [he]
      dsimp [oddPluckerEdge]
      constructor <;> omega
    simp [hne]

/-- The two anti-diagonals become the literal Section 4 path coefficients,
including their signs. -/
theorem formMatrix_pathChain_upper (k : ℕ) (l : Fin 2)
    (a : StrictPairs (2*k+1)) :
    formMatrix (R := K) (if l = 0 then 2*k+1 else 2*k)
      (pathChainEquiv k a.val.1) (pathChainEquiv k a.val.2) =
        sectionFourPluckerForms k l a := by
  have ha := a.property
  have hi := a.val.1.isLt
  have hj := a.val.2.isLt
  change a.val.1.val < a.val.2.val at ha
  fin_cases l
  · change formMatrix (R := K) (2*k+1)
      (pathChainEquiv k a.val.1) (pathChainEquiv k a.val.2) = oddPluckerForms k 1 a
    rw [oddPluckerForms_edge_value]
    simp only [Fin.val_one, pathChainEquiv, Equiv.coe_fn_mk, formMatrix, pathToChain]
    split_ifs <;> (try simp_all only [Fin.val_mk, Fin.mk_lt_mk, neg_zero, neg_neg, true_and, not_true_eq_false]) <;> omega
  · change formMatrix (R := K) (2*k)
      (pathChainEquiv k a.val.1) (pathChainEquiv k a.val.2) = -oddPluckerForms k 0 a
    rw [oddPluckerForms_edge_value]
    simp only [Fin.val_zero, pathChainEquiv, Equiv.coe_fn_mk, formMatrix, pathToChain]
    split_ifs <;> (try simp_all only [Fin.val_mk, Fin.mk_lt_mk, neg_zero, neg_neg, true_and, not_true_eq_false]) <;> omega

/-- Both actual exterior forms are carried to the chain coordinates. -/
theorem sectionFour_forms_pathChain (k : ℕ) (l : Fin 2) :
    exteriorPower.map 2 (pathChainLinearEquiv (K := K) k).toLinearMap
      (twoFormOfCoefficients (sectionFourPluckerForms k l) (Pi.basisFun K (Fin (2*k+1)))) =
        twoFormOfCoefficients (canonicalForms (2*k+1) (2*k) l)
          (Pi.basisFun K (Fin (2*k+1))) := by
  apply orbitExteriorCoefficientMatrix_injective
  funext u v
  obtain ⟨i, rfl⟩ := (pathChainEquiv k).surjective u
  obtain ⟨j, rfl⟩ := (pathChainEquiv k).surjective v
  rw [orbitExteriorCoefficient_pathChain]
  change _ = orbitExteriorCoefficientMatrix
    (twoFormOfCoefficients (canonicalCoefficient (if l = 0 then 2*k+1 else 2*k))
      (Pi.basisFun K (Fin (2*k+1)))) _ _
  rw [coefficientMatrix_canonicalCoefficient]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [coefficientMatrix_twoForm_upper _ i j h]
    exact (formMatrix_pathChain_upper k l ⟨(i,j),h⟩).symm
  · rw [orbitExteriorCoefficientMatrix_diagonal, formMatrix_self]
  · rw [orbitExteriorCoefficientMatrix_skew, coefficientMatrix_twoForm_upper _ j i h,
      formMatrix_swap]
    exact congrArg Neg.neg (formMatrix_pathChain_upper k l ⟨(j,i),h⟩).symm

variable [CharZero K]

/-- The attracting-coordinate scheme is isomorphic to the paper's actual
Section 4 scheme, through the displayed linear change of basis. -/
def chainSectionFourIso (k t : ℕ) :
    Proj (isotropicProjectiveGrading (t := t)
      (canonicalForms (K := K) (n := 2*k+1) (2*k+1) (2*k))) ≅
      Proj (isotropicProjectiveGrading (t := t) (sectionFourPluckerForms (K := K) k)) :=
  isotropicProjLinearIso (pathChainLinearEquiv k) (sectionFourPluckerForms k)
    (canonicalForms (2*k+1) (2*k)) (sectionFour_forms_pathChain k)

theorem chainSectionFourIso_hom_over (k t : ℕ) :
    (chainSectionFourIso (K := K) k t).hom ≫
      isotropicStructureMap (sectionFourPluckerForms k) =
        isotropicStructureMap (canonicalForms (2*k+1) (2*k)) :=
  isotropicProjLinearIso_hom_over _ _ _ _

/-- Actual smoothness of the ambient scheme used by the affine paving. -/
theorem chainCanonical_isotropicStructureMap_smooth (k t : ℕ) :
    Smooth (isotropicStructureMap (t := t)
      (canonicalForms (K := K) (n := 2*k+1) (2*k+1) (2*k))) := by
  have hpath : Smooth (isotropicStructureMap (t := t) (sectionFourPluckerForms (K := K) k)) :=
    (isotropicStructureMap_smooth_of_ideal_eq _ _ (sectionFour_isotropicPluckerIdeal k t)).mpr
      (canonicalOdd_isotropicStructureMap_smooth k t)
  exact (isotropicStructureMap_smooth_linearEquiv (t := t) (pathChainLinearEquiv k)
    (sectionFourPluckerForms k) (canonicalForms (2*k+1) (2*k))
    (sectionFour_forms_pathChain k)).mp hpath

end PaperVerification.IsotropicAttractingCharts
