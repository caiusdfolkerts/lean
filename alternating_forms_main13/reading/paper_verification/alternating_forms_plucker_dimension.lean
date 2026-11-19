module

public import PaperVerification.AlternatingFormsPluckerHomogeneity
public import TauCeti.RingTheory.KrullDimension.FiniteType
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Dimension lower bounds from the actual isotropic matrix chart

The maximal-minor map is surjective after fixing its pivot coordinate to one.
Its factor through the isotropy equations maps onto the quotient by exactly
m choose(s,2) row equations. At an isotropic coordinate plane, the polynomial
origin is a maximal ideal containing those equations. Krull's height theorem
and the regular dehomogenizing element give the expected cone lower bound.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Matrix
open scoped BigOperators

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {s n t m : ℕ}

/-- The nonpivot matrix has exactly s(n-s) independent coordinates. -/
theorem card_pluckerChartVariable (p : PluckerIndex s n) :
    Fintype.card (PluckerChartVariable p) = s*(n-s) := by
  classical
  have h : Fintype.card (Set.range p.val)=s := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_congr (Equiv.ofInjective p.val p.property.injective)).symm
  rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_subtype_compl,Fintype.card_fin,h]

theorem matrixMinorEvaluation_chart_surjective (p : PluckerIndex s n) :
    Function.Surjective (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)) := by
  intro y
  obtain ⟨q,hq⟩ := (pluckerBigCellEquiv (K := K) p).surjective y
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mkₐ_surjective K (pluckerBigCellIdeal p) q
  exact ⟨f,hq⟩

theorem isotropicChartEvaluation_surjective (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    Function.Surjective (isotropicChartEvaluation p forms) :=
  (Ideal.Quotient.mkₐ_surjective K _).comp (matrixMinorEvaluation_chart_surjective p)

def isotropicConeToChart (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    (MvPolynomial (PluckerIndex (t+2) n) K ⧸ isotropicPluckerIdeal forms) →ₐ[K]
      (MvPolynomial (PluckerChartVariable p) K ⧸ isotropicChartIdeal p forms) :=
  Ideal.Quotient.liftₐ _ (isotropicChartEvaluation p forms)
    (fun f hf => isotropicPluckerIdeal_le_chartKernel p forms hf)

theorem isotropicConeToChart_surjective (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) : Function.Surjective (isotropicConeToChart p forms) := by
  intro y
  obtain ⟨f,hf⟩ := isotropicChartEvaluation_surjective p forms y
  exact ⟨Ideal.Quotient.mk _ f,hf⟩

theorem isotropicConeToChart_pivot (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    isotropicConeToChart p forms (Ideal.Quotient.mk _ (X p))=1 := by
  change (Ideal.Quotient.mkₐ K _) (matrixMinorEvaluation _ (X p))=1
  simp only [matrixMinorEvaluation,aeval_X,pluckerChartMatrix_pivot,Matrix.det_one,map_one]

theorem isotropic_cone_dimension_ge_chart_succ
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    ringKrullDim (MvPolynomial (PluckerChartVariable p) K ⧸ isotropicChartIdeal p forms)+1 ≤
      ringKrullDim (MvPolynomial (PluckerIndex (t+2) n) K ⧸ isotropicPluckerIdeal forms) :=
  GradedDehomogenization.dimension_succ_le_of_dehomogenized_surjection
    (isotropicPluckerIdeal forms) (isotropicPluckerIdeal_isHomogeneous forms) p
    (isotropicConeToChart p forms).toRingHom (isotropicConeToChart_surjective p forms)
    (isotropicConeToChart_pivot p forms)

/-- The coordinate s-plane at the origin of this matrix chart. -/
def pluckerCoordinatePlane (p : PluckerIndex s n) : Matrix (Fin s) (Fin n) K :=
  fun i j => if j=p.val i then 1 else 0

theorem constantCoeff_pluckerChartMatrix (p : PluckerIndex s n) (i : Fin s) (j : Fin n) :
    constantCoeff (pluckerChartMatrix (K := K) p i j) = pluckerCoordinatePlane (K := K) p i j := by
  classical
  by_cases h₁ : j = p.val i
  · simp only [pluckerChartMatrix, Matrix.of_apply, pluckerCoordinatePlane,
      if_pos h₁, map_one]
  · simp only [pluckerChartMatrix, Matrix.of_apply, pluckerCoordinatePlane,if_neg h₁]
    split_ifs <;> simp

theorem constantCoeff_alternatingRowPair (p : PluckerIndex (t+2) n)
    (f : StrictPairs n → K) (i j : Fin (t+2)) :
    constantCoeff (alternatingRowPair f (pluckerChartMatrix (K := K) p) i j) =
      alternatingRowPair f (pluckerCoordinatePlane (K := K) p) i j := by
  simp only [alternatingRowPair,map_sum,constantCoeff_smul,map_sub,map_mul,
    constantCoeff_pluckerChartMatrix]

/-- The exact generator-count dimension inequality for every family of
alternating forms and every isotropic coordinate plane. -/
theorem isotropic_chart_dimension_bound
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (hp : ∀ l i j, alternatingRowPair (forms l) (pluckerCoordinatePlane (K := K) p) i j=0) :
    (((t+2)*(n-(t+2)) : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (PluckerChartVariable p) K ⧸ isotropicChartIdeal p forms) +
        (m*(t+2).choose 2 : ℕ) := by
  classical
  let P := MvPolynomial (PluckerChartVariable p) K
  let M : Ideal P := RingHom.ker (constantCoeff : P →+* K)
  letI : M.IsMaximal := RingHom.ker_isMaximal_of_surjective _
    (fun c => ⟨C c,constantCoeff_C _ c⟩)
  let gen : Fin m × StrictPairs (t+2) → P := fun a =>
    alternatingRowPair (forms a.1) (pluckerChartMatrix (K := K) p) a.2.val.1 a.2.val.2
  have hgen : Set.range gen ⊆ M := by
    rintro q ⟨a,rfl⟩
    change constantCoeff (gen a)=0
    exact (constantCoeff_alternatingRowPair p _ _ _).trans (hp _ _ _)
  have hd := Ideal.height_le_ringKrullDim_quotient_add_encard (p := M) (Set.range gen) hgen
  rw [MvPolynomial.height_eq_natCard_of_isMaximal] at hd
  have hc : (Set.range gen).encard ≤ (m*(t+2).choose 2 : ℕ) := by
    simpa only [Set.image_univ,Set.encard_univ,ENat.card_eq_coe_fintype_card,
      Fintype.card_prod,Fintype.card_fin,card_strictPairs] using
      Set.encard_image_le gen Set.univ
  have hd' := hd.trans (add_le_add (le_refl _) (WithBot.coe_le_coe.mpr hc))
  convert hd' using 1 <;>
    simp only [Nat.card_eq_fintype_card,card_pluckerChartVariable,P,gen,isotropicChartIdeal,
      WithBot.coe_natCast] <;> rfl

/-- The full expected cone bound, before specializing the number of forms. -/
theorem isotropic_cone_dimension_bound
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (hp : ∀ l i j, alternatingRowPair (forms l) (pluckerCoordinatePlane (K := K) p) i j=0) :
    (((t+2)*(n-(t+2))+1 : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (PluckerIndex (t+2) n) K ⧸ isotropicPluckerIdeal forms) +
        (m*(t+2).choose 2 : ℕ) := by
  have h₁ := add_le_add_right (isotropic_chart_dimension_bound p forms hp) 1
  have h₂ := add_le_add_right (isotropic_cone_dimension_ge_chart_succ p forms)
    ((m*(t+2).choose 2 : ℕ) : WithBot ℕ∞)
  calc
    (((t+2)*(n-(t+2))+1 : ℕ) : WithBot ℕ∞) ≤
        (ringKrullDim (MvPolynomial (PluckerChartVariable p) K ⧸
          isotropicChartIdeal p forms)+1) + ((m*(t+2).choose 2 : ℕ) : WithBot ℕ∞) := by
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using h₁
    _ ≤ _ := by simpa only [add_comm] using h₂

end PaperVerification.AlternatingForms
