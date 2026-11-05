module

public import PaperVerification.HypersurfaceFreeness
public import PaperVerification.GradedComponentBasis
public import PaperVerification.JacobianDefect

/-!
# Actual homogeneous bases of the Brieskorn components

The polynomial-module basis is expanded into powers of the given potential.
The degree-`d` component has exactly the basis vectors `F^j b_i` with
`j*h + degree(b_i) = d`. Its finite-dimensionality is proved independently
from the finite polynomial component, so `finrank` never conceals an infinite
component in the Hilbert-function statement.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Polynomial Module

namespace PaperVerification.JacobianDivergence

variable {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
local notation "P" => MvPolynomial ι K

theorem brieskorn_piece_finite (F : P) (w : ι → ℕ) (h d : ℕ)
    (hw : ∀ i, 0 < w i) (hF : F.IsWeightedHomogeneous w h) :
    Module.Finite K ((brieskornGrading F w h hF).piece (-(d : ℤ))) := by
  have he :
      weightedHomogeneousSubmodule K (NegativeWeightedGrading.negativeWeights w) (-(d : ℤ)) =
      weightedHomogeneousSubmodule K w d := by
    ext p
    exact NegativeWeightedGrading.homogeneous_negative_iff w p d
  rw [brieskornGrading_piece, he]
  letI : Module.Finite K (weightedHomogeneousSubmodule K w d) :=
    Module.Finite.of_fg
      (MvPolynomial.weightedHomogeneousSubmodule_fg K w (fun i => Nat.ne_of_gt (hw i)) d)
  infer_instance

/-- Every coefficient-field basis vector is the actual class of `F^j b_i`,
and the exact degree condition computes the finite homogeneous dimensions. -/
theorem homogeneous_milnor_tower_basis {n : ℕ} {I : Type*}
    (hn : 2 ≤ n) (F : MvPolynomial (Fin n) K) (w : Fin n → ℕ) (h : ℕ)
    (hw : ∀ i, 0 < w i) (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) K)
      (List.ofFn (gradient F)))
    (b : I → MvPolynomial (Fin n) K) (degree : I → ℕ)
    (hbhom : ∀ i, (b i).IsWeightedHomogeneous w (degree i))
    (B : Basis I K (MilnorQuotient F))
    (hB : ∀ i, (jacobianSubmodule F).mkQ (b i) = B i) :
    ∃ towers : Basis (ℕ × I) K (BrieskornModule F),
      (∀ a, towers a = classOf F (F ^ a.1 * b a.2)) ∧
      ∀ d : ℕ,
        Module.Finite K ((brieskornGrading F w h hF).piece (-(d : ℤ))) ∧
        Module.finrank K ((brieskornGrading F w h hF).piece (-(d : ℤ))) =
          Nat.card {a : ℕ × I // a.1 * h + degree a.2 = d} := by
  obtain ⟨Bpol, hBpol⟩ := homogeneous_milnor_basis_lifts hn F w h hw hh hF hreg
    b (fun i => ⟨degree i, hbhom i⟩) B hB
  let G := brieskornGrading F w h hF
  have hbG : ∀ i, Bpol i ∈ G.piece (-(degree i : ℤ)) := by
    intro i
    rw [hBpol i, mem_brieskornGrading_piece]
    exact ⟨b i, (NegativeWeightedGrading.homogeneous_negative_iff w (b i) (degree i)).mpr
      (hbhom i), rfl⟩
  refine ⟨GradedComponentBasis.towerBasis Bpol, ?_, ?_⟩
  · intro a
    rw [GradedComponentBasis.towerBasis_apply, hBpol a.2, X_pow_smul_classOf]
  · intro d
    refine ⟨brieskorn_piece_finite F w h d hw hF, ?_⟩
    rw [GradedComponentBasis.finrank_tower_piece G Bpol
      (fun i => -(degree i : ℤ)) h hbG (parameter_homogeneous F w h hF) (-(d : ℤ))]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro a
    rw [← Nat.cast_mul]
    omega

/-- The component in the raw polynomial quotient and the component in its
polynomial-module presentation are identified by the actual quotient equivalence. -/
def rawBrieskornComponentEquiv (F : P) (w : ι → ℕ) (h d : ℕ)
    (hF : F.IsWeightedHomogeneous w h) :
    EulerResonance.quotientComponent w d (divergenceSpace F) ≃ₗ[K]
      (brieskornGrading F w h hF).piece (-(d : ℤ)) := by
  let e := Module.AEval'.of (potentialAction F)
  have hspace :
      weightedHomogeneousSubmodule K (NegativeWeightedGrading.negativeWeights w) (-(d : ℤ)) =
      weightedHomogeneousSubmodule K w d := by
    ext p
    exact NegativeWeightedGrading.homogeneous_negative_iff w p d
  have he :
      (EulerResonance.quotientComponent w d (divergenceSpace F)).map e.toLinearMap =
      (brieskornGrading F w h hF).piece (-(d : ℤ)) := by
    rw [EulerResonance.quotientComponent_eq_map, brieskornGrading_piece, hspace]
    simp only [classOf, Submodule.map_comp, e]
  exact (e.submoduleMap _).trans (LinearEquiv.ofEq _ _ he)

def exceptionalDefectComponentEquiv
    (F : P) (w : ι → ℕ) (h d : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hres : (h : K) + t * ((∑ i, w i : ℕ) + d : K) = 0) :
    DefectQuotient F t ≃ₗ[K] (brieskornGrading F w h hF).piece (-(d : ℤ)) :=
  (exceptionalDefectQuotientEquiv F w h d t hh hF hres).trans
    (rawBrieskornComponentEquiv F w h d hF)

/-- The finite exceptional defect has the full, untruncated polynomial-tower
count. The isolation hypothesis can supply `hreg` by the preceding theorem. -/
theorem exceptional_defect_dimension {n : ℕ} {I : Type*}
    (hn : 2 ≤ n) (F : MvPolynomial (Fin n) K) (w : Fin n → ℕ) (h d : ℕ) (t : K)
    (hw : ∀ i, 0 < w i) (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hres : (h : K) + t * ((∑ i, w i : ℕ) + d : K) = 0)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) K)
      (List.ofFn (gradient F)))
    (b : I → MvPolynomial (Fin n) K) (degree : I → ℕ)
    (hbhom : ∀ i, (b i).IsWeightedHomogeneous w (degree i))
    (B : Basis I K (MilnorQuotient F))
    (hB : ∀ i, (jacobianSubmodule F).mkQ (b i) = B i) :
    Module.Finite K (DefectQuotient F t) ∧
    Module.finrank K (DefectQuotient F t) =
      Nat.card {a : ℕ × I // a.1 * h + degree a.2 = d} := by
  obtain ⟨_, _, hpieces⟩ := homogeneous_milnor_tower_basis hn F w h hw hh hF hreg
    b degree hbhom B hB
  let e := exceptionalDefectComponentEquiv F w h d t hh hF hres
  letI := (hpieces d).1
  exact ⟨Module.Finite.equiv e.symm, e.finrank_eq.trans (hpieces d).2⟩

end PaperVerification.JacobianDivergence
