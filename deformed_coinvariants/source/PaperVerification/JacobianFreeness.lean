module

public import PaperVerification.JacobianPolynomialModule
public import PaperVerification.NegativeWeightedGrading
public import PaperVerification.GradedBasisLifting

/-!
# Lifting a homogeneous Milnor basis to the actual divergence quotient

This theorem is an algebraic intermediate in the paper's hypersurface result.
It assumes regularity of the gradient explicitly. The separate implication
from the paper's isolated-critical-point hypothesis must be supplied before
this can be identified with that full theorem.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MvPolynomial Polynomial Module

namespace PaperVerification.JacobianDivergence

variable {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
local notation "P" => MvPolynomial ι K

def brieskornGrading (F : P) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h) : TauCeti.InternalGrading K (BrieskornModule F) :=
  ((NegativeWeightedGrading.grading w).quotient (divergenceSpace F)
    (NegativeWeightedGrading.divergenceSpace_homogeneous F w h hF)).map
      (Module.AEval'.of (potentialAction F))

theorem brieskornGrading_piece (F : P) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h) (p : ℤ) :
    (brieskornGrading F w h hF).piece p =
      (weightedHomogeneousSubmodule K (NegativeWeightedGrading.negativeWeights w) p).map
        (classOf F) := by
  rw [brieskornGrading, TauCeti.InternalGrading.map_piece,
    TauCeti.InternalGrading.quotient_piece, ← Submodule.map_comp,
    NegativeWeightedGrading.grading, TauCeti.InternalGrading.ofDecomposition_piece]
  rfl

theorem mem_brieskornGrading_piece (F : P) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h) (p : ℤ) (x : BrieskornModule F) :
    x ∈ (brieskornGrading F w h hF).piece p ↔
      ∃ u : P, u.IsWeightedHomogeneous (NegativeWeightedGrading.negativeWeights w) p ∧
        classOf F u = x := by
  rw [brieskornGrading_piece, Submodule.mem_map]
  rfl

theorem brieskornGrading_boundedAbove (F : P) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h) :
    BddAbove {p | (brieskornGrading F w h hF).piece p ≠ ⊥} := by
  refine ⟨0, ?_⟩
  intro p hp
  by_contra hpos
  have hp0 : 0 < p := lt_of_not_ge hpos
  apply hp
  rw [brieskornGrading_piece]
  have hz := NegativeWeightedGrading.piece_positive_eq_bot (K := K) w p hp0
  rw [NegativeWeightedGrading.grading, TauCeti.InternalGrading.ofDecomposition_piece] at hz
  rw [hz, Submodule.map_bot]

theorem parameter_homogeneous (F : P) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h) :
    ∀ ⦃p : ℤ⦄ ⦃x : BrieskornModule F⦄,
      x ∈ (brieskornGrading F w h hF).piece p →
      (Polynomial.X : K[X]) • x ∈ (brieskornGrading F w h hF).piece (p - h) := by
  intro p x hx
  obtain ⟨u, hu, rfl⟩ := (mem_brieskornGrading_piece F w h hF p x).mp hx
  rw [X_smul_classOf, mem_brieskornGrading_piece]
  refine ⟨F * u, ?_, rfl⟩
  have hFn := (NegativeWeightedGrading.homogeneous_negative_iff w F h).mpr hF
  convert hFn.mul hu using 1 <;> abel

/-- Every choice of homogeneous representatives of a Milnor basis is a basis
of the actual divergence quotient over `K[X]`, with `X` acting as `F`.
The gradient-regularity input is exposed, not hidden in a replacement definition. -/
theorem homogeneous_milnor_basis_lifts {n : ℕ} {I : Type*}
    (hn : 2 ≤ n) (F : MvPolynomial (Fin n) K) (w : Fin n → ℕ) (h : ℕ)
    (hw : ∀ i, 0 < w i) (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) K)
      (List.ofFn (gradient F)))
    (b : I → MvPolynomial (Fin n) K)
    (hbhom : ∀ i, ∃ d : ℕ, (b i).IsWeightedHomogeneous w d)
    (B : Basis I K (MilnorQuotient F))
    (hB : ∀ i, (jacobianSubmodule F).mkQ (b i) = B i) :
    ∃ basis : Basis I K[X] (BrieskornModule F), ∀ i, basis i = classOf F (b i) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine GradedBasisLifting.basis_lifts
    (brieskornGrading F w h hF) h (Nat.ne_of_gt hh)
    (brieskornGrading_boundedAbove F w h hF)
    (parameter_homogeneous F w h hF)
    (parameter_regular F w h hw hh hF hreg)
    (milnorMap F hreg) ?_ (fun i => classOf F (b i)) ?_ B ?_
  · exact milnorMap_ker hn F w h hw hh hF hreg
  · intro i
    obtain ⟨d, hd⟩ := hbhom i
    refine ⟨-(d : ℤ), ?_⟩
    exact (mem_brieskornGrading_piece F w h hF _ _).mpr
      ⟨b i, (NegativeWeightedGrading.homogeneous_negative_iff w (b i) d).mpr hd, rfl⟩
  · intro i
    simpa only [milnorMap_classOf] using hB i

end PaperVerification.JacobianDivergence
