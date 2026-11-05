module

public import PaperVerification.HomogeneousModuleFinite
public import PaperVerification.VectorEulerAction

/-!
# Proposition 6.5: the complete-intersection family in full codimension

Positive homogeneous regularity supplies finiteness over the literal
parameter subalgebra. Characteristic zero then forces the actual polynomial
Jacobian kernel to vanish. The canonical Euler calculation identifies every
resonant defect with the entire homogeneous polynomial space. All integer
target degrees and all weight-preserving linear group actions are retained.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MvPolynomial RingTheory.Sequence
open scoped BigOperators

namespace PaperVerification.VectorEuler

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
local notation "P" => MvPolynomial (Fin n) K

/-- The kernel vanishes as a consequence of the original regular-sequence
hypotheses, not as an extra rank or independence assumption. -/
theorem regular_coefficient_injective
    (F : Fin n → P) (h w : Fin n → ℕ)
    (hw : ∀ i, 0 < w i) (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (hreg : IsWeaklyRegular P (List.ofFn F)) :
    Function.Injective (VectorJacobian.normalizedJacobianMap F h) := by
  letI : Module.Finite (Algebra.adjoin K (Set.range F)) P :=
    HomogeneousLocalization.homogeneous_regular_finite_over_adjoin w hw F h hh hF hreg
  exact VectorJacobian.normalizedJacobianMap_injective F h hh

theorem regular_hit_ne_at_occurring_resonance
    (F : Fin n → P) (h w : Fin n → ℕ) (t : K) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (hreg : IsWeaklyRegular P (List.ofFn F))
    (hd : d ∈ EulerJacobian.occurringDegrees (K := K) w)
    (hres : 1 + t * ((∑ i, w i : ℕ) + d : K) = 0) :
    hit F h t ≠ coefficientSpace F h := by
  intro heq
  obtain ⟨p, hp0, hp⟩ := hd
  let e := homogeneousDefectEquiv F h w t d hh hF
    (regular_coefficient_injective F h w hw hh hF hreg) hres
  have hbot : defectImage F h t = ⊥ := by
    rw [defectImage, ← heq, Submodule.mkQ_map_self]
  have hz : e ⟨p, hp⟩ = 0 := by
    apply Subtype.ext
    change (e ⟨p, hp⟩ : (Fin n → P) ⧸ hit F h t) = 0
    simpa only [Submodule.mem_bot] using hbot.le (e ⟨p, hp⟩).property
  have hpz : (⟨p, hp⟩ : weightedHomogeneousSubmodule K w d) = 0 :=
    e.injective (hz.trans e.map_zero.symm)
  exact hp0 (congrArg Subtype.val hpz)

/-- The exceptional set is exact: all and only the degrees with `P_d ≠ 0`
produce an actual failure of equality of the two target subspaces. -/
theorem regular_hit_ne_iff (hn : 0 < n)
    (F : Fin n → P) (h w : Fin n → ℕ) (t : K)
    (hw : ∀ i, 0 < w i) (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (hreg : IsWeaklyRegular P (List.ofFn F)) :
    hit F h t ≠ coefficientSpace F h ↔
      ∃ d ∈ EulerJacobian.occurringDegrees (K := K) w,
        t = -(1 : K) / ((∑ i, w i : ℕ) + d : K) := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  constructor
  · intro hneq
    by_contra hnone
    push_neg at hnone
    exact hneq (hit_eq_coefficient_of_nonresonant F h w t hw hh hF hnone)
  · rintro ⟨d, hd, ht⟩
    apply regular_hit_ne_at_occurring_resonance F h w t d hw hh hF hreg hd
    simpa only [Nat.cast_one] using (EulerJacobian.eigenvalue_zero_iff w hw 1 d t).mpr
      (by simpa only [Nat.cast_one] using ht)

def regularDefectEquiv (hn : 0 < n)
    (F : Fin n → P) (h w : Fin n → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (hreg : IsWeaklyRegular P (List.ofFn F)) :
    weightedHomogeneousSubmodule K w d ≃ₗ[K]
      Defect F h (-(1 : K) / ((∑ i, w i : ℕ) + d : K)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let t : K := -(1 : K) / ((∑ i, w i : ℕ) + d : K)
  have hres : 1 + t * ((∑ i, w i : ℕ) + d : K) = 0 := by
    simpa only [Nat.cast_one] using (EulerJacobian.eigenvalue_zero_iff w hw 1 d t).mpr
      (by simp only [Nat.cast_one, t])
  exact (homogeneousDefectEquiv F h w t d hh hF
    (regular_coefficient_injective F h w hw hh hF hreg) hres).trans
      (defectEquivImage F h t).symm

/-- The canonical identification is induced by multiplication by the literal
vector `(F₁,…,Fₙ)`. It is not an unspecified dimension-count isomorphism. -/
theorem regularDefectEquiv_canonical (hn : 0 < n)
    (F : Fin n → P) (h w : Fin n → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (hreg : IsWeaklyRegular P (List.ofFn F))
    (p : weightedHomogeneousSubmodule K w d) :
    let t : K := -(1 : K) / ((∑ i, w i : ℕ) + d : K)
    (defectEquivImage F h t (regularDefectEquiv hn F h w d hw hh hF hreg p) :
      (Fin n → P) ⧸ hit F h t) = (hit F h t).mkQ (potential F p) := by
  simp only [regularDefectEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, homogeneousDefectEquiv_apply]

/-- All scalar claims of Proposition 6.5. The coefficient identity is stated
for every integer target degree, so it is precisely the Laurent Hilbert-series
identity even when the baseline has nonzero negative-degree components. -/
theorem paper_proposition_6_5_scalar (hn : 0 < n)
    (F : Fin n → P) (h w : Fin n → ℕ)
    (hw : ∀ i, 0 < w i) (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (hreg : IsWeaklyRegular P (List.ofFn F)) :
    (∀ t : K, hit F h t ≤ coefficientSpace F h) ∧
    (∀ t : K, hit F h t ≠ coefficientSpace F h ↔
      ∃ d ∈ EulerJacobian.occurringDegrees (K := K) w,
        t = -(1 : K) / ((∑ i, w i : ℕ) + d : K)) ∧
    (∀ d : ℕ,
      let t : K := -(1 : K) / ((∑ i, w i : ℕ) + d : K)
      Nonempty (weightedHomogeneousSubmodule K w d ≃ₗ[K] Defect F h t) ∧
      defectImage F h t ≤ quotientTargetPiece w h (d : ℤ) (hit F h t) ∧
      ∀ e : ℤ,
        Module.finrank K (quotientTargetPiece w h e (hit F h t)) =
          Module.finrank K (quotientTargetPiece w h e (coefficientSpace F h)) +
            if e = (d : ℤ) then Module.finrank K (weightedHomogeneousSubmodule K w d) else 0) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨fun t => hit_le_coefficient F h w t hh hF,
    fun t => regular_hit_ne_iff hn F h w t hw hh hF hreg, ?_⟩
  intro d
  let t : K := -(1 : K) / ((∑ i, w i : ℕ) + d : K)
  have hres : 1 + t * ((∑ i, w i : ℕ) + d : K) = 0 := by
    simpa only [Nat.cast_one] using (EulerJacobian.eigenvalue_zero_iff w hw 1 d t).mpr
      (by simp only [Nat.cast_one, t])
  have hC := regular_coefficient_injective F h w hw hh hF hreg
  exact ⟨⟨regularDefectEquiv hn F h w d hw hh hF hreg⟩,
    exceptional_defect_concentrated F h w t d hh hF hC hres,
    fun e => exceptional_hilbert_function F h w t d e hw hh hF hC hres⟩

/-- The same canonical equivalence is an isomorphism for every actual linear
group fixing every equation and preserving its positive grading. In particular
this includes every finite linear group in the paper; finiteness is unnecessary
for this canonical defect map. -/
theorem paper_proposition_6_5_equivariant {G : Type*} [Group G]
    (hn : 0 < n) (F : Fin n → P) (h w : Fin n → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (hreg : IsWeaklyRegular P (List.ofFn F))
    (ρ : G →* (Matrix (Fin n) (Fin n) K)ˣ)
    (hW : ∀ g, JacobianLinearAction.RespectsWeights w (ρ g : Matrix (Fin n) (Fin n) K))
    (hFix : ∀ g a, linearSubst (ρ g : Matrix (Fin n) (Fin n) K) (F a) = F a)
    (g : G) (p : weightedHomogeneousSubmodule K w d) :
    let t : K := -(1 : K) / ((∑ i, w i : ℕ) + d : K)
    regularDefectEquiv hn F h w d hw hh hF hreg
        (homogeneousPolynomialRepresentation ρ w d hW g p) =
      defectQuotientRepresentation ρ F h t hFix g
        (regularDefectEquiv hn F h w d hw hh hF hreg p) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let t : K := -(1 : K) / ((∑ i, w i : ℕ) + d : K)
  have hres : 1 + t * ((∑ i, w i : ℕ) + d : K) = 0 := by
    simpa only [Nat.cast_one] using (EulerJacobian.eigenvalue_zero_iff w hw 1 d t).mpr
      (by simp only [Nat.cast_one, t])
  apply (defectEquivImage F h t).injective
  rw [defectEquivImage_intertwines]
  simp only [t, regularDefectEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  exact homogeneousDefectEquiv_intertwines ρ F h w t d hh hF
    (regular_coefficient_injective F h w hw hh hF hreg) hres hW hFix g p

end PaperVerification.VectorEuler
