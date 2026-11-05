module

public import PaperVerification.PowerDegreeMatrices
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Rank comparison for the actual graded tail quotient

The degree piece is literally the image of the homogeneous polynomial
subspace in the quotient by the vector-space sum of operator images. Its
dimension is computed from the finite matrix, with no identification of the
operator image with an ideal. Homogeneous projection gives all necessary
image and kernel identifications.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Module Matrix
open scoped BigOperators

namespace PaperVerification.PowerOperators

section Ring

variable {R : Type*} [CommRing R] {n : ℕ}

theorem range_tailMap (c : Fin n → R) (lam : R) (m : ℕ) :
    LinearMap.range (tailMap c lam m) = tailHit c lam m := by
  rw [tailHit_eq_firstTailHit]
  apply le_antisymm
  · rintro p ⟨v, rfl⟩
    rw [tailMap_apply]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.subset_span ⟨i, v i, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, p, rfl⟩
    exact ⟨Pi.single i p, tailMap_single c lam m i p⟩

theorem shiftedProjection_tailMap (c : Fin n → R) (lam : R) (m d : ℕ)
    (v : Fin n → MvPolynomial (Fin n) R) :
    shiftedProjection 0 d (tailMap c lam m v) =
      tailMap c lam m (fun i => shiftedProjection (m+i.val) d (v i)) := by
  simp only [tailMap_apply, map_sum, shiftedProjection_reversed, Nat.zero_add]

/-- The actual hit submodule is homogeneous; projection preserves it even
though it is generally not a polynomial ideal. -/
theorem homogeneousComponent_mem_tailHit (c : Fin n → R) (lam : R) (m d : ℕ)
    {p : MvPolynomial (Fin n) R} (hp : p ∈ tailHit c lam m) :
    homogeneousComponent d p ∈ tailHit c lam m := by
  rw [← range_tailMap] at hp ⊢
  obtain ⟨v, rfl⟩ := hp
  refine ⟨fun i => shiftedProjection (m+i.val) d (v i), ?_⟩
  simpa only [shiftedProjection, Nat.zero_le, ite_true, Nat.sub_zero] using
    (shiftedProjection_tailMap c lam m d v).symm

/-- The first finite degree map, with its actual homogeneous target. -/
def tailDegreeMap (c : Fin n → R) (lam : R) (m d : ℕ) :
    (TailDegreeIndex n m d → R) →ₗ[R] shiftedPiece R n 0 d :=
  (shiftedPieceBasis R n 0 d).equivFun.symm.toLinearMap.comp
    (tailDegreeMatrix c lam m d).mulVecLin

theorem tailDegreeMap_apply (c : Fin n → R) (lam : R) (m d : ℕ)
    (v : TailDegreeIndex n m d → R) :
    (tailDegreeMap c lam m d v : MvPolynomial (Fin n) R) =
      tailMap c lam m (tailDegreeDecode m d v) :=
  shiftedDecode_tailDegreeMatrix c lam m d v

/-- The matrix image is precisely the actual homogeneous hit subspace.
The reverse inclusion projects a polynomial preimage before taking coordinates. -/
theorem range_tailDegreeMap (c : Fin n → R) (lam : R) (m d : ℕ) :
    LinearMap.range (tailDegreeMap c lam m d) =
      (tailHit c lam m).comap (shiftedPiece R n 0 d).subtype := by
  apply le_antisymm
  · rintro q ⟨v, rfl⟩
    change (tailDegreeMap c lam m d v : MvPolynomial (Fin n) R) ∈ tailHit c lam m
    rw [tailDegreeMap_apply, ← range_tailMap]
    exact ⟨tailDegreeDecode m d v, rfl⟩
  · intro q hq
    change (q : MvPolynomial (Fin n) R) ∈ tailHit c lam m at hq
    rw [← range_tailMap] at hq
    obtain ⟨v, hv⟩ := hq
    let z : TailDegreeIndex n m d → R :=
      fun a => (shiftedProjection (m+a.1.val) d (v a.1)).coeff a.2.val
    have hz : tailDegreeDecode m d z =
        (fun i => shiftedProjection (m+i.val) d (v i)) := by
      funext i
      dsimp only [tailDegreeDecode,z]
      exact shiftedDecode_coeffs (R := R) (n := n) (m+i.val) d
        (shiftedProjection (m+i.val) d (v i))
        (shiftedProjection_mem (R := R) (n := n) (m+i.val) d (v i))
    refine ⟨z, ?_⟩
    apply Subtype.ext
    rw [tailDegreeMap_apply, hz, ← shiftedProjection_tailMap, hv,
      shiftedProjection_of_mem q.property]

/-- The literal degree-`d` subspace of the polynomial quotient. -/
def tailQuotientDegree (c : Fin n → R) (lam : R) (m d : ℕ) :
    Submodule R (MvPolynomial (Fin n) R ⧸ tailHit c lam m) :=
  (homogeneousSubmodule (Fin n) R d).map (tailHit c lam m).mkQ

theorem tailQuotientDegree_eq_shifted (c : Fin n → R) (lam : R) (m d : ℕ) :
    tailQuotientDegree c lam m d =
      (shiftedPiece R n 0 d).map (tailHit c lam m).mkQ := by
  rw [shiftedPiece_eq_homogeneous (Nat.zero_le d), Nat.sub_zero]
  rfl

instance tailQuotientDegree_finite (c : Fin n → R) (lam : R) (m d : ℕ) :
    Module.Finite R (tailQuotientDegree c lam m d) := by
  rw [tailQuotientDegree_eq_shifted]
  infer_instance

end Ring

section Field

variable {K : Type*} [Field K] {n : ℕ}

theorem tailDegreeMatrix_rank_eq_finrank_hit_piece (c : Fin n → K) (lam : K) (m d : ℕ) :
    (tailDegreeMatrix c lam m d).rank =
      Module.finrank K ((tailHit c lam m).comap (shiftedPiece K n 0 d).subtype) := by
  rw [← range_tailDegreeMap]
  change Module.finrank K (LinearMap.range (tailDegreeMatrix c lam m d).mulVecLin) = _
  rw [tailDegreeMap, LinearMap.range_comp,
    (shiftedPieceBasis K n 0 d).equivFun.symm.finrank_map_eq]

/-- Rank-nullity on the actual homogeneous quotient map, in every degree. -/
theorem tailQuotientDegree_finrank_add_rank (c : Fin n → K) (lam : K) (m d : ℕ) :
    Module.finrank K (tailQuotientDegree c lam m d) +
      (tailDegreeMatrix c lam m d).rank = Fintype.card (ShiftedExponent n 0 d) := by
  let P := shiftedPiece K n 0 d
  let q := (tailHit c lam m).mkQ.domRestrict P
  have hrange : LinearMap.range q = tailQuotientDegree c lam m d := by
    rw [tailQuotientDegree_eq_shifted]
    dsimp only [q, LinearMap.domRestrict, P]
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hkernel : LinearMap.ker q =
      (tailHit c lam m).comap (shiftedPiece K n 0 d).subtype := by
    dsimp only [q, LinearMap.domRestrict, P]
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have h := q.finrank_range_add_finrank_ker
  rw [hrange, hkernel, ← tailDegreeMatrix_rank_eq_finrank_hit_piece] at h
  exact h.trans (Module.finrank_eq_card_basis (shiftedPieceBasis K n 0 d))

/-- The full degreewise lower bound for the actual quotient. The comparison
field retains independent coefficients and has slope zero. The caller supplies
only the paper's positive tail index, not regularity or a rank hypothesis. -/
theorem tailQuotientDegree_finrank_ge_generic_zero
    (c : Fin n → K) (lam : K) (m d : ℕ) (hm : 0 < m) :
    Module.finrank (GenericCoefficientField K n)
      (tailQuotientDegree (genericCoefficient K n) 0 m d) ≤
        Module.finrank K (tailQuotientDegree c lam m d) := by
  have h := tailDegreeMatrix_rank_le_generic_zero K c lam m d hm
  have hactual := tailQuotientDegree_finrank_add_rank c lam m d
  have hgeneric := tailQuotientDegree_finrank_add_rank (genericCoefficient K n) 0 m d
  omega

end Field

end PaperVerification.PowerOperators
