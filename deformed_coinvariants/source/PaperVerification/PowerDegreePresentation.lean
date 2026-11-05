module

public import PaperVerification.PowerDegreeActions

/-!
# The literal equivariant degreewise cokernel presentation

The target is the image of the homogeneous polynomial subspace in the actual
joint operator-image quotient. The presentation map is induced by decoding
monomial coordinates and taking the actual quotient class. Its surjectivity,
kernel, and equivariance are all proved here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Representation Matrix

namespace PaperVerification.PowerOperators

section Ring

variable {R : Type*} [CommRing R] {n : ℕ}

def degreeQuotientMap (c : Fin n → R) (lam : R) (m d : ℕ) :
    (ShiftedExponent n 0 d → R) →ₗ[R] tailQuotientDegree c lam m d :=
  (((tailHit c lam m).mkQ).comp (shiftedDecode 0 d)).codRestrict _ (by
    intro v
    rw [tailQuotientDegree_eq_shifted]
    exact ⟨shiftedDecode 0 d v, shiftedDecode_mem 0 d v, rfl⟩)

@[simp] theorem degreeQuotientMap_apply (c : Fin n → R) (lam : R) (m d : ℕ)
    (v : ShiftedExponent n 0 d → R) :
    (degreeQuotientMap c lam m d v : MvPolynomial (Fin n) R ⧸ tailHit c lam m) =
      (tailHit c lam m).mkQ (shiftedDecode 0 d v) := rfl

theorem degreeQuotientMap_surjective (c : Fin n → R) (lam : R) (m d : ℕ) :
    Function.Surjective (degreeQuotientMap c lam m d) := by
  intro z
  have hz := (tailQuotientDegree_eq_shifted c lam m d).le z.property
  obtain ⟨p,hp,hpz⟩ := hz
  refine ⟨fun a => p.coeff a.val, ?_⟩
  apply Subtype.ext
  rw [degreeQuotientMap_apply, shiftedDecode_coeffs 0 d p hp]
  exact hpz

theorem degreeQuotientMap_kernel (c : Fin n → R) (lam : R) (m d : ℕ) :
    LinearMap.range (tailDegreeMatrix c lam m d).mulVecLin =
      LinearMap.ker (degreeQuotientMap c lam m d) := by
  apply le_antisymm
  · rintro v ⟨u,rfl⟩
    apply Subtype.ext
    change (tailHit c lam m).mkQ (shiftedDecode 0 d ((tailDegreeMatrix c lam m d) *ᵥ u)) = 0
    rw [shiftedDecode_tailDegreeMatrix]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rw [← range_tailMap]
    exact ⟨tailDegreeDecode m d u,rfl⟩
  · intro v hv
    change degreeQuotientMap c lam m d v = 0 at hv
    have hmem : shiftedDecode 0 d v ∈ tailHit c lam m := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      exact congrArg Subtype.val hv
    let a : shiftedPiece R n 0 d := ⟨shiftedDecode 0 d v,shiftedDecode_mem 0 d v⟩
    have ha : (shiftedPieceBasis R n 0 d).equivFun a = v := by
      ext b
      rw [shiftedPieceBasis_equivFun_apply]
      exact shiftedDecode_coeff 0 d v b
    have haHit : a ∈ (tailHit c lam m).comap (shiftedPiece R n 0 d).subtype := hmem
    obtain ⟨u,hu⟩ := (range_tailDegreeMap c lam m d).ge haHit
    refine ⟨u, ?_⟩
    have hc := congrArg (shiftedPieceBasis R n 0 d).equivFun hu
    change (shiftedPieceBasis R n 0 d).equivFun
      ((shiftedPieceBasis R n 0 d).equivFun.symm ((tailDegreeMatrix c lam m d) *ᵥ u)) =
        (shiftedPieceBasis R n 0 d).equivFun a at hc
    rw [LinearEquiv.apply_symm_apply,ha] at hc
    exact hc

end Ring

section Field

variable {K : Type*} [Field K] {n : ℕ}

/-- The actual quotient presentation, as a genuine intertwining map. -/
def degreeQuotientIntertwiner (G : Subgroup (Equiv.Perm (Fin n)))
    (c : Fin n → K) (lam : K) (m d : ℕ)
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i) :
    IntertwiningMap (shiftedDegreeAction (R := K) G 0 d)
      (tailQuotientDegreeRepresentation G c lam m hfix d) where
  toLinearMap := degreeQuotientMap c lam m d
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change (tailHit c lam m).mkQ
      (shiftedDecode 0 d (shiftedRename (g : Equiv.Perm (Fin n)) 0 d v)) =
      tailQuotientAction G c lam m hfix g ((tailHit c lam m).mkQ (shiftedDecode 0 d v))
    rw [shiftedDecode_shiftedRename,tailQuotientAction_mkQ]

@[simp] theorem degreeQuotientIntertwiner_toLinearMap
    (G : Subgroup (Equiv.Perm (Fin n))) (c : Fin n → K) (lam : K) (m d : ℕ)
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i) :
    (degreeQuotientIntertwiner G c lam m d hfix).toLinearMap = degreeQuotientMap c lam m d := rfl

end Field

end PaperVerification.PowerOperators
