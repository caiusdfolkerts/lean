module

public import PaperVerification.PowerOriginalDegreeMatrices
public import PaperVerification.PowerOriginalAction

/-!
# The original-family degree quotient and its full equivariant presentation

No diagonal factor is assumed invertible. The finite matrix includes all
original operators which can contribute in the given degree, and its image
is proved to be the kernel of the literal polynomial quotient map.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Representation Matrix

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}

theorem originalTailQuotientDegree_eq_shifted (c : Fin n → K) (lam : K) (m d : ℕ) :
    originalTailQuotientDegree c lam m d =
      (shiftedPiece K n 0 d).map (originalTailHit c lam m).mkQ := by
  rw [shiftedPiece_eq_homogeneous (Nat.zero_le d)]
  simp only [Nat.sub_zero,originalTailQuotientDegree]

instance originalTailQuotientDegree_finite (c : Fin n → K) (lam : K) (m d : ℕ) :
    Module.Finite K (originalTailQuotientDegree c lam m d) := by
  rw [originalTailQuotientDegree_eq_shifted]
  infer_instance

def originalDegreeQuotientMap (c : Fin n → K) (lam : K) (m d : ℕ) :
    (ShiftedExponent n 0 d → K) →ₗ[K] originalTailQuotientDegree c lam m d :=
  (((originalTailHit c lam m).mkQ).comp (shiftedDecode 0 d)).codRestrict _ (by
    intro v
    rw [originalTailQuotientDegree_eq_shifted]
    exact ⟨shiftedDecode 0 d v,shiftedDecode_mem 0 d v,rfl⟩)

@[simp] theorem originalDegreeQuotientMap_apply (c : Fin n → K) (lam : K) (m d : ℕ)
    (v : ShiftedExponent n 0 d → K) :
    (originalDegreeQuotientMap c lam m d v :
      MvPolynomial (Fin n) K ⧸ originalTailHit c lam m) =
      (originalTailHit c lam m).mkQ (shiftedDecode 0 d v) := rfl

theorem originalDegreeQuotientMap_surjective (c : Fin n → K) (lam : K) (m d : ℕ) :
    Function.Surjective (originalDegreeQuotientMap c lam m d) := by
  intro z
  have hz := (originalTailQuotientDegree_eq_shifted c lam m d).le z.property
  obtain ⟨p,hp,hpz⟩ := hz
  refine ⟨fun a => p.coeff a.val,?_⟩
  apply Subtype.ext
  rw [originalDegreeQuotientMap_apply,shiftedDecode_coeffs 0 d p hp]
  exact hpz

theorem originalDegreeQuotientMap_kernel (c : Fin n → K) (lam : K) (m d : ℕ) :
    LinearMap.range (originalDegreeMatrix c lam m d).mulVecLin =
      LinearMap.ker (originalDegreeQuotientMap c lam m d) := by
  apply le_antisymm
  · rintro v ⟨u,rfl⟩
    apply Subtype.ext
    change (originalTailHit c lam m).mkQ
      (shiftedDecode 0 d ((originalDegreeMatrix c lam m d) *ᵥ u)) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact originalDegreePolynomialMap_mem_hit c lam m d u
  · intro v hv
    change originalDegreeQuotientMap c lam m d v = 0 at hv
    have hmem : shiftedDecode 0 d v ∈ originalTailHit c lam m := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      exact congrArg Subtype.val hv
    obtain ⟨u,hu⟩ := original_projection_mem_degree_range c lam m d hmem
    refine ⟨u,shiftedDecode_injective 0 d ?_⟩
    change originalDegreePolynomialMap c lam m d u = shiftedDecode 0 d v
    rw [hu,shiftedProjection_of_mem (shiftedDecode_mem 0 d v)]

theorem originalTailQuotientAction_preserves_degree
    (G : Subgroup (Equiv.Perm (Fin n))) (c : Fin n → K) (lam : K) (m : ℕ)
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i)
    (g : G) (d : ℕ) {z : MvPolynomial (Fin n) K ⧸ originalTailHit c lam m}
    (hz : z ∈ originalTailQuotientDegree c lam m d) :
    originalTailQuotientAction G c lam m hfix g z ∈ originalTailQuotientDegree c lam m d := by
  obtain ⟨p,hp,rfl⟩ := hz
  rw [originalTailQuotientAction_mkQ]
  exact ⟨_,rename_mem_homogeneousSubmodule (g : Equiv.Perm (Fin n)) d hp,rfl⟩

def originalTailQuotientDegreeRepresentation
    (G : Subgroup (Equiv.Perm (Fin n))) (c : Fin n → K) (lam : K) (m : ℕ)
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i) (d : ℕ) :
    Representation K G (originalTailQuotientDegree c lam m d) :=
  Representation.subrepresentation (originalTailQuotientAction G c lam m hfix)
    (originalTailQuotientDegree c lam m d)
    (fun g _ hz => originalTailQuotientAction_preserves_degree G c lam m hfix g d hz)

def originalDegreeQuotientIntertwiner
    (G : Subgroup (Equiv.Perm (Fin n))) (c : Fin n → K) (lam : K) (m d : ℕ)
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i) :
    IntertwiningMap (shiftedDegreeAction (R := K) G 0 d)
      (originalTailQuotientDegreeRepresentation G c lam m hfix d) where
  toLinearMap := originalDegreeQuotientMap c lam m d
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change (originalTailHit c lam m).mkQ
      (shiftedDecode 0 d (shiftedRename (g : Equiv.Perm (Fin n)) 0 d v)) =
      originalTailQuotientAction G c lam m hfix g
        ((originalTailHit c lam m).mkQ (shiftedDecode 0 d v))
    rw [shiftedDecode_shiftedRename,originalTailQuotientAction_mkQ]

@[simp] theorem originalDegreeQuotientIntertwiner_toLinearMap
    (G : Subgroup (Equiv.Perm (Fin n))) (c : Fin n → K) (lam : K) (m d : ℕ)
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i) :
    (originalDegreeQuotientIntertwiner G c lam m d hfix).toLinearMap =
      originalDegreeQuotientMap c lam m d := rfl

end PaperVerification.PowerOperators
