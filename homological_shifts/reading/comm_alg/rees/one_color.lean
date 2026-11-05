import CommAlg.IntegralClosure.OrdinaryRees

/-! # The actual equivalence between ordinary and one-color Rees algebras -/

noncomputable section

namespace CommAlg

open Classical

variable {R : Type*} [CommRing R]

theorem reesToMulti_injective (I : Ideal R) : Function.Injective (reesToMulti I) := by
  intro p q h
  apply Subtype.ext
  apply (MvPolynomial.uniqueAlgEquiv R Unit).symm.injective
  exact congrArg Subtype.val h

theorem reesToMulti_surjective (I : Ideal R) : Function.Surjective (reesToMulti I) := by
  intro q
  have hp : (MvPolynomial.uniqueAlgEquiv R Unit) q.val ∈ reesAlgebra I := by
    intro n
    rw [MvPolynomial.coeff_uniqueAlgEquiv]
    simpa [powerProduct] using q.property (Finsupp.single () n)
  refine ⟨⟨(MvPolynomial.uniqueAlgEquiv R Unit) q.val, hp⟩, ?_⟩
  apply Subtype.ext
  exact (MvPolynomial.uniqueAlgEquiv R Unit).symm_apply_apply q.val

/-- Ordinary polynomial grading and the one-color multigrading define
isomorphic Rees algebras, with their actual coefficient conditions. -/
def reesMultiEquiv (I : Ideal R) : reesAlgebra I ≃ₐ[R] multiReesAlgebra (fun _ : Unit => I) :=
  AlgEquiv.ofBijective (reesToMulti I) ⟨reesToMulti_injective I, reesToMulti_surjective I⟩

@[simp] theorem reesMultiEquiv_apply (I : Ideal R) (p : reesAlgebra I) :
    reesMultiEquiv I p = reesToMulti I p := rfl

theorem reesMultiEquiv_symm_val (I : Ideal R)
    (q : multiReesAlgebra (fun _ : Unit => I)) :
    ((reesMultiEquiv I).symm q).val = (MvPolynomial.uniqueAlgEquiv R Unit) q.val := by
  have h := congrArg Subtype.val ((reesMultiEquiv I).apply_symm_apply q)
  change (MvPolynomial.uniqueAlgEquiv R Unit).symm ((reesMultiEquiv I).symm q).val = q.val at h
  have hh := congrArg (MvPolynomial.uniqueAlgEquiv R Unit) h
  simpa only [AlgEquiv.apply_symm_apply] using hh

end CommAlg
