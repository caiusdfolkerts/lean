module

public import PaperVerification.AlternatingFormsOddStandardBasis
public import PaperVerification.HomogeneousIdealPieces

/-!
# Every actual homogeneous piece of the canonical odd Plücker ring

The full lifted basis restricts by the ordinary polynomial degree.  Its
degree-r component is indexed by precisely the length-r interval chains,
and each vector is the original product of its Plücker coordinates.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

def oddPluckerDegree (k t r : ℕ) : Submodule K
    (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) :=
  HomogeneousIdealPieces.piece _ r

def oddStandardDegreeEquiv (k t : ℕ) (hs : t+2≤k+1) (r : ℕ) :
    {C : OddStandardIndex k t hs // C.1=r} ≃
      BandChain (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) r where
  toFun C := C.property ▸ C.val.2
  invFun C := ⟨⟨r,C⟩,rfl⟩
  left_inv := by
    rintro ⟨⟨a,C⟩,h⟩
    change a=r at h
    subst a
    rfl
  right_inv C := rfl

theorem oddPluckerStandardBasis_mem_degree (k t : ℕ) (hs : t+2≤k+1)
    (C : OddStandardIndex k t hs) :
    oddPluckerStandardBasis (K := K) k t hs C∈oddPluckerDegree k t C.1 := by
  rw [oddPluckerStandardBasis_apply]
  exact ⟨oddStandardRepresentative k t hs C,
    oddStandardRepresentative_homogeneous k t hs C,rfl⟩

def oddPluckerDegreeBasis (k t : ℕ) (hs : t+2≤k+1) (r : ℕ) :
    Module.Basis
      (BandChain (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) r)
      K (oddPluckerDegree (K := K) k t r) :=
  (HomogeneousIdealPieces.componentBasis _ (isotropicPluckerIdeal_isHomogeneous _)
    (oddPluckerStandardBasis k t hs) (fun C => C.1)
    (oddPluckerStandardBasis_mem_degree k t hs) r).reindex
      (oddStandardDegreeEquiv k t hs r)

@[simp] theorem oddPluckerDegreeBasis_apply (k t : ℕ) (hs : t+2≤k+1) (r : ℕ)
    (C : BandChain (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) r) :
    (oddPluckerDegreeBasis (K := K) k t hs r C :
      MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))=
      Ideal.Quotient.mk _ (chainPluckerProduct _ _ C) := by
  unfold oddPluckerDegreeBasis
  erw [Module.Basis.reindex_apply,HomogeneousIdealPieces.componentBasis_coe]
  change oddPluckerStandardBasis (K := K) k t hs ⟨r,C⟩ = _
  exact oddPluckerStandardBasis_apply (K := K) k t hs ⟨r,C⟩

theorem oddPluckerDegree_finrank (k t : ℕ) (hs : t+2≤k+1) (r : ℕ) :
    Module.finrank K (oddPluckerDegree (K := K) k t r)=
      Fintype.card (BandChain (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) r) :=
  Module.finrank_eq_card_basis (oddPluckerDegreeBasis k t hs r)

end PaperVerification.AlternatingForms
