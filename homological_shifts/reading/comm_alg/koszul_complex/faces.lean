import CommAlg.KoszulComplex.MonomialBasis
import CommAlg.Simplicial.Homology

/-! # The actual upper Koszul faces and their homogeneous chain indices -/

noncomputable section

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul

open Classical CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

abbrev FaceIndex (B : Family V) (a : Exponent V) (i : ℕ) :=
  {s : Finset V // koszulFaces B a s ∧ s.card = i}

def faceChainBasis (B : Family V) (a : Exponent V) (i : ℕ) :
    Module.Basis (FaceIndex B a i) k (Simplicial.Chains (k := k) (koszulFaces B a) i) :=
  Grading.restrictedBasis Simplicial.basis (fun s => koszulFaces B a s ∧ s.card = i)

@[simp] lemma faceChainBasis_val (B : Family V) (a : Exponent V) (i : ℕ)
    (s : FaceIndex B a i) : (faceChainBasis (k := k) B a i s).val = Simplicial.basis s.val :=
  Grading.restrictedBasis_val _ _ _

/-- Exact matching of simplicial face bases with actual monomial-exterior bases of degree `a`. -/
def faceMonomialEquiv (B : Family V) (a : Exponent V) (i : ℕ) :
    FaceIndex B a i ≃ {t : MonomialIndex B i // monomialDegree t = a} where
  toFun s := ⟨⟨⟨s.val, s.property.2⟩,
    ⟨a - faceExponent s.val, s.property.1.2⟩⟩,
    tsub_add_cancel_of_le s.property.1.1⟩
  invFun t := ⟨t.val.1.val, ⟨⟨by
    exact (le_add_of_nonneg_left (show (0 : Exponent V) ≤ t.val.2.val from zero_le)).trans_eq t.property, by
    have he : a - faceExponent t.val.1.val = t.val.2.val := by
      exact (congrArg (fun b : Exponent V => b - faceExponent t.val.1.val)
        t.property.symm).trans (add_tsub_cancel_right _ _)
    rw [he]
    exact t.val.2.property⟩, t.val.1.property⟩⟩
  left_inv s := rfl
  right_inv t := by
    rcases t with ⟨⟨s, b⟩, ht⟩
    apply Subtype.ext
    dsimp only
    have hb : a - faceExponent s.val = b.val :=
      (congrArg (fun c : Exponent V => c - faceExponent s.val)
        ht.symm).trans (add_tsub_cancel_right _ _)
    exact congrArg (fun c : {c : Exponent V // Contains B c} => (⟨s, c⟩ : MonomialIndex B i))
      (Subtype.ext hb)

/-- The isomorphism acts on real chains in the actual Koszul homogeneous component. -/
def faceHomogeneousEquiv (B : Family V) (a : Exponent V) (i : ℕ) :
    Simplicial.Chains (k := k) (koszulFaces B a) i ≃ₗ[k] homogeneousPiece (k := k) B a i :=
  (faceChainBasis (k := k) B a i).equiv
    (Grading.restrictedBasis (monomialCoefficientBasis (k := k) B i)
      (fun t => monomialDegree t = a)) (faceMonomialEquiv B a i)

@[simp] lemma faceHomogeneousEquiv_basis (B : Family V) (a : Exponent V) (i : ℕ)
    (s : FaceIndex B a i) :
    (faceHomogeneousEquiv (k := k) B a i (faceChainBasis (k := k) B a i s)).val =
      monomialCoefficientBasis (k := k) B i (faceMonomialEquiv B a i s).val := by
  unfold faceHomogeneousEquiv
  rw [Module.Basis.equiv_apply]
  exact Grading.restrictedBasis_val _ _ _

end CommAlg.Koszul
