import CommAlg.KoszulComplex.Coordinates
import CommAlg.Grading.BasisPieces
import CommAlg.Polymatroid.Exponents
import CommAlg.KoszulComplex.FaceCombinatorics
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! # Actual monomial bases and the multigrading of the tensor Koszul complex -/

noncomputable section

set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul

open Classical MvPolynomial CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma monomialIdeal_restrict_eq_span (B : Family V) :
    (monomialIdeal k B).restrictScalars k =
      Submodule.span k ((MvPolynomial.basisMonomials V k) '' {a | Contains B a}) := by
  ext f
  change f ∈ monomialIdeal k B ↔ _
  rw [mem_monomialIdeal_iff, Module.Basis.mem_span_image]
  rfl

def idealScalarEquiv (B : Family V) :
    (monomialIdeal k B).restrictScalars k ≃ₗ[k] monomialIdeal k B where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- All the monomials in a monomial ideal form an actual coefficient-ring basis. -/
def monomialBasis (B : Family V) :
    Module.Basis {a : Exponent V // Contains B a} k (monomialIdeal k B) :=
  (Grading.restrictedBasis (MvPolynomial.basisMonomials V k) (Contains B)).map
    ((LinearEquiv.ofEq _ _ (monomialIdeal_restrict_eq_span B).symm).trans (idealScalarEquiv B))

@[simp] lemma monomialBasis_val (B : Family V) (a : {a : Exponent V // Contains B a}) :
    (monomialBasis (k := k) B a).val = MvPolynomial.monomial a.val 1 := by
  unfold monomialBasis
  rw [Module.Basis.map_apply]
  change (Grading.restrictedBasis (MvPolynomial.basisMonomials V k) (Contains B) a).val = _
  exact Grading.restrictedBasis_val (MvPolynomial.basisMonomials V k) (Contains B) a

abbrev MonomialIndex (B : Family V) (i : ℕ) :=
  Σ s : Set.powersetCard V i, {a : Exponent V // Contains B a}

/-- The exterior-monomial basis of the actual coefficient module of the Koszul complex. -/
def monomialCoefficientBasis (B : Family V) (i : ℕ) :
    Module.Basis (MonomialIndex B i) k
      (Set.powersetCard V i →₀ (monomialIdeal k B)) :=
  Finsupp.basis (fun _ : Set.powersetCard V i => monomialBasis B)

@[simp] lemma monomialCoefficientBasis_apply (B : Family V) (i : ℕ)
    (s : Set.powersetCard V i) (a : {a : Exponent V // Contains B a}) :
    monomialCoefficientBasis (k := k) B i ⟨s, a⟩ =
      Finsupp.single s (monomialBasis B a) := by
  simp [monomialCoefficientBasis, Finsupp.coe_basis]

attribute [irreducible] monomialBasis monomialCoefficientBasis

/-- Its multidegree includes the exterior factor, as in the standard graded Koszul resolution. -/
def monomialDegree {B : Family V} {i : ℕ} (t : MonomialIndex B i) : Exponent V :=
  t.2.val + faceExponent t.1.val

/-- The degree-`a` submodule of the actual tensor Koszul coefficient module. -/
def homogeneousPiece (B : Family V) (a : Exponent V) (i : ℕ) :
    Submodule k (Set.powersetCard V i →₀ (monomialIdeal k B)) :=
  Grading.Piece (R := k) (M := Set.powersetCard V i →₀ (monomialIdeal k B)) (monomialCoefficientBasis (k := k) B i) monomialDegree a

instance homogeneousPiece_addCommGroup (B : Family V) (a : Exponent V) (i : ℕ) :
    AddCommGroup (homogeneousPiece (k := k) B a i) :=
  Submodule.addCommGroup (R := k) (M := Set.powersetCard V i →₀ (monomialIdeal k B))
    (homogeneousPiece B a i)

/-- Its canonical homogeneous projection on the actual coefficient module. -/
def homogeneousProjection (B : Family V) (a : Exponent V) (i : ℕ) :
    (Set.powersetCard V i →₀ (monomialIdeal k B)) →ₗ[k]
      (Set.powersetCard V i →₀ (monomialIdeal k B)) :=
  Grading.projection (R := k) (M := Set.powersetCard V i →₀ (monomialIdeal k B)) (monomialCoefficientBasis (k := k) B i) monomialDegree a

lemma homogeneousProjection_mem (B : Family V) (a : Exponent V) (i : ℕ)
    (x : Set.powersetCard V i →₀ (monomialIdeal k B)) :
    homogeneousProjection (k := k) B a i x ∈ homogeneousPiece (k := k) B a i :=
by
  unfold homogeneousProjection homogeneousPiece
  exact Grading.projection_mem (R := k) (M := Set.powersetCard V i →₀ (monomialIdeal k B))
    (monomialCoefficientBasis (k := k) B i) monomialDegree a x

lemma homogeneous_decomposition (B : Family V) (i : ℕ)
    (x : Set.powersetCard V i →₀ (monomialIdeal k B)) :
    ∑ a ∈ ((monomialCoefficientBasis (k := k) B i).repr x).support.image monomialDegree,
      homogeneousProjection (k := k) B a i x = x :=
by
  unfold homogeneousProjection
  exact Grading.sum_projections (R := k) (M := Set.powersetCard V i →₀ (monomialIdeal k B))
    (monomialCoefficientBasis (k := k) B i) monomialDegree x

end CommAlg.Koszul
