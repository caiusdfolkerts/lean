module

public import PaperVerification.ToricQuotientStarCovering
public import PaperVerification.ToricFanFaceHulls
public import PaperVerification.ToricFaceCoordinates

@[expose] public section

/-!
# Actual saturated affine coordinates on a support face

The normal quotient and the tangent embedding are dual under the ordinary
coordinate pairing. The origin solves precisely the active support
equalities. At integral support values this is an actual saturated integral
affine chart, so all lattice and parity coordinates retain their meaning.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

variable {n : ℕ}

def complementaryEmbedding (I : Finset (Fin n)) : Fin (n - I.card) ↪ Fin n where
  toFun j := ((quotientIndexEquivFin I).symm j : Fin n)
  inj' := Subtype.val_injective.comp (quotientIndexEquivFin I).symm.injective

theorem mem_range_complementaryEmbedding_iff (I : Finset (Fin n)) (i : Fin n) :
    i ∈ Set.range (complementaryEmbedding I) ↔ i ∉ I := by
  constructor
  · rintro ⟨j, rfl⟩
    exact ((quotientIndexEquivFin I).symm j).property
  · intro hi
    refine ⟨quotientIndexEquivFin I ⟨i, hi⟩, ?_⟩
    simp only [complementaryEmbedding, Function.Embedding.coeFn_mk,
      Equiv.symm_apply_apply]

def faceTangentReal (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) : Ambient (n - I.card) →ₗ[ℝ] Ambient n :=
  selectedBasisMap (integralBasisReal (integralDualBasis b)) (complementaryEmbedding I)

def faceTangentLattice (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) : Lattice (n - I.card) →ₗ[ℤ] Lattice n :=
  selectedBasisMap (integralDualBasis b) (complementaryEmbedding I)

/-- The tangent embedding is literally dual to the saturated normal
quotient, not merely isomorphic after tensoring with the reals. -/
theorem faceTangentReal_pairing (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (u : Ambient n) (x : Ambient (n - I.card)) :
    (dotProductEquiv ℝ (Fin n) u) (faceTangentReal b I x) =
      (dotProductEquiv ℝ (Fin (n - I.card)) (coneQuotientReal b I u)) x := by
  have hp (j : Fin (n - I.card)) :
      (dotProductEquiv ℝ (Fin n) u)
        (integralBasisReal (integralDualBasis b) (complementaryEmbedding I j)) =
      (integralBasisReal b).repr u (complementaryEmbedding I j) := by
    rw [integralBasisReal_apply]
    change (∑ k, u k * embed n (integralDualBasis b (complementaryEmbedding I j)) k) = _
    simpa only [mul_comm] using
      integralDualBasis_real_pairing b (complementaryEmbedding I j) u
  simp only [faceTangentReal, selectedBasisMap_apply, map_sum, map_smul, hp, smul_eq_mul]
  change (∑ j, x j * (integralBasisReal b).repr u (complementaryEmbedding I j)) =
    ∑ j, (coneQuotientReal b I u) j * x j
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

def quotientFaceOrigin (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) : Ambient n :=
  -∑ i ∈ I, a (b i) • integralBasisReal (integralDualBasis b) i

def quotientFaceOriginLattice (a : Lattice n → ℤ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) : Lattice n :=
  -∑ i ∈ I, a (b i) • integralDualBasis b i

theorem embed_quotientFaceOrigin (a : Lattice n → ℤ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    embed n (quotientFaceOriginLattice a b I) =
      quotientFaceOrigin (fun u => (a u : ℝ)) b I := by
  simp only [quotientFaceOriginLattice, quotientFaceOrigin, map_neg, map_sum,
    embed_int_smul, integralBasisReal_apply]

theorem quotientFaceOrigin_coordinate (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) (i : Fin n) :
    (integralBasisReal (integralDualBasis b)).repr (quotientFaceOrigin a b I) i =
      if i ∈ I then -a (b i) else 0 := by
  by_cases hi : i ∈ I <;>
    simp [quotientFaceOrigin, map_sum, map_smul, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, Module.Basis.repr_self_apply, Finsupp.single_apply, smul_eq_mul, hi]

def quotientFaceMap (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    Ambient (n - I.card) →ᵃ[ℝ] Ambient n :=
  AffineMap.const ℝ _ (quotientFaceOrigin a b I) + (faceTangentReal b I).toAffineMap

@[simp] theorem quotientFaceMap_apply (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (x : Ambient (n - I.card)) :
    quotientFaceMap a b I x = quotientFaceOrigin a b I + faceTangentReal b I x := rfl

theorem quotientFaceMap_injective (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    Function.Injective (quotientFaceMap a b I) := by
  intro x y h
  apply selectedBasisMap_injective (integralBasisReal (integralDualBasis b))
    (complementaryEmbedding I)
  exact add_left_cancel h

theorem normal_pairing_eq_dual_coordinate
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (x : Ambient n) :
    (dotProductEquiv ℝ (Fin n) (embed n (b i))) x =
      (integralBasisReal (integralDualBasis b)).repr x i := by
  change (∑ j, embed n (b i) j * x j) = _
  simpa only [integralDualBasis_involutive] using
    integralDualBasis_real_pairing (integralDualBasis b) i x

theorem quotientFaceMap_active (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (x : Ambient (n - I.card)) (i : Fin n) (hi : i ∈ I) :
    (dotProductEquiv ℝ (Fin n) (embed n (b i))) (quotientFaceMap a b I x) = -a (b i) := by
  rw [normal_pairing_eq_dual_coordinate, quotientFaceMap_apply,
    map_add, Finsupp.add_apply, quotientFaceOrigin_coordinate, if_pos hi]
  have hnot : i ∉ Set.range (complementaryEmbedding I) := by
    rw [mem_range_complementaryEmbedding_iff]
    exact not_not.mpr hi
  rw [show faceTangentReal b I x = selectedBasisMap
      (integralBasisReal (integralDualBasis b)) (complementaryEmbedding I) x from rfl,
    selectedBasisMap_coordinate_eq_zero _ _ _ _ hnot, add_zero]

/-- The affine chart covers exactly the genuine active hyperplanes, with
no unproved saturation or affine-span premise. -/
theorem mem_range_quotientFaceMap_iff (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) (x : Ambient n) :
    x ∈ Set.range (quotientFaceMap a b I) ↔ ∀ i ∈ I,
      (dotProductEquiv ℝ (Fin n) (embed n (b i))) x = -a (b i) := by
  constructor
  · rintro ⟨y, rfl⟩ i hi
    exact quotientFaceMap_active a b I y i hi
  · intro hx
    have hzero : ∀ i ∉ Set.range (complementaryEmbedding I),
        (integralBasisReal (integralDualBasis b)).repr
          (x - quotientFaceOrigin a b I) i = 0 := by
      intro i hi
      have hiI : i ∈ I := by
        simpa only [mem_range_complementaryEmbedding_iff, not_not] using hi
      rw [map_sub, Finsupp.sub_apply, quotientFaceOrigin_coordinate, if_pos hiI,
        ← normal_pairing_eq_dual_coordinate, hx i hiI, sub_self]
    obtain ⟨y, hy⟩ := (mem_range_selectedBasisMap_iff
      (integralBasisReal (integralDualBasis b)) (complementaryEmbedding I)
      (x - quotientFaceOrigin a b I)).mpr hzero
    refine ⟨y, ?_⟩
    change quotientFaceOrigin a b I +
      selectedBasisMap (integralBasisReal (integralDualBasis b)) (complementaryEmbedding I) y = x
    rw [hy]
    abel

/-- Integral support gives the actual saturated affine lattice chart. -/
def quotientFaceIntegralChart (a : Lattice n → ℤ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    IntegralAffineEmbedding (n - I.card) n :=
  selectedBasisChart (quotientFaceOriginLattice a b I)
    (integralDualBasis b) (complementaryEmbedding I)

theorem quotientFaceIntegralChart_realMap (a : Lattice n → ℤ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    (quotientFaceIntegralChart a b I).realMap =
      quotientFaceMap (fun u => (a u : ℝ)) b I := by
  ext x
  simp only [quotientFaceIntegralChart, IntegralAffineEmbedding.realMap_apply,
    selectedBasisChart, embed_quotientFaceOrigin, quotientFaceMap_apply,
    faceTangentReal]

/-- A linear form vanishing on the deleted normals factors through the
explicit saturated quotient, with the actual chosen section. -/
theorem linear_face_factorization
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (hℓ : ∀ i ∈ I, ℓ (integralBasisReal b i) = 0) (u : Ambient n) :
    ℓ (coneQuotientSectionReal b I (coneQuotientReal b I u)) = ℓ u := by
  change ℓ (basisSection (integralBasisReal b) I
    ((quotientCoordinateFinEquiv ℝ I).symm
      (quotientCoordinateFinEquiv ℝ I (basisProjection (integralBasisReal b) I u)))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact map_basisSection_projection (integralBasisReal b) I ℓ hℓ u

end PaperVerification.ToricGeometry
