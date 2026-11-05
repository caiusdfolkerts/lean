module

public import PaperVerification.ToricBundleFanWeights
public import PaperVerification.ToricIntegralAffine


@[expose] public section
/-!
# The saturated integral lattice of every homogeneous fiber slice

The chart at a fixed integral homogeneous weight is an explicit integral
affine embedding.  Its image lattice is saturated, because its base-coordinate
inverse pairs with the integral section of the quotient.  This is the exact
lattice statement needed for parity classes and inherited edge lengths.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

def integerDualVector {n : ℕ} (f : Lattice n →ₗ[ℤ] ℤ) : Lattice n :=
  fun i => f (Pi.basisFun ℤ (Fin n) i)

theorem embed_standard_basis (n : ℕ) (i : Fin n) :
    embed n (Pi.basisFun ℤ (Fin n) i) = Pi.basisFun ℝ (Fin n) i := by
  funext j
  simp [Pi.basisFun_apply, Pi.single_apply, embed]

theorem embed_integerDualVector {n : ℕ}
    (f : Lattice n →ₗ[ℤ] ℤ) (g : Ambient n →ₗ[ℝ] ℝ)
    (hfg : ∀ z : Lattice n, g (embed n z) = (f z : ℝ)) :
    embed n (integerDualVector f) = dualVector g := by
  funext i
  have h := hfg (Pi.basisFun ℤ (Fin n) i)
  rw [embed_standard_basis] at h
  exact h.symm

namespace SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation}
  (c : R.BundleCoordinates)

def integerBaseWeight (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (a α : Lattice n → ℤ) (q : Lattice (n - c.fiberIndices.card)) : ℤ :=
  a (c.baseRayLift hR hN q) + ∑ i ∈ c.fiberIndices,
    c.basis.repr (c.baseRayLift hR hN q) i * (α (c.basis i) - a (c.basis i))

theorem integerBaseWeight_cast (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (a α : Lattice n → ℤ) (q : Lattice (n - c.fiberIndices.card)) :
    (c.integerBaseWeight hR hN a α q : ℝ) =
      c.baseWeight hR hN (fun v => (a v : ℝ)) (fun v => (α v : ℝ)) q := by
  simp only [integerBaseWeight, baseWeight]
  push_cast
  rfl

def integerPointFunctional (a α : Lattice n → ℤ)
    (y : Lattice (n - c.fiberIndices.card)) : Lattice n →ₗ[ℤ] ℤ :=
  (∑ i ∈ c.fiberIndices, (α (c.basis i) - a (c.basis i)) • c.basis.coord i) +
    (dotProductEquiv ℤ (Fin (n - c.fiberIndices.card)) y).comp c.quotientLattice

def integerPoint (a α : Lattice n → ℤ)
    (y : Lattice (n - c.fiberIndices.card)) : Lattice n :=
  integerDualVector (c.integerPointFunctional a α y)

theorem pointFunctional_compatible (a α : Lattice n → ℤ)
    (y : Lattice (n - c.fiberIndices.card)) (z : Lattice n) :
    c.pointFunctional (fun v => (a v : ℝ)) (fun v => (α v : ℝ))
      (embed (n - c.fiberIndices.card) y) (embed n z) =
        (c.integerPointFunctional a α y z : ℝ) := by
  simp only [pointFunctional, fiberFunctional, integerPointFunctional,
    LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, Module.Basis.coord_apply, smul_eq_mul,
    integralBasisReal_repr, coneQuotient_compatible]
  change (∑ i ∈ c.fiberIndices,
      ((α (c.basis i) : ℝ) - (a (c.basis i) : ℝ)) * (c.basis.repr z i : ℝ)) +
    (∑ j, (y j : ℝ) * (c.quotientLattice z j : ℝ)) =
      (((∑ i ∈ c.fiberIndices,
          (α (c.basis i) - a (c.basis i)) * c.basis.repr z i) +
        ∑ j, y j * c.quotientLattice z j : ℤ) : ℝ)
  push_cast
  rfl

theorem integerPoint_compatible (a α : Lattice n → ℤ)
    (y : Lattice (n - c.fiberIndices.card)) :
    embed n (c.integerPoint a α y) =
      c.point (fun v => (a v : ℝ)) (fun v => (α v : ℝ))
        (embed (n - c.fiberIndices.card) y) :=
  embed_integerDualVector _ _ (c.pointFunctional_compatible a α y)

theorem fiberFunctional_section (a α : Lattice n → ℝ)
    (y : Ambient (n - c.fiberIndices.card)) :
    c.fiberFunctional a α (coneQuotientSectionReal c.basis c.fiberIndices y) = 0 := by
  simp only [fiberFunctional, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.Basis.coord_apply, smul_eq_mul, coneQuotientSectionReal,
    LinearMap.comp_apply, basisSection_repr]
  apply Finset.sum_eq_zero
  intro i hi
  rw [dif_pos hi, mul_zero]

theorem basePoint_point (a α : Lattice n → ℝ)
    (y : Ambient (n - c.fiberIndices.card)) : c.basePoint (c.point a α y) = y := by
  funext j
  change (dotProductEquiv ℝ (Fin n) (c.point a α y))
      (coneQuotientSectionReal c.basis c.fiberIndices
        (Pi.basisFun ℝ (Fin (n - c.fiberIndices.card)) j)) = y j
  rw [show (dotProductEquiv ℝ (Fin n) (c.point a α y))
      (coneQuotientSectionReal c.basis c.fiberIndices
        (Pi.basisFun ℝ (Fin (n - c.fiberIndices.card)) j)) =
      (dotProductEquiv ℝ (Fin n)
        (coneQuotientSectionReal c.basis c.fiberIndices
          (Pi.basisFun ℝ (Fin (n - c.fiberIndices.card)) j))) (c.point a α y) by
      exact dotProduct_comm (c.point a α y)
        (coneQuotientSectionReal c.basis c.fiberIndices
          (Pi.basisFun ℝ (Fin (n - c.fiberIndices.card)) j))]
  rw [point, dotProductEquiv_dualVector]
  simp only [pointFunctional, LinearMap.add_apply, LinearMap.comp_apply,
    c.fiberFunctional_section, coneQuotient_section_real, zero_add]
  simp [dotProductEquiv, dotProduct, Pi.basisFun_apply, Pi.single_apply]

def integerBasePoint (z : Lattice n) : Lattice (n - c.fiberIndices.card) :=
  integerDualVector ((dotProductEquiv ℤ (Fin n) z).comp
    (coneQuotientSectionLattice c.basis c.fiberIndices))

theorem integerBasePoint_compatible (z : Lattice n) :
    embed (n - c.fiberIndices.card) (c.integerBasePoint z) = c.basePoint (embed n z) := by
  apply embed_integerDualVector
  intro y
  simp only [LinearMap.comp_apply, coneQuotientSection_compatible]
  change (∑ i, (z i : ℝ) * (coneQuotientSectionLattice c.basis c.fiberIndices y i : ℝ)) =
    ((∑ i, z i * coneQuotientSectionLattice c.basis c.fiberIndices y i : ℤ) : ℝ)
  push_cast
  rfl

def baseLinearLattice : Lattice (n - c.fiberIndices.card) →+ Lattice n where
  toFun y := c.integerPoint 0 0 y
  map_zero' := by
    funext i
    simp [integerPoint, integerDualVector, integerPointFunctional]
  map_add' y z := by
    funext i
    simp [integerPoint, integerDualVector, integerPointFunctional, map_add]

def baseLinearReal : Ambient (n - c.fiberIndices.card) →ₗ[ℝ] Ambient n where
  toFun y := c.point 0 0 y
  map_add' y z := by
    funext i
    simp [point, dualVector, pointFunctional, fiberFunctional, map_add]
  map_smul' a y := by
    funext i
    simp [point, dualVector, pointFunctional, fiberFunctional, map_smul]

theorem baseLinear_compatible (z : Lattice (n - c.fiberIndices.card)) :
    embed n (c.baseLinearLattice z) = c.baseLinearReal (embed (n - c.fiberIndices.card) z) := by
  change embed n (c.integerPoint 0 0 z) =
    c.point 0 0 (embed (n - c.fiberIndices.card) z)
  have hzero : (fun v : Lattice n => (((0 : Lattice n → ℤ) v : ℤ) : ℝ)) =
      (0 : Lattice n → ℝ) := by
    funext v
    simp only [Pi.zero_apply, Int.cast_zero]
  have h := c.integerPoint_compatible (0 : Lattice n → ℤ) (0 : Lattice n → ℤ) z
  rw [hzero] at h
  exact h

theorem baseLinear_injective : Function.Injective c.baseLinearReal := by
  intro x y h
  have he := congrArg c.basePoint h
  change c.basePoint (c.point 0 0 x) = c.basePoint (c.point 0 0 y) at he
  rw [c.basePoint_point, c.basePoint_point] at he
  exact he

theorem baseLinear_saturated (z : Lattice n)
    (hz : embed n z ∈ Set.range c.baseLinearReal) :
    ∃ w : Lattice (n - c.fiberIndices.card), c.baseLinearLattice w = z := by
  obtain ⟨y, hy⟩ := hz
  have hycoord : y = embed (n - c.fiberIndices.card) (c.integerBasePoint z) := by
    have he := congrArg c.basePoint hy
    rw [show c.baseLinearReal y = c.point 0 0 y from rfl, c.basePoint_point,
      ← c.integerBasePoint_compatible z] at he
    exact he
  refine ⟨c.integerBasePoint z, ?_⟩
  apply embed_injective n
  rw [c.baseLinear_compatible, ← hycoord, hy]

/-- Fixed integral homogeneous weight gives a saturated integral affine chart. -/
def fiberChart (a α : Lattice n → ℤ) : IntegralAffineEmbedding (n - c.fiberIndices.card) n where
  origin := c.integerPoint a α 0
  linear := c.baseLinearLattice
  realLinear := c.baseLinearReal
  injective := c.baseLinear_injective
  compatible := c.baseLinear_compatible
  saturated := c.baseLinear_saturated

theorem point_add_base (a α : Lattice n → ℝ)
    (y : Ambient (n - c.fiberIndices.card)) :
    c.point a α y = c.point a α 0 + c.baseLinearReal y := by
  funext i
  simp [point, dualVector, pointFunctional, fiberFunctional, baseLinearReal]

theorem fiberChart_realMap (a α : Lattice n → ℤ)
    (y : Ambient (n - c.fiberIndices.card)) :
    (c.fiberChart a α).realMap y =
      c.point (fun v => (a v : ℝ)) (fun v => (α v : ℝ)) y := by
  rw [IntegralAffineEmbedding.realMap_apply]
  change embed n (c.integerPoint a α 0) + c.baseLinearReal y = _
  rw [c.integerPoint_compatible]
  simpa only [map_zero] using (c.point_add_base (fun v => (a v : ℝ))
    (fun v => (α v : ℝ)) y).symm

end SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

end PaperVerification.ToricGeometry
