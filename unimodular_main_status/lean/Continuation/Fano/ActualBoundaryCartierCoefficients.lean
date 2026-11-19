module

public import Continuation.Fano.ActualBoundaryRayDictionary

/-!
# Actual Cartier coefficients on and off the toric boundary

These formulas use orders in the actual local rings at genuine scheme points.
They identify the ordinary Cartier polytope of a fan line bundle with the
inequalities on its original rays.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped BigOperators

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
    (k : Type u) [Field k]

local instance boundaryCoefficientIntegral : IsIntegral (F.fanSchemeOver k).left := by
  change IsIntegral (F.fanScheme k)
  infer_instance

local instance boundaryCoefficientNoetherian : IsLocallyNoetherian (F.fanSchemeOver k).left := by
  change IsLocallyNoetherian (F.fanScheme k)
  infer_instance

theorem fanCartier_weilCoefficient_fullBoundary (a : Lattice n → ℤ)
    (s : F.fullCones) (i : Fin n) :
    (F.fanCartierData k F.isPure a).weilCoefficient (F.fullBoundaryPoint k s i) =
      a (F.fullConeBasis s i) := by
  have hmem : F.fullBoundaryPoint k s i ∈ F.fullChartOpen k s :=
    ⟨Spec.map (F.fullBoundaryPolynomialEquiv k s).toRingEquiv.toCommRingCatIso.hom
      (coordinateBoundaryPrime k i), rfl⟩
  rw [fanCartierData, (F.fanCartierCocycle k F.isPure a).weilCoefficient_eq (ULift.up s) hmem]
  change -(F.fanScheme k).ord
    (F.rationalCharacter k (F.cartierLatticePoint a s) : (F.fanScheme k).functionField)
      (F.fullBoundaryPoint k s i) = _
  rw [← F.intrinsicCharacter_fan k]
  change -(F.intrinsicToricEmbedding k).characterOrder (F.fullBoundaryPoint k s i)
    (F.cartierLatticePoint a s) = _
  rw [F.fullBoundaryPoint_character_order, F.cartierLatticePoint_pairing a s]
  · exact neg_neg _
  · rw [F.fullConeBasis_ray_set s]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem fanCartier_weilCoefficient_boundary (a : Lattice n → ℤ)
    (q : (F.intrinsicToricEmbedding k).BoundaryPrime) :
    (F.fanCartierData k F.isPure a).weilCoefficient q.val =
      a ((F.intrinsicToricEmbedding k).boundaryValuation q) := by
  obtain ⟨s, i, hq⟩ := F.boundaryPrime_eq_fullBoundaryPoint k q
  change (F.fanCartierData k F.isPure a).weilCoefficient q.val =
    a ((F.intrinsicToricEmbedding k).valuationVector q.val)
  rw [← hq, F.fanCartier_weilCoefficient_fullBoundary, F.fullBoundaryPoint_valuationVector]

theorem fanCartier_weilCoefficient_off_boundary (a : Lattice n → ℤ)
    (x : F.fanScheme k) (hx : x ∉ (F.intrinsicToricEmbedding k).boundary) :
    (F.fanCartierData k F.isPure a).weilCoefficient x = 0 := by
  have hxT : x ∈ ((F.intrinsicToricEmbedding k).torusOpen :
      Set (F.fanSchemeOver k).left) := by
    simpa only [SplitToricEmbedding.boundary, Set.mem_compl_iff, not_not] using hx
  obtain ⟨z, rfl⟩ := hxT
  obtain ⟨s, hs⟩ := F.fullChartOpen_cover k F.isPure
    ((F.intrinsicToricEmbedding k).torus.left z)
  change (F.fanCartierCocycle k F.isPure a).toCartierData.weilCoefficient
    (F.splitTorusOpenMap k z) = 0
  change F.splitTorusOpenMap k z ∈ F.fullChartOpen k s at hs
  rw [(F.fanCartierCocycle k F.isPure a).weilCoefficient_eq (ULift.up s) hs]
  change -(F.fanScheme k).ord
    (F.rationalCharacter k (F.cartierLatticePoint a s) : (F.fanScheme k).functionField)
      ((F.intrinsicToricEmbedding k).torus.left z) = 0
  rw [← F.intrinsicCharacter_fan k]
  change -(F.intrinsicToricEmbedding k).characterOrder
    ((F.intrinsicToricEmbedding k).torus.left z) (F.cartierLatticePoint a s) = 0
  rw [(F.intrinsicToricEmbedding k).characterOrder_torus, neg_zero]

#print axioms fanCartier_weilCoefficient_boundary
#print axioms fanCartier_weilCoefficient_off_boundary

end PaperVerification.ToricGeometry.SmoothCompleteFan
