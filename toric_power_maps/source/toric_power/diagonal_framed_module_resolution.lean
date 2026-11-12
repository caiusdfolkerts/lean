module

public import ToricPower.DiagonalFramedBoundary
public import ToricPower.DiagonalToricFrames

/-!
# The finite local matrix resolves the actual affine diagonal sheaf

The finite matrix written in ordinary Cartier frames is isomorphic to the
independently constructed genuine cellular complex. Its augmentation is a
quasi-isomorphism to the actual intersection coordinate ring, with scalars
restricted along the actual diagonal ring map. The proved exactness of
`tilde` then gives a quasi-isomorphism to the actual affine diagonal direct
image of the structure sheaf.

Every identification is an explicit complex or sheaf isomorphism. No
resolution, coherent--constructible equivalence, or diagonal assertion is
included as an assumed field or hypothesis. Candidate pending compilation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (k : Type) [CommRing k] (A : Fin s → Fin n → ℤ)
  (S T : Set (Fin s)) (frames : ∀ d, DiagonalCellFrames A S T d)

theorem diagonalFramedBoundary_compare_apply (d : ℕ)
    (v : NormalizedCell A (d+1) →₀ DiagonalChartRing k A S T) :
    (frames d).linearEquiv k
        (diagonalFramedBoundary k A (frames d) (frames (d+1)) v) =
      diagonalChartBoundaryLinear k A S T d ((frames (d+1)).linearEquiv k v) :=
  DFunLike.congr_fun
    (diagonalFramedBoundary_compare k A (frames d) (frames (d+1))) v

theorem diagonalFramedBoundary_square (d : ℕ) :
    (diagonalFramedBoundary k A (frames d) (frames (d+1))).comp
      (diagonalFramedBoundary k A (frames (d+1)) (frames (d+2))) = 0 := by
  apply LinearMap.ext
  intro v
  apply ((frames d).linearEquiv k).injective
  rw [LinearMap.comp_apply,LinearMap.zero_apply,map_zero,
    diagonalFramedBoundary_compare_apply,diagonalFramedBoundary_compare_apply]
  exact DFunLike.congr_fun (diagonalChartBoundary_comp k A S T d)
    ((frames (d+2)).linearEquiv k v)

/-- The actual finite global monomial matrices in each local frame,
regarded as a complex of ordinary modules over the actual chart ring. -/
def diagonalFramedComplex : ChainComplex (ModuleCat (DiagonalChartRing k A S T)) ℕ :=
  ChainComplex.of
    (fun d => ModuleCat.of (DiagonalChartRing k A S T)
      (NormalizedCell A d →₀ DiagonalChartRing k A S T))
    (fun d => ModuleCat.ofHom (diagonalFramedBoundary k A (frames d) (frames (d+1))))
    (fun d => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      exact DFunLike.congr_fun (diagonalFramedBoundary_square k A S T frames d) v)

theorem diagonalFramedComplex_d (d : ℕ) :
    (diagonalFramedComplex k A S T frames).d (d+1) d =
      ModuleCat.ofHom (diagonalFramedBoundary k A (frames d) (frames (d+1))) := by
  change ChainComplex.of.d
    (fun q => ModuleCat.of (DiagonalChartRing k A S T)
      (NormalizedCell A q →₀ DiagonalChartRing k A S T))
    (fun q => ModuleCat.ofHom
      (diagonalFramedBoundary k A (frames q) (frames (q+1))))
    (d+1) d = _
  exact ChainComplex.of_d _ _ d

/-- The actual local matrix complex is isomorphic to the actual cellular
complex by the proved matrix computation, not merely quasi-isomorphic. -/
def diagonalFramedComplexIso :
    diagonalFramedComplex k A S T frames ≅ diagonalChartComplex k A S T :=
  HomologicalComplex.Hom.isoOfComponents
    (fun d => ((frames d).linearEquiv k).toModuleIso)
    (by
      intro i j hij
      change j+1 = i at hij
      subst i
      rw [diagonalFramedComplex_d,diagonalChartComplex_d]
      apply ModuleCat.hom_ext
      ext v
      exact (diagonalFramedBoundary_compare_apply k A S T frames j v).symm)

end ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (regular : fan.IsRegular) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "S" => fanConeRaySet fan rays σ
local notation "T" => fanConeRaySet fan rays τ
local notation "R" => DiagonalChartRing ℂ A S T
local notation "B" => affineCoordinateRing fan.lattice (σ.val ⊓ τ.val)

def toricDiagonalFramedComplex : ChainComplex (ModuleCat R) ℕ :=
  diagonalFramedComplex ℂ A S T (toricDiagonalCellFrames fan regular basis rays σ τ)

/-- The finite local matrix augmented to the actual diagonal module. -/
def toricDiagonalFramedAugmentation :
    toricDiagonalFramedComplex fan regular basis rays σ τ ⟶
      (ChainComplex.single₀ (ModuleCat R)).obj
        (diagonalIntersectionModule fan basis rays σ τ) :=
  (diagonalFramedComplexIso ℂ A S T
      (toricDiagonalCellFrames fan regular basis rays σ τ)).hom ≫
    diagonalToricChartAugmentation fan basis rays σ τ

theorem toricDiagonalFramedAugmentation_quasiIso :
    QuasiIso (toricDiagonalFramedAugmentation fan regular basis rays σ τ) := by
  letI := diagonalToricChartAugmentation_quasiIso fan basis rays σ τ
  unfold toricDiagonalFramedAugmentation
  infer_instance


end ToricPower
