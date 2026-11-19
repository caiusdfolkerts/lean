module

public import ToricPower.AffineFiniteFreeDual
public import ToricPower.AffineTildeCochain

/-!
# Internal duality of actual finite free affine complexes

The objectwise free-basis comparison is compatible with every original
differential. This gives a genuine isomorphism of the complete complexes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable (R : CommRingCat.{0}) (I : ℕ → Type) [∀ q, Fintype (I q)]
  (d : ∀ q, ModuleCat.of R (I (q+1) →₀ R) ⟶ ModuleCat.of R (I q →₀ R))
  (square : ∀ q, d (q+1) ≫ d q = 0)

/-- The full ring-dual/tilde/internal-dual comparison in the actual
finite free matrices, with no assertion that dualization is exact. -/
def affineFiniteFreeDualComplexIso :
    (affineTildeCochainFunctor R).obj
        (moduleDualComplex R (ChainComplex.of (fun q => ModuleCat.of R (I q →₀ R)) d square)) ≅
      internalDualComplex (Spec R).Modules
        ((affineTildeChainFunctor R).obj
          (ChainComplex.of (fun q => ModuleCat.of R (I q →₀ R)) d square)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => affineFiniteFreeDualIso R (I q))
    (fun i j _ => (affineFiniteFreeDualIso_naturality R (I j) (I i)
      ((ChainComplex.of (fun q => ModuleCat.of R (I q →₀ R)) d square).d j i)).symm)

end ToricPower
