module

public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Exact affine sheafification on actual chain complexes

This generic interface keeps the affine ring abstract while constructing
the genuine mapped complex and its degree-zero comparison. The only
exactness used is the previously proved exactness of affine tilde.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u

variable (R : CommRingCat.{u})

/-- The actual affine sheafification functor applied to chain complexes. -/
def affineTildeChainFunctor :
    ChainComplex (ModuleCat.{u} R) ℕ ⥤ ChainComplex (Spec R).Modules ℕ :=
  (tilde.functor R).mapHomologicalComplex (ComplexShape.down ℕ)

/-- The genuine degree-zero comparison for mapped complexes. -/
def affineTildeSingleZeroIso (M : ModuleCat.{u} R) :
    (affineTildeChainFunctor R).obj ((ChainComplex.single₀ (ModuleCat.{u} R)).obj M) ≅
      (ChainComplex.single₀ (Spec R).Modules).obj (tilde M) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (tilde.functor R) (ComplexShape.down ℕ) 0).app M

/-- Actual affine sheafification preserves quasi-isomorphisms. -/
instance affineTildeChainFunctor_map_quasiIso
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((affineTildeChainFunctor R).map f) := by
  change QuasiIso (((tilde.functor R).mapHomologicalComplex _).map f)
  infer_instance

end ToricPower
