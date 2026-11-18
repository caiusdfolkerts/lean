module

public import ToricPower.AffineTildeComplex

/-!
# Exact affine sheafification of cochain complexes

The generic interface fixes the actual ring before the functor is
specialized to geometric coordinate rings.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ToricPower

universe u

variable (R : CommRingCat.{u})

def affineTildeCochainFunctor :
    CochainComplex (ModuleCat.{u} R) ℕ ⥤ CochainComplex (Spec R).Modules ℕ :=
  (tilde.functor R).mapHomologicalComplex (.up ℕ)

def affineTildeSingleIso (M : ModuleCat.{u} R) (n : ℕ) :
    (affineTildeCochainFunctor R).obj
        ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℕ) n).obj M) ≅
      (HomologicalComplex.single (Spec R).Modules (.up ℕ) n).obj (tilde M) :=
  (HomologicalComplex.singleMapHomologicalComplex (tilde.functor R) (.up ℕ) n).app M

instance affineTildeCochainFunctor_map_quasiIso
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((affineTildeCochainFunctor R).map f) := by
  change QuasiIso (((tilde.functor R).mapHomologicalComplex _).map f)
  infer_instance

end ToricPower
