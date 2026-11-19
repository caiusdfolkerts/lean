module

public import ToricPower.ExtComparisonAcyclic
public import ToricPower.QuasicoherentInjectiveFlasque
public import ToricPower.QuasicoherentCartierTensor
public import ToricPower.ModuleCohomologyFunctorIso

/-!
# Cartier-source Ext in the actual quasicoherent category

The exact inclusion from quasicoherent sheaves to all module sheaves induces
a bijection on every Ext group whose source is an actual Cartier line bundle.
This is proved, not obtained from an assumed equivalence of derived categories.

The acyclicity argument is geometric: inverse Cartier tensoring preserves
injectivity in `QCoh`; those injectives are flasque; the proved module Ext /
cohomology comparison then gives the vanishing needed by the comparison theorem.
All resulting comparisons are natural in the actual quasicoherent target.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Abelian MonoidalCategory Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace ToricPower

universe u

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] [X.IsSeparated]

local instance quasicoherentCartierExtHasExt : HasExt.{u} (QCoh X) :=
  hasExt_of_enoughInjectives (QCoh X)

local instance quasicoherentCartierAmbientHasExt : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

/-- The actual Cartier module sheaf as an object of the actual quasicoherent
category. Quasicoherence follows from its proved invertibility. -/
def quasicoherentCartierObject (D : CartierDivisor X) : QCoh X :=
  ⟨D.sheaf, inferInstance⟩

include k in
/-- Images of quasicoherent injectives are acyclic for Ext from any actual
Cartier line bundle, without being asserted injective among all module sheaves. -/
theorem quasicoherentInjective_cartierExt_subsingleton
    (D : CartierDivisor X) (J : QCoh X) [Injective J] (n : ℕ) :
    Subsingleton (Ext.{u} D.sheaf J.obj (n+1)) := by
  let F := (quasicoherentCartierTensorEquivalence (-D)).functor
  let L : QCoh X := F.obj J
  letI : Injective L := inferInstanceAs (Injective (F.obj J))
  have h : Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      ((-D).sheaf ⊗ J.obj) (n+1)) :=
    quasicoherentInjective_cohomology_subsingleton L n
  exact (cartierExtCohomology k X D J.obj (n+1)).toEquiv.subsingleton_congr.mpr h

include k in
/-- The actual inclusion-induced Ext map is bijective in every degree. -/
theorem quasicoherentCartier_mapExt_bijective (D : CartierDivisor X)
    (M : QCoh X) (n : ℕ) :
    Function.Bijective ((quasicoherentInclusion X).mapExtAddHom
      (quasicoherentCartierObject X D) M n) := by
  apply mapExt_bijective_of_injective_images_acyclic (quasicoherentInclusion X)
    (quasicoherentCartierObject X D)
  intro J hJ m
  letI := hJ
  exact quasicoherentInjective_cartierExt_subsingleton k X D J m

/-- This is specifically the actual map induced by the exact inclusion,
upgraded to an additive equivalence by the preceding bijectivity proof. -/
def quasicoherentCartierExtComparison (D : CartierDivisor X) (M : QCoh X) (n : ℕ) :
    Ext.{u} (quasicoherentCartierObject X D) M n ≃+ Ext.{u} D.sheaf M.obj n :=
  AddEquiv.ofBijective
    ((quasicoherentInclusion X).mapExtAddHom (quasicoherentCartierObject X D) M n)
    (quasicoherentCartier_mapExt_bijective k X D M n)

/-- The exact inclusion gives a natural isomorphism of the two actual
covariant Ext functors, not a family of unrelated vector-space bijections. -/
def quasicoherentCartierExtComparisonNatIso (D : CartierDivisor X) (n : ℕ) :
    (extFunctor n).obj (op (quasicoherentCartierObject X D)) ≅
      quasicoherentInclusion X ⋙ (extFunctor n).obj (op D.sheaf) :=
  NatIso.ofComponents
    (fun M => (quasicoherentCartierExtComparison k X D M n).toAddCommGrpIso)
    (by
      intro M N f
      ext x
      change (x.comp (Ext.mk₀ f) (add_zero n)).mapExactFunctor
          (quasicoherentInclusion X) =
        (x.mapExactFunctor (quasicoherentInclusion X)).comp
          (Ext.mk₀ ((quasicoherentInclusion X).map f)) (add_zero n)
      rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀])

/-- The actual quasicoherent Ext functor from a Cartier line bundle is
naturally ordinary cohomology of the actual inverse-Cartier tensor sheaf. -/
def quasicoherentCartierCohomologyNatIso (D : CartierDivisor X) (n : ℕ) :
    (extFunctor n).obj (op (quasicoherentCartierObject X D)) ≅
      quasicoherentInclusion X ⋙ tensorLeft (-D).sheaf ⋙
        TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyFunctor X n :=
  quasicoherentCartierExtComparisonNatIso k X D n ≪≫
    Functor.isoWhiskerLeft (quasicoherentInclusion X) (cartierExtCohomologyNatIso k X D n)

end ToricPower

end
