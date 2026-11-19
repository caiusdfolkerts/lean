module

public import ToricPower.QuasicoherentCartierCechSourceNaturality

/-!
# Cartier sources as an actual functor category

Objects carry a Cartier divisor and morphisms are all morphisms between
its actual line sheaves. The inverse-tensor construction is a genuine
contravariant functor. The full Cartier Ext/Čech comparison is then one
natural isomorphism in the source label, with its components natural in
the quasicoherent coefficient sheaf.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 600000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian MonoidalCategory Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace ToricPower

universe u
variable (X : Scheme.{u}) [IsIntegral X]

/-- Cartier divisors labelled by their actual module sheaves, with all
actual sheaf morphisms as arrows. -/
abbrev CartierSources := InducedCategory X.Modules (CartierDivisor.sheaf (X := X))

/-- The divisor carried by a labelled source. -/
def cartierSourceDivisor (D : CartierSources X) : CartierDivisor X := D

/-- The actual quasicoherent Cartier source functor. -/
def cartierSourcesQuasicoherent : CartierSources X ⥤ QCoh X where
  obj D := quasicoherentCartierObject X (cartierSourceDivisor X D)
  map f := ObjectProperty.homMk f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inverse-tensor maps are actual mates of the exact tensor
adjunctions, and their identities and composition laws are proved. -/
def cartierSourcesInverseTensor : (CartierSources X)ᵒᵖ ⥤ X.Modules ⥤ X.Modules where
  obj D := tensorLeft (-(cartierSourceDivisor X D.unop)).sheaf
  map f := cartierDualTwistMap X f.unop.hom
  map_id D := by
    let adj := (cartierTensorEquivalence (cartierSourceDivisor X D.unop)).toAdjunction
    have mapped := (tensoringLeft X.Modules).map_id (cartierSourceDivisor X D.unop).sheaf
    exact (congrArg (conjugateEquiv adj adj) mapped).trans (conjugateEquiv_id adj)
  map_comp {D E F} f g := by
    let adjD := (cartierTensorEquivalence (cartierSourceDivisor X D.unop)).toAdjunction
    let adjE := (cartierTensorEquivalence (cartierSourceDivisor X E.unop)).toAdjunction
    let adjF := (cartierTensorEquivalence (cartierSourceDivisor X F.unop)).toAdjunction
    have mapped := (tensoringLeft X.Modules).map_comp g.unop.hom f.unop.hom
    exact (congrArg (conjugateEquiv adjD adjF) mapped).trans
      (conjugateEquiv_comp adjD adjE adjF
        ((tensoringLeft X.Modules).map f.unop.hom)
        ((tensoringLeft X.Modules).map g.unop.hom)).symm

/-- The same actual inverse tensor functor, restricted to quasicoherent
coefficients. -/
def cartierSourcesQuasicoherentInverseTensor :
    (CartierSources X)ᵒᵖ ⥤ QCoh X ⥤ QCoh X where
  obj D := (quasicoherentCartierTensorEquivalence (-(cartierSourceDivisor X D.unop))).functor
  map f :=
    { app M := ObjectProperty.homMk ((cartierDualTwistMap X f.unop.hom).app M.obj)
      naturality {M N} g := by
        apply ObjectProperty.hom_ext
        exact (cartierDualTwistMap X f.unop.hom).naturality g.hom }
  map_id D := by
    apply NatTrans.ext
    funext M
    apply ObjectProperty.hom_ext
    exact NatTrans.congr_app ((cartierSourcesInverseTensor X).map_id D) M.obj
  map_comp f g := by
    apply NatTrans.ext
    funext M
    apply ObjectProperty.hom_ext
    exact NatTrans.congr_app ((cartierSourcesInverseTensor X).map_comp f g) M.obj

variable (k : Type u) [CommRing k] [X.Over (Spec (.of k))]
  [IsLocallyNoetherian X] [CompactSpace X] [X.IsSeparated]
  {Index : Type u} [Finite Index] (opens : Index → X.Opens)
  (cover : iSup opens = ⊤) (affine : ∀ index, IsAffineOpen (opens index))

local instance cartierSourcesHasExt : HasExt.{u} (QCoh X) :=
  hasExt_of_enoughInjectives (QCoh X)

/-- Ext of actual quasicoherent sheaves, with all contravariant Cartier
source maps retained. -/
def cartierSourcesExt (n : ℕ) :
    (CartierSources X)ᵒᵖ ⥤ QCoh X ⥤ AddCommGrpCat.{u} :=
  (cartierSourcesQuasicoherent X).op ⋙ extFunctor n

/-- Actual Čech cohomology of the actual inverse tensor twist, with
its complete source and coefficient functoriality. -/
def cartierSourcesCech (n : ℕ) :
    (CartierSources X)ᵒᵖ ⥤ QCoh X ⥤ AddCommGrpCat.{u} :=
  cartierSourcesQuasicoherentInverseTensor X ⋙
    (Functor.whiskeringRight (QCoh X) (QCoh X) AddCommGrpCat.{u}).obj
      (quasicoherentInclusion X ⋙ CechNaturality.cechHomologyFunctor opens n)

/-- A single natural isomorphism retains every Cartier-source arrow and
every quasicoherent coefficient arrow in every cohomological degree. -/
def cartierSourcesExtCechNatIso (n : ℕ) :
    cartierSourcesExt X n ≅ cartierSourcesCech X opens n :=
  NatIso.ofComponents
    (fun D => quasicoherentCartierCechNatIso k X opens cover affine (cartierSourceDivisor X D.unop) n)
    (by
      intro D E f
      apply NatTrans.ext
      funext M
      exact quasicoherentCartierCechNatIso_source_naturality k X opens cover affine
        ((cartierSourcesQuasicoherent X).map f.unop) M n)

end ToricPower
