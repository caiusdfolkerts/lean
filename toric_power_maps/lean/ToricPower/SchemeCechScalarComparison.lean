module

public import ToricPower.CechScalarForget
public import ToricPower.CechFunctorLinear
public import ToricPower.SchemeCohomologyLinear
public import ToricPower.QuasicoherentCechComparison
public import ToricPower.QuasicoherentBaseLinear

/-!
# The actual base-linear affine Čech cohomology comparison

The already checked additive comparison is natural in every coefficient
map. Applied to scalar multiplication endomorphisms, this naturality
forces compatibility with the specified base-ring actions. The resulting
linear isomorphism compares the genuine ordinary sheaf cohomology with
the genuine full module-valued Čech complex.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TauCeti.AlgebraicGeometry.Scheme.Modules
open BondalThomsen.FiniteAffineCechHigherComparison

namespace ToricPower.CechScalar

universe u
variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  {Index : Type u} (opens : Index → X.Opens)

/-- The scalar-forgetting comparison retains the literal sheaf section
complex and all coefficient maps. -/
def schemeComplexForgetNatIso :
    linearComplexFunctor k X opens ⋙ (forgetScalars k).mapHomologicalComplex (.up ℕ) ≅
      schemeCechComplexFunctor opens :=
  NatIso.ofComponents (fun M => cochainForgetIso k
      (FormalCoproduct.mk Index opens).cech ((FiniteCover.schemeBasePresheaf k X).obj M))
    (fun f => cochainForgetIso_naturality k (FormalCoproduct.mk Index opens).cech
      ((FiniteCover.schemeBasePresheaf k X).map f))

/-- Forgetting actual linear Čech cohomology gives actual additive Čech
cohomology, naturally in the coefficient sheaf. -/
def schemeHomologyForgetNatIso (degree : ℕ) :
    linearHomologyFunctor k X opens degree ⋙ forgetScalars k ≅
      CechNaturality.cechHomologyFunctor opens degree :=
  (Functor.isoWhiskerLeft (linearComplexFunctor k X opens)
      (homologyForgetNatIso k degree)).symm ≪≫
    Functor.isoWhiskerRight (schemeComplexForgetNatIso k X opens)
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) degree)

variable [IsLocallyNoetherian X] [CompactSpace X] [X.IsSeparated] [Finite Index]
  (cover : iSup opens = ⊤) (affine : ∀ a, IsAffineOpen (opens a))

/-- An actual scalar-linear natural isomorphism between ordinary sheaf
cohomology and the full finite-affine Čech cohomology on quasicoherent
sheaves. No transported or replacement scalar action is introduced. -/
def quasicoherentLinearCechNatIso (degree : ℕ) :
    quasicoherentInclusion X ⋙ cohomologyBaseFunctor k X degree ≅
      quasicoherentInclusion X ⋙ linearHomologyFunctor k X opens degree := by
  let F := quasicoherentInclusion X ⋙ cohomologyBaseFunctor k X degree
  let G := quasicoherentInclusion X ⋙ linearHomologyFunctor k X opens degree
  let additive : F ⋙ forgetScalars k ≅ G ⋙ forgetScalars k :=
    Functor.isoWhiskerLeft (quasicoherentInclusion X)
        (cohomologyBaseFunctorForgetIso k X degree) ≪≫
      CechNaturality.quasicoherentCechNatIso opens cover affine degree ≪≫
        (Functor.isoWhiskerLeft (quasicoherentInclusion X)
          (schemeHomologyForgetNatIso k X opens degree)).symm
  exact (additiveLinearLiftForgetIso k F).symm ≪≫
    additiveLinearLiftNatIso k additive ≪≫ additiveLinearLiftForgetIso k G

/-- The component is a genuine linear equivalence for the canonical
base action on ordinary sheaf cohomology. -/
def quasicoherentLinearCechIso (M : X.Modules) [M.IsQuasicoherent] (degree : ℕ) :
    ModuleCat.of k (Cohomology M degree) ≅
      ((linearComplexFunctor k X opens).obj M).homology degree :=
  (quasicoherentLinearCechNatIso k X opens cover affine degree).app ⟨M, inferInstance⟩

end ToricPower.CechScalar

end
