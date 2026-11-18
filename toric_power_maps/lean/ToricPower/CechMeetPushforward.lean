module

public import ToricPower.CechMeetLinearComparison
public import ToricPower.SchemePushforwardBaseSections
public import ToricPower.SchemeCechScalarComparison
public import ToricPower.QuasicoherentOpenAdjunction

/-! # Literal Čech cohomology of an affine direct image

Every tuple coefficient of the direct image is the section module on
the inverse-image intersection. The comparison below preserves the
actual scalar action and every restriction differential. It does not
require direct image to preserve injective objects.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open BondalThomsen.FiniteAffineCechHigherComparison
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace ToricPower.FiniteCech

variable {B : Type} [SemilatticeInf B] (k : Type) [Field k]
  {X Y : Scheme} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (opens : B ⥤ Y.Opens)
  (meetEq : ∀ (q : ℕ) (t : Fin (q+1) → B),
    cechIntersection opens.obj q t = opens.obj (tupleMeet t))

/-- Inverse image preserves each actual finite tuple intersection. -/
theorem inverseImage_cechIntersection (q : ℕ) (t : Fin (q+1) → B) :
    cechIntersection (opens ⋙ Opens.map f.base).obj q t =
      f ⁻¹ᵁ cechIntersection opens.obj q t := by
  simp only [cechIntersection,productOpens_eq_iInf,Functor.comp_obj]
  apply Opens.ext
  rw [Opens.coe_iInf,Scheme.Hom.coe_preimage,Opens.coe_iInf]
  change (⋂ j, f ⁻¹' (opens.obj (t j) : Set Y)) = f ⁻¹' ⋂ j, (opens.obj (t j) : Set Y)
  exact (Set.preimage_iInter).symm

include meetEq in
theorem inverseImage_tupleMeet (q : ℕ) (t : Fin (q+1) → B) :
    cechIntersection (opens ⋙ Opens.map f.base).obj q t =
      (opens ⋙ Opens.map f.base).obj (tupleMeet t) := by
  rw [inverseImage_cechIntersection,meetEq]
  rfl

/-- An isomorphism of the full section diagram induces an isomorphism
of the original tuple coefficient complexes. -/
def tupleCoefficientIso {F G : Bᵒᵖ ⥤ ModuleCat k} (e : F ≅ G) :
    tupleCoefficientComplex k F ≅ tupleCoefficientComplex k G :=
  (NatIso.mapHomologicalComplex
    ((linearYoneda k (Bᵒᵖ ⥤ ModuleCat k)).mapIso e) (.up ℕ)).app (tupleComplex k).op

/-- The direct-image section comparison at every actual chart. -/
def pushforwardMeetSectionsIso (M : X.Modules) :
    opens.op ⋙ ((FiniteCover.schemeBasePresheaf k Y).obj
      ((Scheme.Modules.pushforward f).obj M)) ≅
      (opens ⋙ Opens.map f.base).op ⋙ ((FiniteCover.schemeBasePresheaf k X).obj M) :=
  (pushforwardChartBaseSectionsIso k f opens.op).app M

/-- The full, scalar-linear, original tuple Čech complexes agree. -/
def pushforwardMeetCechIso (M : X.Modules) :
    (CechScalar.linearComplexFunctor k Y opens.obj).obj
        ((Scheme.Modules.pushforward f).obj M) ≅
      (CechScalar.linearComplexFunctor k X (opens ⋙ Opens.map f.base).obj).obj M :=
  meetLinearCechComplexIso k Y opens meetEq
      ((FiniteCover.schemeBasePresheaf k Y).obj ((Scheme.Modules.pushforward f).obj M)) ≪≫
    tupleCoefficientIso k (pushforwardMeetSectionsIso k f opens M) ≪≫
    (meetLinearCechComplexIso k X (opens ⋙ Opens.map f.base)
      (inverseImage_tupleMeet f opens meetEq)
      ((FiniteCover.schemeBasePresheaf k X).obj M)).symm

variable [Finite B] [IsLocallyNoetherian X] [CompactSpace X] [X.IsSeparated]
  [IsLocallyNoetherian Y] [CompactSpace Y] [Y.IsSeparated] [IsAffineHom f]
  (cover : iSup opens.obj = ⊤) (affine : ∀ b, IsAffineOpen (opens.obj b))

/-- Ordinary sheaf cohomology of an affine direct image, with the
canonical base-field action and no omitted degree. -/
def affinePushforwardCohomologyIso (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    ModuleCat.of k (Cohomology ((Scheme.Modules.pushforward f).obj M) q) ≅
      ModuleCat.of k (Cohomology M q) :=
  CechScalar.quasicoherentLinearCechIso k Y opens.obj cover affine
      ((Scheme.Modules.pushforward f).obj M) q ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) q).mapIso
      (pushforwardMeetCechIso k f opens meetEq M) ≪≫
    (CechScalar.quasicoherentLinearCechIso k X (opens ⋙ Opens.map f.base).obj
      (f.iSup_preimage_eq_top cover) (fun b => (affine b).preimage f) M q).symm

end ToricPower.FiniteCech

end
