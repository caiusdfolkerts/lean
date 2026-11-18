module

public import ToricPower.FiniteCoverIntersections
public import ToricPower.QuasicoherentCategory
public import ToricPower.CartierCore

/-!
# The exact affine-intersection diagram of an actual quasicoherent sheaf

The scalar action is restriction along the actual structure morphism
`X → Spec k`.  Each component is literally the module of sections on the
corresponding intersection, and each arrow is its literal restriction.
Affineness of finite nonempty intersections follows from separation.

The diagram functor is exact because sections of quasicoherent sheaves
are exact on affine opens.  Its ordinary limit is the actual module of
global sections, by the proved sheaf-gluing comparison.  No unbounded
derived comparison is inferred from that ordinary statement.

-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace ToricPower.FiniteCover

universe u

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The actual sheaf of base-field vector spaces underlying an
`O_X`-module.  The construction restricts the global scalar action
through the actual structural ring homomorphism. -/
def schemeBaseSheaf : X.Modules ⥤ TopCat.Sheaf (ModuleCat.{u} k) X := by
  letI : (Opens.grothendieckTopology X).HasSheafCompose
      (ModuleCat.restrictScalars.{u} (Scheme.Modules.baseRingToGlobalSections k X)) :=
    hasSheafCompose_of_preservesLimitsOfSize _
  exact SheafOfModules.forgetToSheafModuleCat X.ringCatSheaf (op ⊤)
    (initialOpOfTerminal isTerminalTop) ⋙
  sheafCompose _ (ModuleCat.restrictScalars
    (Scheme.Modules.baseRingToGlobalSections k X))

/-- The same actual base-field sheaf, viewed as a presheaf. -/
abbrev schemeBasePresheaf : X.Modules ⥤ X.Opensᵒᵖ ⥤ ModuleCat.{u} k :=
  schemeBaseSheaf k X ⋙ TopCat.Sheaf.forget _ _

instance schemeBasePresheaf_additive : (schemeBasePresheaf k X).Additive where
  map_add {M N} {f g} := by
    ext U x
    rfl

/-- Sections on one actual open, with the actual base-field action. -/
abbrev schemeBaseSections (U : X.Opens) : X.Modules ⥤ ModuleCat.{u} k :=
  schemeBasePresheaf k X ⋙ (evaluation _ _).obj (op U)

@[simp]
theorem schemeBaseSections_map_apply (U : X.Opens) {M N : X.Modules}
    (f : M ⟶ N) (x : (schemeBaseSections k X U).obj M) :
    (schemeBaseSections k X U).map f x = f.app U x := rfl

instance schemeBaseSections_additive (U : X.Opens) :
    (schemeBaseSections k X U).Additive := inferInstance

/-- Taking sections is left exact.  This proof reflects actual finite
limits through the ordinary forgetful functor to abelian groups. -/
instance schemeBaseSections_preservesFiniteLimits (U : X.Opens) :
    PreservesFiniteLimits (schemeBaseSections k X U) := by
  let G := forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}
  have h : schemeBaseSections k X U ⋙ G =
      SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
          (evaluation _ AddCommGrpCat.{u}).obj (op U) := rfl
  letI : PreservesFiniteLimits (schemeBaseSections k X U ⋙ G) := by
    rw [h]
    exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _
      (inferInstanceAs (PreservesFiniteLimits (SheafOfModules.forget.{u} X.ringCatSheaf)))
      (inferInstanceAs (PreservesFiniteLimits
        (PresheafOfModules.toPresheaf.{u} X.ringCatSheaf.obj ⋙
          (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op U))))
  exact preservesFiniteLimits_of_reflects_of_preserves _ G

/-- Affine sections of an actual short exact sequence of quasicoherent
sheaves are short exact over the base field. -/
theorem schemeBaseSections_shortExact (U : X.Opens) (hU : IsAffineOpen U)
    (S : ShortComplex (QCoh X)) (hS : S.ShortExact) :
    (S.map (quasicoherentInclusion X ⋙ schemeBaseSections k X U)).ShortExact := by
  let F := quasicoherentInclusion X ⋙ schemeBaseSections k X U
  have hA := hS.map_of_exact (quasicoherentInclusion X)
  letI : ((quasicoherentInclusion X).obj S.X₂).IsQuasicoherent := S.X₂.property
  letI : ((quasicoherentInclusion X).obj S.X₃).IsQuasicoherent := S.X₃.property
  letI : Epi ((quasicoherentInclusion X).map S.g) := hA.epi_g
  letI : Epi (F.map S.g) := (ModuleCat.epi_iff_surjective _).2
    (ToricPower.affineSections_surjective_of_epi
      ((quasicoherentInclusion X).map S.g) hU)
  letI := hS.mono_f
  exact
    { exact := hS.exact.map_of_mono_of_preservesKernel F inferInstance inferInstance
      mono_f := (inferInstance : Mono (F.map S.f))
      epi_g := (inferInstance : Epi (F.map S.g)) }

theorem schemeBaseSections_exact (U : X.Opens) (hU : IsAffineOpen U) :
    PreservesFiniteLimits (quasicoherentInclusion X ⋙ schemeBaseSections k X U) ∧
      PreservesFiniteColimits (quasicoherentInclusion X ⋙ schemeBaseSections k X U) := by
  exact ((Functor.exact_tfae
    (quasicoherentInclusion X ⋙ schemeBaseSections k X U)).out 1 4).mp (by
    intro S hS
    exact schemeBaseSections_shortExact k X U hU S hS)

variable {I : Type u} [DecidableEq I] (U : I → X.Opens)

/-- The literal intersection diagram of a quasicoherent sheaf. -/
def quasicoherentIntersectionSections : QCoh X ⥤ Index I ⥤ ModuleCat.{u} k :=
  quasicoherentInclusion X ⋙ schemeBasePresheaf k X ⋙
    (Functor.whiskeringLeft (Index I) X.Opensᵒᵖ (ModuleCat.{u} k)).obj
      (intersectionFunctor U)

@[simp]
theorem quasicoherentIntersectionSections_obj (M : QCoh X) (S : Index I) :
    ((quasicoherentIntersectionSections k X U).obj M).obj S =
      (schemeBaseSections k X (intersection U S)).obj M.obj := rfl

@[simp]
theorem quasicoherentIntersectionSections_map_apply (M : QCoh X)
    {S T : Index I} (f : S ⟶ T)
    (x : ((quasicoherentIntersectionSections k X U).obj M).obj S) :
    ((quasicoherentIntersectionSections k X U).obj M).map f x =
      M.obj.val.map (homOfLE (intersection_antitone U (leOfHom f))).op x := rfl

instance quasicoherentIntersectionSections_additive :
    (quasicoherentIntersectionSections k X U).Additive where
  map_add {M N} {f g} := by
    ext S x
    rfl

theorem quasicoherentIntersectionSections_evaluation (S : Index I) :
    quasicoherentIntersectionSections k X U ⋙
        (evaluation (Index I) (ModuleCat.{u} k)).obj S =
      quasicoherentInclusion X ⋙ schemeBaseSections k X (intersection U S) := rfl

/-- Finite nonempty intersections of affine opens in a separated scheme
are affine; this is the actual geometric input for exactness. -/
theorem intersection_isAffine [X.IsSeparated] (hU : ∀ i, IsAffineOpen (U i))
    (S : Index I) : IsAffineOpen (intersection U S) := by
  exact IsAffineOpen.biInf (S.val : Set I) S.val.finite_toSet
    (by simpa using S.property) (fun i _ => hU i)

/-- The literal finite-intersection diagram functor is exact on QCoh. -/
theorem quasicoherentIntersectionSections_exact [X.IsSeparated]
    (hU : ∀ i, IsAffineOpen (U i)) :
    PreservesFiniteLimits (quasicoherentIntersectionSections k X U) ∧
      PreservesFiniteColimits (quasicoherentIntersectionSections k X U) := by
  constructor
  · apply preservesFiniteLimits_of_evaluation
    intro S
    rw [quasicoherentIntersectionSections_evaluation]
    exact (schemeBaseSections_exact k X (intersection U S)
      (intersection_isAffine X U hU S)).1
  · apply preservesFiniteColimits_of_evaluation
    intro S
    rw [quasicoherentIntersectionSections_evaluation]
    exact (schemeBaseSections_exact k X (intersection U S)
      (intersection_isAffine X U hU S)).2

/-- The actual ordinary global-sections/limit comparison.  Its proof uses
sheaf gluing on the given cover; it does not assume derived descent. -/
def quasicoherentGlobalSectionsLimitIso (hU : iSup U = ⊤) (M : QCoh X) :
    (schemeBaseSections k X ⊤).obj M.obj ≅
      limit ((quasicoherentIntersectionSections k X U).obj M) :=
  ((schemeBaseSheaf k X).obj M.obj).obj.mapIso (eqToIso hU).op ≪≫
    globalSectionsLimitIso U ((schemeBaseSheaf k X).obj M.obj)

end ToricPower.FiniteCover

end
