module

public import PaperVerification.ExtRightDerived
public import PaperVerification.InjectiveGoodShift
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable

/-!
# Derived global sections and the single-degree Leray comparison

The cohomology on both sides below is Mathlib's original `Sheaf.H`, defined
as Ext from the constant integer sheaf. The intermediate right-derived
functors are explicitly compared to it. Pushforward of abelian sheaves
preserves injectives because its inverse-image left adjoint is exact;
no analogous assertion about arbitrary module-sheaf pullback is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace PaperVerification.SheafDerivedComparison

universe u

/-- Ordinary global sections of actual abelian sheaves. -/
def globalSections (X : TopCat.{u}) : X.Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op ⊤)

instance (X : TopCat.{u}) : (globalSections X).Additive where
  map_add := rfl

/-- The constant integer sheaf corepresents global sections additively. -/
def globalSectionsHomIso (X : TopCat.{u}) :
    preadditiveCoyoneda.obj (op
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ)))) ≅ globalSections X :=
  NatIso.ofComponents
    (fun F =>
      (((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homAddEquiv (AddCommGrpCat.of (ULift ℤ)) F).trans
          (AddCommGrpCat.uliftZMultiplesAddEquiv _)).toAddCommGrpIso)
    (by
      intro F G f
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro a
      change AddCommGrpCat.uliftZMultiplesAddEquiv _
        ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homEquiv _ G (a ≫ f)) = _
      rw [Adjunction.homEquiv_naturality_right]
      rfl)

/-- A natural isomorphism induces a natural isomorphism of the actual
nonnegative right-derived functors. -/
def rightDerivedIso {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasInjectiveResolutions C]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G) (n : ℕ) :
    F.rightDerived n ≅ G.rightDerived n where
  hom := e.hom.rightDerived n
  inv := e.inv.rightDerived n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

/-- Native sheaf cohomology agrees with the right-derived global-section
functor, with an actual additive equivalence in every degree. -/
def cohomologyEquiv (X : TopCat.{u}) (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    CategoryTheory.Sheaf.H.{u} F n ≃+ ((globalSections X).rightDerived n).obj F :=
  by
  letI : (globalSections X).Additive := { map_add := rfl }
  exact (ExtRightDerived.extRightDerivedEquiv _ F n).trans
    ((rightDerivedIso (globalSectionsHomIso X) n).app F).addCommGroupIsoToAddEquiv

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

instance pushforward_additive : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive where
  map_add := rfl

/-- Inverse image of abelian sheaves preserves finite limits. -/
instance pullback_preservesFiniteLimits :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) := by
  dsimp only [TopCat.Sheaf.pullback]
  exact CategoryTheory.Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
      (Opens.map f) AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- Consequently, abelian-sheaf pushforward preserves injectives for every
continuous map. This is proved from the actual sheaf adjunction. -/
instance pushforward_preservesInjectives :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)

/-- Taking global sections after pushforward is taking global sections on
the source, via the equality of the inverse image of the top open. -/
def pushforwardGlobalSectionsIso :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙ globalSections Y ≅ globalSections X := by
  have h : (Opens.map f).obj ⊤ = ⊤ := by ext x; simp
  exact NatIso.ofComponents (fun F => F.obj.mapIso (eqToIso h.symm).op)
    (fun g => (g.hom.naturality _).symm)

/-- Leray comparison when the actual derived direct image is concentrated
in one degree. Every group in the statement is native sheaf cohomology. -/
def concentratedLerayEquiv (F : X.Sheaf AddCommGrpCat.{u}) (k : ℕ)
    (hF : ∀ q, q ≠ k → IsZero
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived q).obj F)) (n : ℕ) :
    CategoryTheory.Sheaf.H.{u} F (k + n) ≃+
      CategoryTheory.Sheaf.H.{u}
        (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived k).obj F) n :=
  by
  let eΓ := (rightDerivedIso (pushforwardGlobalSectionsIso f).symm (k + n)).app F
  let eL := DerivedConcentration.compositionConcentratedIso
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) (globalSections Y) F k hF n
  exact (cohomologyEquiv X F (k + n)).trans
    (eΓ.addCommGroupIsoToAddEquiv.trans
      (eL.addCommGroupIsoToAddEquiv.trans (cohomologyEquiv Y _ n).symm))

end PaperVerification.SheafDerivedComparison
