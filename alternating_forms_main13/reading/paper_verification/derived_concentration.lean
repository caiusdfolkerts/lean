module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Acyclic objects and composition of right derived functors

The hypotheses below concern the actual derived functors, constructed from
injective resolutions. They are useful for the projective-line reflection:
pushforward preserves injectives on abelian sheaves, while the required
vanishing is proved by the relative Čech calculation.

The first construction turns any bounded below complex of injectives which
is exact in positive degrees into an injective resolution of its zero cycles.
It does not assume that a functor is exact on all objects. Consequently, the
composition comparison applies to an individual acyclic sheaf, precisely
the form needed in the flag-bundle induction.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace PaperVerification.DerivedConcentration

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The inclusion of the zero cycles into a nonnegative cochain complex,
regarded as a map of complexes. -/
def cyclesAugmentation (K : CochainComplex C ℕ) :
    (CochainComplex.single₀ C).obj (K.cycles 0) ⟶ K :=
  (CochainComplex.fromSingle₀Equiv K (K.cycles 0)).symm
    ⟨K.iCycles 0, by simp⟩

@[simp]
lemma cyclesAugmentation_f_zero (K : CochainComplex C ℕ) :
    (cyclesAugmentation K).f 0 = K.iCycles 0 := by
  simp [cyclesAugmentation]

lemma cyclesMap_cyclesAugmentation (K : CochainComplex C ℕ) :
    cyclesMap (cyclesAugmentation K) 0 =
      (singleObjCyclesSelfIso (ComplexShape.up ℕ) 0 (K.cycles 0)).hom := by
  apply (cancel_mono (K.iCycles 0)).1
  rw [cyclesMap_i, cyclesAugmentation_f_zero,
    singleObjCyclesSelfIso_hom]
  change _ = ((_ ≫ 𝟙 _) ≫ _)
  simp only [Category.comp_id, Category.assoc]

lemma homologyMap_cyclesAugmentation (K : CochainComplex C ℕ) :
    homologyMap (cyclesAugmentation K) 0 =
      (singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (K.cycles 0)).hom ≫
        K.homologyπ 0 := by
  apply (cancel_epi
    (((CochainComplex.single₀ C).obj (K.cycles 0)).homologyπ 0)).1
  rw [homologyπ_naturality,
    homologyπ_singleObjHomologySelfIso_hom_assoc,
    cyclesMap_cyclesAugmentation]

instance cyclesAugmentation_quasiIsoAt_zero (K : CochainComplex C ℕ) :
    QuasiIsoAt (cyclesAugmentation K) 0 := by
  rw [quasiIsoAt_iff_isIso_homologyMap, homologyMap_cyclesAugmentation]
  change IsIso
    ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (K.cycles 0)).hom ≫
      K.isoHomologyπ₀.hom)
  infer_instance

/-- A complex of injectives with no positive cohomology resolves its zero
cycles. Exactness is a proved property of the complex, not extra data in a
replacement definition of cohomology. -/
def cyclesResolution (K : CochainComplex C ℕ)
    [∀ n, Injective (K.X n)] (hK : ∀ n, K.ExactAt (n + 1)) :
    InjectiveResolution (K.cycles 0) where
  cocomplex := K
  ι := cyclesAugmentation K
  quasiIso := by
    rw [quasiIso_iff]
    intro n
    cases n with
    | zero => infer_instance
    | succ n =>
        rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _)]
        exact hK n

section Composition

variable [HasInjectiveResolutions C]
  {D : Type*} [Category* D] [Abelian D] [HasInjectiveResolutions D]
  {E : Type*} [Category* E] [Abelian E]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  [F.PreservesInjectiveObjects]

/-- Applying a left exact functor to an injective resolution gives an
injective resolution whenever its positive derived functors vanish on the
particular object. -/
def imageResolution {X : C} (I : InjectiveResolution X)
    (hX : ∀ n, IsZero ((F.rightDerived (n + 1)).obj X)) :
    InjectiveResolution (F.obj X) where
  cocomplex := (F.mapHomologicalComplex _).obj I.cocomplex
  injective n := Functor.PreservesInjectiveObjects.injective_obj (I.injective n)
  ι := (CochainComplex.single₀ D).map (I.toRightDerivedZero' F) ≫
    cyclesAugmentation ((F.mapHomologicalComplex _).obj I.cocomplex)
  quasiIso := by
    let K := (F.mapHomologicalComplex _).obj I.cocomplex
    have hK : ∀ n, K.ExactAt (n + 1) := by
      intro n
      rw [exactAt_iff_isZero_homology]
      exact IsZero.of_iso (hX n) (I.isoRightDerivedObj F (n + 1)).symm
    haveI : ∀ n, Injective (K.X n) := fun n =>
      Functor.PreservesInjectiveObjects.injective_obj (I.injective n)
    haveI : QuasiIso (cyclesAugmentation K) := (cyclesResolution K hK).quasiIso
    infer_instance

@[simp]
lemma imageResolution_ι_f_zero {X : C} (I : InjectiveResolution X)
    (hX : ∀ n, IsZero ((F.rightDerived (n + 1)).obj X)) :
    (imageResolution F I hX).ι.f 0 = F.map (I.ι.f 0) := by
  simp [imageResolution]

/-- The objectwise Leray comparison for an acyclic object. This derives
`Rⁿ(G ∘ F)(X) ≅ RⁿG(F(X))` from the literal injective resolutions, assuming
only positive-degree acyclicity of `X` for `F`. -/
def compositionIso (G : D ⥤ E) [G.Additive] (X : C)
    (hX : ∀ n, IsZero ((F.rightDerived (n + 1)).obj X)) (n : ℕ) :
    ((F ⋙ G).rightDerived n).obj X ≅
      (G.rightDerived n).obj (F.obj X) :=
  (injectiveResolution X).isoRightDerivedObj (F ⋙ G) n ≪≫
    ((imageResolution F (injectiveResolution X) hX).isoRightDerivedObj G n).symm

end Composition

end PaperVerification.DerivedConcentration
