module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Cover.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

@[expose] public section

/-!
# Gluing genuine group actions over a directed open cover

The construction uses the actual base change of an open cover along the
second projection. Consequently its descent and action laws are equalities
of scheme morphisms, over arbitrary base schemes and all residue fields.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory MonObj

variable {S X : Scheme.{u}} [X.Over S]
    (C : X.OpenCover) [Category C.I₀] [C.LocallyDirected] [C.Over S]

instance directedCoverTrans_isOver {i j : C.I₀} (h : i ⟶ j) :
    (C.trans h).IsOver S where
  comp_over := by
    rw [← comp_over (C.f j) S, ← Category.assoc, C.trans_map, comp_over]

/-- The pullback of a chart along the second projection is its actual
product with the first factor. -/
def tensorPullbackChartIso (A : Over S) (i : C.I₀) :
    (C.pullback₁ (pullback.snd A.hom (X ↘ S))).X i ≅
      (A ⊗ (C.X i).asOver S).left :=
  pullbackLeftPullbackSndIso A.hom (X ↘ S) (C.f i) ≪≫
    pullback.congrHom rfl (comp_over (C.f i) S)

@[reassoc (attr := simp)] theorem tensorPullbackChartIso_hom_fst
    (A : Over S) (i : C.I₀) :
    (tensorPullbackChartIso C A i).hom ≫ pullback.fst A.hom (C.X i ↘ S) =
      pullback.fst (pullback.snd A.hom (X ↘ S)) (C.f i) ≫
        pullback.fst A.hom (X ↘ S) := by
  change (pullbackLeftPullbackSndIso A.hom (X ↘ S) (C.f i) ≪≫
    pullback.congrHom rfl (comp_over (C.f i) S)).hom ≫ _ = _
  simp

@[reassoc (attr := simp)] theorem tensorPullbackChartIso_hom_snd
    (A : Over S) (i : C.I₀) :
    (tensorPullbackChartIso C A i).hom ≫ pullback.snd A.hom (C.X i ↘ S) =
      pullback.snd (pullback.snd A.hom (X ↘ S)) (C.f i) := by
  change (pullbackLeftPullbackSndIso A.hom (X ↘ S) (C.f i) ≪≫
    pullback.congrHom rfl (comp_over (C.f i) S)).hom ≫ _ = _
  simp

@[reassoc (attr := simp)] theorem tensorPullbackChartIso_hom_map
    (A : Over S) (i : C.I₀) :
    (tensorPullbackChartIso C A i).hom ≫ (A ◁ (C.f i).asOver S).left =
      (C.pullback₁ (pullback.snd A.hom (X ↘ S))).f i := by
  change (tensorPullbackChartIso C A i).hom ≫ (A ◁ (C.f i).asOver S).left =
    pullback.fst (pullback.snd A.hom (X ↘ S)) (C.f i)
  apply pullback.hom_ext
  all_goals dsimp only [Scheme.asOver, OverClass.asOver]
  · simp only [Category.assoc, Over.whiskerLeft_left_fst]
    dsimp only [Over.mk]
    exact tensorPullbackChartIso_hom_fst C A i
  · simp only [Category.assoc, Over.whiskerLeft_left_snd, OverClass.asOverHom_left]
    dsimp only [Over.mk]
    exact (tensorPullbackChartIso_hom_snd_assoc C A i (C.f i)).trans
      (pullback.condition (f := pullback.snd A.hom (X ↘ S)) (g := C.f i)).symm

@[reassoc (attr := simp)] theorem tensorPullbackChartIso_inv_map
    (A : Over S) (i : C.I₀) :
    (tensorPullbackChartIso C A i).inv ≫
        (C.pullback₁ (pullback.snd A.hom (X ↘ S))).f i =
      (A ◁ (C.f i).asOver S).left := by
  calc
    (tensorPullbackChartIso C A i).inv ≫
        (C.pullback₁ (pullback.snd A.hom (X ↘ S))).f i =
      (tensorPullbackChartIso C A i).inv ≫
        (tensorPullbackChartIso C A i).hom ≫ (A ◁ (C.f i).asOver S).left :=
          congrArg (fun f => (tensorPullbackChartIso C A i).inv ≫ f)
            (tensorPullbackChartIso_hom_map C A i).symm
    _ = _ := Iso.inv_hom_id_assoc _ _

@[reassoc (attr := simp)] theorem tensorPullbackChartIso_naturality
    (A : Over S) {i j : C.I₀} (h : i ⟶ j) :
    Scheme.Cover.trans (C.pullback₁ (pullback.snd A.hom (X ↘ S))) h ≫
        (tensorPullbackChartIso C A j).hom =
      (tensorPullbackChartIso C A i).hom ≫
        (A ◁ (C.trans h).asOver S).left := by
  apply pullback.hom_ext
  all_goals dsimp only [Scheme.asOver, OverClass.asOver]
  · change Scheme.Cover.trans (C.pullback₁ (pullback.snd A.hom (X ↘ S))) h ≫
        (tensorPullbackChartIso C A j).hom ≫ pullback.fst A.hom (C.X j ↘ S) = _
    simp only [tensorPullbackChartIso_hom_fst, Category.assoc,
      Over.whiskerLeft_left_fst]
    change pullback.map _ _ _ _ (𝟙 _) (C.trans h) (𝟙 _) (by simp) (by simp) ≫
      pullback.fst _ _ ≫ pullback.fst _ _ = _
    simp
  · change Scheme.Cover.trans (C.pullback₁ (pullback.snd A.hom (X ↘ S))) h ≫
        (tensorPullbackChartIso C A j).hom ≫ pullback.snd A.hom (C.X j ↘ S) = _
    simp only [tensorPullbackChartIso_hom_snd, Category.assoc,
      Over.whiskerLeft_left_snd, OverClass.asOverHom_left,
      tensorPullbackChartIso_hom_snd_assoc]
    change pullback.map _ _ _ _ (𝟙 _) (C.trans h) (𝟙 _) (by simp) (by simp) ≫ pullback.snd _ _ = _
    simp

/-- Tensoring a genuine open cover is jointly epimorphic. The proof uses
scheme-theoretic base change, not an assertion about pairs of points. -/
theorem tensorCover_hom_ext (A Y : Over S)
    (f g : A ⊗ X.asOver S ⟶ Y)
    (h : ∀ i, A ◁ (C.f i).asOver S ≫ f = A ◁ (C.f i).asOver S ≫ g) :
    f = g := by
  apply Over.OverMorphism.ext
  apply Scheme.Cover.hom_ext (C.pullback₁ (pullback.snd A.hom (X ↘ S)))
  intro i
  rw [← tensorPullbackChartIso_hom_map C A i]
  simpa only [Over.comp_left, Category.assoc] using
    congrArg (fun z => (tensorPullbackChartIso C A i).hom ≫ z.left) (h i)

section Actions

variable (G : Over S) [MonObj G]
    [∀ i, ModObj G ((C.X i).asOver S)]
    (htrans : ∀ {i j : C.I₀} (h : i ⟶ j),
      IsModHom G ((C.trans h).asOver S))

/-- Compatible chart actions descend to an actual scheme morphism. -/
def gluedAction : G ⊗ X.asOver S ⟶ X.asOver S := by
  letI : Category (C.pullback₁ (pullback.snd G.hom (X ↘ S))).I₀ :=
    inferInstanceAs (Category C.I₀)
  letI : Scheme.Cover.LocallyDirected
      (C.pullback₁ (pullback.snd G.hom (X ↘ S))) :=
    Scheme.Cover.locallyDirectedPullbackCover C (pullback.snd G.hom (X ↘ S))
  exact Scheme.OpenCover.glueMorphismsOverOfLocallyDirected
    (X := G ⊗ X.asOver S) (Y := X.asOver S)
    (C.pullback₁ (pullback.snd G.hom (X ↘ S)))
    (fun (i : C.I₀) => (tensorPullbackChartIso C G i).hom ≫
      (γ[G,(C.X i).asOver S]).left ≫ C.f i)
    (by
      intro i j h
      letI := htrans h
      rw [← Category.assoc, tensorPullbackChartIso_naturality C, Category.assoc]
      have heq : (γ[G,(C.X i).asOver S]).left ≫ C.trans h =
          (G ◁ (C.trans h).asOver S).left ≫ (γ[G,(C.X j).asOver S]).left := by
        simpa only [Over.comp_left, OverClass.asOverHom_left,
          selfLeftAction_actionObj, selfLeftAction_actionHomRight,
          OverClass.asOver_left] using
          congrArg (fun z => z.left)
            (IsModHom.smul_hom (A := G) (f := (C.trans h).asOver S))
      simpa only [Category.assoc, C.trans_map] using
        congrArg (fun f => (tensorPullbackChartIso C G i).hom ≫ f ≫ C.f j) heq.symm)
    (by
      intro i
      change (tensorPullbackChartIso C G i).hom ≫
        (γ[G,(C.X i).asOver S]).left ≫ C.f i ≫ (X ↘ S) = _
      rw [comp_over]
      change (tensorPullbackChartIso C G i).hom ≫
        (γ[G,(C.X i).asOver S]).left ≫ ((C.X i).asOver S).hom = _
      rw [Over.w]
      change (tensorPullbackChartIso C G i).hom ≫
        pullback.fst G.hom (C.X i ↘ S) ≫ G.hom = _
      simp only [tensorPullbackChartIso_hom_fst_assoc]
      rfl)

/-- The descended morphism restricts to the original action on every
actual affine chart. -/
@[reassoc (attr := simp)] theorem gluedAction_restrict (i : C.I₀) :
    G ◁ (C.f i).asOver S ≫ gluedAction C G htrans =
      γ[G,(C.X i).asOver S] ≫ (C.f i).asOver S := by
  letI : Category (C.pullback₁ (pullback.snd G.hom (X ↘ S))).I₀ :=
    inferInstanceAs (Category C.I₀)
  letI : Scheme.Cover.LocallyDirected
      (C.pullback₁ (pullback.snd G.hom (X ↘ S))) :=
    Scheme.Cover.locallyDirectedPullbackCover C (pullback.snd G.hom (X ↘ S))
  apply Over.OverMorphism.ext
  apply (cancel_epi (tensorPullbackChartIso C G i).hom).mp
  simp only [Over.comp_left, Category.assoc]
  rw [tensorPullbackChartIso_hom_map_assoc]
  simp only [gluedAction, OverClass.asOverHom_left]
  erw [Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left]
  intro i j h
  letI := htrans h
  rw [← Category.assoc, tensorPullbackChartIso_naturality C, Category.assoc]
  have heq : (γ[G,(C.X i).asOver S]).left ≫ C.trans h =
      (G ◁ (C.trans h).asOver S).left ≫ (γ[G,(C.X j).asOver S]).left := by
    simpa only [Over.comp_left, OverClass.asOverHom_left,
      selfLeftAction_actionObj, selfLeftAction_actionHomRight,
      OverClass.asOver_left] using
      congrArg (fun z => z.left)
        (IsModHom.smul_hom (A := G) (f := (C.trans h).asOver S))
  simpa only [Category.assoc, C.trans_map] using
    congrArg (fun f => (tensorPullbackChartIso C G i).hom ≫ f ≫ C.f j) heq.symm

/-- Unit and multiplication laws descend from the actual chart laws. -/
def gluedModObj : ModObj G (X.asOver S) where
  smul := gluedAction C G htrans
  one_smul := by
    change (η[G] ▷ X.asOver S) ≫ gluedAction C G htrans =
      (λ_ (X.asOver S)).hom
    apply tensorCover_hom_ext C (𝟙_ (Over S)) (X.asOver S)
    intro i
    rw [whisker_exchange_assoc, gluedAction_restrict C,
      ← Category.assoc, ModObj.one_smul_self, leftUnitor_naturality]
  mul_smul := by
    change (μ[G] ▷ X.asOver S) ≫ gluedAction C G htrans =
      (α_ G G (X.asOver S)).hom ≫
        (G ◁ gluedAction C G htrans) ≫ gluedAction C G htrans
    apply tensorCover_hom_ext C (G ⊗ G) (X.asOver S)
    intro i
    rw [whisker_exchange_assoc, gluedAction_restrict C,
      ← Category.assoc, ModObj.mul_smul_self, Category.assoc]
    rw [associator_naturality_right_assoc]
    rw [← whiskerLeft_comp_assoc, gluedAction_restrict C, whiskerLeft_comp]
    simp only [Category.assoc]
    rw [gluedAction_restrict C]

/-- Every chart inclusion is equivariant for the descended action. -/
theorem gluedModObj_chart (i : C.I₀) :
    letI := gluedModObj C G htrans
    IsModHom G ((C.f i).asOver S) := by
  letI := gluedModObj C G htrans
  refine ⟨?_⟩
  change γ[G,(C.X i).asOver S] ≫ (C.f i).asOver S =
    (G ◁ (C.f i).asOver S) ≫ gluedAction C G htrans
  exact (gluedAction_restrict C G htrans i).symm

end Actions

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.gluedModObj
