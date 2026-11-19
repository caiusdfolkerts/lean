module

public import ToricPower.CellularFiniteResolution
public import ToricPower.VectorAcyclicContraction

/-!
# K-projectivity of the unbounded cellular vector cover

A map out of the actual vector cover is determined by one linear map
at every object of the incidence category. This universal property is
proved for the literal coproduct cover. It transfers the actual pointwise
vector-space contractions to a genuine homotopy of diagram complexes.

Consequently the vector cover of any unbounded complex is K-projective.
The coefficient complexes are never replaced by bounded truncations, and
all actual morphisms of the incidence category remain present.

-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex

namespace ToricPower.Cellular

universe u

variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]

/-- Evaluation of an actual cover morphism on the identity-incidence
generator. This is an actual linear map of vector spaces. -/
def diagramCoverEvaluation {F G : C ⥤ ModuleCat.{u} k}
    (a : diagramVectorCoverObj k F ⟶ G) (c : C) : F.obj c ⟶ G.obj c :=
  diagramVectorCoverSection k F c ≫ a.app c

@[simp]
theorem diagramCoverEvaluation_apply {F G : C ⥤ ModuleCat.{u} k}
    (a : diagramVectorCoverObj k F ⟶ G) (c : C) (x : F.obj c) :
    diagramCoverEvaluation k a c x =
      a.app c ((diagramVectorCoverInclusion k F c x).app c (ModuleCat.freeMk (𝟙 c))) := rfl

/-- The pointwise section is natural in the input diagram, even though
it is not a natural transformation in the cell variable. -/
@[reassoc]
theorem diagramVectorCoverSection_natural {F G : C ⥤ ModuleCat.{u} k}
    (η : F ⟶ G) (c : C) :
    diagramVectorCoverSection k F c ≫ ((diagramVectorCover k).map η).app c =
      η.app c ≫ diagramVectorCoverSection k G c := by
  ext x
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (diagramVectorCoverInclusion_natural k η c x) c)
    (ModuleCat.freeMk (𝟙 c))
  simp only [NatTrans.comp_app, ModuleCat.comp_apply] at h
  exact h

@[simp]
theorem diagramCoverEvaluation_precomp {F F' G : C ⥤ ModuleCat.{u} k}
    (η : F ⟶ F') (a : diagramVectorCoverObj k F' ⟶ G) (c : C) :
    diagramCoverEvaluation k ((diagramVectorCover k).map η ≫ a) c =
      η.app c ≫ diagramCoverEvaluation k a c := by
  simp only [diagramCoverEvaluation, NatTrans.comp_app,
    diagramVectorCoverSection_natural_assoc, Category.assoc]

@[simp]
theorem diagramCoverEvaluation_postcomp {F G G' : C ⥤ ModuleCat.{u} k}
    (a : diagramVectorCoverObj k F ⟶ G) (η : G ⟶ G') (c : C) :
    diagramCoverEvaluation k (a ≫ η) c =
      diagramCoverEvaluation k a c ≫ η.app c := by
  simp only [diagramCoverEvaluation, NatTrans.comp_app, Category.assoc]

@[simp]
theorem diagramCoverEvaluation_add {F G : C ⥤ ModuleCat.{u} k}
    (a b : diagramVectorCoverObj k F ⟶ G) (c : C) :
    diagramCoverEvaluation k (a+b) c =
      diagramCoverEvaluation k a c + diagramCoverEvaluation k b c := by
  simp only [diagramCoverEvaluation, NatTrans.app_add, Preadditive.comp_add]

@[simp]
theorem diagramCoverEvaluation_zero (F G : C ⥤ ModuleCat.{u} k) (c : C) :
    diagramCoverEvaluation k (0 : diagramVectorCoverObj k F ⟶ G) c = 0 := by
  simp only [diagramCoverEvaluation, NatTrans.app_zero, comp_zero]

/-- Evaluation at all actual objects detects cover morphisms. This is
the ordinary representable universal property inside both coproducts. -/
theorem diagramCoverEvaluation_hom_ext {F G : C ⥤ ModuleCat.{u} k}
    {a b : diagramVectorCoverObj k F ⟶ G}
    (h : ∀ c : C, diagramCoverEvaluation k a c = diagramCoverEvaluation k b c) : a = b := by
  apply Sigma.hom_ext
  intro c
  apply vectorCopower_hom_ext k (representable k c) (F.obj c)
  intro x
  apply (representableHomEquiv k G c).injective
  exact ConcreteCategory.congr_hom (h c) x

/-- An arbitrary family of actual linear maps extends to one actual
diagram morphism from the vector cover. -/
def diagramCoverDesc {F G : C ⥤ ModuleCat.{u} k}
    (a : ∀ c : C, F.obj c ⟶ G.obj c) : diagramVectorCoverObj k F ⟶ G :=
  Sigma.desc (fun c => (vectorCopowerHomEquiv k (representable k c) (F.obj c) G).symm
    (ModuleCat.ofHom ((fromValueLinear k G c).comp (a c).hom)))

@[reassoc]
theorem diagramVectorCoverInclusion_desc {F G : C ⥤ ModuleCat.{u} k}
    (a : ∀ c : C, F.obj c ⟶ G.obj c) (c : C) (x : F.obj c) :
    diagramVectorCoverInclusion k F c x ≫ diagramCoverDesc k a =
      fromValue k G c (a c x) := by
  simp only [diagramVectorCoverInclusion, diagramCoverDesc, Category.assoc,
    Sigma.ι_comp_desc, vectorCopowerInclusion_desc, ModuleCat.ofHom_apply,
    LinearMap.comp_apply, fromValueLinear_apply]
  rfl

@[simp]
theorem diagramCoverEvaluation_desc {F G : C ⥤ ModuleCat.{u} k}
    (a : ∀ c : C, F.obj c ⟶ G.obj c) (c : C) :
    diagramCoverEvaluation k (diagramCoverDesc k a) c = a c := by
  ext x
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (diagramVectorCoverInclusion_desc k a c x) c)
    (ModuleCat.freeMk (𝟙 c))
  simp only [NatTrans.comp_app, ModuleCat.comp_apply] at h
  exact h.trans (evaluate_fromValue k G c (a c x))

/-- The actual linear universal property of the entire vector cover. -/
def diagramCoverHomEquiv (F G : C ⥤ ModuleCat.{u} k) :
    (diagramVectorCoverObj k F ⟶ G) ≃ (∀ c : C, F.obj c ⟶ G.obj c) where
  toFun a := diagramCoverEvaluation k a
  invFun a := diagramCoverDesc k a
  left_inv a := by
    apply diagramCoverEvaluation_hom_ext k
    intro c
    exact diagramCoverEvaluation_desc k _ c
  right_inv a := funext (diagramCoverEvaluation_desc k a)

/-- Evaluation of a complex at one actual incidence object. -/
abbrev diagramValueComplex (X : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ) (c : C) :
    CochainComplex (ModuleCat.{u} k) ℤ :=
  (((evaluation C (ModuleCat.{u} k)).obj c).mapHomologicalComplex (.up ℤ)).obj X

/-- A chain map out of the vector cover gives a genuine chain map of
coefficient complexes at every object. -/
def diagramCoverChainComponent
    {X Y : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ}
    (f : ((diagramVectorCover k).mapHomologicalComplex (.up ℤ)).obj X ⟶ Y) (c : C) :
    diagramValueComplex k X c ⟶ diagramValueComplex k Y c where
  f i := diagramCoverEvaluation k (f.f i) c
  comm' i j _ := by
    have h := congrArg (fun a => diagramCoverEvaluation k a c) (f.comm i j)
    change diagramCoverEvaluation k (f.f i ≫ Y.d i j) c =
      diagramCoverEvaluation k ((diagramVectorCover k).map (X.d i j) ≫ f.f j) c at h
    rw [diagramCoverEvaluation_postcomp, diagramCoverEvaluation_precomp] at h
    exact h

/-- Actual evaluation preserves acyclicity, by exactness of evaluation
on the abelian category of actual diagrams. -/
theorem diagramValueComplex_acyclic
    (Y : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ) (hY : Y.Acyclic) (c : C) :
    (diagramValueComplex k Y c).Acyclic := by
  intro i
  change ((Y.sc i).map ((evaluation C (ModuleCat.{u} k)).obj c)).Exact
  exact (hY i).map ((evaluation C (ModuleCat.{u} k)).obj c)

/-- The family of genuine vector-space homotopies lifts to one actual
homotopy of diagram complexes through the coproduct universal property. -/
def diagramCoverChainHomotopyZero
    {X Y : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ}
    (f : ((diagramVectorCover k).mapHomologicalComplex (.up ℤ)).obj X ⟶ Y)
    (hY : Y.Acyclic) : Homotopy f 0 := by
  let h (c : C) : Homotopy (diagramCoverChainComponent k f c) 0 :=
    CochainComplex.IsKProjective.homotopyZero (diagramCoverChainComponent k f c)
      (diagramValueComplex_acyclic k Y hY c)
  refine
    { hom := fun i j => diagramCoverDesc k (fun c => (h c).hom i j)
      zero := ?_
      comm := ?_ }
  · intro i j hij
    apply diagramCoverEvaluation_hom_ext k
    intro c
    rw [diagramCoverEvaluation_desc, diagramCoverEvaluation_zero]
    exact (h c).zero i j hij
  · intro i
    apply diagramCoverEvaluation_hom_ext k
    intro c
    change diagramCoverEvaluation k (F := X.X i) (G := Y.X i) (f.f i) c =
      diagramCoverEvaluation k (F := X.X i) (G := Y.X i)
        ((show diagramVectorCoverObj k (X.X i) ⟶ Y.X i from
          (diagramVectorCover k).map (X.d i ((ComplexShape.up ℤ).next i)) ≫
            diagramCoverDesc k (fun c => (h c).hom ((ComplexShape.up ℤ).next i) i)) +
          (show diagramVectorCoverObj k (X.X i) ⟶ Y.X i from
            (diagramCoverDesc k (fun c => (h c).hom i ((ComplexShape.up ℤ).prev i))) ≫
              Y.d ((ComplexShape.up ℤ).prev i) i) +
          (0 : diagramVectorCoverObj k (X.X i) ⟶ Y.X i)) c
    simp only [diagramCoverEvaluation_add, diagramCoverEvaluation_zero]
    rw [diagramCoverEvaluation_precomp, diagramCoverEvaluation_postcomp]
    simp only [diagramCoverEvaluation_desc]
    exact (h c).comm i

/-- The actual vector cover of every unbounded complex is K-projective.
This follows from constructed homotopies, not from an assumed supply of
unbounded projective resolutions. -/
instance diagramCoverComplex_isKProjective
    (X : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ) :
    CochainComplex.IsKProjective
      (((diagramVectorCover k).mapHomologicalComplex (.up ℤ)).obj X) where
  nonempty_homotopy_zero f hY := ⟨diagramCoverChainHomotopyZero k f hY⟩

end ToricPower.Cellular

end
