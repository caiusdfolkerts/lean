module

public import ToricPower.CellularSyzygyExact
public import ToricPower.CellularRealization
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Finite cone resolution on genuinely unbounded complexes

The actual projective replacement is formed by finitely many mapping
cones of the natural vector-cover kernels. The construction takes an
arbitrary unbounded complex of actual diagrams. After any additive
realization, it preserves quasi-isomorphisms, because every coefficient
functor in its finite filtration is proved exact.

The resulting localization is an actual functor on the unbounded derived
category. Identifying it with the absolute left derived coend, proving
the derived adjunction, and computing the diagonal counit remain separate
obligations; those conclusions are not built into this definition.

-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex

open scoped ZeroObject

namespace ToricPower.Cellular

universe u v w v' w'

section Cones

variable {B : Type u} [Category.{v} B]
  {A : Type w} [Category.{v'} A] [Abelian A]
  {F G L : B ⥤ CochainComplex A ℤ}

/-- The actual functorial cone of an actual natural transformation. -/
def coneFunctor (τ : F ⟶ G) : B ⥤ CochainComplex A ℤ where
  obj X := mappingCone (τ.app X)
  map {X Y} f := mappingCone.map (τ.app X) (τ.app Y)
    (F.map f) (G.map f) (τ.naturality f).symm
  map_id X := by
    change mappingCone.map (τ.app X) (τ.app X) (F.map (𝟙 X)) (G.map (𝟙 X)) _ = _
    simp only [CategoryTheory.Functor.map_id]
    exact mappingCone.map_id _
  map_comp f g := by
    simpa only [CategoryTheory.Functor.map_comp] using
      mappingCone.map_comp (τ.app _) (τ.app _) (τ.app _)
        (F.map f) (G.map f) (τ.naturality f).symm
        (F.map g) (G.map g) (τ.naturality g).symm

/-- An actual zero composite gives the canonical map from the cone.
Naturality follows from the literal morphism of the two short complexes. -/
def coneDescNatTrans (τ : F ⟶ G) (β : G ⟶ L)
    (h : ∀ X, τ.app X ≫ β.app X = 0) : coneFunctor τ ⟶ L where
  app X := mappingCone.descShortComplex (ShortComplex.mk (τ.app X) (β.app X) (h X))
  naturality {X Y} f := by
    exact mappingCone.map_descShortComplex
      (ShortComplex.mk (τ.app X) (β.app X) (h X))
      (ShortComplex.mk (τ.app Y) (β.app Y) (h Y))
      { τ₁ := F.map f
        τ₂ := G.map f
        τ₃ := L.map f
        comm₁₂ := τ.naturality f
        comm₂₃ := β.naturality f }

variable {D : Type w'} [Category.{v'} D] [Abelian D]
  (H : A ⥤ D) [H.Additive]
  {K₁ K₂ L₁ L₂ : CochainComplex A ℤ}
  (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
  (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (h : φ₁ ≫ b = a ≫ φ₂)

/-- An additive functor carries a map of cones to a quasi-isomorphism
whenever it does so on the two other vertices. This uses the actual
mapping-cone triangles and the triangulated five lemma after localization. -/
theorem additive_map_coneMap_quasiIso
    [QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map a)]
    [QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map b)] :
    QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
      (mappingCone.map φ₁ φ₂ a b h)) := by
  letI := HasDerivedCategory.standard D
  let HC := H.mapHomologicalComplex (.up ℤ)
  let QD : CochainComplex D ℤ ⥤ DerivedCategory D := DerivedCategory.Q
  have h₁ : QD.mapTriangle.obj (HC.mapTriangle.obj (mappingCone.triangle φ₁)) ∈
      distTriang (DerivedCategory D) :=
    isomorphic_distinguished _
      (DerivedCategory.mappingCone_triangle_distinguished (HC.map φ₁)) _
      (QD.mapTriangle.mapIso (mappingCone.mapTriangleIso φ₁ H))
  have h₂ : QD.mapTriangle.obj (HC.mapTriangle.obj (mappingCone.triangle φ₂)) ∈
      distTriang (DerivedCategory D) :=
    isomorphic_distinguished _
      (DerivedCategory.mappingCone_triangle_distinguished (HC.map φ₂)) _
      (QD.mapTriangle.mapIso (mappingCone.mapTriangleIso φ₂ H))
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact isIso₃_of_isIso₁₂
    (QD.mapTriangle.map (HC.mapTriangle.map (mappingCone.triangleMap φ₁ φ₂ a b h)))
    h₁ h₂
    (by change IsIso (DerivedCategory.Q.map (HC.map a)); infer_instance)
    (by change IsIso (DerivedCategory.Q.map (HC.map b)); infer_instance)

end Cones

section Resolution

variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]

/-- A complex endofunctor together with its actual comparison to the
identity. Quasi-isomorphism is a theorem about particular stages. -/
structure ComplexResolutionStage where
  functor : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ ⥤
    CochainComplex (C ⥤ ModuleCat.{u} k) ℤ
  augmentation : functor ⟶ 𝟭 _

abbrev diagramCoverComplexFunctor :=
  (diagramVectorCover k (C := C)).mapHomologicalComplex (.up ℤ)

abbrev diagramSyzygyComplexFunctor :=
  (diagramSyzygy k (C := C)).mapHomologicalComplex (.up ℤ)

/-- The actual counit on unbounded complexes. -/
def diagramCoverComplexCounit : diagramCoverComplexFunctor k (C := C) ⟶ 𝟭 _ where
  app X :=
    { f := fun i => diagramVectorCoverMap k (X.X i)
      comm' := fun i j _ => ((diagramVectorCoverCounit k).naturality (X.d i j)).symm }
  naturality {_ _} f := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact (diagramVectorCoverCounit k).naturality (f.f i)

/-- The actual kernel inclusion on unbounded complexes. -/
def diagramSyzygyComplexInclusion :
    diagramSyzygyComplexFunctor k (C := C) ⟶ diagramCoverComplexFunctor k :=
  (diagramSyzygyInclusion k).mapHomologicalComplex (.up ℤ)

@[reassoc (attr := simp)]
theorem diagramSyzygyComplexInclusion_cover
    (X : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ) :
    (diagramSyzygyComplexInclusion k).app X ≫
      (diagramCoverComplexCounit k).app X = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact kernel.condition (diagramVectorCoverMap k (X.X i))

/-- The next cone is attached using the previous stage applied to the
actual kernel complex. -/
def complexResolutionArrow (R : ComplexResolutionStage k (C := C)) :
    diagramSyzygyComplexFunctor k ⋙ R.functor ⟶ diagramCoverComplexFunctor k where
  app X := R.augmentation.app ((diagramSyzygyComplexFunctor k).obj X) ≫
    (diagramSyzygyComplexInclusion k).app X
  naturality {X Y} f := by
    dsimp only [Functor.comp_map]
    rw [← Category.assoc, R.augmentation.naturality]
    simp only [Category.assoc, Functor.id_map]
    rw [(diagramSyzygyComplexInclusion k).naturality]

/-- One actual finite cone step. -/
def complexResolutionSuccessor (R : ComplexResolutionStage k (C := C)) :
    ComplexResolutionStage k (C := C) where
  functor := coneFunctor (complexResolutionArrow k R)
  augmentation := coneDescNatTrans (complexResolutionArrow k R) (diagramCoverComplexCounit k)
    (fun X => by
      simp only [complexResolutionArrow, Category.assoc,
        diagramSyzygyComplexInclusion_cover, comp_zero])

/-- The finite construction starts at the actual zero complex. -/
def finiteConeResolution : ℕ → ComplexResolutionStage k (C := C)
  | 0 =>
    { functor := (Functor.const _).obj 0
      augmentation := { app := fun _ => 0 } }
  | m + 1 => complexResolutionSuccessor k (finiteConeResolution m)

/-- The actual kernel--cover sequence is short exact even when the
complex is unbounded in both directions. Exactness is checked in every
degree using the actual kernel sequence. -/
theorem diagramCoverComplex_shortExact
    (X : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ) :
    (ShortComplex.mk ((diagramSyzygyComplexInclusion k).app X)
      ((diagramCoverComplexCounit k).app X)
      (diagramSyzygyComplexInclusion_cover k X)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  change (ShortComplex.kernelSequence (diagramVectorCoverMap k (X.X i))).ShortExact
  exact
    { exact := ShortComplex.kernelSequence_exact _
      epi_g := by
        change Epi (diagramVectorCoverMap k (X.X i))
        infer_instance }

/-- If the actual `m`-th syzygy has vanished in every degree, the
displayed finite cone augmentation is a quasi-isomorphism. This is
proved by induction using actual short-exact-sequence cone comparisons. -/
theorem finiteConeResolution_augmentation_quasiIso_of_syzygy_zero (m : ℕ)
    (X : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ)
    (hzero : ∀ i : ℤ, IsZero ((diagramSyzygyIterate k m).obj (X.X i))) :
    QuasiIso ((finiteConeResolution k m).augmentation.app X) := by
  induction m generalizing X with
  | zero =>
    have hX : IsZero X := by
      rw [IsZero.iff_id_eq_zero]
      apply HomologicalComplex.Hom.ext
      funext i
      exact (hzero i).eq_of_src _ _
    letI : IsIso ((finiteConeResolution k 0).augmentation.app X) :=
      (isZero_zero _).isIso hX _
    infer_instance
  | succ m ih =>
    let KX := (diagramSyzygyComplexFunctor k).obj X
    let α := (finiteConeResolution k m).augmentation.app KX
    let ι := (diagramSyzygyComplexInclusion k).app X
    let ρ := (diagramCoverComplexCounit k).app X
    have hα : QuasiIso α := ih KX (fun i => by
      change IsZero ((diagramSyzygyIterate k m).obj ((diagramSyzygy k).obj (X.X i)))
      rw [diagramSyzygyIterate_commute_obj]
      exact hzero i)
    letI : QuasiIso α := hα
    let S₀ := ShortComplex.mk ι ρ (diagramSyzygyComplexInclusion_cover k X)
    let S₁ := ShortComplex.mk (α ≫ ι) ρ (by
      simp only [Category.assoc, ι, ρ, diagramSyzygyComplexInclusion_cover, comp_zero])
    let φ : S₁ ⟶ S₀ :=
      { τ₁ := α
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by simp only [S₀, S₁, Category.comp_id]
        comm₂₃ := by simp only [S₀, S₁, Category.comp_id, Category.id_comp] }
    let γ := mappingCone.map S₁.f S₀.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm
    letI : QuasiIso γ := by
      have h := additive_map_coneMap_quasiIso (𝟭 (C ⥤ ModuleCat.{u} k))
        S₁.f S₀.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm
      exact h
    letI : QuasiIso (mappingCone.descShortComplex S₀) :=
      mappingCone.quasiIso_descShortComplex (diagramCoverComplex_shortExact k X)
    have hcomp : (finiteConeResolution k (m+1)).augmentation.app X =
        γ ≫ mappingCone.descShortComplex S₀ := by
      have h := mappingCone.map_descShortComplex S₁ S₀ φ
      simpa only [finiteConeResolution, complexResolutionSuccessor,
        coneDescNatTrans, complexResolutionArrow, γ, S₁, KX, α, ι, ρ,
        φ, Category.comp_id] using h.symm
    rw [hcomp]
    infer_instance

/-- A bound on the dimensions of the entire direct category makes the
actual finite replacement a quasi-isomorphism on every unbounded complex. -/
theorem finiteConeResolution_augmentation_quasiIso
    (grade : C → ℕ)
    (grade_le : ∀ {c d : C} (_ : c ⟶ d), grade c ≤ grade d)
    (eq_of_grade_eq : ∀ {c d : C} (_ : c ⟶ d), grade c = grade d → c = d)
    [∀ c : C, Subsingleton (c ⟶ c)]
    (N : ℕ) (hbound : ∀ c : C, grade c ≤ N)
    (X : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ) :
    QuasiIso ((finiteConeResolution k (N+1)).augmentation.app X) :=
  finiteConeResolution_augmentation_quasiIso_of_syzygy_zero k (N+1) X
    (fun i => diagramSyzygyIterate_isZero k grade grade_le eq_of_grade_eq (X.X i) N hbound)

section Target

variable {A : Type w} [Category.{u} A] [Abelian A]
  (H : (C ⥤ ModuleCat.{u} k) ⥤ A) [H.Additive]

/-- The syzygy is exact, so its degreewise functor preserves actual
quasi-isomorphisms of unbounded complexes. -/
theorem diagramSyzygyComplex_map_quasiIso
    {X Y : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ} (f : X ⟶ Y) [QuasiIso f] :
    QuasiIso ((diagramSyzygyComplexFunctor k).map f) := by
  infer_instance

/-- The vector cover makes every short exact sequence split before
applying the additive target functor, so this composite is exact. -/
theorem realizedDiagramCover_map_quasiIso
    {X Y : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ} (f : X ⟶ Y) [QuasiIso f] :
    QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
      ((diagramCoverComplexFunctor k).map f)) := by
  change QuasiIso (((diagramVectorCover k ⋙ H).mapHomologicalComplex (.up ℤ)).map f)
  infer_instance

/-- Preservation of quasi-isomorphisms passes through one actual cone
attachment. Keeping this step separate prevents the kernel from repeatedly
unfolding the recursively defined resolution when checking the induction. -/
theorem complexResolutionSuccessor_map_quasiIso
    (R : ComplexResolutionStage k (C := C))
    (hR : ∀ {X Y : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ} (f : X ⟶ Y),
      QuasiIso f → QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map (R.functor.map f)))
    {X Y : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ} (f : X ⟶ Y) [QuasiIso f] :
    QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
      ((complexResolutionSuccessor k R).functor.map f)) := by
  letI : QuasiIso ((diagramSyzygyComplexFunctor k).map f) :=
    diagramSyzygyComplex_map_quasiIso k f
  letI : QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
      (R.functor.map ((diagramSyzygyComplexFunctor k).map f))) :=
    hR _ inferInstance
  letI : QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
      ((diagramCoverComplexFunctor k).map f)) := realizedDiagramCover_map_quasiIso k H f
  change QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
    (mappingCone.map _ _ (R.functor.map ((diagramSyzygyComplexFunctor k).map f))
      ((diagramCoverComplexFunctor k).map f)
      ((complexResolutionArrow k R).naturality f).symm))
  exact additive_map_coneMap_quasiIso H _ _ _ _ _

/-- Each finite stage, after the actual additive realization, preserves
quasi-isomorphisms of arbitrary unbounded complexes. Only finitely many
cone steps are used; no convergence or boundedness assumption is hidden. -/
theorem finiteConeResolution_map_quasiIso (m : ℕ)
    {X Y : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ} (f : X ⟶ Y) [QuasiIso f] :
    QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
      ((finiteConeResolution k m).functor.map f)) := by
  induction m generalizing X Y with
  | zero =>
    change QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map (𝟙 _))
    simp only [CategoryTheory.Functor.map_id]
    infer_instance
  | succ m ih =>
    apply complexResolutionSuccessor_map_quasiIso k H (finiteConeResolution k m) _ f
    intro X Y g hg
    letI := hg
    exact ih g

variable [HasDerivedCategory (C ⥤ ModuleCat.{u} k)] [HasDerivedCategory A]

/-- The actual functor obtained by localizing this finite cone stage.
Its name deliberately records the stage: the absolute left-derived
universal property and derived adjunction have not been asserted here. -/
def finiteConeRealizationStageDerived (m : ℕ) :
    DerivedCategory (C ⥤ ModuleCat.{u} k) ⥤ DerivedCategory A :=
  Localization.lift (W := HomologicalComplex.quasiIso (C ⥤ ModuleCat.{u} k) (.up ℤ))
    ((finiteConeResolution k m).functor ⋙ H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (fun X Y f hf => by
      letI : QuasiIso f := hf
      letI := finiteConeResolution_map_quasiIso k H m f
      exact (inferInstance : IsIso (DerivedCategory.Q.map
        ((H.mapHomologicalComplex (.up ℤ)).map
          ((finiteConeResolution k m).functor.map f)))))
    DerivedCategory.Q

/-- The localization comparison is the genuine universal factorization
provided by the canonical localization of actual complexes. -/
def finiteConeRealizationStageDerivedFactors (m : ℕ) :
    DerivedCategory.Q ⋙ finiteConeRealizationStageDerived k H m ≅
      (finiteConeResolution k m).functor ⋙ H.mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  Localization.fac _ _ _

end Target

end Resolution

end ToricPower.Cellular

end
