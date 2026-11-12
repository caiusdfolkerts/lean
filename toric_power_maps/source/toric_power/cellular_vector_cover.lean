module

public import ToricPower.LinearVectorCopower
public import ToricPower.CellularFoundations
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# The genuine vector cover of a cellular diagram

Unlike the redundant all-vectors projective cover, this cover uses an
actual vector-space copower at each cell. Its value at a minimal
support stratum therefore has no artificial linear relations. It is
functorial in the entire cellular diagram, with an actual natural
epimorphism onto that diagram.

This is the degree-zero stage of the finite direct-category resolution.
The support drop of its successive kernels and the finite total derived
realization are separate proof obligations.

-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower.Cellular

universe u

variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]

/-- The actual representable Hom equivalence is linear, including all
distinct incidences in each free module. -/
def representableHomLinearEquiv (F : C ⥤ ModuleCat.{u} k) (c : C) :
    (representable k c ⟶ F) ≃ₗ[k] F.obj c where
  toEquiv := representableHomEquiv k F c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The vector-valued Yoneda inverse as an actual linear map. -/
def fromValueLinear (F : C ⥤ ModuleCat.{u} k) (c : C) :
    F.obj c →ₗ[k] (representable k c ⟶ F) :=
  (representableHomLinearEquiv k F c).symm.toLinearMap

@[simp]
theorem fromValueLinear_apply (F : C ⥤ ModuleCat.{u} k) (c : C) (x : F.obj c) :
    fromValueLinear k F c x = fromValue k F c x := rfl

@[reassoc]
theorem fromValue_comp {F G : C ⥤ ModuleCat.{u} k}
    (η : F ⟶ G) (c : C) (x : F.obj c) :
    fromValue k F c x ≫ η = fromValue k G c (η.app c x) := by
  apply (representableHomEquiv k G c).injective
  simp only [representableHomEquiv, Equiv.coe_fn_mk,
    evaluate_comp, evaluate_fromValue]

/-- The genuine vector cover, retaining all independent vector
coefficients and all representable incidence maps. -/
def diagramVectorCoverObj (F : C ⥤ ModuleCat.{u} k) : C ⥤ ModuleCat.{u} k :=
  ∐ (fun c : C => vectorCopower k (representable k c) (F.obj c))

instance diagramVectorCoverObj_projective (F : C ⥤ ModuleCat.{u} k) :
    Projective (diagramVectorCoverObj k F) := by
  unfold diagramVectorCoverObj
  letI (c : C) : Projective (vectorCopower k (representable k c) (F.obj c)) := by
    unfold vectorCopower
    infer_instance
  infer_instance

/-- A vector at a cell determines its actual representable inclusion
into the cover. -/
def diagramVectorCoverInclusion (F : C ⥤ ModuleCat.{u} k) (c : C)
    (x : F.obj c) : representable k c ⟶ diagramVectorCoverObj k F :=
  vectorCopowerInclusion k (representable k c) (F.obj c) x ≫
    Sigma.ι (fun c : C => vectorCopower k (representable k c) (F.obj c)) c

/-- The actual epimorphism from the vector cover. -/
def diagramVectorCoverMap (F : C ⥤ ModuleCat.{u} k) :
    diagramVectorCoverObj k F ⟶ F :=
  Sigma.desc (fun c =>
    (vectorCopowerHomEquiv k (representable k c) (F.obj c) F).symm
      (ModuleCat.ofHom (fromValueLinear k F c)))

@[reassoc]
theorem diagramVectorCoverInclusion_map (F : C ⥤ ModuleCat.{u} k)
    (c : C) (x : F.obj c) :
    diagramVectorCoverInclusion k F c x ≫ diagramVectorCoverMap k F =
      fromValue k F c x := by
  simp only [diagramVectorCoverInclusion, diagramVectorCoverMap, Category.assoc,
    Sigma.ι_comp_desc, vectorCopowerInclusion_desc, ModuleCat.ofHom_apply,
    fromValueLinear_apply]
  rfl

instance diagramVectorCoverMap_epi (F : C ⥤ ModuleCat.{u} k) :
    Epi (diagramVectorCoverMap k F) := by
  rw [NatTrans.epi_iff_epi_app]
  intro c
  rw [ModuleCat.epi_iff_surjective]
  intro x
  refine ⟨(diagramVectorCoverInclusion k F c x).app c (ModuleCat.freeMk (𝟙 c)), ?_⟩
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (diagramVectorCoverInclusion_map k F c x) c)
    (ModuleCat.freeMk (𝟙 c))
  simp only [NatTrans.comp_app, ModuleCat.comp_apply] at h
  exact h.trans (evaluate_fromValue k F c x)

/-- The cover is an actual functor in the entire coherent module
diagram; changes of basis are handled by the copower universal map. -/
def diagramVectorCover : (C ⥤ ModuleCat.{u} k) ⥤ C ⥤ ModuleCat.{u} k where
  obj := diagramVectorCoverObj k
  map η := CategoryTheory.Limits.Sigma.map (fun c => (vectorCopowerFunctor k (representable k c)).map (η.app c))
  map_id F := by
    simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]
    exact Sigma.map_id
  map_comp η θ := by
    simp only [NatTrans.comp_app, CategoryTheory.Functor.map_comp, Sigma.map_comp_map]

instance diagramVectorCover_additive : (diagramVectorCover k (C := C)).Additive where
  map_add {F G η θ} := by
    apply Sigma.hom_ext
    intro c
    simp only [diagramVectorCover, Sigma.ι_map, NatTrans.app_add, Functor.map_add,
      Preadditive.comp_add, Preadditive.add_comp]

/-- A short exact sequence becomes split after applying the vector
cover: each coefficient sequence splits over the field, and the actual
coproduct of those splittings is again a splitting. This holds for
arbitrary coefficient dimensions and even for an infinite object set. -/
def diagramVectorCoverSplitting
    (S : ShortComplex (C ⥤ ModuleCat.{u} k)) (hS : S.ShortExact) :
    (S.map (diagramVectorCover k)).Splitting := by
  let spl (c : C) : ((S.map ((evaluation C (ModuleCat.{u} k)).obj c)).map
      (vectorCopowerFunctor k (representable k c))).Splitting := by
    letI : Projective (S.X₃.obj c) :=
      ModuleCat.projective_of_free (Module.Basis.ofVectorSpace k (S.X₃.obj c))
    exact (hS.map_of_exact ((evaluation C (ModuleCat.{u} k)).obj c)).splittingOfProjective.map
      (vectorCopowerFunctor k (representable k c))
  refine
    { r := CategoryTheory.Limits.Sigma.map (fun c => (spl c).r)
      s := CategoryTheory.Limits.Sigma.map (fun c => (spl c).s)
      f_r := ?_
      s_g := ?_
      id := ?_ }
  · apply Sigma.hom_ext
    intro c
    change Sigma.ι _ c ≫ CategoryTheory.Limits.Sigma.map _ ≫ CategoryTheory.Limits.Sigma.map _ = Sigma.ι _ c ≫ 𝟙 _
    simp only [Category.assoc, Sigma.ι_map_assoc, Sigma.ι_map, Category.comp_id]
    have h := congrArg (fun f => f ≫
      Sigma.ι (fun c => vectorCopower k (representable k c) (S.X₁.obj c)) c) (spl c).f_r
    simp only [Category.assoc, Category.id_comp] at h
    exact h
  · apply Sigma.hom_ext
    intro c
    change Sigma.ι _ c ≫ CategoryTheory.Limits.Sigma.map _ ≫ CategoryTheory.Limits.Sigma.map _ = Sigma.ι _ c ≫ 𝟙 _
    simp only [Category.assoc, Sigma.ι_map_assoc, Sigma.ι_map, Category.comp_id]
    have h := congrArg (fun f => f ≫
      Sigma.ι (fun c => vectorCopower k (representable k c) (S.X₃.obj c)) c) (spl c).s_g
    simp only [Category.assoc, Category.id_comp] at h
    exact h
  · apply Sigma.hom_ext
    intro c
    simp only [Preadditive.comp_add, Category.assoc, diagramVectorCover,
      ShortComplex.map_f, ShortComplex.map_g, Sigma.ι_map_assoc, Sigma.ι_map,
      Category.comp_id]
    have h := congrArg (fun f => f ≫
      Sigma.ι (fun c => vectorCopower k (representable k c) (S.X₂.obj c)) c) (spl c).id
    simp only [Preadditive.add_comp, Category.assoc, Category.id_comp] at h
    exact h

/-- The actual vector-cover functor is exact, as follows from the
constructed splittings rather than an imposed acyclicity condition. -/
theorem diagramVectorCover_exact :
    PreservesFiniteLimits (diagramVectorCover k (C := C)) ∧
      PreservesFiniteColimits (diagramVectorCover k (C := C)) :=
  ((Functor.exact_tfae (diagramVectorCover k (C := C))).out 1 4).mp
    (fun S hS => (diagramVectorCoverSplitting k S hS).shortExact)

instance diagramVectorCover_preservesFiniteLimits :
    PreservesFiniteLimits (diagramVectorCover k (C := C)) :=
  (diagramVectorCover_exact k).1

instance diagramVectorCover_preservesFiniteColimits :
    PreservesFiniteColimits (diagramVectorCover k (C := C)) :=
  (diagramVectorCover_exact k).2

@[reassoc]
theorem diagramVectorCoverInclusion_natural {F G : C ⥤ ModuleCat.{u} k}
    (η : F ⟶ G) (c : C) (x : F.obj c) :
    diagramVectorCoverInclusion k F c x ≫ (diagramVectorCover k).map η =
      diagramVectorCoverInclusion k G c (η.app c x) := by
  simp only [diagramVectorCoverInclusion, diagramVectorCover, Category.assoc,
    Sigma.ι_map, vectorCopowerInclusion_map_assoc]

/-- The actual cover epimorphisms are natural, not merely individually
chosen projective presentations. -/
def diagramVectorCoverCounit : diagramVectorCover k ⟶ 𝟭 (C ⥤ ModuleCat.{u} k) where
  app := diagramVectorCoverMap k
  naturality {F G} η := by
    apply Sigma.hom_ext
    intro c
    apply vectorCopower_hom_ext k (representable k c) (F.obj c)
    intro x
    change diagramVectorCoverInclusion k F c x ≫
        (diagramVectorCover k).map η ≫ diagramVectorCoverMap k G =
      diagramVectorCoverInclusion k F c x ≫ diagramVectorCoverMap k F ≫ η
    rw [diagramVectorCoverInclusion_natural_assoc,
      diagramVectorCoverInclusion_map, diagramVectorCoverInclusion_map_assoc,
      fromValue_comp]

/-- This canonical presentation has no redundant free generators at a
minimal cell, unlike the all-vectors fallback cover. -/
def diagramVectorProjectivePresentation (F : C ⥤ ModuleCat.{u} k) :
    ProjectivePresentation F where
  p := diagramVectorCoverObj k F
  f := diagramVectorCoverMap k F

end ToricPower.Cellular

end
