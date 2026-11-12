module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# Functorial fibers of actual maps of complexes

These constructions retain the literal mapping cone and its shift. The
projection to the source is a natural chain map, including the sign in
Mathlib's mapping-cocone convention. Exact additive functors detect the
vanishing of these fibers through the usual distinguished triangle.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CochainComplex CochainComplex.HomComplex

namespace ToricPower.ComplexCone

universe u v w z

variable {B : Type u} [Category.{v} B]
  {A : Type w} [Category.{z} A] [Abelian A]
  {F G : B ⥤ CochainComplex A ℤ}

/-- The literal functorial mapping cone. -/
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

/-- The right inclusion is an actual natural chain map. -/
def coneInclusion (τ : F ⟶ G) : G ⟶ coneFunctor τ where
  app X := mappingCone.inr (τ.app X)
  naturality {X Y} f :=
    (mappingCone.triangleMap (τ.app X) (τ.app Y) (F.map f) (G.map f)
      (τ.naturality f).symm).comm₂.symm

/-- The functorial mapping fiber, with the actual shift by minus one. -/
def coconeFunctor (τ : F ⟶ G) : B ⥤ CochainComplex A ℤ :=
  coneFunctor τ ⋙ CategoryTheory.shiftFunctor _ (-1 : ℤ)

theorem mappingCone_map_fst_v {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : φ₁ ≫ b = a ≫ φ₂) (p q : ℤ) (hpq : p + 1 = q) :
    (mappingCone.map φ₁ φ₂ a b h).f p ≫ (mappingCone.fst φ₂).1.v p q hpq =
      (mappingCone.fst φ₁).1.v p q hpq ≫ a.f q := by
  apply mappingCone.ext_from φ₁ q p hpq
  · simp [mappingCone.map]
  · simp [mappingCone.map]

theorem mappingCocone_fst_f {K L : CochainComplex A ℤ} (φ : K ⟶ L) (p : ℤ) :
    (mappingCocone.fst φ).f p =
      (mappingCone.fst φ).1.v (p + -1) p (by omega) := by
  change -(((mappingCone.fst φ).1.leftShift (-1) 0 (by omega)).v p p (by omega)) = _
  rw [Cochain.leftShift_v (mappingCone.fst φ).1 (-1) 0 (by omega)
    p p (by omega) (p + -1) (by omega)]
  simp [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl]

/-- The mapping-fiber projection is natural on the original complexes. -/
def coconeProjection (τ : F ⟶ G) : coconeFunctor τ ⟶ F where
  app X := mappingCocone.fst (τ.app X)
  naturality {X Y} f := by
    ext p
    change ((mappingCone.map (τ.app X) (τ.app Y) (F.map f) (G.map f)
        (τ.naturality f).symm)⟦(-1 : ℤ)⟧').f p ≫
        (mappingCocone.fst (τ.app Y)).f p =
      (mappingCocone.fst (τ.app X)).f p ≫ (F.map f).f p
    rw [shiftFunctor_map_f', mappingCocone_fst_f, mappingCocone_fst_f]
    exact mappingCone_map_fst_v _ _ _ _ _ _ _ _

section ExactImage

variable {D : Type*} [Category D] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory D]
  (H : A ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  {K L : CochainComplex A ℤ} (φ : K ⟶ L)

/-- The image of a mapping fiber vanishes if the image of its original
map is a quasi-isomorphism. -/
theorem cocone_image_isZero
    [QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map φ)] :
    IsZero (DerivedCategory.Q.obj
      ((H.mapHomologicalComplex (.up ℤ)).obj (mappingCocone φ))) := by
  let T := DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle φ)
  have hT : T ∈ distTriang (DerivedCategory A) :=
    DerivedCategory.mappingCocone_triangle_distinguished φ
  have hφ : IsIso (H.mapDerivedCategory.map (DerivedCategory.Q.map φ)) := by
    apply (NatIso.isIso_map_iff H.mapDerivedCategoryFactors φ).mpr
    change IsIso (DerivedCategory.Q.map ((H.mapHomologicalComplex (.up ℤ)).map φ))
    infer_instance
  have hz := Triangle.isZero₁_of_isIso₂
    (H.mapDerivedCategory.mapTriangle.obj T)
    (H.mapDerivedCategory.map_distinguished T hT) hφ
  exact (H.mapDerivedCategoryFactors.app (mappingCocone φ)).isZero_iff.mp hz

end ExactImage

end ToricPower.ComplexCone

end
