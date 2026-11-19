module

public import ToricPower.ComplexCoconeRetraction

/-!
# Functorial finite cone filtrations

For composable chain maps the cones form the usual octahedral triangle.
Here its map on a commuting diagram is retained explicitly. The resulting
five-lemma criterion applies after an arbitrary additive functor; exactness
is required only for the pieces to which the criterion is applied.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CochainComplex CochainComplex.HomComplex

namespace ToricPower.ComplexCone

universe u v w z

variable {A : Type u} [Category.{v} A] [Abelian A]
  {D : Type w} [Category.{z} D] [Abelian D]
  [HasDerivedCategory D]

/-- Every additive functor preserves distinguished triangles from the
homotopy category, even when it is not exact on the abelian categories. -/
theorem additive_image_distinguished (H : A ⥤ D) [H.Additive]
    (T : Triangle (CochainComplex A ℤ))
    (hT : (HomotopyCategory.quotient A (.up ℤ)).mapTriangle.obj T ∈
      distTriang (HomotopyCategory A (.up ℤ))) :
    DerivedCategory.Q.mapTriangle.obj
      ((H.mapHomologicalComplex (.up ℤ)).mapTriangle.obj T) ∈
        distTriang (DerivedCategory D) := by
  let HC := H.mapHomologicalComplex (.up ℤ)
  let HH := H.mapHomotopyCategory (.up ℤ)
  let QA := HomotopyCategory.quotient A (.up ℤ)
  let QD := HomotopyCategory.quotient D (.up ℤ)
  let Qh : HomotopyCategory D (.up ℤ) ⥤ DerivedCategory D := DerivedCategory.Qh
  have h := Qh.map_distinguished _ (HH.map_distinguished _ hT)
  let e : (QA ⋙ HH) ⋙ Qh ≅ HC ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight (H.mapHomotopyCategoryFactors (.up ℤ)) Qh ≪≫
      Functor.associator HC QD Qh ≪≫
        Functor.isoWhiskerLeft HC (DerivedCategory.quotientCompQhIso D)
  letI : NatTrans.CommShift e.hom ℤ := by dsimp [e]; infer_instance
  let eT :=
    Qh.mapTriangle.mapIso ((Functor.mapTriangleCompIso QA HH).symm.app T) ≪≫
    (Functor.mapTriangleCompIso (QA ⋙ HH) Qh).symm.app T ≪≫
    (Functor.mapTriangleIso e).app T ≪≫
    (Functor.mapTriangleCompIso HC DerivedCategory.Q).app T
  exact isomorphic_distinguished _ h _ eT.symm

/-- The image of a cone of an identity is zero for every additive functor. -/
theorem additive_cone_identity_isZero (H : A ⥤ D) [H.Additive]
    (K : CochainComplex A ℤ) :
    IsZero (DerivedCategory.Q.obj
      ((H.mapHomologicalComplex (.up ℤ)).obj (mappingCone (𝟙 K)))) := by
  exact Triangle.isZero₃_of_isIso₁ _
    (additive_image_distinguished H (mappingCone.triangle (𝟙 K))
      (HomotopyCategory.mappingCone_triangleh_distinguished (𝟙 K)))
    (by change IsIso (DerivedCategory.Q.map
          ((H.mapHomologicalComplex (.up ℤ)).map (𝟙 K))); infer_instance)

/-- The triangulated five lemma for the literal map of two cones. -/
theorem additive_cone_map_quasiIso (H : A ⥤ D) [H.Additive]
    {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : φ₁ ≫ b = a ≫ φ₂)
    [QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map a)]
    [QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map b)] :
    QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
      (mappingCone.map φ₁ φ₂ a b h)) := by
  let HC := H.mapHomologicalComplex (.up ℤ)
  let Q : CochainComplex D ℤ ⥤ DerivedCategory D := DerivedCategory.Q
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact isIso₃_of_isIso₁₂
    (Q.mapTriangle.map (HC.mapTriangle.map (mappingCone.triangleMap φ₁ φ₂ a b h)))
    (additive_image_distinguished H _
      (HomotopyCategory.mappingCone_triangleh_distinguished φ₁))
    (additive_image_distinguished H _
      (HomotopyCategory.mappingCone_triangleh_distinguished φ₂))
    (by change IsIso (Q.map (HC.map a)); infer_instance)
    (by change IsIso (Q.map (HC.map b)); infer_instance)

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : CochainComplex A ℤ}
  (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (f' : Y₁ ⟶ Y₂) (g' : Y₂ ⟶ Y₃)
  (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂) (c : X₃ ⟶ Y₃)
  (hf : f ≫ b = a ≫ f') (hg : g ≫ c = b ≫ g')

/-- The literal map of cone-composition triangles. -/
def coneCompositionTriangleMap :
    mappingConeCompTriangle f g ⟶ mappingConeCompTriangle f' g' where
  hom₁ := mappingCone.map f f' a b hf
  hom₂ := mappingCone.map (f ≫ g) (f' ≫ g') a c (by rw [Category.assoc, hg,
    ← Category.assoc, hf, Category.assoc])
  hom₃ := mappingCone.map g g' b c hg
  comm₁ := by
    dsimp [mappingConeCompTriangle]
    rw [← mappingCone.map_comp, ← mappingCone.map_comp]
    simp only [Category.id_comp, Category.comp_id]
    congr 1
  comm₂ := by
    dsimp [mappingConeCompTriangle]
    rw [← mappingCone.map_comp, ← mappingCone.map_comp]
    simp only [Category.id_comp, Category.comp_id]
    congr 1
  comm₃ := (mappingConeCompTriangle_mor₃_naturality f g f' g'
    (ComposableArrows.homMk₂ a b c hf hg)).symm

/-- If the two successive cofiber maps are quasi-isomorphisms after an
additive functor, so is the cofiber map for their composite. -/
theorem additive_map_compositeCone_quasiIso (H : A ⥤ D) [H.Additive]
    [QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
      (mappingCone.map f f' a b hf))]
    [QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
      (mappingCone.map g g' b c hg))] :
    QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
      (mappingCone.map (f ≫ g) (f' ≫ g') a c
        (by rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]))) := by
  let HC := H.mapHomologicalComplex (.up ℤ)
  let Q : CochainComplex D ℤ ⥤ DerivedCategory D := DerivedCategory.Q
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact isIso₂_of_isIso₁₃
    (Q.mapTriangle.map (HC.mapTriangle.map
      (coneCompositionTriangleMap f g f' g' a b c hf hg)))
    (additive_image_distinguished H _
      (HomotopyCategory.mappingConeCompTriangleh_distinguished f g))
    (additive_image_distinguished H _
      (HomotopyCategory.mappingConeCompTriangleh_distinguished f' g'))
    (by change IsIso (Q.map (HC.map (mappingCone.map f f' a b hf))); infer_instance)
    (by change IsIso (Q.map (HC.map (mappingCone.map g g' b c hg))); infer_instance)

end ToricPower.ComplexCone

end
