module

public import ToricPower.ComplexCoconeRetraction

/-!
# Naturality of the fiber--cofiber contraction

The contraction is compatible with every commuting square of chain maps.
This supplies a natural comparison, rather than an unrelated isomorphism
for each object, when finite coresolutions are compared on morphisms.
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

/-- Naturality of the second projection from the original cone. -/
theorem mappingCone_map_snd_v {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : φ₁ ≫ b = a ≫ φ₂) (p : ℤ) :
    (mappingCone.map φ₁ φ₂ a b h).f p ≫ (mappingCone.snd φ₂).v p p (by omega) =
      (mappingCone.snd φ₁).v p p (by omega) ≫ b.f p := by
  apply mappingCone.ext_from φ₁ (p + 1) p rfl
  · simp [mappingCone.map]
  · simp [mappingCone.map]

/-- Naturality of the degree-minus-one projection from the fiber. -/
theorem mappingCocone_map_snd_v {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : φ₁ ≫ b = a ≫ φ₂) (p q : ℤ) (hpq : p + -1 = q) :
    ((mappingCone.map φ₁ φ₂ a b h)⟦(-1 : ℤ)⟧').f p ≫
        (mappingCocone.snd φ₂).v p q hpq =
      (mappingCocone.snd φ₁).v p q hpq ≫ b.f q := by
  obtain rfl : q = p + -1 := by omega
  simpa [mappingCocone.snd, Cochain.leftShift_v _ (-1) (-1) (zero_add _) p
    (p + -1) rfl (p + -1) (by omega), CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, shiftFunctor_map_f'] using
      mappingCone_map_snd_v φ₁ φ₂ a b h (p + -1)

/-- The explicit retraction respects the actual map of fiber projections. -/
theorem fiberProjectionConeRetraction_naturality
    {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : φ₁ ≫ b = a ≫ φ₂)
    (hπ : mappingCocone.fst φ₁ ≫ a =
      (mappingCone.map φ₁ φ₂ a b h)⟦(-1 : ℤ)⟧' ≫ mappingCocone.fst φ₂) :
    mappingCone.map (mappingCocone.fst φ₁) (mappingCocone.fst φ₂)
        ((mappingCone.map φ₁ φ₂ a b h)⟦(-1 : ℤ)⟧') a hπ ≫
        fiberProjectionConeRetraction φ₂ =
      fiberProjectionConeRetraction φ₁ ≫ b := by
  ext p
  apply mappingCone.ext_from (mappingCocone.fst φ₁) (p + 1) p rfl
  · simp only [HomologicalComplex.comp_f, Category.assoc, mappingCone.map,
      mappingCone.inl_v_desc_f_assoc, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      fiberProjectionConeRetraction, mappingCone.inl_v_desc_f, Cochain.neg_v,
      Preadditive.comp_neg, Preadditive.neg_comp]
    exact congrArg Neg.neg (mappingCocone_map_snd_v φ₁ φ₂ a b h (p + 1) p (by omega))
  · simp only [HomologicalComplex.comp_f, Category.assoc, mappingCone.map,
      mappingCone.inr_f_desc_f_assoc, fiberProjectionConeRetraction,
      mappingCone.inr_f_desc_f]
    exact (congrArg (fun f => f.f p) h).symm

variable {B : Type w} [Category.{z} B]
  {F G : B ⥤ CochainComplex A ℤ}

/-- The retractions form an actual natural transformation. -/
def fiberProjectionConeRetractionNatTrans (τ : F ⟶ G) :
    coneFunctor (coconeProjection τ) ⟶ G where
  app X := fiberProjectionConeRetraction (τ.app X)
  naturality {X Y} f :=
    fiberProjectionConeRetraction_naturality (τ.app X) (τ.app Y)
      (F.map f) (G.map f) (τ.naturality f).symm ((coconeProjection τ).naturality f).symm

variable {D : Type*} [Category D] [Abelian D]
  [HasDerivedCategory D] (H : A ⥤ D) [H.Additive]

/-- Every additive functor carries the retraction to a quasi-isomorphism,
because the displayed inverse is already an inverse up to chain homotopy. -/
theorem additive_fiberProjectionConeRetraction_quasiIso
    {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
      (fiberProjectionConeRetraction φ)) := by
  have h := H.homotopyEquivalences_mapHomologicalComplex_map
    (fiberProjectionConeRetraction φ)
    (show HomologicalComplex.homotopyEquivalences A (.up ℤ) (fiberProjectionConeRetraction φ) from
      ⟨fiberProjectionConeHomotopyEquiv φ, rfl⟩)
  exact homotopyEquivalences_le_quasiIso D (.up ℤ) _ h

/-- Quasi-isomorphisms on the original target induce quasi-isomorphisms
on the cofiber of the fiber projection after any additive functor. -/
theorem additive_fiberProjectionCone_map_quasiIso (τ : F ⟶ G)
    {X Y : B} (f : X ⟶ Y)
    [QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map (G.map f))] :
    QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
      ((coneFunctor (coconeProjection τ)).map f)) := by
  let HC := H.mapHomologicalComplex (.up ℤ)
  let Q : CochainComplex D ℤ ⥤ DerivedCategory D := DerivedCategory.Q
  let ε := Functor.whiskerRight (fiberProjectionConeRetractionNatTrans τ) (HC ⋙ Q)
  letI : ∀ X, IsIso (ε.app X) := fun X => by
    letI := additive_fiberProjectionConeRetraction_quasiIso H (τ.app X)
    change IsIso (Q.map (HC.map (fiberProjectionConeRetraction (τ.app X))))
    infer_instance
  letI : IsIso ε := NatIso.isIso_of_isIso_app ε
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  apply (NatIso.isIso_map_iff (asIso ε) f).mpr
  change IsIso (Q.map ((H.mapHomologicalComplex (.up ℤ)).map (G.map f)))
  infer_instance

end ToricPower.ComplexCone

end
