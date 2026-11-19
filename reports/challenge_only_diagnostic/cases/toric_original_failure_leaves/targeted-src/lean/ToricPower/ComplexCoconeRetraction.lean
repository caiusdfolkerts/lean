module

public import ToricPower.ComplexCoconeFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-!
# The cofiber of a mapping-fiber projection

The cofiber of `mappingCocone φ → K` retracts onto the original target
of `φ : K → L`. The comparison below is a literal, natural chain map,
with an explicit contracting homotopy. Consequently every additive
functor preserves this comparison up to quasi-isomorphism. No exactness
of that additive functor is required.
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
  {K L : CochainComplex A ℤ} (φ : K ⟶ L)

/-- The second fiber projection is the specified nullhomotopy of the
composite of the first projection with the original map. -/
theorem mappingCocone_delta_snd :
    δ (-1) 0 (mappingCocone.snd φ) =
      -Cochain.ofHom (mappingCocone.fst φ ≫ φ) := by
  dsimp [mappingCocone.snd]
  rw [Cochain.δ_leftShift _ (-1) (-1) 0 (by omega) 1 (by omega)]
  simp only [mappingCone.δ_snd, Cochain.leftShift_neg]
  ext p
  simp [mappingCocone_fst_f, Cochain.leftShift_v
    (mappingCone.fst φ).1 (-1) 0 (by omega)
    p p (by omega) (p + -1) (by omega),
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl]

/-- The left inclusion in the fiber has the complementary boundary. -/
theorem mappingCocone_delta_inl :
    δ 0 1 (mappingCocone.inl φ) =
      -(Cochain.ofHom φ).comp (mappingCocone.inr φ).1 (zero_add 1) := by
  dsimp [mappingCocone.inl]
  rw [Cochain.δ_rightShift _ (-1) 0 1 (by omega) 0 (by omega)]
  simp only [mappingCone.δ_inl]
  ext p q hpq
  simp [mappingCocone.inr, Cochain.rightShift_v,
    Cochain.comp_v _ _ (zero_add 1) p p q (by omega) hpq]

/-- The natural retraction from the cofiber of the fiber projection. -/
def fiberProjectionConeRetraction :
    mappingCone (mappingCocone.fst φ) ⟶ L :=
  mappingCone.desc (mappingCocone.fst φ) (-mappingCocone.snd φ) φ (by
    rw [δ_neg, mappingCocone_delta_snd, neg_neg])

/-- Its explicit section. -/
def fiberProjectionConeSection :
    L ⟶ mappingCone (mappingCocone.fst φ) :=
  mappingCone.lift (mappingCocone.fst φ) (-mappingCocone.inr φ) 0 (by
    ext p q hpq
    simp [Cochain.comp_v _ _ (add_zero 1) p q q hpq (by omega)])

@[reassoc (attr := simp)]
theorem fiberProjectionConeSection_retraction :
    fiberProjectionConeSection φ ≫ fiberProjectionConeRetraction φ = 𝟙 L := by
  ext p
  simp [fiberProjectionConeSection, fiberProjectionConeRetraction,
    mappingCone.lift_desc_f _ _ _ _ _ _ _ p (p + 1) rfl]

/-- The discarded pair of copies of `K` has an explicit contraction. -/
def fiberProjectionConeHomotopy :
    Homotopy (fiberProjectionConeRetraction φ ≫ fiberProjectionConeSection φ) (𝟙 _) := by
  refine mappingCone.liftHomotopy (mappingCocone.fst φ) _ _
    (-((mappingCone.snd (mappingCocone.fst φ)).comp
      (mappingCocone.inl φ) (zero_add 0))) 0 ?_ ?_
  · rw [δ_neg, δ_comp _ _ (zero_add 0) 1 1 1 rfl rfl rfl,
      mappingCone.δ_snd, mappingCocone_delta_inl]
    ext p q hpq
    simp only [Cochain.ofHom_comp, Cochain.comp_neg, Cochain.neg_comp,
      neg_neg, Cochain.id_comp,
      Cochain.add_v, Cochain.neg_v]
    simp only [fiberProjectionConeSection, fiberProjectionConeRetraction] 
    simp [
      Cochain.comp_v _ _ (zero_add 1) p p q (by omega) hpq,
      Cochain.comp_v _ _ (add_zero 1) p q q hpq (by omega),
      mappingCone.ext_from_iff _ q p hpq]
    rw [← mappingCocone.id_X φ q p (by omega)]
    abel
  · ext p
    simp [fiberProjectionConeSection, Cochain.ofHom_comp,
      Cochain.comp_v _ _ (zero_add 0) p p p (by omega) (by omega)]

/-- A homotopy equivalence, with no hypotheses on the original map. -/
def fiberProjectionConeHomotopyEquiv :
    HomotopyEquiv (mappingCone (mappingCocone.fst φ)) L where
  hom := fiberProjectionConeRetraction φ
  inv := fiberProjectionConeSection φ
  homotopyHomInvId := fiberProjectionConeHomotopy φ
  homotopyInvHomId := Homotopy.ofEq (fiberProjectionConeSection_retraction φ)

end ToricPower.ComplexCone

end
