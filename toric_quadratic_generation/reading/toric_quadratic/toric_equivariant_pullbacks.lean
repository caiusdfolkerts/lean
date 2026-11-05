module

public import PaperVerification.ToricIntrinsicAction
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

@[expose] public section

/-!
# Actual equivariant fibre products

The action on a fibre product is constructed by its categorical universal
property.  Both projections are genuine equivariant morphisms.  Forgetting
the base scheme preserves this pullback, so the construction supplies the
actual invariant affine restrictions used in the orbit classification.
-/

noncomputable section

universe v u

namespace PaperVerification.ToricSchemes

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj

section Categorical

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (G : C) [MonObj G] {X Y Z : C}
    [ModObj G X] [ModObj G Y] [ModObj G Z]
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsModHom G f] [IsModHom G g]
    [HasPullback f g]

def equivariantPullbackActionMap : G ⊗ pullback f g ⟶ pullback f g :=
  pullback.lift
    (G ◁ pullback.fst f g ≫ γ[G,X])
    (G ◁ pullback.snd f g ≫ γ[G,Y]) (by
      have hf := IsModHom.smul_hom (A := G) (f := f)
      have hg := IsModHom.smul_hom (A := G) (f := g)
      change γ[G,X] ≫ f = G ◁ f ≫ γ[G,Z] at hf
      change γ[G,Y] ≫ g = G ◁ g ≫ γ[G,Z] at hg
      rw [Category.assoc, hf, ← whiskerLeft_comp_assoc,
        pullback.condition, whiskerLeft_comp, Category.assoc, ← hg, Category.assoc])

@[reassoc (attr := simp)] theorem equivariantPullbackActionMap_fst :
    equivariantPullbackActionMap G f g ≫ pullback.fst f g =
      G ◁ pullback.fst f g ≫ γ[G,X] :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem equivariantPullbackActionMap_snd :
    equivariantPullbackActionMap G f g ≫ pullback.snd f g =
      G ◁ pullback.snd f g ≫ γ[G,Y] :=
  pullback.lift_snd _ _ _

/-- Actions on schemes, rather than only actions on geometric points,
are preserved by an equivariant fibre product. -/
def equivariantPullbackModObj : ModObj G (pullback f g) where
  smul := equivariantPullbackActionMap G f g
  one_smul := by
    change (η[G] ▷ pullback f g) ≫ equivariantPullbackActionMap G f g =
      (λ_ (pullback f g)).hom
    apply pullback.hom_ext
    · simp only [Category.assoc, equivariantPullbackActionMap_fst]
      rw [← whisker_exchange_assoc, ModObj.one_smul_self,
        leftUnitor_naturality]
    · simp only [Category.assoc, equivariantPullbackActionMap_snd]
      rw [← whisker_exchange_assoc, ModObj.one_smul_self,
        leftUnitor_naturality]
  mul_smul := by
    change (μ[G] ▷ pullback f g) ≫ equivariantPullbackActionMap G f g =
      (α_ G G (pullback f g)).hom ≫
        (G ◁ equivariantPullbackActionMap G f g) ≫ equivariantPullbackActionMap G f g
    apply pullback.hom_ext
    · simp only [Category.assoc, equivariantPullbackActionMap_fst]
      rw [← whiskerLeft_comp_assoc, equivariantPullbackActionMap_fst,
        whiskerLeft_comp, ← whisker_exchange_assoc,
        ModObj.mul_smul_self, associator_naturality_right_assoc]
      simp only [Category.assoc]
    · simp only [Category.assoc, equivariantPullbackActionMap_snd]
      rw [← whiskerLeft_comp_assoc, equivariantPullbackActionMap_snd,
        whiskerLeft_comp, ← whisker_exchange_assoc,
        ModObj.mul_smul_self, associator_naturality_right_assoc]
      simp only [Category.assoc]

theorem equivariantPullback_fst_isModHom :
    letI := equivariantPullbackModObj G f g
    IsModHom G (pullback.fst f g) := by
  letI := equivariantPullbackModObj G f g
  exact ⟨equivariantPullbackActionMap_fst G f g⟩

theorem equivariantPullback_snd_isModHom :
    letI := equivariantPullbackModObj G f g
    IsModHom G (pullback.snd f g) := by
  letI := equivariantPullbackModObj G f g
  exact ⟨equivariantPullbackActionMap_snd G f g⟩

end Categorical

open AlgebraicGeometry

variable {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Z) (g : Y ⟶ Z)

/-- The underlying square is the actual scheme-theoretic fibre product.
Connected-limit preservation is a theorem of the ordinary over category. -/
theorem overPullback_isPullback :
    IsPullback (pullback.fst f g).left (pullback.snd f g).left f.left g.left :=
  (Over.forget S).map_isPullback (IsPullback.of_hasPullback f g)

theorem overPullback_fst_isClosedImmersion [IsClosedImmersion g.left] :
    IsClosedImmersion (pullback.fst f g).left :=
  MorphismProperty.of_isPullback (overPullback_isPullback f g).flip inferInstance

theorem overPullback_snd_isOpenImmersion [IsOpenImmersion f.left] :
    IsOpenImmersion (pullback.snd f g).left :=
  MorphismProperty.of_isPullback (overPullback_isPullback f g) inferInstance

/-- An actual point in the inverse image of an open chart produces a
point of the equivariant pullback, including its residue-field data. -/
theorem overPullback_nonempty [IsOpenImmersion f.left]
    (y : Y.left) (hy : g.left y ∈ f.left.opensRange) :
    Nonempty (pullback f g).left := by
  have hy' : y ∈ Set.range (pullback.snd f.left g.left) := by
    rw [IsOpenImmersion.range_pullbackSnd]
    exact hy
  obtain ⟨p, hp⟩ := hy'
  exact ⟨(overPullback_isPullback f g).isoPullback.inv p⟩

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.equivariantPullbackModObj
#print axioms PaperVerification.ToricSchemes.overPullback_isPullback
