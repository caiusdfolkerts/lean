module

public import ToricPower.InverseSerreAmbientFullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Transporting inverse Serre duality through an actual adjunction

A fully faithful right adjoint embeds the entire unbounded geometric
category into the diagram category. The ambient inverse-Serre pairing
then represents the geometric Hom dual by the actual left-adjoint image.
Both naturalities retain the original functor maps.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower.SerrePairing

universe r u v u' v' u'' v''
variable (k : Type r) [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear k D]
variable {E : Type u''} [Category.{v''} E] [Preadditive E] [Linear k E]
variable {A : E ⥤ D} {B : D ⥤ E} [B.Additive] [B.Linear k]

/-- The genuine adjunction bijection with its inherited scalar action. -/
def adjunctionLinearEquiv (adj : A ⊣ B) (X : E) (Y : D) :
    (A.obj X ⟶ Y) ≃ₗ[k] (X ⟶ B.obj Y) :=
  { adj.homEquiv X Y with
    map_add' f g := by
      change adj.unit.app X ≫ B.map (f + g) =
        adj.unit.app X ≫ B.map f + adj.unit.app X ≫ B.map g
      rw [B.map_add, Preadditive.comp_add]
    map_smul' r f := by
      change adj.unit.app X ≫ B.map (r • f) = r • (adj.unit.app X ≫ B.map f)
      rw [B.map_smul, Linear.comp_smul] }

variable [B.Full] [B.Faithful]
variable (adj : A ⊣ B) (i : C ⥤ D) (N : C ⥤ E)
variable (pairing : ∀ (G : C) (Y : E),
  (Y ⟶ B.obj (i.obj G)) ≃ₗ[k] Module.Dual k (N.obj G ⟶ Y))

/-- The representing functor is literally `N ⋙ A`. In particular, the
second argument still ranges over every object of the ambient category. -/
def adjunctionTransferredPairing (G : C) (Y : D) :
    (Y ⟶ i.obj G) ≃ₗ[k] Module.Dual k ((N ⋙ A).obj G ⟶ Y) :=
  (LinearEquiv.ofBijective (B.mapLinearMap k) ⟨B.map_injective, B.map_surjective⟩).trans
    ((pairing G (B.obj Y)).trans (adjunctionLinearEquiv k adj (N.obj G) Y).dualMap)

theorem adjunctionTransferredPairing_apply (G : C) (Y : D)
    (f : Y ⟶ i.obj G) (g : (N ⋙ A).obj G ⟶ Y) :
    adjunctionTransferredPairing k adj i N pairing G Y f g =
      pairing G (B.obj Y) (B.map f) (adj.homEquiv (N.obj G) Y g) := rfl

theorem adjunctionTransferredPairing_source_naturality
    (natural : ∀ (G : C) {Y Z : E} (a : Y ⟶ Z)
      (f : Z ⟶ B.obj (i.obj G)) (g : N.obj G ⟶ Y),
      pairing G Y (a ≫ f) g = pairing G Z f (g ≫ a))
    (G : C) {Y Z : D} (a : Y ⟶ Z) (f : Z ⟶ i.obj G)
    (g : (N ⋙ A).obj G ⟶ Y) :
    adjunctionTransferredPairing k adj i N pairing G Y (a ≫ f) g =
      adjunctionTransferredPairing k adj i N pairing G Z f (g ≫ a) := by
  simp only [adjunctionTransferredPairing_apply, CategoryTheory.Functor.map_comp,
    adj.homEquiv_naturality_right]
  exact natural G (B.map a) (B.map f) (adj.homEquiv (N.obj G) Y g)

theorem adjunctionTransferredPairing_target_naturality
    (natural : ∀ {G H : C} (a : G ⟶ H) (Y : E)
      (f : Y ⟶ B.obj (i.obj G)) (g : N.obj H ⟶ Y),
      pairing H Y (f ≫ B.map (i.map a)) g =
        pairing G Y f (N.map a ≫ g))
    {G H : C} (a : G ⟶ H) (Y : D) (f : Y ⟶ i.obj G)
    (g : (N ⋙ A).obj H ⟶ Y) :
    adjunctionTransferredPairing k adj i N pairing H Y (f ≫ i.map a) g =
      adjunctionTransferredPairing k adj i N pairing G Y f ((N ⋙ A).map a ≫ g) := by
  simp only [adjunctionTransferredPairing_apply, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.comp_map, adj.homEquiv_naturality_left]
  exact natural a (B.obj Y) (B.map f) (adj.homEquiv (N.obj H) Y g)

end ToricPower.SerrePairing

end
