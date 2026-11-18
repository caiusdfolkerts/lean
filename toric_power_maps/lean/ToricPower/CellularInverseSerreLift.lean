module

public import ToricPower.CellularHomotopySerre
public import ToricPower.InverseSerreAdjunction

/-!
# Signed inverse Serre duality for a naturally identified finite lift

The comparison to the ambient diagram object is an actual natural
isomorphism. Transporting along it keeps the chosen model's membership
proof and the large geometric functor outside definitional conversion.
Both source and target maps are retained explicitly.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace ToricPower.Cellular

universe u w v v'
variable (k : Type u) [Field k] {J : Type u} [Category.{u} J]
  [Finite J] [∀ c d : J, Finite (c ⟶ d)]
  [HasDerivedCategory.{w} (J ⥤ ModuleCat.{u} k)]
  {C : Type v} [Category.{v'} C]
  (F : C ⥤ FiniteDerivedDiagrams k (C := J))
  (K : C ⥤ DerivedCategory (J ⥤ ModuleCat.{u} k))
  (comparison : F ⋙ finiteDerivedInclusion k ≅ K)

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

def liftedHomotopyInverseSerreEquiv (G : C)
    (E : DerivedCategory (J ⥤ ModuleCat.{u} k)) :
    (E ⟶ K.obj G) ≃ₗ[k]
      Module.Dual k ((F ⋙ finiteInverseNakayama k).obj G ⟶ E) :=
  SerrePairing.transport k (homotopyInverseSerreEquiv k (F.obj G) E)
    (Iso.refl E) (comparison.app G) (Iso.refl _)

theorem liftedHomotopyInverseSerreEquiv_source_naturality (G : C)
    {E E' : DerivedCategory (J ⥤ ModuleCat.{u} k)} (a : E ⟶ E')
    (f : E' ⟶ K.obj G) (g : (F ⋙ finiteInverseNakayama k).obj G ⟶ E) :
    liftedHomotopyInverseSerreEquiv k F K comparison G E (a ≫ f) g =
      liftedHomotopyInverseSerreEquiv k F K comparison G E' f (g ≫ a) := by
  apply SerrePairing.transport_source_naturality
  exact fun a f g => homotopyInverseSerreEquiv_source_naturality k (F.obj G) a f g

theorem liftedHomotopyInverseSerreEquiv_target_naturality {G H : C} (a : G ⟶ H)
    (E : DerivedCategory (J ⥤ ModuleCat.{u} k)) (f : E ⟶ K.obj G)
    (g : (F ⋙ finiteInverseNakayama k).obj H ⟶ E) :
    liftedHomotopyInverseSerreEquiv k F K comparison H E (f ≫ K.map a) g =
      liftedHomotopyInverseSerreEquiv k F K comparison G E f
        ((F ⋙ finiteInverseNakayama k).map a ≫ g) := by
  apply SerrePairing.transport_target_naturality k _ _ _ _ _ _ _
    (K.map a) ((F ⋙ finiteInverseNakayama k).map a)
    ((finiteInverseNakayama k).map (F.map a))
    (by
      change 𝟙 _ ≫ (finiteInverseNakayama k).map (F.map a) =
        (finiteInverseNakayama k).map (F.map a) ≫ 𝟙 _
      exact (Category.id_comp _).trans (Category.comp_id _).symm)
  intro f' g'
  have same : ((comparison.app G).hom ≫ K.map a) ≫ (comparison.app H).inv =
      (F.map a).hom := by
    have natural : (F.map a).hom ≫ (comparison.app H).hom =
        (comparison.app G).hom ≫ K.map a := comparison.hom.naturality a
    rw [← natural, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simpa only [same] using homotopyInverseSerreEquiv_target_naturality k (F.map a) E f' g'

end ToricPower.Cellular
end
