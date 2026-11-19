module

public import ToricPower.CellularInverseNakayamaPoints
public import ToricPower.SerrePairingRetract

/-!
# The point pairing is natural in every injective incidence map

Finite Hom sets identify every map between the co-representable
injectives with a finite linear combination of actual incidence maps.
The proof below checks each such incidence using the two original
naturality squares. No diagram map is discarded or replaced by support
data.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.Cellular

universe u
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  [∀ c d : C, Finite (c ⟶ d)]

def pointCodomainPairing (c : C) :
    SerrePairing.CodomainPairing k (inverseNakayama k) (pointCorepresentable k c) where
  equiv E := (pointSerreLinearEquiv k c E).trans
    (Linear.homCongr k (inverseNakayamaCorepresentableIso k c) (Iso.refl E)).dualMap
  naturality {E E'} a f g := by
    change pointSerreLinearEquiv k c E (a ≫ f)
        ((inverseNakayamaCorepresentableIso k c).inv ≫ g ≫ 𝟙 E) =
      pointSerreLinearEquiv k c E' f
        ((inverseNakayamaCorepresentableIso k c).inv ≫ (g ≫ a) ≫ 𝟙 E')
    simp only [Category.comp_id]
    rw [pointSerreLinearEquiv_naturality]
    simp only [LinearMap.comp_apply, Linear.rightComp_apply, Category.assoc]

theorem pointCodomainPairing_apply (c : C) (E : C ⥤ ModuleCat.{u} k)
    (f : E ⟶ pointCorepresentable k c)
    (g : (inverseNakayama k).obj (pointCorepresentable k c) ⟶ E) :
    (pointCodomainPairing k c).equiv E f g =
      f.app c (g.app c (𝟙 (pointCorepresentable k c))) (𝟙 c) := by
  change pointSerreLinearEquiv k c E f
    ((inverseNakayamaCorepresentableIso k c).inv ≫ g ≫ 𝟙 E) = _
  rw [Category.comp_id, pointSerreLinearEquiv_apply]
  change f.app c (g.app c
    ((inverseNakayamaPointMap k c).app c (ModuleCat.freeMk (𝟙 c)))) (𝟙 c) = _
  rw [inverseNakayamaPointMap, fromValue_app_freeMk,
    CategoryTheory.Functor.map_id, ModuleCat.id_apply]

theorem inverseNakayamaPointMap_basis (c d : C) (a : c ⟶ d) :
    (inverseNakayamaPointMap k c).app d (ModuleCat.freeMk a) =
      (pointCorepresentableDiagram k).map a.op := by
  rw [inverseNakayamaPointMap, fromValue_app_freeMk]
  change (pointCorepresentableDiagram k).map a.op ≫ 𝟙 _ = _
  rw [Category.comp_id]

theorem pointCodomainPairing_compatible (c d : C)
    (a : pointCorepresentable k c ⟶ pointCorepresentable k d) :
    SerrePairing.Compatible k (pointCodomainPairing k c)
      (pointCodomainPairing k d) a := by
  intro E f g
  let left : (pointCorepresentable k c ⟶ pointCorepresentable k d) →ₗ[k] k :=
    { toFun := fun a => (pointCodomainPairing k d).equiv E (f ≫ a) g
      map_add' := by intros; simp only [Preadditive.comp_add, map_add, LinearMap.add_apply]
      map_smul' := by intros; simp only [Linear.comp_smul, map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  let right : (pointCorepresentable k c ⟶ pointCorepresentable k d) →ₗ[k] k :=
    { toFun := fun a => (pointCodomainPairing k c).equiv E f
        ((inverseNakayama k).map a ≫ g)
      map_add' := by intros; simp only [CategoryTheory.Functor.map_add,
        Preadditive.add_comp, map_add]
      map_smul' := by intros; simp only [CategoryTheory.Functor.map_smul,
        Linear.smul_comp, map_smul, RingHom.id_apply] }
  let basisMap := (inverseNakayamaPointMap k d).app c
  have equal : left.comp basisMap.hom = right.comp basisMap.hom := by
    apply (Finsupp.basisSingleOne : Module.Basis (d ⟶ c) k ((d ⟶ c) →₀ k)).ext
    intro b
    change (pointCodomainPairing k d).equiv E
        (f ≫ (inverseNakayamaPointMap k d).app c (ModuleCat.freeMk b)) g =
      (pointCodomainPairing k c).equiv E f
        ((inverseNakayama k).map
          ((inverseNakayamaPointMap k d).app c (ModuleCat.freeMk b)) ≫ g)
    rw [inverseNakayamaPointMap_basis, pointCodomainPairing_apply,
      pointCodomainPairing_apply]
    let v := g.app d (𝟙 (pointCorepresentable k d))
    have hg := ConcreteCategory.congr_hom (g.naturality b)
      (𝟙 (pointCorepresentable k d))
    change g.app c ((pointCorepresentableDiagram k).map b.op ≫ 𝟙 _) = E.map b v at hg
    rw [Category.comp_id] at hg
    have hf := congrArg (fun h : E.obj d ⟶ (pointCorepresentable k c).obj c =>
      h v (𝟙 c)) (f.naturality b)
    change f.app c (E.map b v) (𝟙 c) = f.app d v (b ≫ 𝟙 c) at hf
    rw [Category.comp_id] at hf
    change f.app d v (𝟙 d ≫ b) =
      f.app c (g.app c (𝟙 _ ≫ (pointCorepresentableDiagram k).map b.op)) (𝟙 c)
    rw [Category.id_comp, Category.id_comp, hg]
    exact hf.symm
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso basisMap).surjective a
  have h := LinearMap.congr_fun equal x
  change left (basisMap x) = right (basisMap x) at h
  rw [hx] at h
  exact h

end ToricPower.Cellular

end
