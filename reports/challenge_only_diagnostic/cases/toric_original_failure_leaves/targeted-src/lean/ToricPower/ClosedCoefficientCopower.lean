module

public import ToricPower.VectorCopowerFiniteFunctions
public import ToricPower.CellularCovariantLabels
public import ToricPower.OpenClosedScalar

/-! # Actual copowers by closed constant coefficients

This comparison keeps every morphism of the indexing category. A closed
support contributes its label module, and an absent support contributes
the zero module. Face maps are the actual label maps restricted to the
closed support, including maps from supported to unsupported objects.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

variable (k : Type) [Field k] {C : Type} [Category.{0} C]
  (Q : C ⥤ ModuleCat.{0} k) (supported : C → Prop)
  (downward : ∀ {c d : C}, (c ⟶ d) → supported d → supported c)

def closedScalarDiagram : C ⥤ ModuleCat.{0} k where
  obj c := ModuleCat.of k (PLift (supported c) → k)
  map f := ModuleCat.ofHom (MorseCoefficients.closedScalarMap k (downward f))
  map_id _ := rfl
  map_comp _ _ := rfl

def closedLabelFunctor : C ⥤ ModuleCat.{0} k where
  obj c := ModuleCat.of k (PLift (supported c) → Q.obj c)
  map {c d} f := ModuleCat.ofHom
    { toFun := fun x h => Q.map f (x ⟨downward f h.down⟩)
      map_add' x y := by ext h; exact map_add (Q.map f).hom _ _
      map_smul' a x := by ext h; exact map_smul (Q.map f).hom a _ }
  map_id c := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext h
    change Q.map (𝟙 c) (x _) = x h
    rw [Q.map_id,ModuleCat.id_apply]
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext h
    change Q.map (f ≫ g) (x _) = Q.map g (Q.map f (x _))
    rw [Q.map_comp,ModuleCat.comp_apply]

/-- The full coefficient diagram comparison is natural on the
original category, with its original arrows. -/
def closedCoefficientCopowerIso :
    covariantCopowerDiagram k Q (closedScalarDiagram k supported downward) ≅
      closedLabelFunctor k Q supported downward :=
  NatIso.ofComponents
    (fun c => vectorCopowerFiniteFunctionsIso k (Q.obj c) (PLift (supported c)))
    (by
      intro c d f
      apply vectorCopower_hom_ext k (Q.obj c)
        ((closedScalarDiagram k supported downward).obj c)
      intro x
      rw [← Category.assoc,covariantCopowerDiagram_map_inclusion]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      funext h
      change (vectorCopowerFiniteFunctionsIso k (Q.obj d) (PLift (supported d))).hom
          (vectorCopowerInclusion k (Q.obj d) (ModuleCat.of k (PLift (supported d) → k))
            ((closedScalarDiagram k supported downward).map f x) (Q.map f v)) h =
        Q.map f
          ((vectorCopowerFiniteFunctionsIso k (Q.obj c) (PLift (supported c))).hom
            (vectorCopowerInclusion k (Q.obj c)
              (ModuleCat.of k (PLift (supported c) → k)) x v)
              ⟨downward f h.down⟩)
      rw [vectorCopowerFiniteFunctionsIso_inclusion,
        vectorCopowerFiniteFunctionsIso_inclusion]
      exact (map_smul (Q.map f).hom (x ⟨downward f h.down⟩) v).symm)

end ToricPower.Cellular

end
