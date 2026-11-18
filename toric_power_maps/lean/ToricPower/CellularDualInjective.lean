module

public import ToricPower.CellularDiagramDual
public import ToricPower.CellularPointSerre

/-!
# Duals of actual projective incidence diagrams are injective

The proof uses the literal bilinear transposition of natural
transformations. Scalar duality carries monomorphisms to epimorphisms
over a field, without any finite-dimensionality hypothesis.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower.Cellular

universe u
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]

def reversedScalarDual (F : C ⥤ ModuleCat.{u} k) : Cᵒᵖ ⥤ ModuleCat.{u} k :=
  F.op ⋙ scalarDual k

def reversedScalarDualMap {F G : C ⥤ ModuleCat.{u} k} (f : F ⟶ G) :
    reversedScalarDual k G ⟶ reversedScalarDual k F :=
  Functor.whiskerRight (NatTrans.op f) (scalarDual k)

instance reversedScalarDualMap_epi {F G : C ⥤ ModuleCat.{u} k}
    (f : F ⟶ G) [Mono f] : Epi (reversedScalarDualMap k f) := by
  letI : PreservesFiniteColimits (scalarDual k) :=
    (scalarDual k).preservesFiniteColimits_of_preservesHomology
  rw [NatTrans.epi_iff_epi_app]
  intro c
  change Epi ((scalarDual k).map (f.app c.unop).op)
  infer_instance

/-- Transposition of the actual componentwise bilinear pairing. -/
def diagramDualTranspose (F : C ⥤ ModuleCat.{u} k)
    (P : Cᵒᵖ ⥤ ModuleCat.{u} k) :
    (F ⟶ (diagramScalarDual k C).obj (op P)) ≃ₗ[k]
      (P ⟶ reversedScalarDual k F) where
  toFun f :=
    { app c := ModuleCat.ofHom
        { toFun := fun p => ModuleCat.ofHom
            { toFun := fun x =>
                (show P.obj c ⟶ ModuleCat.of k k from f.app c.unop x) p
              map_add' := by intros; rw [map_add]; rfl
              map_smul' := by intros; rw [map_smul]; rfl }
          map_add' := by
            intro p q
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            exact map_add (show P.obj c ⟶ ModuleCat.of k k from f.app c.unop x).hom p q
          map_smul' := by
            intro a p
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            exact map_smul (show P.obj c ⟶ ModuleCat.of k k from f.app c.unop x).hom a p }
      naturality {c d} a := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro p
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        have h := congrArg (fun z : F.obj d.unop ⟶
            ((diagramScalarDual k C).obj (op P)).obj c.unop =>
          (show P.obj c ⟶ ModuleCat.of k k from z x) p)
          (f.naturality a.unop)
        exact h.symm }
  invFun g :=
    { app c := ModuleCat.ofHom
        { toFun := fun x => ModuleCat.ofHom
            { toFun := fun p =>
                (show F.obj c ⟶ ModuleCat.of k k from g.app (op c) p) x
              map_add' := by intros; rw [map_add]; rfl
              map_smul' := by intros; rw [map_smul]; rfl }
          map_add' := by
            intro x y
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro p
            exact map_add (show F.obj c ⟶ ModuleCat.of k k from g.app (op c) p).hom x y
          map_smul' := by
            intro a x
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro p
            exact map_smul (show F.obj c ⟶ ModuleCat.of k k from g.app (op c) p).hom a x }
      naturality {c d} a := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro p
        have h := congrArg (fun z : P.obj (op d) ⟶ (reversedScalarDual k F).obj (op c) =>
          (show F.obj c ⟶ ModuleCat.of k k from z p) x) (g.naturality a.op)
        exact h.symm }
  left_inv f := by
    apply NatTrans.ext
    funext c
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    rfl
  right_inv g := by
    apply NatTrans.ext
    funext c
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_add' _ _ := by ext c p x; rfl
  map_smul' _ _ := by ext c p x; rfl

theorem diagramDualTranspose_precomp {F G : C ⥤ ModuleCat.{u} k}
    (P : Cᵒᵖ ⥤ ModuleCat.{u} k) (a : F ⟶ G)
    (f : G ⟶ (diagramScalarDual k C).obj (op P)) :
    diagramDualTranspose k F P (a ≫ f) =
      diagramDualTranspose k G P f ≫ reversedScalarDualMap k a := by
  ext c p x
  rfl

theorem diagramScalarDual_injective (P : Cᵒᵖ ⥤ ModuleCat.{u} k)
    [Projective P] : Injective ((diagramScalarDual k C).obj (op P)) where
  factors {F G} g f _ := by
    obtain ⟨h, factor⟩ := Projective.factors (diagramDualTranspose k F P g)
      (reversedScalarDualMap k f)
    refine ⟨(diagramDualTranspose k G P).symm h, ?_⟩
    apply (diagramDualTranspose k F P).injective
    rw [diagramDualTranspose_precomp, LinearEquiv.apply_symm_apply]
    exact factor

end ToricPower.Cellular

end
