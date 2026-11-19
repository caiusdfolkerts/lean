module

public import ToricPower.VectorCopowerHomLinear
public import ToricPower.ClosedContravariantLabels
public import ToricPower.ClosedCoefficientCopower

/-! # Hom from the actual closed scalar copowers

The finite scalar basis is the literal proof type of closed support.
Dualizing its genuine copower gives a finite biproduct of ordinary Hom
modules. Every face map is retained, including absent-support maps and
translated incidences; the comparison is also natural in the target.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.Cellular

universe v

variable (k : Type) [Field k]
  {C : Type} [Category.{0} C]
  {B : Type v} [Category.{0} B] [Preadditive B] [Linear k B]
  [HasCoproducts.{0} B] [HasFiniteBiproducts B]
  (Q : C ⥤ B) (supported : C → Prop)
  (downward : ∀ {c d : C}, (c ⟶ d) → supported d → supported c)

local instance closedHomProofFinite (c : C) : Fintype (PLift (supported c)) :=
  Fintype.ofFinite _

def closedCopowerHomTermIso (M : B) (c : C) :
    ((linearYoneda k B).obj M).obj
      (op ((covariantCopowerDiagram k Q (closedScalarDiagram k supported downward)).obj c)) ≅
      ⨁ fun _ : PLift (supported c) => ((linearYoneda k B).obj M).obj (op (Q.obj c)) :=
  (vectorCopowerFiniteFunctionsHomEquiv k (Q.obj c) M
    (PLift (supported c))).toModuleIso ≪≫
      (ModuleCat.biproductIsoPi (fun _ : PLift (supported c) =>
        ((linearYoneda k B).obj M).obj (op (Q.obj c)))).symm

theorem closedCopowerHomTermIso_projection (M : B) (c : C)
    (g : (covariantCopowerDiagram k Q (closedScalarDiagram k supported downward)).obj c ⟶ M)
    (h : PLift (supported c)) :
    biproduct.π (fun _ : PLift (supported c) => ((linearYoneda k B).obj M).obj (op (Q.obj c))) h
      ((closedCopowerHomTermIso k Q supported downward M c).hom g) =
        vectorCopowerInclusion k (Q.obj c)
          (ModuleCat.of k (PLift (supported c) → k)) (Pi.single h 1) ≫ g := by
  change ((ModuleCat.biproductIsoPi (fun _ : PLift (supported c) =>
    ((linearYoneda k B).obj M).obj (op (Q.obj c)))).inv ≫ biproduct.π _ h)
      (vectorCopowerFiniteFunctionsHomEquiv k (Q.obj c) M (PLift (supported c)) g) = _
  rw [ModuleCat.biproductIsoPi_inv_comp_π]
  exact vectorCopowerFiniteFunctionsHomEquiv_apply k (Q.obj c) M (PLift (supported c)) g h

theorem closedCopowerHomTermIso_inverse_inclusion (M : B) (c : C)
    (h : PLift (supported c)) (g : Q.obj c ⟶ M) :
    vectorCopowerInclusion k (Q.obj c)
        (ModuleCat.of k (PLift (supported c) → k)) (Pi.single h 1) ≫
      (closedCopowerHomTermIso k Q supported downward M c).inv
        (biproduct.ι (fun _ : PLift (supported c) => ((linearYoneda k B).obj M).obj (op (Q.obj c))) h g) = g := by
  rw [← closedCopowerHomTermIso_projection]
  have cancel : (closedCopowerHomTermIso k Q supported downward M c).hom
      ((closedCopowerHomTermIso k Q supported downward M c).inv
        (biproduct.ι (fun _ : PLift (supported c) => ((linearYoneda k B).obj M).obj (op (Q.obj c))) h g)) =
      biproduct.ι (fun _ : PLift (supported c) => ((linearYoneda k B).obj M).obj (op (Q.obj c))) h g :=
    ConcreteCategory.congr_hom (Iso.inv_hom_id (closedCopowerHomTermIso k Q supported downward M c)) _
  rw [cancel]
  exact ConcreteCategory.congr_hom (biproduct.ι_π_self
    (fun _ : PLift (supported c) => ((linearYoneda k B).obj M).obj (op (Q.obj c))) h) g

/-- Full source naturality, computed on the original scalar generators. -/
theorem closedCopowerHomTermIso_source (M : B) {c d : C} (f : c ⟶ d) :
    ((linearYoneda k B).obj M).map
        ((covariantCopowerDiagram k Q (closedScalarDiagram k supported downward)).map f).op ≫
      (closedCopowerHomTermIso k Q supported downward M c).hom =
    (closedCopowerHomTermIso k Q supported downward M d).hom ≫
      (closedContravariantLabels supported downward (Q.op ⋙ (linearYoneda k B).obj M)).map f.op := by
  apply (cancel_epi (closedCopowerHomTermIso k Q supported downward M d).inv).mp
  rw [Iso.inv_hom_id_assoc]
  apply biproduct.hom_ext'
  intro hd
  refine Eq.trans ?_
    (closedContravariantLabels_map_inclusion supported downward
      (Q.op ⋙ (linearYoneda k B).obj M) f.op hd).symm
  apply biproduct.hom_ext
  intro hc
  have same : (⟨downward f hd.down⟩ : PLift (supported c)) = hc := Subsingleton.elim _ _
  rw [same]
  simp only [Functor.comp_obj,Functor.op_obj,unop_op,Category.assoc,
    biproduct.ι_π_self,Category.comp_id]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  change biproduct.π (fun _ : PLift (supported c) =>
      ((linearYoneda k B).obj M).obj (op (Q.obj c))) hc
    ((closedCopowerHomTermIso k Q supported downward M c).hom
      ((covariantCopowerDiagram k Q (closedScalarDiagram k supported downward)).map f ≫
        (closedCopowerHomTermIso k Q supported downward M d).inv (biproduct.ι (fun _ : PLift (supported d) =>
          ((linearYoneda k B).obj M).obj (op (Q.obj d))) hd g))) = Q.map f ≫ g
  rw [closedCopowerHomTermIso_projection,← Category.assoc]
  refine (congrArg (fun t => t ≫
    (closedCopowerHomTermIso k Q supported downward M d).inv
      (biproduct.ι (fun _ : PLift (supported d) =>
        ((linearYoneda k B).obj M).obj (op (Q.obj d))) hd g))
    (covariantCopowerDiagram_map_inclusion k Q
      (closedScalarDiagram k supported downward) f (Pi.single hc 1))).trans ?_
  rw [Category.assoc]
  have scalar : (closedScalarDiagram k supported downward).map f (Pi.single hc 1) =
      Pi.single hd 1 := by
    funext h
    have one : h=hd := Subsingleton.elim _ _
    subst h
    change (Pi.single hc (1 : k) : PLift (supported c) → k) ⟨downward f hd.down⟩ =
      (Pi.single hd (1 : k) : PLift (supported d) → k) hd
    rw [same,Pi.single_eq_same,Pi.single_eq_same]
  rw [scalar]
  exact congrArg (fun t => Q.map f ≫ t)
    (closedCopowerHomTermIso_inverse_inclusion k Q supported downward M d hd g)

def closedCopowerHomIso (M : B) :
    (covariantCopowerDiagram k Q (closedScalarDiagram k supported downward)).op ⋙
        (linearYoneda k B).obj M ≅
      closedContravariantLabels supported downward (Q.op ⋙ (linearYoneda k B).obj M) :=
  NatIso.ofComponents (fun c => closedCopowerHomTermIso k Q supported downward M c.unop)
    (fun f => closedCopowerHomTermIso_source k Q supported downward M f.unop)

/-- Coefficient naturality is literal postcomposition before taking
closed-support coordinates. -/
theorem closedCopowerHomTermIso_target {M N : B} (f : M ⟶ N) (c : C) :
    ((linearCoyoneda k B).obj
        (op ((covariantCopowerDiagram k Q (closedScalarDiagram k supported downward)).obj c))).map f ≫
      (closedCopowerHomTermIso k Q supported downward N c).hom =
    (closedCopowerHomTermIso k Q supported downward M c).hom ≫
      biproduct.map (fun _ : PLift (supported c) =>
        ((linearCoyoneda k B).obj (op (Q.obj c))).map f) := by
  apply biproduct.hom_ext
  intro h
  simp only [Category.assoc]
  erw [biproduct.map_π]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  change biproduct.π (fun _ : PLift (supported c) => ((linearYoneda k B).obj N).obj (op (Q.obj c))) h ((closedCopowerHomTermIso k Q supported downward N c).hom (g ≫ f)) =
    (biproduct.π (fun _ : PLift (supported c) => ((linearYoneda k B).obj M).obj (op (Q.obj c))) h ((closedCopowerHomTermIso k Q supported downward M c).hom g)) ≫ f
  rw [closedCopowerHomTermIso_projection,closedCopowerHomTermIso_projection,Category.assoc]

/-- The whole target functors are isomorphic, before any localization. -/
def closedCopowerHomFunctorIso :
    linearYoneda k B ⋙
      (Functor.whiskeringLeft Cᵒᵖ Bᵒᵖ (ModuleCat k)).obj
        (covariantCopowerDiagram k Q (closedScalarDiagram k supported downward)).op ≅
    (linearYoneda k B ⋙ (Functor.whiskeringLeft Cᵒᵖ Bᵒᵖ (ModuleCat k)).obj Q.op) ⋙
      closedContravariantLabelEndofunctor supported downward :=
  NatIso.ofComponents (closedCopowerHomIso k Q supported downward) (by
    intro M N f
    apply NatTrans.ext
    funext c
    exact closedCopowerHomTermIso_target k Q supported downward f c.unop)

end ToricPower.Cellular

end

