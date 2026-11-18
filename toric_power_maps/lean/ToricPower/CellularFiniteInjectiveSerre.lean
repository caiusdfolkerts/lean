module

public import ToricPower.CellularPointSerreNaturality
public import ToricPower.SerrePairingBiproduct
public import ToricPower.FiniteDiagramSyzygies
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Inverse Nakayama on finite injective diagrams

Every pointwise finite-dimensional injective diagram is an actual
retract of a finite sum of co-representable injectives. The point
pairings therefore extend to all such injectives, naturally for every
map between them. The other argument of the pairing remains arbitrary.
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

abbrev finiteCorepresentableIndex (F : C ⥤ ModuleCat.{u} k) :=
  Σ c : C, Module.Free.ChooseBasisIndex k (F.obj c)

def finiteCorepresentableFamily (F : C ⥤ ModuleCat.{u} k) :
    finiteCorepresentableIndex k F → C ⥤ ModuleCat.{u} k :=
  fun i => pointCorepresentable k i.1

variable [Finite C]

instance finiteCorepresentableIndex_finite (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] : Finite (finiteCorepresentableIndex k F) := by
  unfold finiteCorepresentableIndex
  infer_instance

instance finiteCorepresentableIndex_fintype (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] : Fintype (finiteCorepresentableIndex k F) :=
  Fintype.ofFinite _

instance finiteCorepresentableFamily_hasBiproduct (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] : HasBiproduct (finiteCorepresentableFamily k F) :=
  HasBiproduct.of_hasCoproduct _

def finiteCorepresentableSum (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] : C ⥤ ModuleCat.{u} k :=
  ⨁ finiteCorepresentableFamily k F

def finiteCorepresentableEmbedding (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] : F ⟶ finiteCorepresentableSum k F :=
  biproduct.lift fun i =>
    (pointCoinducedHomLinearEquiv k F i.1 (ModuleCat.of k k)).symm
      ((Module.Free.chooseBasis k (F.obj i.1)).coord i.2)

theorem finiteCorepresentableEmbedding_π (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] (i : finiteCorepresentableIndex k F) :
    finiteCorepresentableEmbedding k F ≫ biproduct.π (finiteCorepresentableFamily k F) i =
      (pointCoinducedHomLinearEquiv k F i.1 (ModuleCat.of k k)).symm
        ((Module.Free.chooseBasis k (F.obj i.1)).coord i.2) :=
  biproduct.lift_π _ _

theorem finiteCorepresentableEmbedding_π_value (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] (c : C)
    (i : Module.Free.ChooseBasisIndex k (F.obj c)) (x : F.obj c) :
    (finiteCorepresentableEmbedding k F ≫
      biproduct.π (finiteCorepresentableFamily k F) ⟨c, i⟩).app c x (𝟙 c) =
        (Module.Free.chooseBasis k (F.obj c)).coord i x := by
  rw [finiteCorepresentableEmbedding_π]
  exact LinearMap.congr_fun
    ((pointCoinducedHomLinearEquiv k F c (ModuleCat.of k k)).apply_symm_apply
      ((Module.Free.chooseBasis k (F.obj c)).coord i)) x

instance finiteCorepresentableEmbedding_mono (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] : Mono (finiteCorepresentableEmbedding k F) := by
  rw [NatTrans.mono_iff_mono_app]
  intro c
  rw [ModuleCat.mono_iff_injective]
  intro x y equal
  apply (Module.Free.chooseBasis k (F.obj c)).repr.injective
  ext i
  have h := congrArg (fun z : (finiteCorepresentableSum k F).obj c =>
    (biproduct.π (finiteCorepresentableFamily k F) ⟨c, i⟩).app c z (𝟙 c)) equal
  change (finiteCorepresentableEmbedding k F ≫
      biproduct.π (finiteCorepresentableFamily k F) ⟨c, i⟩).app c x (𝟙 c) =
    (finiteCorepresentableEmbedding k F ≫
      biproduct.π (finiteCorepresentableFamily k F) ⟨c, i⟩).app c y (𝟙 c) at h
  rw [finiteCorepresentableEmbedding_π_value, finiteCorepresentableEmbedding_π_value] at h
  exact h

def finiteCorepresentableRetraction (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] [Injective F] :
    finiteCorepresentableSum k F ⟶ F :=
  Injective.factorThru (𝟙 F) (finiteCorepresentableEmbedding k F)

theorem finiteCorepresentable_retract (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] [Injective F] :
    finiteCorepresentableEmbedding k F ≫ finiteCorepresentableRetraction k F = 𝟙 F :=
  Injective.comp_factorThru _ _

variable [∀ c d : C, Finite (c ⟶ d)]

def finiteCorepresentableSumPairing (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] :
    SerrePairing.CodomainPairing k (inverseNakayama k) (finiteCorepresentableSum k F) :=
  SerrePairing.biproductPairing k (finiteCorepresentableFamily k F)
    (inverseNakayama k) (fun i => pointCodomainPairing k i.1)

theorem finiteCorepresentableSumPairing_compatible (F G : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] [∀ c, FiniteDimensional k (G.obj c)]
    (a : finiteCorepresentableSum k F ⟶ finiteCorepresentableSum k G) :
    SerrePairing.Compatible k (finiteCorepresentableSumPairing k F)
      (finiteCorepresentableSumPairing k G) a :=
  SerrePairing.biproductPairing_compatible k (finiteCorepresentableFamily k F)
    (inverseNakayama k) (finiteCorepresentableFamily k G)
    (fun i => pointCodomainPairing k i.1) (fun j => pointCodomainPairing k j.1) a
    (fun i j => pointCodomainPairing_compatible k i.1 j.1 _)

def finiteInjectivePairing (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] [Injective F] :
    SerrePairing.CodomainPairing k (inverseNakayama k) F :=
  SerrePairing.retract (finiteCorepresentableSumPairing k F)
    (finiteCorepresentableEmbedding k F) (finiteCorepresentableRetraction k F)
    (finiteCorepresentable_retract k F)
    (finiteCorepresentableSumPairing_compatible k F F _)

theorem finiteInjectivePairing_compatible (F G : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] [∀ c, FiniteDimensional k (G.obj c)]
    [Injective F] [Injective G] (a : F ⟶ G) :
    SerrePairing.Compatible k (finiteInjectivePairing k F)
      (finiteInjectivePairing k G) a :=
  SerrePairing.retract_compatible (finiteCorepresentableSumPairing k F)
    (finiteCorepresentableEmbedding k F) (finiteCorepresentableRetraction k F)
    (finiteCorepresentable_retract k F)
    (finiteCorepresentableSumPairing_compatible k F F _)
    (finiteCorepresentableSumPairing k G)
    (finiteCorepresentableEmbedding k G) (finiteCorepresentableRetraction k G)
    (finiteCorepresentable_retract k G)
    (finiteCorepresentableSumPairing_compatible k G G _) a
    (finiteCorepresentableSumPairing_compatible k F G _)

theorem inverseNakayama_projective_of_finite_injective (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] [Injective F] :
    Projective ((inverseNakayama k).obj F) := by
  let T := inverseNakayama k (C := C)
  let family := finiteCorepresentableFamily k F
  letI (i : finiteCorepresentableIndex k F) : Projective (T.obj (family i)) :=
    inverseNakayamaCorepresentable_projective k i.1
  have projectiveSum : Projective (T.obj (⨁ family)) :=
    { factors := fun {X Y} f e he => by
        letI := he
        let components : ∀ i, T.obj (family i) ⟶ X :=
          fun i => Projective.factorThru (T.map (biproduct.ι family i) ≫ f) e
        let g := (SerrePairing.mappedBiproductHom k family T X).symm components
        refine ⟨g, ?_⟩
        apply (SerrePairing.mappedBiproductHom k family T Y).injective
        funext i
        have hi := congrFun
          ((SerrePairing.mappedBiproductHom k family T X).apply_symm_apply components) i
        change T.map (biproduct.ι family i) ≫ g = components i at hi
        change T.map (biproduct.ι family i) ≫ (g ≫ e) = _
        rw [← Category.assoc, hi]
        exact Projective.factorThru_comp _ _ }
  letI : Projective (T.obj (finiteCorepresentableSum k F)) := projectiveSum
  refine ⟨fun {X Y} f e he => ?_⟩
  letI := he
  obtain ⟨g, hg⟩ := Projective.factors
    (T.map (finiteCorepresentableRetraction k F) ≫ f) e
  refine ⟨T.map (finiteCorepresentableEmbedding k F) ≫ g, ?_⟩
  rw [Category.assoc, hg, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    finiteCorepresentable_retract, CategoryTheory.Functor.map_id, Category.id_comp]

theorem finiteDiagramHom_finite (F G : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] [∀ c, FiniteDimensional k (G.obj c)] :
    FiniteDimensional k (F ⟶ G) := by
  let components : (F ⟶ G) →ₗ[k] ∀ c, F.obj c →ₗ[k] G.obj c :=
    { toFun := fun f c => (f.app c).hom
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply FiniteDimensional.of_injective components
  intro f g h
  apply NatTrans.ext
  funext c
  apply ModuleCat.hom_ext
  exact congrFun h c

theorem inverseNakayama_finite (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] (c : C) :
    FiniteDimensional k (((inverseNakayama k).obj F).obj c) := by
  letI (d : C) : FiniteDimensional k ((pointCorepresentable k c).obj d) := by
    change FiniteDimensional k ((d ⟶ c) → k)
    infer_instance
  exact finiteDiagramHom_finite k (pointCorepresentable k c) F

end ToricPower.Cellular

end
