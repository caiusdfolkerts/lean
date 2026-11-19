module

public import ToricPower.ArrangementWeightedIncidence
public import Mathlib.LinearAlgebra.DFinsupp
public import ToricPower.ModuleDirectSumComplex
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Direct image of a weighted incidence diagram

The fiber over a normalized cell is the algebraic direct sum over every
integral lift. Incidence maps translate the index by their actual recorded
lattice vector. Thus the construction retains loop monodromy and all
copies of an incidence on the torus.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (R : Type) [CommRing R]

local notation "C" => IncidenceObject A
local notation "W" => WeightedIncidenceObject A

/-- The unique lift of an incidence from a specified source weight. -/
def weightedIncidenceLift {c d : C} (f : c ⟶ d) (m : Fin n → ℤ) :
    WeightedIncidenceHom A (c,m) (d,m+f.val) := ⟨f,rfl⟩

/-- The full sum of the coefficients over one torus cell. -/
def weightedPushdownCell (F : W ⥤ ModuleCat.{0} R) (c : C) : ModuleCat.{0} R :=
  ModuleCat.of R (Π₀ m : Fin n → ℤ, F.obj (c,m))

/-- The literal inclusion of one lift into the full fiber. -/
def weightedPushdownInclusion (F : W ⥤ ModuleCat.{0} R) (c : C) (m : Fin n → ℤ) :
    F.obj (c,m) ⟶ weightedPushdownCell A R F c :=
  ModuleCat.ofHom (DFinsupp.lsingle (R := R) (M := fun w => ↑(F.obj (c,w))) m)

/-- Each summand follows its unique lifted incidence. -/
def weightedPushdownMap (F : W ⥤ ModuleCat.{0} R) {c d : C} (f : c ⟶ d) :
    weightedPushdownCell A R F c ⟶ weightedPushdownCell A R F d :=
  ModuleCat.ofHom (DFinsupp.lsum R (fun m : Fin n → ℤ =>
    (DFinsupp.lsingle (R := R) (M := fun w => ↑(F.obj (d,w))) (m+f.val)).comp
      (F.map (weightedIncidenceLift A f m)).hom))

@[reassoc]
theorem weightedPushdownMap_inclusion (F : W ⥤ ModuleCat.{0} R)
    {c d : C} (f : c ⟶ d) (m : Fin n → ℤ) :
    weightedPushdownInclusion A R F c m ≫ weightedPushdownMap A R F f =
      F.map (weightedIncidenceLift A f m) ≫
        weightedPushdownInclusion A R F d (m+f.val) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (DFinsupp.lsum R (fun w : Fin n → ℤ =>
    (DFinsupp.lsingle (R := R) (M := fun v => ↑(F.obj (d,v))) (w+f.val)).comp
      (F.map (weightedIncidenceLift A f w)).hom)) (DFinsupp.single m x) = _
  rw [DFinsupp.lsum_single]
  rfl

/-- The same inclusion formula with arbitrary specified endpoints. This
form avoids suppressing the transports of lattice-index equalities. -/
theorem weightedPushdownMap_indexedInclusion (F : W ⥤ ModuleCat.{0} R)
    {c d : C} (f : c ⟶ d) (m w : Fin n → ℤ) (h : w = m+f.val) :
    weightedPushdownInclusion A R F c m ≫ weightedPushdownMap A R F f =
      F.map (show WeightedIncidenceHom A (c,m) (d,w) from ⟨f,h⟩) ≫
        weightedPushdownInclusion A R F d w := by
  subst w
  exact weightedPushdownMap_inclusion A R F f m

@[reassoc]
theorem weightedPushdownMap_liftedInclusion (F : W ⥤ ModuleCat.{0} R)
    {c d : W} (f : c ⟶ d) :
    weightedPushdownInclusion A R F c.1 c.2 ≫ weightedPushdownMap A R F f.val =
      F.map f ≫ weightedPushdownInclusion A R F d.1 d.2 :=
  weightedPushdownMap_indexedInclusion A R F f.val c.2 d.2 f.property

/-- Equality of maps out of the direct image is checked on all lifts. -/
theorem weightedPushdown_hom_ext (F : W ⥤ ModuleCat.{0} R) (c : C)
    {M : ModuleCat.{0} R} {f g : weightedPushdownCell A R F c ⟶ M}
    (h : ∀ m, weightedPushdownInclusion A R F c m ≫ f =
      weightedPushdownInclusion A R F c m ≫ g) : f = g := by
  apply ModuleCat.hom_ext
  apply DFinsupp.lhom_ext
  intro m x
  exact ConcreteCategory.congr_hom (h m) x

theorem weightedPushdownMap_id (F : W ⥤ ModuleCat.{0} R) (c : C) :
    weightedPushdownMap A R F (𝟙 c) = 𝟙 (weightedPushdownCell A R F c) := by
  apply weightedPushdown_hom_ext A R F c
  intro m
  let c' : W := (c,m)
  have h := weightedPushdownMap_liftedInclusion A R F (𝟙 c')
  simpa only [weightedIncidence_id_val, F.map_id, Category.id_comp,
    Category.comp_id] using h

theorem weightedPushdownMap_comp (F : W ⥤ ModuleCat.{0} R)
    {c d e : C} (f : c ⟶ d) (g : d ⟶ e) :
    weightedPushdownMap A R F (f ≫ g) =
      weightedPushdownMap A R F f ≫ weightedPushdownMap A R F g := by
  apply weightedPushdown_hom_ext A R F c
  intro m
  let c' : W := (c,m)
  let d' : W := (d,m+f.val)
  let e' : W := (e,(m+f.val)+g.val)
  let f' : c' ⟶ d' := weightedIncidenceLift A f m
  let g' : d' ⟶ e' := weightedIncidenceLift A g (m+f.val)
  calc
    _ = F.map (f' ≫ g') ≫ weightedPushdownInclusion A R F e'.1 e'.2 :=
      weightedPushdownMap_liftedInclusion A R F (f' ≫ g')
    _ = F.map f' ≫ F.map g' ≫ weightedPushdownInclusion A R F e'.1 e'.2 := by
      rw [F.map_comp, Category.assoc]
    _ = F.map f' ≫ weightedPushdownInclusion A R F d'.1 d'.2 ≫
        weightedPushdownMap A R F g := by
      rw [← weightedPushdownMap_liftedInclusion A R F g']
      rfl
    _ = _ := by
      rw [← Category.assoc, ← weightedPushdownMap_liftedInclusion A R F f',
        Category.assoc]
      rfl

/-- The actual direct-image diagram, with all incidence translations. -/
def weightedPushdownObj (F : W ⥤ ModuleCat.{0} R) : C ⥤ ModuleCat.{0} R where
  obj := weightedPushdownCell A R F
  map := weightedPushdownMap A R F
  map_id := weightedPushdownMap_id A R F
  map_comp := weightedPushdownMap_comp A R F

/-- A coefficient transformation acts on each lift without reindexing. -/
def weightedPushdownCellMap {F G : W ⥤ ModuleCat.{0} R} (α : F ⟶ G) (c : C) :
    weightedPushdownCell A R F c ⟶ weightedPushdownCell A R G c :=
  ModuleCat.ofHom (DFinsupp.mapRange.linearMap
    (fun m : Fin n → ℤ => (α.app (c,m)).hom))

@[reassoc]
theorem weightedPushdownCellMap_inclusion {F G : W ⥤ ModuleCat.{0} R}
    (α : F ⟶ G) (c : C) (m : Fin n → ℤ) :
    weightedPushdownInclusion A R F c m ≫ weightedPushdownCellMap A R α c =
      α.app (c,m) ≫ weightedPushdownInclusion A R G c m := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact DFinsupp.mapRange_single (hf := fun w => (α.app (c,w)).hom.map_zero)

/-- The actual transformation of the full pushdown diagrams. -/
def weightedPushdownMapNat {F G : W ⥤ ModuleCat.{0} R} (α : F ⟶ G) :
    weightedPushdownObj A R F ⟶ weightedPushdownObj A R G where
  app := weightedPushdownCellMap A R α
  naturality {c d} f := by
    apply weightedPushdown_hom_ext A R F c
    intro m
    change weightedPushdownInclusion A R F c m ≫
        (weightedPushdownMap A R F f ≫ weightedPushdownCellMap A R α d) =
      weightedPushdownInclusion A R F c m ≫
        (weightedPushdownCellMap A R α c ≫ weightedPushdownMap A R G f)
    rw [weightedPushdownMap_inclusion_assoc, weightedPushdownCellMap_inclusion,
      weightedPushdownCellMap_inclusion_assoc, weightedPushdownMap_inclusion,
      ← Category.assoc, ← Category.assoc, α.naturality]

/-- Direct image on actual module diagrams, before taking complexes. -/
def weightedPushdown : (W ⥤ ModuleCat.{0} R) ⥤ (C ⥤ ModuleCat.{0} R) where
  obj := weightedPushdownObj A R
  map := weightedPushdownMapNat A R
  map_id F := by
    apply NatTrans.ext
    funext c
    apply ModuleCat.hom_ext
    exact DFinsupp.mapRange.linearMap_id
  map_comp α β := by
    apply NatTrans.ext
    funext c
    apply ModuleCat.hom_ext
    exact DFinsupp.mapRange.linearMap_comp _ _

/-- Evaluation of direct image is exactly the unrestricted fiber sum. -/
def weightedPushdownEvaluationIso (c : C) :
    weightedPushdown A R ⋙ (evaluation C (ModuleCat.{0} R)).obj c ≅
      (whiskeringLeft (Discrete (Fin n → ℤ)) W (ModuleCat.{0} R)).obj
          (Discrete.functor (fun m => (c,m))) ⋙ ModuleDirectSum.sumFunctor R :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

instance weightedPushdownPreservesFiniteLimits : PreservesFiniteLimits (weightedPushdown A R) :=
  preservesFiniteLimits_of_evaluation _ (fun c =>
    preservesFiniteLimits_of_natIso (weightedPushdownEvaluationIso A R c).symm)

instance weightedPushdownPreservesFiniteColimits : PreservesFiniteColimits (weightedPushdown A R) :=
  preservesFiniteColimits_of_evaluation _ (fun c =>
    preservesFiniteColimits_of_natIso (weightedPushdownEvaluationIso A R c).symm)

instance weightedPushdownAdditive : (weightedPushdown A R).Additive :=
  (weightedPushdown A R).additive_of_preserves_binary_products

end ToricPower.IntegralArrangement

end
