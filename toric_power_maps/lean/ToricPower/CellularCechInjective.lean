module

public import ToricPower.CellularDiagramDual
public import ToricPower.CechPosetContraction
public import ToricPower.CellularPointAdjunction

/-!
# Actual coinduced tuple modules on an open face region

A retained region is an upward-closed subposet of the true intersection
poset. The cochain term at a cell consists of all functions on tuples
of containing cells. Values at the actual tuple intersection give its
coinduced universal property and prove injectivity, without changing
the incidence maps or truncating the tuple range.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower.FiniteCech

universe u
variable (k : Type u) [Field k] {B : Type u} [SemilatticeInf B]
  (P : B → Prop)

/-- Every actual tuple contributes a scalar-valued coinduced coordinate. -/
def cotupleModule (n : ℕ) : {b : B // P b} ⥤ ModuleCat.{u} k where
  obj b := ModuleCat.of k (UpperTuple b.val n → k)
  map {b c} f := ModuleCat.ofHom
    { toFun := fun x t => x (upperTupleRestrict (homOfLE f.le : b.val ⟶ c.val).op t)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_id b := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext t
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext t
    rfl

/-- The genuine retained tuple intersections. -/
def RetainedTuple (n : ℕ) := {t : Fin (n+1) → B // P (tupleMeet t)}

def retainedTupleCell {n : ℕ} (t : RetainedTuple P n) : {b : B // P b} :=
  ⟨tupleMeet t.val,t.property⟩

/-- Upward closure ensures every local tuple has its actual intersection
inside the retained region. -/
def retainTuple (upward : Monotone P) {n : ℕ} (b : {b : B // P b})
    (t : UpperTuple b.val n) : RetainedTuple P n :=
  ⟨t.val,upward ((le_tupleMeet_iff t.val b.val).mpr t.property) b.property⟩

def retainedTupleArrow (upward : Monotone P) {n : ℕ} (b : {b : B // P b})
    (t : UpperTuple b.val n) : b ⟶ retainedTupleCell P (retainTuple P upward b t) :=
  homOfLE ((le_tupleMeet_iff t.val b.val).mpr t.property)

/-- A linear functional at every retained intersection determines the
whole coinduced map using the actual generization maps. -/
def cotupleDesc (upward : Monotone P) (n : ℕ) (F : {b : B // P b} ⥤ ModuleCat.{u} k)
    (v : ∀ t : RetainedTuple P n,F.obj (retainedTupleCell P t) ⟶ ModuleCat.of k k) :
    F ⟶ cotupleModule k P n where
  app b := ModuleCat.ofHom
    { toFun := fun x t => v (retainTuple P upward b t) (F.map (retainedTupleArrow P upward b t) x)
      map_add' := by
        intro x y
        funext t
        simp only [map_add,Pi.add_apply]
      map_smul' := by
        intro a x
        funext t
        simp only [map_smul,Pi.smul_apply,RingHom.id_apply] }
  naturality {b c} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext t
    change v (retainTuple P upward c t)
        (F.map (retainedTupleArrow P upward c t) (F.map f x)) =
      v (retainTuple P upward b (upperTupleRestrict (homOfLE f.le : b.val ⟶ c.val).op t))
        (F.map (retainedTupleArrow P upward b
          (upperTupleRestrict (homOfLE f.le : b.val ⟶ c.val).op t)) x)
    have arrow : f ≫ retainedTupleArrow P upward c t =
        retainedTupleArrow P upward b
          (upperTupleRestrict (homOfLE f.le : b.val ⟶ c.val).op t) := Subsingleton.elim _ _
    have value := ConcreteCategory.congr_hom
      (F.map_comp f (retainedTupleArrow P upward c t)) x
    rw [arrow] at value
    exact congrArg (fun y => v (retainTuple P upward c t) y) value.symm

/-- The tuple coordinate of any natural map is its actual intersection
coordinate transported along the original face incidence. -/
theorem cotupleMap_coordinate (upward : Monotone P) (n : ℕ)
    (F : {b : B // P b} ⥤ ModuleCat.{u} k) (φ : F ⟶ cotupleModule k P n)
    (b : {b : B // P b}) (x : F.obj b) (t : UpperTuple b.val n) :
    φ.app b x t = φ.app (retainedTupleCell P (retainTuple P upward b t))
      (F.map (retainedTupleArrow P upward b t) x) (tupleAtMeet t.val) := by
  have natural := ConcreteCategory.congr_hom
    (φ.naturality (retainedTupleArrow P upward b t)) x
  have value := congrFun natural (tupleAtMeet t.val)
  exact value.symm

/-- Tuple coordinate evaluation is a literal linear map. -/
def cotupleEvaluation (n : ℕ) (b : {b : B // P b}) (t : UpperTuple b.val n) :
    (cotupleModule k P n).obj b ⟶ ModuleCat.of k k :=
  ModuleCat.ofHom
    { toFun := fun x => x t
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- All these actual coinduced tuple diagrams are injective. The proof
extends one scalar functional at each retained intersection. -/
theorem cotupleModule_injective (upward : Monotone P) (n : ℕ) :
    Injective (cotupleModule k P n) where
  factors {F G} φ η _ := by
    letI : Injective (ModuleCat.of k k) := vectorSpace_injective k _
    let v (t : RetainedTuple P n) : G.obj (retainedTupleCell P t) ⟶ ModuleCat.of k k :=
      Injective.factorThru
        (φ.app (retainedTupleCell P t) ≫ cotupleEvaluation k P n
          (retainedTupleCell P t) (tupleAtMeet t.val))
        (η.app (retainedTupleCell P t))
    refine ⟨cotupleDesc k P upward n G v,?_⟩
    apply NatTrans.ext
    funext b
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext t
    change v (retainTuple P upward b t)
      (G.map (retainedTupleArrow P upward b t) (η.app b x)) = φ.app b x t
    have natural := ConcreteCategory.congr_hom
      (η.naturality (retainedTupleArrow P upward b t)) x
    simp only [ModuleCat.comp_apply] at natural
    rw [← natural]
    have factor := ConcreteCategory.congr_hom
      (Injective.comp_factorThru
        (φ.app (retainedTupleCell P (retainTuple P upward b t)) ≫
          cotupleEvaluation k P n (retainedTupleCell P (retainTuple P upward b t))
            (tupleAtMeet t.val))
        (η.app (retainedTupleCell P (retainTuple P upward b t))))
      (F.map (retainedTupleArrow P upward b t) x)
    exact factor.trans (cotupleMap_coordinate k P upward n F φ b x t).symm

end ToricPower.FiniteCech

end
