module

public import ToricPower.CellularCechDual
public import ToricPower.CechPosetCoefficients
public import ToricPower.AdditiveAlternatingCoface

/-!
# Exact tuple coordinates for derived local sections

Global sections of the actual injective Čech terms are precisely
functions on retained intersections. The comparison is scalar-linear
and commutes with every tuple selection, so it preserves all cofaces,
codegeneracies, and alternating differentials.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace ToricPower.FiniteCech

universe u
variable (k : Type u) [Field k] {B : Type u} [SemilatticeInf B]
  (P : B → Prop) (upward : Monotone P)

abbrev constantFieldDiagram : {b : B // P b} ⥤ ModuleCat.{u} k :=
  (Functor.const {b : B // P b}).obj (ModuleCat.of k k)

/-- A section is determined by its scalar at each retained intersection. -/
theorem cotupleSection_coordinate (n : ℕ)
    (φ : constantFieldDiagram k P ⟶ cotupleModule k P n)
    (b : {b : B // P b}) (r : k) (t : UpperTuple b.val n) :
    φ.app b r t = r * φ.app (retainedTupleCell P (retainTuple P upward b t))
      (1 : k) (tupleAtMeet t.val) := by
  have scale := congrFun ((φ.app b).hom.map_smul r (1 : k)) t
  have coordinate := cotupleMap_coordinate k P upward n (constantFieldDiagram k P)
    φ b (1 : k) t
  change φ.app b (r * 1) t = r * φ.app b (1 : k) t at scale
  rw [mul_one] at scale
  exact scale.trans (congrArg (fun x => r * x) coordinate)

/-- Literal scalar-linear global sections of a coinduced tuple term. -/
def cotupleSectionEquiv (n : ℕ) :
    (constantFieldDiagram k P ⟶ cotupleModule k P n) ≃ₗ[k] (RetainedTuple P n → k) where
  toFun φ t := φ.app (retainedTupleCell P t) (1 : k) (tupleAtMeet t.val)
  invFun values := cotupleDesc k P upward n (constantFieldDiagram k P)
    (fun t => ModuleCat.ofHom (LinearMap.mulRight k (values t)))
  left_inv φ := by
    apply NatTrans.ext
    funext b
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change k at r
    funext t
    change r * φ.app (retainedTupleCell P (retainTuple P upward b t))
      (1 : k) (tupleAtMeet t.val) = φ.app b r t
    exact (cotupleSection_coordinate k P upward n φ b r t).symm
  right_inv values := by
    funext t
    change 1 * values t = values t
    exact one_mul _
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Exact global-section coordinates on the original dual resolution. -/
def cotupleGlobalEvaluation (n : ℕ) :
    (constantFieldDiagram k P ⟶
      (retainedDiagramDual k P).obj (op (tupleModule k (B := B) n))) ≃ₗ[k]
        (RetainedTuple P n → k) :=
  (CategoryTheory.Linear.homCongr k (Iso.refl _) (cotupleDualIso k P n)).trans
    (cotupleSectionEquiv k P upward n)

/-- The literal scalar functional underlying a dual tuple coefficient. -/
def cotupleDualFunctional (n : ℕ) (b : {b : B // P b})
    (x : ((retainedDiagramDual k P).obj (op (tupleModule k (B := B) n))).obj b) :
    (ModuleCat.free k).obj (UpperTuple b.val n) ⟶ ModuleCat.of k k := x

theorem cotupleGlobalEvaluation_apply (n : ℕ)
    (φ : constantFieldDiagram k P ⟶
      (retainedDiagramDual k P).obj (op (tupleModule k (B := B) n)))
    (t : RetainedTuple P n) :
    cotupleGlobalEvaluation k P upward n φ t =
      cotupleDualFunctional k P n (retainedTupleCell P t)
        (φ.app (retainedTupleCell P t) (1 : k)) (ModuleCat.freeMk (tupleAtMeet t.val)) := by
  change ((𝟙 _ ≫ φ) ≫ (cotupleDualIso k P n).hom).app
    (retainedTupleCell P t) (1 : k) (tupleAtMeet t.val) = _
  rw [Category.id_comp]
  rfl

/-- Selecting a tuple retains the genuine larger intersection. -/
def retainedTupleSelect {m n : ℕ} (selection : Fin (m+1) → Fin (n+1))
    (t : RetainedTuple P n) : RetainedTuple P m :=
  ⟨t.val ∘ selection,upward (tupleMeet_le_selection selection t.val) t.property⟩

/-- Every coface and codegeneracy is the literal pullback of tuple
coordinates, including the actual incidence between intersections. -/
theorem cotupleGlobalEvaluation_selection {m n : ℕ}
    (selection : Fin (m+1) → Fin (n+1))
    (φ : constantFieldDiagram k P ⟶
      (retainedDiagramDual k P).obj (op (tupleModule k (B := B) m)))
    (t : RetainedTuple P n) :
    cotupleGlobalEvaluation k P upward n
      (φ ≫ (retainedDiagramDual k P).map (tupleSelection k selection).op) t =
      cotupleGlobalEvaluation k P upward m φ (retainedTupleSelect P upward selection t) := by
  rw [cotupleGlobalEvaluation_apply,cotupleGlobalEvaluation_apply]
  let f : retainedTupleCell P t ⟶
      retainedTupleCell P (retainedTupleSelect P upward selection t) :=
    homOfLE (tupleMeet_le_selection selection t.val)
  have natural := ConcreteCategory.congr_hom (φ.naturality f) (1 : k)
  have value := congrArg
    (fun ψ : (ModuleCat.free k).obj
      (UpperTuple (tupleMeet (t.val ∘ selection)) m) ⟶ ModuleCat.of k k =>
      ψ (ModuleCat.freeMk (tupleAtMeet (t.val ∘ selection)))) natural
  change cotupleDualFunctional k P m
      (retainedTupleCell P (retainedTupleSelect P upward selection t))
      (φ.app (retainedTupleCell P (retainedTupleSelect P upward selection t)) (1 : k))
      (ModuleCat.freeMk (tupleAtMeet (t.val ∘ selection))) =
    cotupleDualFunctional k P m (retainedTupleCell P t)
      (φ.app (retainedTupleCell P t) (1 : k))
      ((tupleModule k m).map
        (homOfLE (tupleMeet_le_selection selection t.val)).op
        (ModuleCat.freeMk (tupleAtMeet (t.val ∘ selection)))) at value
  rw [tupleModule_map_freeMk] at value
  change cotupleDualFunctional k P m (retainedTupleCell P t)
      (φ.app (retainedTupleCell P t) (1 : k))
      ((tupleSelection k selection).app (op (tupleMeet t.val))
        (ModuleCat.freeMk (tupleAtMeet t.val))) = _
  change cotupleDualFunctional k P m (retainedTupleCell P t)
      (φ.app (retainedTupleCell P t) (1 : k))
      ((ModuleCat.free k).map (↾upperTupleSelect selection)
        (ModuleCat.freeMk (tupleAtMeet t.val))) = _
  rw [ModuleCat.free_map_apply]
  exact value.symm

/-- The whole retained-tuple cosimplicial module, with all ordered
tuples and repetitions rather than an unsupported finite truncation. -/
def retainedTupleCosimplicial : CosimplicialObject (ModuleCat.{u} k) where
  obj simplex := ModuleCat.of k (RetainedTuple P simplex.len → k)
  map selection := ModuleCat.ofHom
    { toFun := fun values t => values (retainedTupleSelect P upward selection.toOrderHom t)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_id simplex := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro values
    funext t
    rfl
  map_comp first second := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro values
    funext t
    rfl

/-- The actual source cosimplicial object of the full dual resolution. -/
def cotupleCosimplicial : CosimplicialObject ({b : B // P b} ⥤ ModuleCat.{u} k) :=
  (tupleAugmented k (B := B)).left.rightOp ⋙ retainedDiagramDual k P

/-- The entire scalar-linear global section comparison, natural in
every simplicial operator before taking any homology. -/
def cotupleGlobalCosimplicialIso :
    cotupleCosimplicial k P ⋙
      (linearCoyoneda k ({b : B // P b} ⥤ ModuleCat.{u} k)).obj
        (op (constantFieldDiagram k P)) ≅ retainedTupleCosimplicial k P upward :=
  NatIso.ofComponents (fun simplex =>
    (cotupleGlobalEvaluation k P upward simplex.len).toModuleIso)
    (by
      intro source target selection
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      funext t
      exact cotupleGlobalEvaluation_selection k P upward selection.toOrderHom φ t)

end ToricPower.FiniteCech

end
