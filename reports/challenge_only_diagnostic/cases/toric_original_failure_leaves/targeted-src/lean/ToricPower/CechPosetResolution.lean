module

public import ToricPower.CellularFiniteResolution
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.FinCases

/-!
# The actual tuple resolution of an intersection poset

For an intersection-closed poset of charts, the usual ordered Čech
tuples form a projective resolution of the constant diagram. At a chart
`b`, its generators are precisely the tuples of charts containing `b`.
Inserting `b` contracts the augmented evaluated complex.

The construction keeps all ordered tuples, repetitions, and degrees.
A comparison with the finite projective resolution is therefore a
homotopy comparison, rather than an unsupported truncation of Čech
cochains. This is the algebraic comparison needed before finite Čech
totalization can be used with unbounded coefficient complexes.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace ToricPower.FiniteCech

universe u

variable {B : Type u} [SemilatticeInf B]

/-- Ordered tuples of charts containing the chart at which we evaluate. -/
def UpperTuple (b : B) (n : ℕ) :=
  {t : Fin (n+1) → B // ∀ i, b ≤ t i}

/-- Restriction retains the tuple and composes the actual containments. -/
def upperTupleRestrict {b c : Bᵒᵖ} (f : b ⟶ c) {n : ℕ}
    (t : UpperTuple b.unop n) : UpperTuple c.unop n :=
  ⟨t.val, fun i => (leOfHom f.unop).trans (t.property i)⟩

/-- The presheaf of actual ordered tuples. -/
def upperTupleDiagram (n : ℕ) : Bᵒᵖ ⥤ Type u where
  obj b := UpperTuple b.unop n
  map f := ↾upperTupleRestrict f
  map_id b := rfl
  map_comp f g := rfl

/-- Selecting coordinates gives the simplicial structure, including all
degeneracies that repeat entries. -/
def upperTupleSelect {b : B} {m n : ℕ} (s : Fin (m+1) → Fin (n+1))
    (t : UpperTuple b n) : UpperTuple b m :=
  ⟨t.val ∘ s, fun i => t.property (s i)⟩

/-- The literal simplicial presheaf of ordered chart tuples. -/
def upperTupleSimplicial : SimplicialObject (Bᵒᵖ ⥤ Type u) where
  obj n := upperTupleDiagram n.unop.len
  map s :=
    { app b := ↾upperTupleSelect s.unop.toOrderHom
      naturality {_ _} f := rfl }
  map_id n := by
    apply NatTrans.ext
    funext b
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext b
    rfl

/-- The augmentation is to the actual constant one-point presheaf. -/
def upperTupleAugmented : SimplicialObject.Augmented (Bᵒᵖ ⥤ Type u) where
  left := upperTupleSimplicial
  right := (Functor.const Bᵒᵖ).obj PUnit.{u+1}
  hom :=
    { app n := { app b := ↾fun _ => PUnit.unit }
      naturality {_ _} f := by
        apply NatTrans.ext
        funext b
        rfl }

variable (k : Type u) [Field k]

/-- Pointwise free vector spaces retain each tuple as an actual basis
generator, rather than replacing a diagram by its dimension. -/
def freeTupleDiagrams : (Bᵒᵖ ⥤ Type u) ⥤ Bᵒᵖ ⥤ ModuleCat.{u} k :=
  (Functor.whiskeringRight Bᵒᵖ (Type u) (ModuleCat.{u} k)).obj (ModuleCat.free k)

/-- The free diagram in one simplicial degree. -/
def tupleModule (n : ℕ) : Bᵒᵖ ⥤ ModuleCat.{u} k :=
  (freeTupleDiagrams k).obj (upperTupleDiagram n)

@[simp]
theorem tupleModule_map_freeMk {b c : Bᵒᵖ} (f : b ⟶ c) (n : ℕ)
    (t : UpperTuple b.unop n) :
    (tupleModule k n).map f (ModuleCat.freeMk t) =
      ModuleCat.freeMk (upperTupleRestrict f t) :=
  ModuleCat.free_map_apply _ _

/-- The actual nonempty intersection represented by a tuple. -/
def tupleMeet {n : ℕ} (t : Fin (n+1) → B) : B :=
  Finset.univ.inf' Finset.univ_nonempty t

theorem le_tupleMeet_iff {n : ℕ} (t : Fin (n+1) → B) (b : B) :
    b ≤ tupleMeet t ↔ ∀ i, b ≤ t i := by
  simp only [tupleMeet, Finset.le_inf'_iff, Finset.mem_univ, forall_const]

theorem tupleMeet_le {n : ℕ} (t : Fin (n+1) → B) (i : Fin (n+1)) :
    tupleMeet t ≤ t i :=
  (le_tupleMeet_iff t (tupleMeet t)).mp le_rfl i

/-- The same tuple, evaluated at its own intersection. -/
def tupleAtMeet {n : ℕ} (t : Fin (n+1) → B) : UpperTuple (tupleMeet t) n :=
  ⟨t, tupleMeet_le t⟩

/-- Every tuple generator is the restriction of its generator at the
actual intersection. -/
def tupleSourceMap {b : Bᵒᵖ} {n : ℕ} (t : UpperTuple b.unop n) :
    op (tupleMeet t.val) ⟶ b :=
  (homOfLE ((le_tupleMeet_iff t.val b.unop).mpr t.property)).op

@[simp]
theorem tupleSourceMap_restrict {b : Bᵒᵖ} {n : ℕ} (t : UpperTuple b.unop n) :
    upperTupleRestrict (tupleSourceMap t) (tupleAtMeet t.val) = t := by
  apply Subtype.ext
  rfl

/-- Values at tuple intersections determine a unique natural map from
the free tuple diagram. -/
def tupleDesc (n : ℕ) (F : Bᵒᵖ ⥤ ModuleCat.{u} k)
    (v : ∀ t : Fin (n+1) → B, F.obj (op (tupleMeet t))) : tupleModule k n ⟶ F where
  app b := ModuleCat.freeDesc (↾fun t : UpperTuple b.unop n => F.map (tupleSourceMap t) (v t.val))
  naturality {b c} f := by
    apply ModuleCat.free_hom_ext
    intro t
    change ModuleCat.freeDesc
        (↾fun s : UpperTuple c.unop n => F.map (tupleSourceMap s) (v s.val))
          ((tupleModule k n).map f (ModuleCat.freeMk t)) =
      F.map f (ModuleCat.freeDesc
        (↾fun s : UpperTuple b.unop n => F.map (tupleSourceMap s) (v s.val))
          (ModuleCat.freeMk t))
    rw [tupleModule_map_freeMk, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    change F.map (tupleSourceMap (upperTupleRestrict f t)) (v t.val) =
      F.map f (F.map (tupleSourceMap t) (v t.val))
    rw [← ModuleCat.comp_apply, ← CategoryTheory.Functor.map_comp]
    congr 2

@[simp]
theorem tupleDesc_freeMk (n : ℕ) (F : Bᵒᵖ ⥤ ModuleCat.{u} k)
    (v : ∀ t : Fin (n+1) → B, F.obj (op (tupleMeet t)))
    (b : Bᵒᵖ) (t : UpperTuple b.unop n) :
    (tupleDesc k n F v).app b (ModuleCat.freeMk t) =
      F.map (tupleSourceMap t) (v t.val) :=
  ModuleCat.freeDesc_apply _ _

/-- This generator identity retains every restriction map in the
comparison with ordinary Čech cochains. -/
theorem tupleMap_generator (n : ℕ) (F : Bᵒᵖ ⥤ ModuleCat.{u} k)
    (φ : tupleModule k n ⟶ F) (b : Bᵒᵖ) (t : UpperTuple b.unop n) :
    φ.app b (ModuleCat.freeMk t) =
      F.map (tupleSourceMap t)
        (φ.app (op (tupleMeet t.val)) (ModuleCat.freeMk (tupleAtMeet t.val))) := by
  have h := ConcreteCategory.congr_hom (φ.naturality (tupleSourceMap t))
    (ModuleCat.freeMk (tupleAtMeet t.val))
  simpa only [ModuleCat.comp_apply, tupleModule_map_freeMk,
    tupleSourceMap_restrict] using h

/-- Every term of the actual ordered tuple complex is projective. The
proof lifts one value at each actual chart intersection and transports
it using the genuine presheaf maps. -/
instance tupleModule_projective (n : ℕ) : Projective (tupleModule k (B := B) n) where
  factors {F G} φ η hη := by
    have hsurj (t : Fin (n+1) → B) : Function.Surjective (η.app (op (tupleMeet t))) :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    choose v hv using fun t : Fin (n+1) → B =>
      hsurj t (φ.app (op (tupleMeet t)) (ModuleCat.freeMk (tupleAtMeet t)))
    refine ⟨tupleDesc k n F v, ?_⟩
    apply NatTrans.ext
    funext b
    apply ModuleCat.free_hom_ext
    intro t
    change η.app b ((tupleDesc k n F v).app b (ModuleCat.freeMk t)) =
      φ.app b (ModuleCat.freeMk t)
    rw [tupleDesc_freeMk]
    have h := ConcreteCategory.congr_hom (η.naturality (tupleSourceMap t)) (v t.val)
    simp only [ModuleCat.comp_apply] at h
    rw [h, hv]
    exact (tupleMap_generator k n G φ b t).symm

/-- The genuine augmented simplicial module diagram. -/
def tupleAugmented : SimplicialObject.Augmented (Bᵒᵖ ⥤ ModuleCat.{u} k) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj (freeTupleDiagrams k)).obj
    upperTupleAugmented

/-- The tuple chain complex, before any finite replacement. -/
def tupleComplex : ChainComplex (Bᵒᵖ ⥤ ModuleCat.{u} k) ℕ :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj (tupleAugmented k (B := B)).left

/-- The actual simplicial augmentation, including its degree-zero map. -/
def tupleAugmentation : tupleComplex k (B := B) ⟶
    (ChainComplex.single₀ (Bᵒᵖ ⥤ ModuleCat.{u} k)).obj (tupleAugmented k).right :=
  AlgebraicTopology.AlternatingFaceMapComplex.ε.app (tupleAugmented k)

instance tupleComplex_projective (n : ℕ) :
    Projective ((tupleComplex k (B := B)).X n) :=
  tupleModule_projective k n

end ToricPower.FiniteCech

end
