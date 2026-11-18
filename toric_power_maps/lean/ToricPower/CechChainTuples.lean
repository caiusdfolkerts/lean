module

public import ToricPower.CechIncidenceChains
public import TauCeti.AlgebraicTopology.SimplicialComplex.OrderComplex

/-!
# All chain tuples and genuine contractions on bounded downsets

The underlying complex is TauCeti's actual order complex: its faces are
nonempty finite chains. We retain every tuple with such a support, including
repeated or differently ordered vertices. Both monotone and antitone maps
therefore give literal tuplewise simplicial maps. No reversal sign or
assumed subdivision comparison is used.

A downset bounded by an element has a genuine cone apex. The explicit
incidence extra degeneracy supplies its augmented and positive exactness.
Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open ToricPower.NegativeSupportCech ToricPower.CechIncidenceChains
open scoped Classical Simplicial

namespace ToricPower.CechChainTuples

section FaceTuples

variable {Vertex : Type} (K : PreAbstractSimplicialComplex Vertex)

/-- The actual face-to-vertex membership relation. -/
def faceIncidence (face : {s : Finset Vertex // s ∈ K}) (vertex : Vertex) : Prop :=
  vertex ∈ face.val

/-- The negative nerve of face membership is the original complex,
proved using its actual downward-closure property. -/
theorem faceIncidenceComplex_eq :
    negativeChartComplex (faceIncidence K) (fun _ => True) = K := by
  apply PreAbstractSimplicialComplex.ext
  ext face
  constructor
  · rintro ⟨nonempty, witness, _, contains⟩
    exact (K.isRelLowerSet_faces witness.property).2 contains nonempty
  · intro present
    exact ⟨(K.isRelLowerSet_faces present).1, ⟨face, present⟩, trivial,
      fun _ member => member⟩

/-- A tuple is allowed precisely when its actual finite vertex support
is a face of the given complex. -/
theorem faceTupleAllowed_iff (degree : ℕ) (tuple : Fin (degree + 1) → Vertex) :
    tupleForbidden (faceIncidence K) (fun _ => True) degree tuple ↔
      Finset.univ.image tuple ∈ K := by
  rw [tupleForbidden_iff_face, faceIncidenceComplex_eq]

abbrev faceTupleSet : SSet := incidenceSimplicialSet (faceIncidence K) (fun _ => True)

abbrev faceTupleChains : ChainComplex AddCommGrpCat ℕ :=
  incidenceChains (faceIncidence K) (fun _ => True)

abbrev faceTupleAugmentation : (faceTupleChains K).X 0 ⟶ incidenceAugmentationObject :=
  incidenceChainAugmentation (faceIncidence K) (fun _ => True)

theorem faceIncidence_isCone (anchor : Vertex) (cone : PreAbstractSimplicialComplex.IsCone K anchor) :
    PreAbstractSimplicialComplex.IsCone
      (negativeChartComplex (faceIncidence K) (fun _ => True)) anchor := by
  rw [faceIncidenceComplex_eq]
  exact cone

/-- Actual augmented exactness, obtained from the explicit cone contraction. -/
theorem faceTupleChains_augmentedExact (anchor : Vertex)
    (cone : PreAbstractSimplicialComplex.IsCone K anchor) :
    (ShortComplex.mk ((faceTupleChains K).d 1 0) (faceTupleAugmentation K)
      (incidenceChainAugmentation_zero (faceIncidence K) (fun _ => True))).Exact :=
  incidenceConeChains_augmentedExact (faceIncidence K) (fun _ => True) anchor
    (faceIncidence_isCone K anchor cone)

theorem faceTupleChains_exactAt_positive (anchor : Vertex)
    (cone : PreAbstractSimplicialComplex.IsCone K anchor) (degree : ℕ) :
    (faceTupleChains K).ExactAt (degree + 1) :=
  incidenceConeChains_exactAt_positive (faceIncidence K) (fun _ => True) anchor
    (faceIncidence_isCone K anchor cone) degree

end FaceTuples

section OrderTuples

variable (P : Type) [Preorder P]

abbrev orderTupleSet : SSet :=
  faceTupleSet (TauCeti.AbstractSimplicialComplex.orderComplex P).toPreAbstractSimplicialComplex

abbrev orderTupleChains : ChainComplex AddCommGrpCat ℕ :=
  (orderTupleSet P).chainComplex (AddCommGrpCat.of ℤ)

abbrev orderTupleAugmentation : (orderTupleChains P).X 0 ⟶ incidenceAugmentationObject :=
  faceTupleAugmentation
    (TauCeti.AbstractSimplicialComplex.orderComplex P).toPreAbstractSimplicialComplex

/-- Literal recognition of all chain tuples; no monotonicity of their
index order is required. -/
theorem orderTupleAllowed_iff (degree : ℕ) (tuple : Fin (degree + 1) → P) :
    tupleForbidden
      (faceIncidence (TauCeti.AbstractSimplicialComplex.orderComplex P).toPreAbstractSimplicialComplex)
      (fun _ => True) degree tuple ↔
        ∀ first second, tuple first ≤ tuple second ∨ tuple second ≤ tuple first := by
  rw [faceTupleAllowed_iff,
    AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex,
    TauCeti.AbstractSimplicialComplex.mem_orderComplex_iff']
  constructor
  · rintro ⟨_, comparable⟩ first second
    exact comparable _ (Finset.mem_image.mpr ⟨first, Finset.mem_univ _, rfl⟩)
      _ (Finset.mem_image.mpr ⟨second, Finset.mem_univ _, rfl⟩)
  · intro comparable
    refine ⟨⟨tuple 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩, ?_⟩
    intro first first_mem second second_mem
    obtain ⟨first, _, rfl⟩ := Finset.mem_image.mp first_mem
    obtain ⟨second, _, rfl⟩ := Finset.mem_image.mp second_mem
    exact comparable first second

variable {P} {Q S : Type} [Preorder Q] [Preorder S]

/-- Any map preserving comparability acts on the actual chain tuples. -/
def orderTupleMap (f : P → Q)
    (comparable : ∀ p q, p ≤ q ∨ q ≤ p → f p ≤ f q ∨ f q ≤ f p) :
    orderTupleSet P ⟶ orderTupleSet Q where
  app simplex := ↾fun tuple => ⟨f ∘ tuple.val, by
    apply (orderTupleAllowed_iff Q simplex.unop.len _).mpr
    intro first second
    exact comparable _ _ ((orderTupleAllowed_iff P simplex.unop.len tuple.val).mp
      tuple.property first second)⟩
  naturality {source target} selection := by
    apply ConcreteCategory.hom_ext
    intro tuple
    apply Subtype.ext
    rfl

@[simp]
theorem orderTupleMap_apply (f : P → Q)
    (comparable : ∀ p q, p ≤ q ∨ q ≤ p → f p ≤ f q ∨ f q ≤ f p)
    (degree : ℕ) (tuple : (orderTupleSet P) _⦋degree⦌) :
    ((orderTupleMap f comparable).app _ tuple).val = f ∘ tuple.val := rfl

def monotoneOrderTupleMap (f : P → Q) (monotone : Monotone f) :
    orderTupleSet P ⟶ orderTupleSet Q :=
  orderTupleMap f (fun _ _ h => h.elim
    (fun h => Or.inl (monotone h)) (fun h => Or.inr (monotone h)))

def antitoneOrderTupleMap (f : P → Q) (antitone : Antitone f) :
    orderTupleSet P ⟶ orderTupleSet Q :=
  orderTupleMap f (fun _ _ h => h.elim
    (fun h => Or.inr (antitone h)) (fun h => Or.inl (antitone h)))

theorem orderTupleMap_id (comparable : ∀ p q : P, p ≤ q ∨ q ≤ p → p ≤ q ∨ q ≤ p) :
    orderTupleMap id comparable = 𝟙 (orderTupleSet P) := by
  ext simplex tuple
  apply Subtype.ext
  rfl

theorem orderTupleMap_comp (f : P → Q) (g : Q → S)
    (hf : ∀ p q, p ≤ q ∨ q ≤ p → f p ≤ f q ∨ f q ≤ f p)
    (hg : ∀ p q, p ≤ q ∨ q ≤ p → g p ≤ g q ∨ g q ≤ g p)
    (hgf : ∀ p q, p ≤ q ∨ q ≤ p → g (f p) ≤ g (f q) ∨ g (f q) ≤ g (f p)) :
    orderTupleMap f hf ≫ orderTupleMap g hg = orderTupleMap (g ∘ f) hgf := by
  ext simplex tuple
  apply Subtype.ext
  rfl

theorem orderTupleMap_component_injective (f : P → Q)
    (comparable : ∀ p q, p ≤ q ∨ q ≤ p → f p ≤ f q ∨ f q ≤ f p)
    (injective : Function.Injective f) (simplex : SimplexCategoryᵒᵖ) :
    Function.Injective ((orderTupleMap f comparable).app simplex) := by
  intro first second same
  apply Subtype.ext
  funext column
  apply injective
  exact congrFun (congrArg (fun tuple : (orderTupleSet Q).obj simplex => tuple.val) same) column

theorem orderTupleChainMap_mono (f : P → Q)
    (comparable : ∀ p q, p ≤ q ∨ q ≤ p → f p ≤ f q ∨ f q ≤ f p)
    (injective : Function.Injective f) (degree : ℕ) :
    Mono ((SSet.chainComplexMap (orderTupleMap f comparable) (AddCommGrpCat.of ℤ)).f degree) := by
  let mapping := orderTupleMap f comparable
  letI : ∀ simplex, Mono (mapping.app simplex) := fun simplex =>
    (CategoryTheory.mono_iff_injective _).mpr
      (orderTupleMap_component_injective f comparable injective simplex)
  letI : Mono mapping := NatTrans.mono_of_mono_app mapping
  exact inferInstanceAs (Mono ((SSet.chainComplexMap (SSetPair.of mapping).hom
    (AddCommGrpCat.of ℤ)).f degree))

/-- Every tuplewise chain map preserves the actual constant augmentation. -/
theorem orderTupleChainMap_augmentation (f : P → Q)
    (comparable : ∀ p q, p ≤ q ∨ q ≤ p → f p ≤ f q ∨ f q ≤ f p) :
    (SSet.chainComplexMap (orderTupleMap f comparable) (AddCommGrpCat.of ℤ)).f 0 ≫
      orderTupleAugmentation Q = orderTupleAugmentation P := by
  apply SSet.chainComplex_hom_ext
  intro tuple
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  exact (incidenceChainAugmentation_generator _ _ _).trans
    (incidenceChainAugmentation_generator _ _ _).symm

end OrderTuples

section FiniteChainMaximum

variable {P : Type} [Preorder P]

/-- A nonempty finite chain has a greatest member. The proof only compares
members of the given chain; no linear order on the ambient type is assumed. -/
theorem finiteChain_exists_greatest (face : Finset P)
    (nonempty : face.Nonempty)
    (comparable : ∀ p ∈ face, ∀ q ∈ face, p ≤ q ∨ q ≤ p) :
    ∃ greatest ∈ face, ∀ p ∈ face, p ≤ greatest := by
  classical
  revert nonempty comparable
  induction face using Finset.induction_on with
  | empty =>
    intro nonempty _
    simp at nonempty
  | @insert p face absent ih =>
    intro _ comparable
    by_cases nonempty : face.Nonempty
    · obtain ⟨q, member, greatest⟩ := ih nonempty (fun x hx y hy =>
        comparable x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy))
      rcases comparable p (Finset.mem_insert_self _ _) q (Finset.mem_insert_of_mem member) with hpq | hqp
      · refine ⟨q, Finset.mem_insert_of_mem member, ?_⟩
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hpq
        · exact greatest x hx
      · refine ⟨p, Finset.mem_insert_self _ _, ?_⟩
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact le_rfl
        · exact (greatest x hx).trans hqp
    · refine ⟨p, Finset.mem_insert_self _ _, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact le_rfl
      · exact (nonempty ⟨x, hx⟩).elim

theorem orderTuple_exists_greatest {degree : ℕ} (tuple : (orderTupleSet P) _⦋degree⦌) :
    ∃ greatest ∈ Finset.univ.image tuple.val, ∀ column, tuple.val column ≤ greatest := by
  have comparable := (orderTupleAllowed_iff P degree tuple.val).mp tuple.property
  obtain ⟨greatest, present, bound⟩ := finiteChain_exists_greatest (Finset.univ.image tuple.val)
    ⟨tuple.val 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩ (by
      intro p hp q hq
      obtain ⟨first, _, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨second, _, rfl⟩ := Finset.mem_image.mp hq
      exact comparable first second)
  exact ⟨greatest, present, fun column => bound _
    (Finset.mem_image.mpr ⟨column, Finset.mem_univ _, rfl⟩)⟩

/-- A selected actual member of the tuple support that bounds every term. -/
def greatestValue {degree : ℕ} (tuple : (orderTupleSet P) _⦋degree⦌) : P :=
  (orderTuple_exists_greatest tuple).choose

theorem greatestValue_mem {degree : ℕ} (tuple : (orderTupleSet P) _⦋degree⦌) :
    greatestValue tuple ∈ Finset.univ.image tuple.val :=
  (orderTuple_exists_greatest tuple).choose_spec.1

theorem tuple_le_greatest {degree : ℕ} (tuple : (orderTupleSet P) _⦋degree⦌)
    (column : Fin (degree + 1)) : tuple.val column ≤ greatestValue tuple :=
  (orderTuple_exists_greatest tuple).choose_spec.2 column

theorem greatestValue_is_term {degree : ℕ} (tuple : (orderTupleSet P) _⦋degree⦌) :
    ∃ column, tuple.val column = greatestValue tuple := by
  obtain ⟨column, _, same⟩ := Finset.mem_image.mp (greatestValue_mem tuple)
  exact ⟨column, same⟩

theorem greatestValue_le_of_bound {degree : ℕ} (tuple : (orderTupleSet P) _⦋degree⦌)
    (bound : P) (bounds : ∀ column, tuple.val column ≤ bound) : greatestValue tuple ≤ bound := by
  obtain ⟨column, same⟩ := greatestValue_is_term tuple
  rw [← same]
  exact bounds column

def orderTupleSelect {degree next : ℕ}
    (selection : Fin (degree + 1) → Fin (next + 1))
    (tuple : (orderTupleSet P) _⦋next⦌) : (orderTupleSet P) _⦋degree⦌ :=
  ⟨tuple.val ∘ selection, (orderTupleAllowed_iff P degree _).mpr (fun first second =>
    (orderTupleAllowed_iff P next tuple.val).mp tuple.property (selection first) (selection second))⟩

theorem greatest_precomp_le {degree next : ℕ}
    (selection : Fin (degree + 1) → Fin (next + 1))
    (tuple : (orderTupleSet P) _⦋next⦌) :
    greatestValue (orderTupleSelect selection tuple) ≤ greatestValue tuple := by
  apply greatestValue_le_of_bound
  intro column
  exact tuple_le_greatest tuple (selection column)

theorem greatest_face_le (degree : ℕ) (deleted : Fin (degree + 2))
    (tuple : (orderTupleSet P) _⦋degree + 1⦌) :
    greatestValue ((orderTupleSet P).δ deleted tuple) ≤ greatestValue tuple := by
  apply greatestValue_le_of_bound
  intro column
  exact tuple_le_greatest tuple (deleted.succAbove column)

theorem greatest_map_le {Q : Type} [Preorder Q] (f : P → Q) (monotone : Monotone f)
    {degree : ℕ} (tuple : (orderTupleSet P) _⦋degree⦌) :
    greatestValue ((monotoneOrderTupleMap f monotone).app _ tuple) ≤ f (greatestValue tuple) := by
  apply greatestValue_le_of_bound
  intro column
  exact monotone (tuple_le_greatest tuple column)

end FiniteChainMaximum

section Cones

variable {P : Type} [Preorder P]

/-- The order complex of a preorder with a greatest element is an actual cone. -/
theorem orderComplex_isCone_of_greatest (apex : P) (greatest : ∀ p, p ≤ apex) :
    PreAbstractSimplicialComplex.IsCone
      (TauCeti.AbstractSimplicialComplex.orderComplex P).toPreAbstractSimplicialComplex apex := by
  constructor
  · exact (TauCeti.AbstractSimplicialComplex.orderComplex P).singleton_mem apex
  · intro face present
    rw [AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex,
      TauCeti.AbstractSimplicialComplex.mem_orderComplex_iff'] at present ⊢
    refine ⟨Finset.insert_nonempty _ _, ?_⟩
    intro first first_mem second second_mem
    rcases Finset.mem_insert.mp first_mem with rfl | first_mem
    · exact Or.inr (greatest second)
    · rcases Finset.mem_insert.mp second_mem with rfl | second_mem
      · exact Or.inl (greatest first)
      · exact present.2 first first_mem second second_mem

/-- The actual bounded downset, with its inherited order. -/
abbrev BoundedDownset (apex : P) := {p : P // p ≤ apex}

theorem boundedDownset_isCone (apex : P) :
    @PreAbstractSimplicialComplex.IsCone (BoundedDownset apex) (Classical.decEq _)
      (TauCeti.AbstractSimplicialComplex.orderComplex (BoundedDownset apex)).toPreAbstractSimplicialComplex
      ⟨apex, le_rfl⟩ :=
  orderComplex_isCone_of_greatest (P := BoundedDownset apex)
    ⟨apex, le_rfl⟩ (fun p => p.property)

def boundedDownsetInclusion (apex : P) :
    orderTupleSet (BoundedDownset apex) ⟶ orderTupleSet P :=
  monotoneOrderTupleMap Subtype.val (fun _ _ h => h)

def boundedDownsetRefinement {first second : P} (h : first ≤ second) :
    orderTupleSet (BoundedDownset first) ⟶ orderTupleSet (BoundedDownset second) :=
  monotoneOrderTupleMap (fun p => ⟨p.val, p.property.trans h⟩) (fun _ _ h => h)

theorem boundedDownsetRefinement_inclusion {first second : P} (h : first ≤ second) :
    boundedDownsetRefinement h ≫ boundedDownsetInclusion second = boundedDownsetInclusion first := by
  ext simplex tuple
  apply Subtype.ext
  rfl

theorem boundedDownset_augmentedExact (apex : P) :
    (ShortComplex.mk ((orderTupleChains (BoundedDownset apex)).d 1 0)
      (orderTupleAugmentation (BoundedDownset apex))
      (incidenceChainAugmentation_zero _ _)).Exact :=
  faceTupleChains_augmentedExact _ ⟨apex, le_rfl⟩ (boundedDownset_isCone apex)

theorem boundedDownset_exactAt_positive (apex : P) (degree : ℕ) :
    (orderTupleChains (BoundedDownset apex)).ExactAt (degree + 1) :=
  faceTupleChains_exactAt_positive _ ⟨apex, le_rfl⟩ (boundedDownset_isCone apex) degree

end Cones

section SimplexTuples

variable {Vertex : Type} {Ray : Type*}

/-- A literal simplex on a specified finite set of the original vertices. -/
def simplexIncidence (face : Finset Vertex) (_point : Unit) (vertex : Vertex) : Prop :=
  vertex ∈ face

abbrev simplexTupleSet (face : Finset Vertex) : SSet :=
  incidenceSimplicialSet (simplexIncidence face) (fun _ => True)

abbrev simplexTupleChains (face : Finset Vertex) : ChainComplex AddCommGrpCat ℕ :=
  incidenceChains (simplexIncidence face) (fun _ => True)

abbrev simplexTupleAugmentation (face : Finset Vertex) :
    (simplexTupleChains face).X 0 ⟶ incidenceAugmentationObject :=
  incidenceChainAugmentation (simplexIncidence face) (fun _ => True)

theorem simplexTupleAllowed_iff (face : Finset Vertex) (degree : ℕ)
    (tuple : Fin (degree + 1) → Vertex) :
    tupleForbidden (simplexIncidence face) (fun _ => True) degree tuple ↔
      ∀ column, tuple column ∈ face := by
  constructor
  · rintro ⟨_, _, contains⟩
    exact contains
  · intro contains
    exact ⟨(), trivial, contains⟩

def simplexTupleRefinement {smaller larger : Finset Vertex} (subset : smaller ⊆ larger) :
    simplexTupleSet smaller ⟶ simplexTupleSet larger where
  app simplex := ↾fun tuple => ⟨tuple.val, ⟨(), trivial, fun column =>
    subset ((simplexTupleAllowed_iff smaller simplex.unop.len tuple.val).mp tuple.property column)⟩⟩
  naturality {source target} selection := by
    apply ConcreteCategory.hom_ext
    intro tuple
    apply Subtype.ext
    rfl

/-- A simplex supported on an actual face includes in the actual
incidence nerve by retaining exactly the original vertex tuple. -/
def simplexTupleInclusion (incidence : Ray → Vertex → Prop) (negative : Ray → Prop)
    (face : Finset Vertex) (present : face ∈ negativeChartComplex incidence negative) :
    simplexTupleSet face ⟶ incidenceSimplicialSet incidence negative where
  app simplex := ↾fun tuple => ⟨tuple.val, by
    obtain ⟨_, ray, negativeRay, contains⟩ := present
    exact ⟨ray, negativeRay, fun column => contains _
      ((simplexTupleAllowed_iff face simplex.unop.len tuple.val).mp tuple.property column)⟩⟩
  naturality {source target} selection := by
    apply ConcreteCategory.hom_ext
    intro tuple
    apply Subtype.ext
    rfl

theorem simplexTupleRefinement_inclusion
    (incidence : Ray → Vertex → Prop) (negative : Ray → Prop)
    {smaller larger : Finset Vertex} (subset : smaller ⊆ larger)
    (smallerPresent : smaller ∈ negativeChartComplex incidence negative)
    (largerPresent : larger ∈ negativeChartComplex incidence negative) :
    simplexTupleRefinement subset ≫ simplexTupleInclusion incidence negative larger largerPresent =
      simplexTupleInclusion incidence negative smaller smallerPresent := by
  ext simplex tuple
  apply Subtype.ext
  rfl

def simplexTupleChainInclusion (incidence : Ray → Vertex → Prop) (negative : Ray → Prop)
    (face : Finset Vertex) (present : face ∈ negativeChartComplex incidence negative) :
    simplexTupleChains face ⟶ incidenceChains incidence negative :=
  SSet.chainComplexMap (simplexTupleInclusion incidence negative face present) (AddCommGrpCat.of ℤ)

theorem simplexTupleChainInclusion_mono
    (incidence : Ray → Vertex → Prop) (negative : Ray → Prop)
    (face : Finset Vertex) (present : face ∈ negativeChartComplex incidence negative)
    (degree : ℕ) : Mono ((simplexTupleChainInclusion incidence negative face present).f degree) := by
  let inclusion := simplexTupleInclusion incidence negative face present
  letI : ∀ simplex, Mono (inclusion.app simplex) := fun simplex =>
    (CategoryTheory.mono_iff_injective _).mpr (by
      intro first second equality
      apply Subtype.ext
      exact congrArg (fun tuple : (incidenceSimplicialSet incidence negative).obj simplex => tuple.val)
        equality)
  letI : Mono inclusion := NatTrans.mono_of_mono_app inclusion
  exact inferInstanceAs (Mono ((SSet.chainComplexMap (SSetPair.of inclusion).hom
    (AddCommGrpCat.of ℤ)).f degree))

theorem simplexTupleChainInclusion_augmentation
    (incidence : Ray → Vertex → Prop) (negative : Ray → Prop)
    (face : Finset Vertex) (present : face ∈ negativeChartComplex incidence negative) :
    (simplexTupleChainInclusion incidence negative face present).f 0 ≫
      incidenceChainAugmentation incidence negative = simplexTupleAugmentation face := by
  apply SSet.chainComplex_hom_ext
  intro tuple
  rw [← Category.assoc, simplexTupleChainInclusion, SSet.ι_chainComplexMap_f]
  exact (incidenceChainAugmentation_generator _ _ _).trans
    (incidenceChainAugmentation_generator _ _ _).symm

theorem simplexTuple_isCone (face : Finset Vertex) (anchor : Vertex) (member : anchor ∈ face) :
    PreAbstractSimplicialComplex.IsCone
      (negativeChartComplex (simplexIncidence face) (fun _ => True)) anchor := by
  constructor
  · refine ⟨Finset.singleton_nonempty anchor, (), trivial, ?_⟩
    intro vertex present
    have same : vertex = anchor := Finset.mem_singleton.mp present
    simpa only [simplexIncidence, same] using member
  · intro support present
    obtain ⟨nonempty, _, _, contains⟩ := present
    refine ⟨Finset.insert_nonempty _ _, (), trivial, ?_⟩
    intro vertex present
    rcases Finset.mem_insert.mp present with rfl | present
    · exact member
    · exact contains _ present

theorem simplexTuple_augmentedExact (face : Finset Vertex) (nonempty : face.Nonempty) :
    (ShortComplex.mk ((simplexTupleChains face).d 1 0) (simplexTupleAugmentation face)
      (incidenceChainAugmentation_zero _ _)).Exact := by
  obtain ⟨anchor, member⟩ := nonempty
  exact incidenceConeChains_augmentedExact _ _ anchor (simplexTuple_isCone face anchor member)

theorem simplexTuple_exactAt_positive (face : Finset Vertex)
    (nonempty : face.Nonempty) (degree : ℕ) :
    (simplexTupleChains face).ExactAt (degree + 1) := by
  obtain ⟨anchor, member⟩ := nonempty
  exact incidenceConeChains_exactAt_positive _ _ anchor (simplexTuple_isCone face anchor member) degree

end SimplexTuples

end ToricPower.CechChainTuples
