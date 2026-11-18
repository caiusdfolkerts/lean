module

public import Recovery.Unimodular.WeakFano.EffectiveAllowed
public import Recovery.Unimodular.WeakFano.EffectiveRank
public import Recovery.Unimodular.WeakFano.EffectiveMatrixGeometry

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Set

namespace Unimodular.EffectiveMatrix

variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

/-- All original full-dimensional allowed blocks, with no simpliciality restriction. -/
def fullTest (u : E → Lattice n) (s : Finset E) : Prop :=
  EffectiveAllowed.test u s ∧ EffectiveRank.rankEquals u s n

instance (u : E → Lattice n) (s : Finset E) : Decidable (fullTest u s) := by
  unfold fullTest
  infer_instance

def columns (u : E → Lattice n) : Finset (Finset E) := Finset.univ.filter (fullTest u)

/-- Invalid columns are excluded, rather than padded with zero entries. -/
def Column (u : E → Lattice n) := {s : Finset E // fullTest u s}

instance (u : E → Lattice n) : Fintype (Column u) :=
  Fintype.subtype (columns u) (fun s => by simp only [columns, Finset.mem_filter,
    Finset.mem_univ, true_and])

instance (u : E → Lattice n) : DecidableEq (Column u) :=
  inferInstanceAs (DecidableEq {s : Finset E // fullTest u s})

/-- Every finite label set and every finite cofactor candidate is a row code.
Accepted rows include every allowed facet; unused codes contribute zero rows. -/
abbrev Row (n : ℕ) (E : Type*) := Finset E × ((Fin n → E) × Fin n)

def rowTest (u : E → Lattice n) (r : Row n E) : Prop :=
  EffectiveAllowed.test u r.1 ∧ 0 < n ∧
    EffectiveRank.rankEquals u r.1 (n - 1) ∧
    EffectiveMatrixGeometry.normalTest u r.1 r.2

instance (u : E → Lattice n) (r : Row n E) : Decidable (rowTest u r) := by
  unfold rowTest
  infer_instance

/-- Integer side sign at the literal sum of the parent cone's generators.
The incidence predicate decides actual faces, including nonsimplicial ones. -/
def boundaryEntry (u : E → Lattice n) (r : Row n E) (s : Column u) : ℤ :=
  if rowTest u r ∧ EffectiveAllowed.faceTest u r.1 s.val then
    EffectiveMatrixGeometry.sign
      (EffectiveDirection.rowForm (u ∘ r.2.1) r.2.2
        (EffectiveMatrixGeometry.center (fun e : {e // e ∈ s.val} => u e.val)))
  else 0

/-- The degree row uses the computed generic integer direction and total
integer cone membership; no real-membership oracle is an input. -/
def degreeEntry (u : E → Lattice n) (s : Column u) : ℤ :=
  if EffectiveConeDecision.contains (fun e : {e // e ∈ s.val} => u e.val)
      (EffectiveDirection.direction u) = true then 1 else 0

def matrix (u : E → Lattice n) : Matrix (Option (Row n E)) (Column u) ℤ :=
  fun r s => r.elim (degreeEntry u s) (fun r => boundaryEntry u r s)

/-- The executable finite integer equation map. -/
def equation (u : E → Lattice n) : (Column u → ℤ) →+ (Option (Row n E) → ℤ) where
  toFun c r := ∑ s, matrix u r s * c s
  map_zero' := by ext r; simp
  map_add' c d := by ext r; simp [mul_add, Finset.sum_add_distrib]

def target : Option (Row n E) → ℤ := fun r => r.elim 1 (fun _ => 0)

@[simp] theorem equation_none (u : E → Lattice n) (c : Column u → ℤ) :
    equation u c none = ∑ s, degreeEntry u s * c s := rfl

@[simp] theorem equation_some (u : E → Lattice n) (c : Column u → ℤ) (r : Row n E) :
    equation u c (some r) = ∑ s, boundaryEntry u r s * c s := rfl

noncomputable section
attribute [local instance] Classical.propDecidable

local notation "ι₀" => EffectiveAllowed.embedding n

/-- Literal agreement of the original geometric block span with the tested span. -/
theorem block_span (u : E → Lattice n) (s : Finset E) :
    Submodule.span ℝ (AllowedBlocks.blockCone ι₀ u s : Set (Ambient n)) =
      RayHyperplanes.raySpan (fun e => embed (u e)) s :=
  RayHyperplanes.span_hull_eq _

theorem fullTest_iff (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0) (s : Finset E) :
    fullTest u s ↔ AllowedBlocks.Allowed ι₀ u s ∧
      Submodule.span ℝ (AllowedBlocks.blockCone ι₀ u s : Set (Ambient n)) = ⊤ := by
  have hn : Module.finrank ℝ (Ambient n) = n := by simp [Ambient]
  rw [fullTest, EffectiveAllowed.test_iff u hnz, EffectiveRank.rankEquals_iff,
    AllowedBlocks.full_rank_iff, hn, block_span]

/-- A genuine equivalence with the paper's full column family; the finite
label set itself is unchanged in both directions. -/
def columnEquiv (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0) :
    Column u ≃ AllowedBlocks.FullBlock ι₀ u where
  toFun s := ⟨s.val, (fullTest_iff u hnz s.val).1 s.property⟩
  invFun s := ⟨s.val, (fullTest_iff u hnz s.val).2 s.property⟩
  left_inv s := Subtype.ext rfl
  right_inv s := Subtype.ext rfl

@[simp] theorem columnEquiv_val (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (s : Column u) : (columnEquiv u hnz s).val = s.val := rfl

@[simp] theorem columnEquiv_symm_val (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (s : AllowedBlocks.FullBlock ι₀ u) : ((columnEquiv u hnz).symm s).val = s.val := rfl

/-- Coefficient reindexing is only a coordinate permutation. -/
def coefficientEquiv (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0) :
    (Column u → ℤ) ≃+ (AllowedBlocks.FullBlock ι₀ u → ℤ) where
  toFun c s := c ((columnEquiv u hnz).symm s)
  invFun c s := c (columnEquiv u hnz s)
  left_inv c := by ext s; simp
  right_inv c := by ext s; simp
  map_add' c d := rfl

@[simp] theorem coefficientEquiv_apply_column (u : E → Lattice n)
    (hnz : ∀ e, embed (u e) ≠ 0) (c : Column u → ℤ) (s : Column u) :
    coefficientEquiv u hnz c (columnEquiv u hnz s) = c s := by
  change c ((columnEquiv u hnz).symm (columnEquiv u hnz s)) = c s
  rw [Equiv.symm_apply_apply]

/-- Every accepted finite row represents an actual allowed facet block. -/
def facetOfRow (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (r : Row n E) (hr : rowTest u r) : AllowedBlocks.FacetBlock ι₀ u := by
  refine ⟨r.1, (EffectiveAllowed.test_iff u hnz r.1).1 hr.1, ?_⟩
  rw [block_span]
  have hd := (EffectiveRank.rankEquals_iff u r.1 (n - 1)).1 hr.2.2.1
  have hn : Module.finrank ℝ (Ambient n) = n := by simp [Ambient]
  rw [hn]
  have hp : 0 < n := hr.2.1
  omega

@[simp] theorem facetOfRow_val (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (r : Row n E) (hr : rowTest u r) : (facetOfRow u hnz r hr).val = r.1 := rfl

/-- The finite row family covers every original facet, including facets
without a full coface. No chosen normal is supplied to the algorithm. -/
theorem exists_row_for_facet (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (b : AllowedBlocks.FacetBlock ι₀ u) :
    ∃ (r : Row n E) (hr : rowTest u r), facetOfRow u hnz r hr = b := by
  have hd : Module.finrank ℝ (RayHyperplanes.raySpan (fun e => embed (u e)) b.val) + 1 = n := by
    have h := b.property.2
    rw [block_span] at h
    simpa [Ambient] using h
  obtain ⟨p, hp⟩ := EffectiveMatrixGeometry.exists_normalTest u hspan b.val hd
  have hr : rowTest u (b.val, p) := by
    refine ⟨(EffectiveAllowed.test_iff u hnz b.val).2 b.property.1, ?_, ?_, hp⟩
    · omega
    · apply (EffectiveRank.rankEquals_iff u b.val (n - 1)).2
      omega
  exact ⟨(b.val, p), hr, Subtype.ext rfl⟩

end
end Unimodular.EffectiveMatrix

#print axioms Unimodular.EffectiveMatrix.matrix
#print axioms Unimodular.EffectiveMatrix.columnEquiv
#print axioms Unimodular.EffectiveMatrix.exists_row_for_facet
#check Unimodular.EffectiveMatrix.exists_row_for_facet
