module

public import Recovery.Unimodular.WeakFano.EffectiveFaces
public import Unimodular.AllowedBlocks

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Set TauCeti.Toric

namespace Unimodular.EffectiveAllowed

variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

/-- Exactly the input labels lying on one generated ray, computed by the
proved integer cone decision. Parallel repeated labels are retained. -/
def onRay (u : E → Lattice n) (e : E) : Finset E :=
  Finset.univ.filter (fun j => EffectiveConeDecision.contains (fun _ : Fin 1 => u e) (u j) = true)

def rayTest (u : E → Lattice n) (e : E) : Prop :=
  EffectiveFaces.test u (onRay u e)

instance (u : E → Lattice n) (e : E) : Decidable (rayTest u e) :=
  inferInstanceAs (Decidable (EffectiveFaces.test u (onRay u e)))

/-- The three allowed-block conditions, computed from finite integral input. -/
def test (u : E → Lattice n) (s : Finset E) : Prop :=
  EffectiveFaces.salientTest (fun e : {e // e ∈ s} => u e.val) ∧
    (∀ e : {e // e ∈ s}, rayTest (fun j : {e // e ∈ s} => u j.val) e) ∧
    (∀ e, EffectiveConeDecision.contains (fun j : {e // e ∈ s} => u j.val) (u e) = true ↔ e ∈ s)

instance (u : E → Lattice n) (s : Finset E) : Decidable (test u s) := by
  unfold test
  infer_instance

def blocks (u : E → Lattice n) : Finset (Finset E) := Finset.univ.filter (test u)

/-- Proposed face labels inside the finite parent-column index. -/
def subLabels (t s : Finset E) : Finset {e // e ∈ s} :=
  Finset.univ.filter (fun e => e.val ∈ t)

def faceTest (u : E → Lattice n) (t s : Finset E) : Prop :=
  t ⊆ s ∧ EffectiveFaces.test (fun e : {e // e ∈ s} => u e.val) (subLabels t s)

instance (u : E → Lattice n) (t s : Finset E) : Decidable (faceTest u t s) := by
  unfold faceTest
  infer_instance

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The literal standard lattice embedding; it is used only in correctness
statements, never in the executable predicates. -/
def embedding (n : ℕ) : Lattice n →+ Ambient n where
  toFun := embed
  map_zero' := by ext i; simp [embed]
  map_add' x y := by ext i; simp [embed]

@[simp] theorem embedding_apply (n : ℕ) (x : Lattice n) :
    embedding n x = embed x := rfl

@[simp] theorem mem_onRay (u : E → Lattice n) (e j : E) :
    j ∈ onRay u e ↔ embed (u j) ∈ PointedCone.hull ℝ {embed (u e)} := by
  rw [onRay, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, EffectiveConeDecision.contains_iff, Set.range_const]

/-- All parallel labels generate precisely the original ray. -/
theorem onRay_cone (u : E → Lattice n) (e : E) :
    EffectiveFaces.faceCone u (onRay u e) = PointedCone.hull ℝ {embed (u e)} := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro x ⟨j, hj, rfl⟩
    exact (mem_onRay u e j).1 hj
  · apply Submodule.span_le.2
    rintro x rfl
    exact PointedCone.subset_hull ⟨e, (mem_onRay u e e).2
      (PointedCone.subset_hull (by simp)), rfl⟩

/-- The arithmetic ray test is the literal geometric extreme-ray condition. -/
theorem rayTest_iff (u : E → Lattice n) (e : E) :
    rayTest u e ↔ (PointedCone.hull ℝ {embed (u e)}).IsFaceOf (EffectiveFaces.cone u) := by
  rw [rayTest, EffectiveFaces.test_iff, onRay_cone]
  exact and_iff_left (fun j => (mem_onRay u e j).symm)

/-- Restricting the finite input list has exactly the original block cone. -/
theorem cone_subtype (u : E → Lattice n) (s : Finset E) :
    EffectiveFaces.cone (fun e : {e // e ∈ s} => u e.val) =
      AllowedBlocks.blockCone (embedding n) u s := by
  change PointedCone.hull ℝ (Set.range (fun e : {e // e ∈ s} => embed (u e.val))) =
    PointedCone.hull ℝ ((fun e => embed (u e)) '' (s : Set E))
  apply congrArg (PointedCone.hull ℝ)
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.val, e.property, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨⟨e, he⟩, rfl⟩

/-- The forward part of the extreme-ray list is derived from actual finite
face generation; it is not an extra input to the algorithm. -/
theorem allowed_iff_ray_faces (u : E → Lattice n)
    (hnz : ∀ e, embed (u e) ≠ 0) (s : Finset E) :
    AllowedBlocks.Allowed (embedding n) u s ↔
      (AllowedBlocks.blockCone (embedding n) u s : ConvexCone ℝ (Ambient n)).Salient ∧
      (∀ e ∈ s, (PointedCone.hull ℝ {embed (u e)}).IsFaceOf
        (AllowedBlocks.blockCone (embedding n) u s)) ∧
      (∀ e, embed (u e) ∈ AllowedBlocks.blockCone (embedding n) u s ↔ e ∈ s) := by
  constructor
  · intro h
    refine ⟨h.1, ?_, h.2.2⟩
    intro e he
    exact ((h.2.1 _).2 ⟨e, he, rfl⟩).1
  · rintro ⟨hsal, hray, hsat⟩
    refine ⟨hsal, ?_, hsat⟩
    intro R
    constructor
    · rintro ⟨hR, hd⟩
      let ρ : ToricRay R := ⟨⟨R, PointedCone.IsFaceOf.refl _⟩, hd⟩
      have heq := cone_subtype u s
      have hgen : R = PointedCone.hull ℝ
          ((fun e : {e // e ∈ s} => embed (u e.val)) ''
            {e | embed (u e.val) ∈ R}) :=
        (show (AllowedBlocks.blockCone (embedding n) u s).Face from ⟨R, hR⟩).eq_hull_image heq.symm
      have hex : ∃ e : {e // e ∈ s}, embed (u e.val) ∈ R := by
        by_contra! h
        have hz : {e : {e // e ∈ s} | embed (u e.val) ∈ R} = ∅ := by
          ext e
          simp [h e]
        have hzR : R = ⊥ := by rw [hgen, hz]; simp
        exact ρ.toPointedCone_ne_bot hzR
      obtain ⟨e, he⟩ := hex
      refine ⟨e.val, e.property, ?_⟩
      exact ρ.eq_hull_singleton (hsal.anti hR.le) he (hnz e.val)
    · rintro ⟨e, he, rfl⟩
      exact ⟨hray e he, PointedCone.finrank_span_coe_hull_singleton (hnz e)⟩

/-- Full correctness for every allowed block, including dependent and
nonsimplicial blocks. No uniformity or full-dimensionality premise is needed. -/
theorem test_iff (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0) (s : Finset E) :
    test u s ↔ AllowedBlocks.Allowed (embedding n) u s := by
  rw [allowed_iff_ray_faces u hnz s]
  unfold test
  rw [EffectiveFaces.salientTest_iff, cone_subtype]
  constructor
  · rintro ⟨hs, hr, hsat⟩
    refine ⟨hs, ?_, ?_⟩
    · intro e he
      simpa only [cone_subtype] using
        (rayTest_iff (fun j : {e // e ∈ s} => u j.val) ⟨e, he⟩).1 (hr ⟨e, he⟩)
    · intro e
      rw [← cone_subtype]
      exact (EffectiveConeDecision.contains_iff _ _).symm.trans (hsat e)
  · rintro ⟨hs, hr, hsat⟩
    refine ⟨hs, ?_, ?_⟩
    · intro e
      apply (rayTest_iff _ _).2
      simpa only [cone_subtype] using hr e.val e.property
    · intro e
      rw [EffectiveConeDecision.contains_iff]
      change embed (u e) ∈ EffectiveFaces.cone (fun j : {e // e ∈ s} => u j.val) ↔ e ∈ s
      rw [cone_subtype]
      exact hsat e

/-- Exact executable enumeration of the complete original allowed family. -/
theorem mem_blocks_iff (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0) (s : Finset E) :
    s ∈ blocks u ↔ AllowedBlocks.Allowed (embedding n) u s := by
  simp only [blocks, Finset.mem_filter, Finset.mem_univ, true_and, test_iff u hnz]

theorem subface_cone_eq (u : E → Lattice n) (t s : Finset E) (hts : t ⊆ s) :
    EffectiveFaces.faceCone (fun e : {e // e ∈ s} => u e.val) (subLabels t s) =
      AllowedBlocks.blockCone (embedding n) u t := by
  change PointedCone.hull ℝ
      ((fun e : {e // e ∈ s} => embed (u e.val)) '' (subLabels t s : Set {e // e ∈ s})) =
    PointedCone.hull ℝ ((fun e => embed (u e)) '' (t : Set E))
  apply congrArg (PointedCone.hull ℝ)
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e.val, (Finset.mem_filter.1 he).2, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨⟨e, hts he⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩

/-- Exact face-incidence decision between any two actual allowed blocks;
subset incidence alone is not substituted for nonsimplicial geometric faces. -/
theorem faceTest_iff (u : E → Lattice n) (t s : Finset E)
    (ht : AllowedBlocks.Allowed (embedding n) u t)
    (hs : AllowedBlocks.Allowed (embedding n) u s) :
    faceTest u t s ↔ (AllowedBlocks.blockCone (embedding n) u t).IsFaceOf
      (AllowedBlocks.blockCone (embedding n) u s) := by
  constructor
  · rintro ⟨hts, h⟩
    have hF := (EffectiveFaces.test_iff _ _).1 h |>.1
    simpa only [subface_cone_eq u t s hts, cone_subtype] using hF
  · intro hF
    have hts : t ⊆ s := by
      intro e he
      exact (hs.2.2 e).1 (hF.le ((ht.2.2 e).2 he))
    refine ⟨hts, (EffectiveFaces.test_iff _ _).2 ⟨?_, ?_⟩⟩
    · simpa only [subface_cone_eq u t s hts, cone_subtype] using hF
    · intro e
      rw [subface_cone_eq u t s hts]
      simpa only [subLabels, Finset.mem_filter, Finset.mem_univ, true_and,
        embedding_apply] using ht.2.2 e.val

end
end Unimodular.EffectiveAllowed

#print axioms Unimodular.EffectiveAllowed.blocks
#print axioms Unimodular.EffectiveAllowed.test_iff
#print axioms Unimodular.EffectiveAllowed.mem_blocks_iff
#print axioms Unimodular.EffectiveAllowed.faceTest_iff
#check Unimodular.EffectiveAllowed.mem_blocks_iff
