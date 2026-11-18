module

public import Papers.GraphicalZonotopes.TwoAnchorPureBlocks
public import Papers.GraphicalZonotopes.ThresholdResponse

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

variable {H : Type*} [Fintype H] [LinearOrder H]

structure OrderedTriple (H : Type*) [LinearOrder H] where
  a : H
  b : H
  c : H
  ab : a<b
  bc : b<c

namespace OrderedTriple
variable (T : OrderedTriple H)

def clique : Finset H := {T.a,T.b,T.c}

theorem ac : T.a<T.c := T.ab.trans T.bc

@[simp] theorem card_clique : T.clique.card=3 := by
  simp [clique,T.ab.ne,T.ac.ne,T.bc.ne]

@[simp] theorem a_mem : T.a∈T.clique := by simp [clique]
@[simp] theorem b_mem : T.b∈T.clique := by simp [clique]
@[simp] theorem c_mem : T.c∈T.clique := by simp [clique]

def abPair : PairIn T.clique := orderedPair T.clique T.a T.b T.ab T.a_mem T.b_mem
def acPair : PairIn T.clique := orderedPair T.clique T.a T.c T.ac T.a_mem T.c_mem
def bcPair : PairIn T.clique := orderedPair T.clique T.b T.c T.bc T.b_mem T.c_mem

@[simp] theorem ac_ne_ab : T.acPair≠T.abPair := by
  intro h
  exact T.bc.ne (congrArg (fun e : PairIn T.clique => e.1.1.2) h).symm

@[simp] theorem bc_ne_ab : T.bcPair≠T.abPair := by
  intro h
  exact T.ab.ne (congrArg (fun e : PairIn T.clique => e.1.1.1) h).symm

/-- On a triple, the sum of the two distinguished stars is the distinguished
pair plus the constant pair vector. -/
theorem two_stars_vector :
    starVector T.clique T.a+starVector T.clique T.b=
      pairIndicator {T.abPair}+(fun _ : PairIn T.clique => (1 : ℝ)) := by
  funext e
  have hu : e.1.1.1=T.a ∨ e.1.1.1=T.b ∨ e.1.1.1=T.c := by
    simpa only [clique,mem_insert,mem_singleton] using e.2.1
  have hv : e.1.1.2=T.a ∨ e.1.1.2=T.b ∨ e.1.1.2=T.c := by
    simpa only [clique,mem_insert,mem_singleton] using e.2.2
  have hne : e.1.1.1≠e.1.1.2 := ne_of_lt e.1.2.1
  have he : e=T.abPair ↔
      (T.a=e.1.1.1 ∨ T.a=e.1.1.2) ∧ (T.b=e.1.1.1 ∨ T.b=e.1.1.2) :=
    (pair_contains_two_iff T.clique T.ab T.a_mem T.b_mem e).symm
  simp only [Pi.add_apply,starVector_eq,pairIndicator,mem_singleton,he]
  rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;>
    simp [hu,hv,T.ab.ne,T.ac.ne,T.bc.ne,Ne.symm T.ab.ne,Ne.symm T.ac.ne,Ne.symm T.bc.ne] at hne ⊢

theorem connector_response :
    blockClass T.clique (-pairIndicator {T.abPair})=twoAnchorTarget T.clique T.a T.b := by
  have hz : blockClass T.clique (fun _ : PairIn T.clique => (1 : ℝ))=0 :=
    (blockClass_eq_zero_iff T.clique T.abPair _).mpr ⟨1,fun _ => rfl⟩
  rw [twoAnchorTarget,T.two_stars_vector,map_add,hz,add_zero,map_neg,T.card_clique]
  norm_num

/-- The unique connector column is a genuine negative pure pair module. -/
def pureBlock : WeightedPureBlock T.clique 2 (twoAnchorTarget T.clique T.a T.b) 1 := by
  have hne : blockClass T.clique (-pairIndicator {T.abPair})≠0 := by
    intro hz
    obtain ⟨c,hc⟩ := (blockClass_eq_zero_iff T.clique T.abPair _).mp hz
    have hab := hc T.abPair
    have hac := hc T.acPair
    simp [pairIndicator] at hab hac
    linarith
  exact {
    column := fun _ => -pairIndicator {T.abPair}
    realizable := fun _ => pureRealizable_negative_pair T.clique (by rw [T.card_clique]) T.abPair
    weight := fun _ => 1
    positive := fun _ => by norm_num
    bounded := fun _ => by norm_num
    independent := (linearIndependent_unique_iff).mpr hne
    weighted_sum := by simpa using T.connector_response
  }

def firstRow : HubResponseRow H := pairRow T.clique T.acPair
def secondRow : HubResponseRow H := pairRow T.clique T.bcPair

@[simp] theorem firstRow_clique : rowClique T.firstRow=T.clique := rowClique_pairRow _ _
@[simp] theorem secondRow_clique : rowClique T.secondRow=T.clique := rowClique_pairRow _ _

theorem row_index_eq : rowCliqueIndex T.firstRow=rowCliqueIndex T.secondRow := by
  apply Subtype.ext
  exact T.firstRow_clique.trans T.secondRow_clique.symm

@[simp] theorem threshold_a_first : thresholdSignedStar T.a T.firstRow=1 := by
  rw [thresholdSignedStar,T.firstRow_clique,T.card_clique]
  norm_num [firstRow,acPair,pairRow,orderedPair]

@[simp] theorem threshold_a_second : thresholdSignedStar T.a T.secondRow=0 := by
  simp [thresholdSignedStar,T.secondRow_clique,T.card_clique,secondRow,bcPair,pairRow,orderedPair,
    T.ab.ne,T.ac.ne]

@[simp] theorem threshold_b_first : thresholdSignedStar T.b T.firstRow=0 := by
  simp [thresholdSignedStar,T.firstRow_clique,T.card_clique,firstRow,acPair,pairRow,orderedPair,
    Ne.symm T.ab.ne,T.bc.ne]

@[simp] theorem threshold_b_second : thresholdSignedStar T.b T.secondRow=1 := by
  rw [thresholdSignedStar,T.secondRow_clique,T.card_clique]
  norm_num [secondRow,bcPair,pairRow,orderedPair]

@[simp] theorem pureBlock_first (j : Fin 1) :
    blockCoordinates T.clique (T.pureBlock.column j) T.firstRow=0 := by
  change blockCoordinates T.clique (-pairIndicator {T.abPair}) (pairRow T.clique T.acPair)=0
  rw [blockCoordinates_pairRow]
  simp [pairIndicator]

@[simp] theorem pureBlock_second (j : Fin 1) :
    blockCoordinates T.clique (T.pureBlock.column j) T.secondRow=0 := by
  change blockCoordinates T.clique (-pairIndicator {T.abPair}) (pairRow T.clique T.bcPair)=0
  rw [blockCoordinates_pairRow]
  simp [pairIndicator]

end OrderedTriple
end BooleanModule
end GraphicalZonotopes
