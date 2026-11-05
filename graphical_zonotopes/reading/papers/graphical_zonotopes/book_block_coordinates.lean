module

public import Papers.GraphicalZonotopes.ThresholdResponse
public import Papers.GraphicalZonotopes.PureDecompositions
public import Papers.GraphicalZonotopes.BookCombinatorialCounts
public import Papers.GraphicalZonotopes.BlockFamilies

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

variable {H : Type*} [Fintype H] [LinearOrder H]

def largeBlocks (S : Finset H) : Finset (Finset H) :=
  S.powerset.filter (fun C => 3≤C.card)

@[simp] theorem mem_largeBlocks {S C : Finset H} :
    C∈largeBlocks S ↔ C⊆S ∧ 3≤C.card := by
  simp only [largeBlocks,mem_filter,mem_powerset]

abbrev BookBlock (H : Type*) [Fintype H] [LinearOrder H] :=
  ↥(largeBlocks (univ : Finset H))

def endpointCoefficients (C : Finset H) (d : H → ℝ) : PairIn C → ℝ :=
  fun e => d e.1.1.1+d e.1.1.2

theorem sum_full_stars (C : Finset H) (d : H → ℝ) :
    (∑ a,d a • starVector C a)=endpointCoefficients C d := by
  funext e
  have huv : e.1.1.1≠e.1.1.2 := ne_of_lt e.1.2.1
  have he : ∀ a,starVector C a e=
      (if a=e.1.1.1 then (1 : ℝ) else 0)+(if a=e.1.1.2 then 1 else 0) := by
    intro a
    rw [starVector_eq]
    by_cases hu : a=e.1.1.1
    · have hv : a≠e.1.1.2 := fun h => huv (hu.symm.trans h)
      simp [hu,hv,huv,Ne.symm huv]
    · by_cases hv : a=e.1.1.2 <;> simp [hu,hv,huv,Ne.symm huv]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,he,mul_add,sum_add_distrib,
    mul_ite,mul_one,mul_zero]
  simp only [sum_ite_eq',mem_univ,ite_true,endpointCoefficients]

/-- A threshold module's full coefficient response over all actual clique
blocks. Blocks that do not contain its distinguished vertex contribute zero. -/
theorem threshold_response_largeBlocks (a : H) :
    responseClass (thresholdStar a)=∑ C : BookBlock H,
      (-1 : ℝ)^(C.1.card-3) • blockClass C.1 (starVector C.1 a) := by
  have hcoord : thresholdSignedStar a=∑ C : BookBlock H,
      (-1 : ℝ)^(C.1.card-3) • blockCoordinates C.1 (starVector C.1 a) := by
    funext r
    rw [Finset.sum_apply]
    by_cases hr : 3≤(rowClique r).card
    · let C₀ : BookBlock H := ⟨rowClique r,mem_largeBlocks.mpr ⟨subset_univ _,hr⟩⟩
      rw [sum_eq_single C₀]
      · change thresholdSignedStar a r=
          (-1 : ℝ)^((rowClique r).card-3)*
            blockCoordinates (rowClique r) (starVector (rowClique r) a) r
        have he : blockCoordinates (rowClique r) (starVector (rowClique r) a) r=
            starVector (rowClique r) a (pairAtRow (rowClique r) r rfl) := by
          change (if h : rowClique r=rowClique r then
            starVector (rowClique r) a (pairAtRow (rowClique r) r h) else 0)=_
          rw [dite_eq_left rfl]
        rw [he,starVector_eq]
        change (if 3≤(rowClique r).card ∧ (a=r.1.1.1 ∨ a=r.1.1.2) then
          (-1 : ℝ)^((rowClique r).card-3) else 0)=
          (-1 : ℝ)^((rowClique r).card-3)*(if a=r.1.1.1 ∨ a=r.1.1.2 then 1 else 0)
        by_cases h : a=r.1.1.1 ∨ a=r.1.1.2 <;> simp [hr,h]
      · intro C hC hne
        have hrow : rowClique r≠C.1 := fun h => hne (Subtype.ext h.symm)
        change (-1 : ℝ)^(C.1.card-3)*
          (if h : rowClique r=C.1 then starVector C.1 a (pairAtRow C.1 r h) else 0)=0
        rw [dite_eq_right hrow,mul_zero]
      · simp
    · rw [sum_eq_zero]
      · simp only [thresholdSignedStar,hr,false_and,ite_false]
      · intro C hC
        have hrow : rowClique r≠C.1 := fun h => hr (h ▸ (mem_largeBlocks.mp C.2).2)
        change (-1 : ℝ)^(C.1.card-3)*
          (if h : rowClique r=C.1 then starVector C.1 a (pairAtRow C.1 r h) else 0)=0
        rw [dite_eq_right hrow,mul_zero]
  rw [thresholdStar_response_class,hcoord,map_sum]
  apply sum_congr rfl
  intro C hC
  rw [map_smul]
  rfl

/-- The coefficients of an arbitrary linear combination of threshold modules
are endpoint sums on every clique block, with the exact alternating sign. -/
theorem weighted_threshold_response (d : H → ℝ) :
    (∑ a,d a • responseClass (thresholdStar a))=
      ∑ C : BookBlock H,(-1 : ℝ)^(C.1.card-3) •
        blockClass C.1 (endpointCoefficients C.1 d) := by
  simp_rw [threshold_response_largeBlocks,smul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro C hC
  calc
    _ = (-1 : ℝ)^(C.1.card-3) •
        blockClass C.1 (∑ a,d a • starVector C.1 a) := by
      simp only [map_sum,map_smul,smul_sum]
      apply sum_congr rfl
      intro a ha
      exact smul_comm _ _ _
    _ = _ := by rw [sum_full_stars]

/-- Every actual block in the decomposition has its full constant kernel,
independently of all other blocks. -/
theorem book_block_sum_zero_component
    (x : (C : BookBlock H) → PairIn C.1 → ℝ)
    (hz : (∑ C : BookBlock H,blockClass C.1 (x C))=0) :
    ∀ C,∃ c : ℝ,∀ e,x C e=c := by
  classical
  have hp : ∀ C : BookBlock H,∃ e : PairIn C.1,True := by
    intro C
    obtain ⟨e,he⟩ := cliquePairs_nonempty C.1 C.1 (Subset.refl _)
      (by have h := (mem_largeBlocks.mp C.2).2; omega)
    exact ⟨e,trivial⟩
  let e₀ := fun C => (hp C).choose
  have he := block_sum_zero_component Subtype.val Subtype.val_injective e₀ x hz
  intro C
  exact (blockClass_eq_zero_iff C.1 (e₀ C) (x C)).mp (he C)

end BooleanModule
end GraphicalZonotopes
