module

public import Papers.GraphicalZonotopes.OrdinaryBookBlocks
public import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

structure BalancedQuad (s : ℕ) where
  point : Fin 4 → Fin s
  ordered : StrictMono point
  balanced : (point 0).val+(point 3).val=(point 1).val+(point 2).val

namespace BalancedQuad
variable {s : ℕ} (Q : BalancedQuad s)

def clique : Finset (Fin s) := univ.image Q.point

@[simp] theorem point_mem (i : Fin 4) : Q.point i∈Q.clique :=
  mem_image.mpr ⟨i,mem_univ _,rfl⟩

@[simp] theorem card_clique : Q.clique.card=4 := by
  rw [clique,card_image_of_injective _ Q.ordered.injective]
  rfl

def pair (i j : Fin 4) (hij : i<j) : PairIn Q.clique :=
  orderedPair Q.clique (Q.point i) (Q.point j) (Q.ordered hij) (Q.point_mem i) (Q.point_mem j)

@[simp] theorem pair_eq_iff (i j k l : Fin 4) (hij : i<j) (hkl : k<l) :
    Q.pair i j hij=Q.pair k l hkl ↔ i=k ∧ j=l := by
  constructor
  · intro h
    exact ⟨Q.ordered.injective (congrArg (fun e : PairIn Q.clique => e.1.1.1) h),
      Q.ordered.injective (congrArg (fun e : PairIn Q.clique => e.1.1.2) h)⟩
  · rintro ⟨rfl,rfl⟩
    rfl

def reference : PairIn Q.clique := Q.pair 0 3 (by decide)
def opposite : PairIn Q.clique := Q.pair 1 2 (by decide)

def retainedIndices : Fin 4 → Fin 4×Fin 4 := ![(0,1),(0,2),(1,3),(2,3)]
theorem retainedIndices_order (i : Fin 4) : (retainedIndices i).1<(retainedIndices i).2 := by
  fin_cases i <;> decide
theorem retainedIndices_injective : Function.Injective retainedIndices := by decide

def retainedPair (i : Fin 4) : PairIn Q.clique :=
  Q.pair (retainedIndices i).1 (retainedIndices i).2 (retainedIndices_order i)

theorem retainedPair_injective : Function.Injective Q.retainedPair := by
  intro i j h
  apply retainedIndices_injective
  apply Prod.ext
  · exact ((Q.pair_eq_iff _ _ _ _ _ _).mp h).1
  · exact ((Q.pair_eq_iff _ _ _ _ _ _).mp h).2

@[simp] theorem reference_ne_retained (i : Fin 4) : Q.reference≠Q.retainedPair i := by
  change Q.pair 0 3 _≠Q.pair _ _ _
  rw [ne_eq,pair_eq_iff]
  fin_cases i <;> decide

@[simp] theorem opposite_ne_retained (i : Fin 4) : Q.opposite≠Q.retainedPair i := by
  change Q.pair 1 2 _≠Q.pair _ _ _
  rw [ne_eq,pair_eq_iff]
  fin_cases i <;> decide

def columnSign (i : Fin 4) : ℝ := if i.val<2 then -1 else 1

def column (i : Fin 4) : PairIn Q.clique → ℝ :=
  columnSign i • pairIndicator {Q.retainedPair i}

def label (i : Fin 4) : ℤ := ((Q.point i).val : ℤ)

def weight : Fin 4 → ℤ :=
  ![Q.label 3-Q.label 1,Q.label 3-Q.label 2,Q.label 1-Q.label 0,Q.label 2-Q.label 0]

@[simp] theorem columnSign_ne_zero (i : Fin 4) : columnSign i≠0 := by
  unfold columnSign
  split <;> norm_num

theorem column_realizable (i : Fin 4) : PureRealizable Q.clique (Q.column i) := by
  by_cases h : i.val<2
  · have he : Q.column i= -pairIndicator {Q.retainedPair i} := by
      simp only [column,columnSign,ite_eq_left h,neg_one_smul]
    rw [he]
    exact pureRealizable_negative_pair Q.clique (by rw [Q.card_clique]; omega) (Q.retainedPair i)
  · have he : Q.column i=pairIndicator {Q.retainedPair i} := by
      simp only [column,columnSign,ite_eq_right h,one_smul]
    rw [he]
    exact pureRealizable_pair Q.clique (Q.retainedPair i)

theorem weight_positive (i : Fin 4) : 0<Q.weight i := by
  have h01 : Q.label 0<Q.label 1 := by
    change ((Q.point 0).val : ℤ)<((Q.point 1).val : ℤ)
    exact_mod_cast (show (Q.point 0).val<(Q.point 1).val from Q.ordered (by decide : (0 : Fin 4)<1))
  have h02 : Q.label 0<Q.label 2 := by
    change ((Q.point 0).val : ℤ)<((Q.point 2).val : ℤ)
    exact_mod_cast (show (Q.point 0).val<(Q.point 2).val from Q.ordered (by decide : (0 : Fin 4)<2))
  have h13 : Q.label 1<Q.label 3 := by
    change ((Q.point 1).val : ℤ)<((Q.point 3).val : ℤ)
    exact_mod_cast (show (Q.point 1).val<(Q.point 3).val from Q.ordered (by decide : (1 : Fin 4)<3))
  have h23 : Q.label 2<Q.label 3 := by
    change ((Q.point 2).val : ℤ)<((Q.point 3).val : ℤ)
    exact_mod_cast (show (Q.point 2).val<(Q.point 3).val from Q.ordered (by decide : (2 : Fin 4)<3))
  fin_cases i <;> change 0 < _ - _ <;> omega

theorem weight_bounded (i : Fin 4) : Q.weight i≤((s-1 : ℕ) : ℤ) := by
  have hlo : ∀ j,0≤Q.label j := fun j => Int.natCast_nonneg _
  have hhi : ∀ j,Q.label j<(s : ℤ) := fun j => by
    change ((Q.point j).val : ℤ)<(s : ℤ)
    exact_mod_cast (Q.point j).isLt
  have h0 := hlo 0
  have h1 := hlo 1
  have h2 := hlo 2
  have h3 := hhi 3
  have h1' := hhi 1
  have h2' := hhi 2
  fin_cases i <;> change _ - _ ≤ ((s-1 : ℕ) : ℤ) <;> omega

theorem columns_independent : LinearIndependent ℝ (fun i => blockClass Q.clique (Q.column i)) := by
  let p : Fin 4 → ↥((univ : Finset (PairIn Q.clique)).erase Q.reference) :=
    fun i => ⟨Q.retainedPair i,mem_erase.mpr ⟨Ne.symm (Q.reference_ne_retained i),mem_univ _⟩⟩
  have hp : Function.Injective p := fun i j h => Q.retainedPair_injective (congrArg Subtype.val h)
  have hi : LinearIndependent ℝ (fun i => blockClass Q.clique (pairIndicator {Q.retainedPair i})) :=
    (reference_pair_columns_independent Q.clique Q.reference).comp p hp
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hz : (∑ j,(c j*columnSign j) • blockClass Q.clique (pairIndicator {Q.retainedPair j}))=0 := by
    simpa only [column,map_smul,mul_smul] using hc
  exact (mul_eq_zero.mp ((Fintype.linearIndependent_iff.mp hi) _ hz i)).resolve_right (columnSign_ne_zero i)

@[simp] theorem column_reference (i : Fin 4) : Q.column i Q.reference=0 := by
  simp [column,pairIndicator]

@[simp] theorem column_opposite (i : Fin 4) : Q.column i Q.opposite=0 := by
  simp [column,pairIndicator]

/-- All six pair coordinates are checked: four retained signed pairs have
positive scales, and the two omitted pairs have the same endpoint sum. -/
theorem weighted_columns_vector :
    (∑ i : Fin 4,(Q.weight i : ℝ) • Q.column i)=
      endpointLabels Q.clique-(fun _ => ((Q.label 0+Q.label 3 : ℤ) : ℝ)) := by
  funext e
  obtain ⟨i,hi,hui⟩ := mem_image.mp e.2.1
  obtain ⟨j,hj,hvj⟩ := mem_image.mp e.2.2
  have hij : i<j := by
    by_contra hn
    have hle := Q.ordered.monotone (le_of_not_gt hn)
    have hlt : Q.point i<Q.point j := by simpa only [hui,hvj] using e.1.2.1
    exact (not_le_of_gt hlt) hle
  have he : e=Q.pair i j hij := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hui.symm hvj.symm
  rw [he]
  have hb : ((Q.point 0).val : ℝ)+(Q.point 3).val=
      ((Q.point 1).val : ℝ)+(Q.point 2).val := by exact_mod_cast Q.balanced
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals
    simp [Fin.sum_univ_four,Pi.smul_apply,smul_eq_mul,column,columnSign,pairIndicator,
      retainedPair,retainedIndices,pair_eq_iff,weight,
      Int.cast_sub,Int.cast_add,Int.cast_natCast]
    simp only [endpointLabels,pair,orderedPair,label,Pi.sub_apply]
    push_cast
    linarith

theorem weighted_columns_response :
    (∑ i : Fin 4,(Q.weight i : ℝ) • blockClass Q.clique (Q.column i))=
      ordinaryBookTarget Q.clique := by
  have hz : blockClass Q.clique (fun _ : PairIn Q.clique => ((Q.label 0+Q.label 3 : ℤ) : ℝ))=0 :=
    (blockClass_eq_zero_iff Q.clique Q.reference _).mpr ⟨_,fun _ => rfl⟩
  calc
    _ = blockClass Q.clique (∑ i : Fin 4,(Q.weight i : ℝ) • Q.column i) := by simp only [map_sum,map_smul]
    _ = blockClass Q.clique (endpointLabels Q.clique) := by
      rw [Q.weighted_columns_vector,map_sub,hz,sub_zero]
    _ = ordinaryBookTarget Q.clique := by simp [ordinaryBookTarget,Q.card_clique]

end BalancedQuad
end BooleanModule
end GraphicalZonotopes
