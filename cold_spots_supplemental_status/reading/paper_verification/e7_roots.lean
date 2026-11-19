module

public import PaperVerification.E7MetricMeaning
public import PaperVerification.LatticeTranslations


@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def e7RootVector : Fin 7 → (Fin 8 → ℝ) :=
  ![![-1/2,-1/2,-1/2,-1/2,1/2,1/2,1/2,1/2],
    ![1,-1,0,0,0,0,0,0],![0,1,-1,0,0,0,0,0],
    ![0,0,1,-1,0,0,0,0],![0,0,0,1,-1,0,0,0],
    ![0,0,0,0,1,-1,0,0],![0,0,0,0,0,1,-1,0]]

lemma e7RootVector_sum (j : Fin 7) : (∑ i,e7RootVector j i)=0 := by
  fin_cases j <;> norm_num [e7RootVector,Fin.sum_univ_succ]

def e7SimpleRoot (j : Fin 7) : zeroSumSpace := ⟨e7RootVector j,e7RootVector_sum j⟩

theorem e7SimpleRoot_mem (j : Fin 7) : e7SimpleRoot j ∈ e7Set := by
  fin_cases j
  · refine ⟨![-1,-1,-1,-1,0,0,0,0],by decide,Or.inr ?_⟩
    ext i; fin_cases i <;> norm_num [e7SimpleRoot,e7RootVector]
  · refine ⟨![1,-1,0,0,0,0,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
    ext i; fin_cases i <;> norm_num [e7SimpleRoot,e7RootVector,intVec]
  · refine ⟨![0,1,-1,0,0,0,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
    ext i; fin_cases i <;> norm_num [e7SimpleRoot,e7RootVector,intVec]
  · refine ⟨![0,0,1,-1,0,0,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
    ext i; fin_cases i <;> norm_num [e7SimpleRoot,e7RootVector,intVec]
  · refine ⟨![0,0,0,1,-1,0,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
    ext i; fin_cases i <;> norm_num [e7SimpleRoot,e7RootVector,intVec]
  · refine ⟨![0,0,0,0,1,-1,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
    ext i; fin_cases i <;> norm_num [e7SimpleRoot,e7RootVector,intVec]
  · refine ⟨![0,0,0,0,0,1,-1,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
    ext i; fin_cases i <;> norm_num [e7SimpleRoot,e7RootVector,intVec]

def e7RootSum (t : Fin 7 → ℝ) : Fin 8 → ℝ := ∑ i,t i•e7RootVector i

def e7RootCoordinates (x : Fin 8 → ℝ) : Fin 7 → ℝ :=
  ![2*x 7,x 0+x 7,x 0+x 1+2*x 7,x 0+x 1+x 2+3*x 7,
    x 0+x 1+x 2+x 3+4*x 7,x 0+x 1+x 2+x 3+x 4+3*x 7,
    x 0+x 1+x 2+x 3+x 4+x 5+2*x 7]

theorem e7RootCoordinates_sum (t : Fin 7 → ℝ) : e7RootCoordinates (e7RootSum t)=t := by
  ext i
  fin_cases i <;> simp [e7RootCoordinates,e7RootSum,e7RootVector,Fin.sum_univ_succ] <;> ring

theorem e7RootSum_injective : Function.Injective e7RootSum :=
  Function.LeftInverse.injective e7RootCoordinates_sum

theorem e7RootSum_coordinates (x : zeroSumSpace) : e7RootSum (e7RootCoordinates x.val)=x.val := by
  have hx := zeroSumSpace_sum x
  rw [Fin.sum_univ_eight] at hx
  ext i
  fin_cases i <;>
    norm_num [e7RootCoordinates,e7RootSum,e7RootVector,Fin.sum_univ_seven] <;> linarith

def e7IntCoordinates (m : Fin 8 → ℤ) : Fin 7 → ℤ :=
  ![2*m 7,m 0+m 7,m 0+m 1+2*m 7,m 0+m 1+m 2+3*m 7,
    m 0+m 1+m 2+m 3+4*m 7,m 0+m 1+m 2+m 3+m 4+3*m 7,
    m 0+m 1+m 2+m 3+m 4+m 5+2*m 7]

def e7HalfCoordinates : Fin 7 → ℤ := ![1,1,2,3,4,4,4]

theorem e7RootCoordinates_int (m : Fin 8 → ℤ) :
    e7RootCoordinates (intVec m)=fun i ↦ (e7IntCoordinates m i:ℝ) := by
  ext i
  fin_cases i <;> simp [e7RootCoordinates,e7IntCoordinates,intVec]

theorem e7RootCoordinates_half (m : Fin 8 → ℤ) :
    e7RootCoordinates (fun i ↦ (m i:ℝ)+1/2)=
      fun i ↦ ((e7IntCoordinates m i+e7HalfCoordinates i:ℤ):ℝ) := by
  ext i
  fin_cases i <;> simp [e7RootCoordinates,e7IntCoordinates,e7HalfCoordinates] <;> ring

/-- The root lattice cut out in E₈ is exactly the integer span of seven
simple roots with the E₇ Cartan Gram graph. -/
theorem e7Set_simpleRoot_span (x : zeroSumSpace) : x ∈ e7Set ↔
    ∃ t : Fin 7 → ℤ, x.val=e7RootSum (fun i ↦ (t i:ℝ)) := by
  constructor
  · intro hx
    rcases hx with ⟨m,hm,hx|hx⟩
    · refine ⟨e7IntCoordinates m,?_⟩
      rw [← e7RootCoordinates_int,← hx,e7RootSum_coordinates]
    · refine ⟨fun i ↦ e7IntCoordinates m i+e7HalfCoordinates i,?_⟩
      rw [← e7RootCoordinates_half,← hx,e7RootSum_coordinates]
  · rintro ⟨t,ht⟩
    change x.val ∈ dPlusSet 8
    rw [ht]
    let L := dPlusAddSubgroup 8 (by decide)
    have h : (∑ i,t i•e7RootVector i) ∈ L :=
      L.sum_mem (fun i hi ↦ L.zsmul_mem (e7SimpleRoot_mem i) (t i))
    change (∑ i, t i • e7RootVector i) ∈ dPlusSet 8 at h
    simpa only [e7RootSum, Int.cast_smul_eq_zsmul] using h

def e7Cartan (i j : Fin 7) : ℤ :=
  if i = j then 2 else
    if (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0) ∨
      ((1 : ℕ) ≤ i.val ∧ (1 : ℕ) ≤ j.val ∧
        (i.val + 1 = j.val ∨ j.val + 1 = i.val)) then -1 else 0

theorem e7SimpleRoot_gram (i j : Fin 7) :
    coordinateInner (e7SimpleRoot i).val (e7SimpleRoot j).val=(e7Cartan i j:ℝ) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [e7SimpleRoot,e7RootVector,e7Cartan,coordinateInner,Fin.sum_univ_succ]

end PaperVerification.ColdSpots
