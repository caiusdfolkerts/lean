module

public import Papers.GraphicalZonotopes.FourColorResource
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace GraphicalZonotopes.FourColorResource
open Finset Function

theorem single_plus_three_le_total {a : Fin 4 → ℕ} (ha : ∀ i,0<a i)
    (i : Fin 4) : a i+3≤total a := by
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  fin_cases i <;> simp [total,Fin.sum_univ_succ] <;> omega

theorem other_parts_mono {a b : Fin 4 → ℕ} (hba : ∀ i,b i≤a i) (i : Fin 4) :
    total b-b i≤total a-a i := by
  have h0 := hba 0
  have h1 := hba 1
  have h2 := hba 2
  have h3 := hba 3
  fin_cases i <;> simp [total,Fin.sum_univ_succ] <;> omega

/-- Every balanced active part vector obeys the exact restricted-dimension
bound, even when its largest part differs from the ambient largest part. -/
theorem balanced_dimension_bound {a b : Fin 4 → ℕ}
    (ha : ∀ i,0<a i) (hb : Balanced b) (hba : ∀ i,b i≤a i) :
    total b-1≤min (total a-1) (3*(total a-univ.sup a)-4) := by
  obtain ⟨i,hi,he⟩ := exists_mem_eq_sup (univ : Finset (Fin 4)) (by simp) a
  have htotal : total b≤total a := sum_le_sum (fun i _ => hba i)
  have hother := other_parts_mono hba i
  have hbi := single_plus_three_le_total hb.1 i
  have hai := single_plus_three_le_total ha i
  have hbal := hb.2 i
  rw [he]
  apply le_min
  · omega
  · omega

/-- Truncating one largest part is always optimal. The vector still has all
four positive parts and admits the complete unbounded attachment schedule. -/
theorem optimal_balanced_subcounts (a : Fin 4 → ℕ) (ha : ∀ i,0<a i) :
    ∃ b : Fin 4 → ℕ,Balanced b ∧ (∀ i,b i≤a i) ∧
      total b-1=min (total a-1) (3*(total a-univ.sup a)-4) := by
  obtain ⟨i,hi,he⟩ := exists_mem_eq_sup (univ : Finset (Fin 4)) (by simp) a
  have hmax : ∀ j,a j≤a i := by intro j;rw [← he];exact le_sup (mem_univ _)
  let s := total a-a i
  have hsum : a i+s=total a := by
    have h := single_plus_three_le_total ha i
    dsimp [s]
    omega
  have hs : 3≤s := by have h := single_plus_three_le_total ha i;dsimp [s];omega
  let k := min (a i) (2*s-3)
  have hkpos : 0<k := by have hi := ha i;dsimp [k];omega
  have hkai : k≤a i := min_le_left _ _
  have hks : k≤2*s-3 := min_le_right _ _
  let b := update a i k
  have hbi : b i=k := by simp [b]
  have hbtotal : total b=s+k := by
    have h := total_update a i k
    change total b+a i=total a+k at h
    omega
  have hbjmax : ∀ j,b j≤k := by
    intro j
    by_cases hji : j=i
    · subst j;rw [hbi]
    · have hp := pair_bound ha i j (Ne.symm hji)
      have hm := hmax j
      have hj := ha j
      have hjs : a j≤2*s-3 := by omega
      have hmin : a j≤k := le_min hm hjs
      simpa [b,update_of_ne hji] using hmin
  have hbal : Balanced b := by
    constructor
    · intro j
      by_cases hji : j=i
      · subst j;rwa [hbi]
      · simpa [b,update_of_ne hji] using ha j
    · intro j
      have h := hbjmax j
      rw [hbtotal]
      omega
  refine ⟨b,hbal,?_,?_⟩
  · intro j
    by_cases hji : j=i
    · subst j;rwa [hbi]
    · simp [b,update_of_ne hji]
  · rw [he,hbtotal]
    change s+k-1=min (total a-1) (3*s-4)
    by_cases hcase : a i≤2*s-3
    · have hk : k=a i := min_eq_left hcase
      rw [hk]
      omega
    · have hk : k=2*s-3 := min_eq_right (by omega)
      rw [hk]
      omega

end GraphicalZonotopes.FourColorResource
