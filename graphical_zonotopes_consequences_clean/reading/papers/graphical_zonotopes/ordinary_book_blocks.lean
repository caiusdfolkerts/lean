module

public import Papers.GraphicalZonotopes.StarCoordinateAlgebra

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

variable {s : ℕ}

def endpointLabels (C : Finset (Fin s)) : PairIn C → ℝ :=
  fun e => (e.1.1.1.val : ℝ)+(e.1.1.2.val : ℝ)

def ordinaryBookTarget (C : Finset (Fin s)) : ResponseQuotient (Fin s) :=
  -((-1 : ℝ)^(C.card-3) • blockClass C (endpointLabels C))

private theorem numeric_erased_weight (C : Finset (Fin s)) (m a : Fin s)
    (ha : a∈C) :
    erasedHubWeight C m (fun i => (((i.1.val : ℤ)-(m.val : ℤ)) : ℝ)) a=
      (a.val : ℝ)-(m.val : ℝ) := by
  by_cases h : a=m
  · subst a
    simp
  · have hm : a∈C.erase m := mem_erase.mpr ⟨h,ha⟩
    simp only [erasedHubWeight,dite_eq_left hm,Int.cast_sub,Int.cast_natCast]

private theorem numeric_erased_weight_neg (C : Finset (Fin s)) (m a : Fin s)
    (ha : a∈C) :
    erasedHubWeight C m (fun i => (((m.val : ℤ)-(i.1.val : ℤ)) : ℝ)) a=
      (m.val : ℝ)-(a.val : ℝ) := by
  by_cases h : a=m
  · subst a
    simp
  · have hm : a∈C.erase m := mem_erase.mpr ⟨h,ha⟩
    simp only [erasedHubWeight,dite_eq_left hm,Int.cast_sub,Int.cast_natCast]

private theorem endpoint_stars_positive (C : Finset (Fin s)) (m : Fin s)
    (e₀ : PairIn C) :
    (∑ i : C.erase m,((((i.1.val : ℤ)-(m.val : ℤ)) : ℝ)) •
      blockClass C (starVector C i.1))=blockClass C (endpointLabels C) := by
  have he : (∑ i : C.erase m,((((i.1.val : ℤ)-(m.val : ℤ)) : ℝ)) • starVector C i.1)=
      endpointLabels C-(fun _ : PairIn C => 2*(m.val : ℝ)) := by
    funext e
    rw [sum_erased_stars_eval,numeric_erased_weight C m _ e.2.1,numeric_erased_weight C m _ e.2.2]
    change ((e.1.1.1.val : ℝ)-m.val)+((e.1.1.2.val : ℝ)-m.val)=
      (e.1.1.1.val : ℝ)+e.1.1.2.val-2*m.val
    ring
  have hz : blockClass C (fun _ : PairIn C => 2*(m.val : ℝ))=0 :=
    (blockClass_eq_zero_iff C e₀ _).mpr ⟨2*(m.val : ℝ),fun _ => rfl⟩
  calc
    _ = blockClass C (∑ i : C.erase m,
        ((((i.1.val : ℤ)-(m.val : ℤ)) : ℝ)) • starVector C i.1) := by simp only [map_sum,map_smul]
    _ = _ := by rw [he,map_sub,hz,sub_zero]

private theorem endpoint_stars_negative (C : Finset (Fin s)) (m : Fin s)
    (e₀ : PairIn C) :
    (∑ i : C.erase m,((((m.val : ℤ)-(i.1.val : ℤ)) : ℝ)) •
      blockClass C (starVector C i.1))= -blockClass C (endpointLabels C) := by
  have he : (∑ i : C.erase m,((((m.val : ℤ)-(i.1.val : ℤ)) : ℝ)) • starVector C i.1)=
      (fun _ : PairIn C => 2*(m.val : ℝ))-endpointLabels C := by
    funext e
    rw [sum_erased_stars_eval,numeric_erased_weight_neg C m _ e.2.1,numeric_erased_weight_neg C m _ e.2.2]
    change ((m.val : ℝ)-e.1.1.1.val)+((m.val : ℝ)-e.1.1.2.val)=
      2*(m.val : ℝ)-((e.1.1.1.val : ℝ)+e.1.1.2.val)
    ring
  have hz : blockClass C (fun _ : PairIn C => 2*(m.val : ℝ))=0 :=
    (blockClass_eq_zero_iff C e₀ _).mpr ⟨2*(m.val : ℝ),fun _ => rfl⟩
  calc
    _ = blockClass C (∑ i : C.erase m,
        ((((m.val : ℤ)-(i.1.val : ℤ)) : ℝ)) • starVector C i.1) := by simp only [map_sum,map_smul]
    _ = _ := by rw [he,map_sub,hz,zero_sub]

/-- Every ordinary clique block in Theorem 7.10 admits every intermediate
rank with strictly positive integral scales at most `s-1`. The target is the
literal cancellation of all weighted threshold-star responses on the block. -/
theorem ordinary_book_block_interpolation (C : Finset (Fin s)) (hC : 3≤C.card)
    {k : ℕ} (hklo : C.card-1≤k) (hkhi : k≤C.card.choose 2-1) :
    Nonempty (WeightedStarFamily C ((s-1 : ℕ) : ℤ) (ordinaryBookTarget C) k) := by
  classical
  have hne : C.Nonempty := card_pos.mp (by omega)
  obtain ⟨e₀,he₀⟩ := cliquePairs_nonempty C C (Subset.refl _) (by omega)
  rcases neg_one_pow_eq_or ℝ (C.card-3) with hsign | hsign
  · let m := C.max' hne
    have hm : m∈C := max'_mem C hne
    let w : C.erase m → ℤ := fun i => (m.val : ℤ)-(i.1.val : ℤ)
    have hw : ∀ i,0<w i := by
      intro i
      have hle : i.1≤m := le_max' C i.1 (mem_of_mem_erase i.2)
      have hni : i.1≠m := (mem_erase.mp i.2).1
      have hlt : i.1<m := lt_of_le_of_ne hle hni
      have hval : i.1.val<m.val := hlt
      dsimp only [w]
      omega
    have hb : ∀ i,w i≤((s-1 : ℕ) : ℤ) := by
      intro i
      have hmval := m.isLt
      dsimp only [w]
      omega
    have hp := weighted_full_stars_interpolation C hC m hm w ((s-1 : ℕ) : ℤ) hw hb hklo hkhi
    have he := endpoint_stars_negative C m e₀
    have he' : (∑ i : C.erase m,(w i : ℝ) • blockClass C (starVector C i.1))=
        -blockClass C (endpointLabels C) := by
      simpa only [w,Int.cast_sub,Int.cast_natCast] using he
    rw [he'] at hp
    simpa only [ordinaryBookTarget,hsign,one_smul] using hp
  · let m := C.min' hne
    have hm : m∈C := min'_mem C hne
    let w : C.erase m → ℤ := fun i => (i.1.val : ℤ)-(m.val : ℤ)
    have hw : ∀ i,0<w i := by
      intro i
      have hle : m ≤ i.1 := min'_le C i.1 (mem_of_mem_erase i.2)
      have hni : m≠i.1 := Ne.symm (mem_erase.mp i.2).1
      have hlt : m < i.1 := lt_of_le_of_ne hle hni
      have hval : m.val < i.1.val := hlt
      dsimp only [w]
      omega
    have hb : ∀ i,w i≤((s-1 : ℕ) : ℤ) := by
      intro i
      have hival := i.1.isLt
      dsimp only [w]
      omega
    have hp := weighted_full_stars_interpolation C hC m hm w ((s-1 : ℕ) : ℤ) hw hb hklo hkhi
    have he := endpoint_stars_positive C m e₀
    have he' : (∑ i : C.erase m,(w i : ℝ) • blockClass C (starVector C i.1))=
        blockClass C (endpointLabels C) := by
      simpa only [w,Int.cast_sub,Int.cast_natCast] using he
    rw [he'] at hp
    simpa only [ordinaryBookTarget,hsign,neg_one_smul,neg_neg] using hp

end BooleanModule
end GraphicalZonotopes
