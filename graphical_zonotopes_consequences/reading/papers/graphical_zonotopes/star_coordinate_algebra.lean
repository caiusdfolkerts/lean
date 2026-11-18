module

public import Papers.GraphicalZonotopes.WeightedStarRefinement
public import Papers.GraphicalZonotopes.PureDecompositions

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

def erasedHubWeight (C : Finset H) (m : H) (t : C.erase m → ℝ) (a : H) : ℝ :=
  if h : a∈C.erase m then t ⟨a,h⟩ else 0

@[simp] theorem erasedHubWeight_self (C : Finset H) (m : H) (t : C.erase m → ℝ) :
    erasedHubWeight C m t m=0 := by
  simp [erasedHubWeight]

@[simp] theorem erasedHubWeight_subtype (C : Finset H) (m : H)
    (t : C.erase m → ℝ) (a : C.erase m) : erasedHubWeight C m t a.1=t a := by
  simp only [erasedHubWeight,dite_eq_left a.2]

private theorem sum_erased_indicator (C : Finset H) (m : H)
    (t : C.erase m → ℝ) (a : H) :
    (∑ i : C.erase m,t i*(if i.1=a then (1 : ℝ) else 0))=erasedHubWeight C m t a := by
  classical
  by_cases ha : a∈C.erase m
  · have he : ∀ i : C.erase m,i.1=a ↔ i=⟨a,ha⟩ :=
      fun i => ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
    simp [he,erasedHubWeight,ha]
  · have hn : ∀ i : C.erase m,i.1≠a := fun i h => ha (h ▸ i.2)
    simp [hn,erasedHubWeight,ha]

theorem sum_erased_stars_eval (C : Finset H) (m : H)
    (t : C.erase m → ℝ) (e : PairIn C) :
    (∑ i : C.erase m,t i • starVector C i.1) e=
      erasedHubWeight C m t e.1.1.1+erasedHubWeight C m t e.1.1.2 := by
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply,smul_eq_mul,starVector_eq]
  have he : ∀ i : C.erase m,t i*(if i.1=e.1.1.1 ∨ i.1=e.1.1.2 then (1 : ℝ) else 0)=
      t i*(if i.1=e.1.1.1 then 1 else 0)+t i*(if i.1=e.1.1.2 then 1 else 0) := by
    intro i
    by_cases hu : i.1=e.1.1.1 <;> by_cases hv : i.1=e.1.1.2
    · exact False.elim ((ne_of_lt e.1.2.1) (hu.symm.trans hv))
    all_goals simp [hu,hv,ne_of_lt e.1.2.1,Ne.symm (ne_of_lt e.1.2.1)]
  rw [sum_congr rfl (fun i _ => he i),sum_add_distrib,
    sum_erased_indicator,sum_erased_indicator]

theorem sum_erased_stars_at_pair (C : Finset H) (m : H) (t : C.erase m → ℝ)
    (u v : H) (huv : u≠v) (hu : u∈C) (hv : v∈C) :
    (∑ i : C.erase m,t i • starVector C i.1) (pairOfNe C u v huv hu hv)=
      erasedHubWeight C m t u+erasedHubWeight C m t v := by
  rw [sum_erased_stars_eval]
  rcases pairOfNe_endpoints C u v huv hu hv with h | h <;> simp [h.1,h.2,add_comm]

/-- The stars centered at all but one vertex are independent modulo the
constant pair vector. This is proved from the actual pair quotient. -/
theorem erased_star_columns_independent (C : Finset H) (hC : 3≤C.card)
    (m : H) (hm : m∈C) :
    LinearIndependent ℝ (fun i : C.erase m => blockClass C (starVector C i.1)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro t ht i
  have hmap : blockClass C (∑ j : C.erase m,t j • starVector C j.1)=0 := by
    simpa only [map_sum,map_smul] using ht
  have herase : 2≤(C.erase m).card := by rw [card_erase_of_mem hm]; omega
  obtain ⟨u,hu,v,hv,huv⟩ := one_lt_card.mp (show 1<(C.erase m).card by omega)
  let e₀ := pairOfNe C u v huv (mem_of_mem_erase hu) (mem_of_mem_erase hv)
  obtain ⟨c,hc⟩ := (blockClass_eq_zero_iff C e₀ _).mp hmap
  have hscale : ∀ j : C.erase m,t j=c := by
    intro j
    have h := hc (pairOfNe C m j.1 (Ne.symm (mem_erase.mp j.2).1) hm (mem_of_mem_erase j.2))
    rw [sum_erased_stars_at_pair,erasedHubWeight_self,erasedHubWeight_subtype,zero_add] at h
    exact h
  have hz := hc e₀
  rw [sum_erased_stars_at_pair] at hz
  have hu' : erasedHubWeight C m t u=t ⟨u,hu⟩ := erasedHubWeight_subtype C m t ⟨u,hu⟩
  have hv' : erasedHubWeight C m t v=t ⟨v,hv⟩ := erasedHubWeight_subtype C m t ⟨v,hv⟩
  rw [hu',hv',hscale,hscale] at hz
  have hc0 : c=0 := by linarith
  exact (hscale i).trans hc0

def fullStarPiece (C : Finset H) (hC : 2≤C.card) (i : C) : StarPiece C where
  center := i.1
  leaves := C.erase i.1
  center_mem := i.2
  leaves_subset := erase_subset _ _
  nonempty := card_pos.mp (by rw [card_erase_of_mem i.2]; omega)
  center_notMem := notMem_erase _ _

theorem fullStarPiece_response (C : Finset H) (hC : 2≤C.card) (i : C) :
    (fullStarPiece C hC i).response=blockClass C (starVector C i.1) := rfl

/-- Positive vertex-star scales have independent positive partial-star
refinements at every count between `|C|-1` and the full block dimension. -/
theorem weighted_full_stars_interpolation (C : Finset H) (hC : 3≤C.card)
    (m : H) (hm : m∈C) (w : C.erase m → ℤ) (M : ℤ)
    (hw : ∀ i,0<w i) (hM : ∀ i,w i≤M) {k : ℕ}
    (hklo : C.card-1≤k) (hkhi : k≤C.card.choose 2-1) :
    Nonempty (WeightedStarFamily C M
      (∑ i : C.erase m,(w i : ℝ) • blockClass C (starVector C i.1)) k) := by
  classical
  let P : C.erase m → StarPiece C := fun i => fullStarPiece C (by omega) ⟨i.1,mem_of_mem_erase i.2⟩
  have hi : LinearIndependent ℝ (fun i => (P i).response) :=
    erased_star_columns_independent C hC m hm
  have hc : ∀ e : PairIn C,∃ j,e∈(P j).edges := by
    intro e
    by_cases hu : e.1.1.1=m
    · have hv : e.1.1.2≠m := fun h => (ne_of_lt e.1.2.1) (hu.trans h.symm)
      let j : C.erase m := ⟨e.1.1.2,mem_erase.mpr ⟨hv,e.2.2⟩⟩
      refine ⟨j,mem_starPairs.mpr (Or.inr ⟨rfl,?_⟩)⟩
      exact mem_erase.mpr ⟨ne_of_lt e.1.2.1,e.2.1⟩
    · let j : C.erase m := ⟨e.1.1.1,mem_erase.mpr ⟨hu,e.2.1⟩⟩
      refine ⟨j,mem_starPairs.mpr (Or.inl ⟨rfl,?_⟩)⟩
      exact mem_erase.mpr ⟨Ne.symm (ne_of_lt e.1.2.1),e.2.2⟩
  obtain ⟨Q⟩ := weightedStarFamily_of_data P w hw hM hi rfl hc
    (r:=C.card-1) (by simp only [Fintype.card_coe,card_erase_of_mem hm])
  obtain ⟨e₀,he₀⟩ := cliquePairs_nonempty C C (Subset.refl _) (by omega)
  exact Q.refine e₀ hklo hkhi

end BooleanModule
end GraphicalZonotopes
