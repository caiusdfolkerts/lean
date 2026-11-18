module

public import Papers.GraphicalZonotopes.BookBlockCoordinates

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

/-- Every integral vector interval realizes every intermediate total. -/
theorem interval_sum_composition {B : Type*} [Fintype B] [DecidableEq B]
    (l u : B → ℕ) (hlu : ∀ b,l b≤u b) {n : ℕ}
    (hnlo : (∑ b,l b)≤n) (hnhi : n≤∑ b,u b) :
    ∃ k : B → ℕ,(∀ b,l b≤k b ∧ k b≤u b) ∧ (∑ b,k b)=n := by
  have hsum : (∑ b,(u b-l b))+(∑ b,l b)=∑ b,u b := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun b _ => Nat.sub_add_cancel (hlu b))
  obtain ⟨f,hf,hfs⟩ := bounded_sum_composition (univ : Finset B) (fun b => u b-l b)
    (n:=n-∑ b,l b) (by omega)
  refine ⟨fun b => f b+l b,?_,?_⟩
  · intro b
    have hfb := hf b (mem_univ b)
    have hb := hlu b
    constructor <;> dsimp only <;> omega
  · rw [sum_add_distrib,hfs]
    omega

variable {H : Type*} [Fintype H] [LinearOrder H]

theorem largeBlocks_dimension_sum (S : Finset H) :
    (∑ C∈largeBlocks S,(C.card.choose 2-1))=blockDimensionSum S := by
  unfold blockDimensionSum
  apply sum_subset (filter_subset _ _)
  intro C hC hn
  have hc : C.card<3 := by
    have h : ¬3≤C.card := fun h => hn (mem_largeBlocks.mpr ⟨mem_powerset.mp hC,h⟩)
    omega
  interval_cases hcard : C.card <;> norm_num [hcard,Nat.choose]

theorem BookBlock_dimension_sum :
    (∑ C : BookBlock H,(C.1.card.choose 2-1))+1=cliqueCapacity (Fintype.card H) := by
  rw [sum_coe_sort (largeBlocks (univ : Finset H)) (fun C : Finset H => C.card.choose 2-1)]
  rw [largeBlocks_dimension_sum,← cliqueCapacity_eq_dimension_sum,card_univ]

theorem largeBlocks_lower_count (S : Finset H) :
    (∑ C∈largeBlocks S,(C.card-1))+S.card.choose 2+2^S.card=
      S.card*2^(S.card-1)+1 := by
  let E := S.powerset.filter (fun C => C.Nonempty)
  have hEcard : E.card+1=2^S.card := by
    have hpartition := card_filter_add_card_filter_not (s:=S.powerset) (p:=fun C => C.Nonempty)
    have hempty : S.powerset.filter (fun C => ¬C.Nonempty)={∅} := by
      ext C
      simp only [mem_filter,mem_powerset,not_nonempty_iff_eq_empty,mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl
        exact ⟨empty_subset _,rfl⟩
    rw [hempty,card_singleton,card_powerset] at hpartition
    exact hpartition
  have hsumE : (∑ C∈E,(C.card-1))+E.card=∑ C∈S.powerset,C.card := by
    calc
      _ = ∑ C∈E,((C.card-1)+1) := by simp [sum_add_distrib]
      _ = ∑ C∈E,C.card := sum_congr rfl (fun C hC =>
        Nat.sub_add_cancel (show 1≤C.card from (card_pos.mpr (mem_filter.mp hC).2)))
      _ = _ := by
        apply sum_subset (filter_subset _ _)
        intro C hC hn
        have hz : ¬C.Nonempty := fun h => hn (mem_filter.mpr ⟨hC,h⟩)
        exact card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hz)
  have hsplit : (∑ C∈E,(C.card-1))=
      (∑ C∈largeBlocks S,(C.card-1))+S.card.choose 2 := by
    have hfilter : E.filter (fun C => 3≤C.card)=largeBlocks S := by
      ext C
      simp only [E,mem_filter,mem_powerset,mem_largeBlocks]
      constructor
      · exact fun h => ⟨h.1.1,h.2⟩
      · exact fun h => ⟨⟨h.1,card_pos.mp (by omega)⟩,h.2⟩
    have hsmall : (∑ C∈E.filter (fun C => ¬3≤C.card),(C.card-1))=
        (S.powersetCard 2).card := by
      have hp : S.powersetCard 2⊆E.filter (fun C => ¬3≤C.card) := by
        intro C hC
        obtain ⟨hCS,hcard⟩ := mem_powersetCard.mp hC
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr hCS,
          card_pos.mp (by omega)⟩,by omega⟩
      calc
        _ = ∑ C∈S.powersetCard 2,(C.card-1) := by
          symm
          apply sum_subset hp
          intro C hC hn
          have hsize := (mem_filter.mp hC).2
          have hCS := mem_powerset.mp (mem_filter.mp (mem_filter.mp hC).1).1
          have hne2 : C.card≠2 := fun h => hn (mem_powersetCard.mpr ⟨hCS,h⟩)
          omega
        _ = _ := by
          have he : ∀ C∈S.powersetCard 2,C.card-1=1 := fun C hC => by
            rw [(mem_powersetCard.mp hC).2]
          simp only [sum_congr rfl he,sum_const,nsmul_eq_mul,mul_one,Nat.cast_id]
    have hpartition := sum_filter_add_sum_filter_not (s:=E) (p:=fun C => 3≤C.card)
      (f:=fun C => C.card-1)
    rw [hfilter,hsmall,card_powersetCard] at hpartition
    exact hpartition.symm
  rw [hsplit,sum_powerset_card] at hsumE
  omega

theorem BookBlock_lower_sum {s : ℕ} (hs : 2≤s) :
    (∑ C : BookBlock (Fin s),(C.1.card-1))+s.choose 2=
      (s-2)*2^(s-1)+1 := by
  have h := largeBlocks_lower_count (univ : Finset (Fin s))
  simp only [card_univ,Fintype.card_fin] at h
  rw [← sum_coe_sort (largeBlocks (univ : Finset (Fin s)))
    (fun C : Finset (Fin s) => C.card-1)] at h
  have hspos : 0<s := by omega
  have hp : 2^s=2*2^(s-1) := by
    have he : s-1+1=s := by omega
    calc
      2^s=2^(s-1+1) := congrArg (fun n => 2^n) he.symm
      _ = 2*2^(s-1) := by rw [pow_succ]; ring
  have hm : s*2^(s-1)=(s-2)*2^(s-1)+2*2^(s-1) := by
    calc
      s*2^(s-1)=((s-2)+2)*2^(s-1) := congrArg (fun n => n*2^(s-1)) (Nat.sub_add_cancel hs).symm
      _ = _ := by rw [Nat.add_mul]
  rw [hp,hm] at h
  exact Nat.add_right_cancel (h.trans (by ac_rfl))

end BooleanModule
end GraphicalZonotopes
