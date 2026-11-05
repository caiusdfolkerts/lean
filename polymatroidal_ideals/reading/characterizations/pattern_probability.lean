import Characterizations.PointUniformity

/-! # The exact rejection mass of an active order pattern -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Characterizations
open Classical Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem finiteFraction_congr {X : Type*} [Fintype X] {P Q : X → Prop}
    (h : ∀ x, P x ↔ Q x) : finiteFraction P = finiteFraction Q :=
  congrArg finiteFraction (funext (fun x => propext (h x)))

theorem finiteFraction_mono {X : Type*} [Fintype X] {P Q : X → Prop}
    (h : ∀ x, P x → Q x) : finiteFraction P ≤ finiteFraction Q := by
  have hc : Nat.card {x // P x} ≤ Nat.card {x // Q x} :=
    Nat.card_le_card_of_injective (fun x => (⟨x.val,h x.val x.property⟩ : {x // Q x}))
      (fun _ _ he => Subtype.ext (congrArg (fun z : {x // Q x} => z.val) he))
  unfold finiteFraction
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg _)

theorem finiteFraction_true {X : Type*} [Fintype X] [Nonempty X] :
    finiteFraction (fun _ : X => True) = 1 := by
  unfold finiteFraction
  simp [Nat.card_eq_fintype_card,Fintype.card_pos.ne']

theorem finiteFraction_le_one {X : Type*} [Fintype X] [Nonempty X] (P : X → Prop) :
    finiteFraction P ≤ 1 := by
  rw [← finiteFraction_true (X := X)]
  exact finiteFraction_mono (fun _ _ => trivial)

theorem coversPoint_pair_iff {o : VariableOrder V} {i q j : V}
    (hiq : i ≠ q) (hij : i ≠ j) (hqj : q ≠ j) :
    CoversPoint o (⟨j,⟨{i,q},by simp [insert_subset_iff,hij,hqj],by simp [hiq]⟩⟩ : PointedTriple V) ↔
      FinalTriple o i q j := by
  constructor
  · rintro ⟨a,b,hab,hA,hf⟩
    exact hf.of_pair_eq hiq hab hA
  · intro hf
    exact ⟨i,q,hiq,rfl,hf⟩

theorem restricted_finalTriple_iff (T : Finset V) (o : VariableOrder V) (i q j : T) :
    FinalTriple (restrictedOrder o (Function.Embedding.subtype (· ∈ T))) i q j ↔
      OrderPattern o (T \ {i.val,q.val,j.val}) i.val q.val j.val := by
  simp only [FinalTriple,OrderPattern,restrictedOrder_lt_iff]
  constructor
  · rintro ⟨hi,hq,hr⟩
    refine ⟨hi,hq,?_⟩
    intro x hx
    obtain ⟨hxT,hxn⟩ := mem_sdiff.mp hx
    have hxi : x ≠ i.val := fun he => hxn (by simp [he])
    have hxq : x ≠ q.val := fun he => hxn (by simp [he])
    have hxj : x ≠ j.val := fun he => hxn (by simp [he])
    exact hr ⟨x,hxT⟩ (fun he => hxi (congrArg Subtype.val he))
      (fun he => hxq (congrArg Subtype.val he)) (fun he => hxj (congrArg Subtype.val he))
  · rintro ⟨hi,hq,hr⟩
    refine ⟨hi,hq,?_⟩
    intro x hxi hxq hxj
    apply hr x.val
    exact mem_sdiff.mpr ⟨x.property,by
      simp only [mem_insert,mem_singleton,not_or]
      exact ⟨fun he => hxi (Subtype.ext he),fun he => hxq (Subtype.ext he),fun he => hxj (Subtype.ext he)⟩⟩

theorem restricted_point_probability (T : Finset V) (hT : 3 ≤ T.card) (P : PointedTriple T) :
    finiteFraction (fun o : VariableOrder V => CoversPoint
      (restrictedOrder o (Function.Embedding.subtype (· ∈ T))) P) =
      1 / (T.card * (T.card-1).choose 2 : ℕ) := by
  calc
    _ = finiteFraction (fun r : VariableOrder T => CoversPoint r P) := restriction_uniform T _
    _ = _ := by
      have hh := pointedTriple_probability (V := T) (by simpa using hT) P
      simpa only [Fintype.card_coe] using hh

theorem orderPattern_probability (C : Finset V) (i q j : V)
    (hiq : i ≠ q) (hij : i ≠ j) (hqj : q ≠ j) (hC : C ⊆ tripleCap i q j) :
    finiteFraction (fun o : VariableOrder V => OrderPattern o C i q j) =
      1 / ((C.card+3) * (C.card+2).choose 2 : ℕ) := by
  let T := patternActive C i q j
  let I : T := ⟨i,by simp [T,patternActive]⟩
  let Q : T := ⟨q,by simp [T,patternActive]⟩
  let J : T := ⟨j,by simp [T,patternActive]⟩
  have hIQ : I ≠ Q := fun he => hiq (congrArg Subtype.val he)
  have hIJ : I ≠ J := fun he => hij (congrArg Subtype.val he)
  have hQJ : Q ≠ J := fun he => hqj (congrArg Subtype.val he)
  let P : PointedTriple T := ⟨J,⟨{I,Q},by simp [insert_subset_iff,hIJ,hQJ],by simp [hIQ]⟩⟩
  have hTC : T \ {i,q,j} = C := by
    ext x
    have hiC : i ∉ C := fun h => by simpa using hC h
    have hqC : q ∉ C := fun h => by simpa using hC h
    have hjC : j ∉ C := fun h => by simpa using hC h
    by_cases hxi : x = i <;> by_cases hxq : x = q <;> by_cases hxj : x = j <;>
      simp [T,patternActive,hxi,hxq,hxj,hiC,hqC,hjC]
  have he (o : VariableOrder V) :
      CoversPoint (restrictedOrder o (Function.Embedding.subtype (· ∈ T))) P ↔ OrderPattern o C i q j := by
    rw [coversPoint_pair_iff hIQ hIJ hQJ, restricted_finalTriple_iff]
    simpa only [I,Q,J,hTC]
  have hcard : Fintype.card T = C.card+3 := by
    rw [Fintype.card_coe]
    exact patternActive_card hiq hij hqj hC
  calc
    _ = finiteFraction (fun o : VariableOrder V => CoversPoint
        (restrictedOrder o (Function.Embedding.subtype (· ∈ T))) P) := finiteFraction_congr (fun o => (he o).symm)
    _ = _ := by
      have hTc : T.card = C.card+3 := by simpa only [Fintype.card_coe] using hcard
      rw [restricted_point_probability T (by omega) P,hTc]
      simp

/-- The fraction in the paper's displayed rational form. -/
theorem orderPattern_probability_formula (C : Finset V) (i q j : V)
    (hiq : i ≠ q) (hij : i ≠ j) (hqj : q ≠ j) (hC : C ⊆ tripleCap i q j) :
    finiteFraction (fun o : VariableOrder V => OrderPattern o C i q j) =
      2 / (((C.card:ℝ)+1) * ((C.card:ℝ)+2) * ((C.card:ℝ)+3)) := by
  rw [orderPattern_probability C i q j hiq hij hqj hC]
  have hn := Nat.add_one_mul_choose_eq (C.card+1) 1
  have hn' : ((C.card+2).choose 2 : ℝ)*2 = ((C.card:ℝ)+1)*((C.card:ℝ)+2) := by
    have hh : (C.card+2).choose 2 * 2 = (C.card+1)*(C.card+2) := by simpa [mul_comm] using hn.symm
    exact_mod_cast hh
  have hpos : (0:ℝ) < (C.card+2).choose 2 := by
    exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ C.card+2))
  push_cast
  field_simp
  nlinarith

end Characterizations
