module

public import Papers.GraphicalZonotopes.SignedPairBases
public import Papers.GraphicalZonotopes.OrdinaryBookBlocks

@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule
open Finset
open scoped BigOperators

/-- Distinct numerical hub labels have a unique largest endpoint sum: the
pair of the two largest vertices of the clique. -/
theorem exists_unique_maximum_label_pair {s : ℕ} (C : Finset (Fin s)) (hC : 3≤C.card) :
    ∃ e₀ : PairIn C,∀ e : PairIn C,e≠e₀ → endpointLabels C e<endpointLabels C e₀ := by
  have hne : C.Nonempty := card_pos.mp (by omega)
  let m := C.max' hne
  have hm : m∈C := max'_mem C hne
  have hecard : 2≤(C.erase m).card := by rw [card_erase_of_mem hm]; omega
  have hene : (C.erase m).Nonempty := card_pos.mp (by omega)
  let n := (C.erase m).max' hene
  have hn : n∈C.erase m := max'_mem _ hene
  have hnC := (mem_erase.mp hn).2
  have hnm : n<m := lt_of_le_of_ne (le_max' C n hnC) (mem_erase.mp hn).1
  let e₀ := orderedPair C n m hnm hnC hm
  refine ⟨e₀,?_⟩
  intro e he
  have hv : e.1.1.2≤m := le_max' C _ e.2.2
  have hu : e.1.1.1<m := lt_of_lt_of_le e.1.2.1 hv
  have huErase : e.1.1.1∈C.erase m := mem_erase.mpr ⟨ne_of_lt hu,e.2.1⟩
  have hun : e.1.1.1≤n := le_max' _ _ huErase
  have heq : ¬(e.1.1.1=n ∧ e.1.1.2=m) := by
    rintro ⟨hu,hv⟩
    exact he (Subtype.ext (Subtype.ext (Prod.ext hu hv)))
  have hun' : e.1.1.1.val≤n.val := hun
  have hvm' : e.1.1.2.val≤m.val := hv
  have heq' : ¬(e.1.1.1.val=n.val ∧ e.1.1.2.val=m.val) := by
    rintro ⟨hu,hv⟩
    exact heq ⟨Fin.ext hu,Fin.ext hv⟩
  have hh : e.1.1.1.val+e.1.1.2.val<n.val+m.val := by omega
  change (e.1.1.1.val : ℝ)+(e.1.1.2.val : ℝ)<(n.val : ℝ)+(m.val : ℝ)
  exact_mod_cast hh

/-- Every clique block admits a full independent signed pair basis cancelling
any signed endpoint-label vector, with positive integral scales. -/
theorem saturated_pair_basis {s : ℕ} (C : Finset (Fin s)) (hC : 3≤C.card)
    (ε : ℝ) (hε : ε=1 ∨ ε= -1) :
    Nonempty (WeightedPureBlock C (2*s : ℕ) (ε • blockClass C (endpointLabels C))
      (C.card.choose 2-1)) := by
  obtain ⟨e₀,he₀⟩ := exists_unique_maximum_label_pair C hC
  let w : PairIn C → ℤ := fun e =>
    ((e₀.1.1.1.val : ℤ)+(e₀.1.1.2.val : ℤ))-((e.1.1.1.val : ℤ)+(e.1.1.2.val : ℤ))
  have hw0 : w e₀=0 := by simp [w]
  have hwp : ∀ e,e≠e₀ → 0<w e := by
    intro e he
    dsimp only [w]
    apply sub_pos.mpr
    have hh := he₀ e he
    unfold endpointLabels at hh
    exact_mod_cast hh
  have hwb : ∀ e,w e≤(2*s : ℕ) := by
    intro e
    have h1 := e₀.1.1.1.isLt
    have h2 := e₀.1.1.2.isLt
    dsimp [w,endpointLabels]
    push_cast
    omega
  have hε' : -ε=1 ∨ -ε= -1 := by rcases hε with rfl | rfl <;> norm_num
  let P := signed_pair_basis C hC e₀ (-ε) hε' w hw0 hwp (2*s : ℕ) (fun e _ => hwb e)
  have hfun : (fun e : PairIn C => (w e : ℝ))=
      (fun _ : PairIn C => (endpointLabels C e₀ : ℝ))-
      (fun e : PairIn C => (endpointLabels C e : ℝ)) := by
    funext e
    simp [w,endpointLabels]
  have hz : blockClass C (fun _ : PairIn C => (endpointLabels C e₀ : ℝ))=0 :=
    (blockClass_eq_zero_iff C e₀ _).mpr ⟨_,fun _ => rfl⟩
  have ht : blockClass C ((-ε) • fun e : PairIn C => (w e : ℝ))=
      ε • blockClass C (fun e => (endpointLabels C e : ℝ)) := by
    rw [hfun,map_smul,map_sub,hz,zero_sub]
    simp
  exact ⟨ht ▸ P⟩

end GraphicalZonotopes.BooleanModule
