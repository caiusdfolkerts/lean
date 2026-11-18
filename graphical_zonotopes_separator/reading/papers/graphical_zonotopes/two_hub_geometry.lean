module

public import Papers.GraphicalZonotopes.TwoHubAssembly
public import Papers.GraphicalZonotopes.TwoHubGraphIso

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace TwoHub
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem module_u_essential (ε : Finset I) (i : I) : Essential (moduleFunction ε) (u i) := by
  refine ⟨hubSet {false},by simp [u],?_⟩
  rw [module_spoke,corner_false]

theorem module_a_essential (ε : Finset I) : Essential (moduleFunction ε) a := by
  by_cases he : ε=∅
  · refine ⟨context ∅ (∅ : Finset I),by simp [a],?_⟩
    rw [a,←context_insert_hub,insert_empty_eq,module_a_zero_cover]
    simp [he,eta]
  · obtain ⟨i,hi⟩:=nonempty_iff_ne_empty.mpr he
    refine ⟨context ∅ {i},by simp [a],?_⟩
    rw [a,←context_insert_hub,insert_empty_eq,module_a_zero_cover]
    simp [eta,he,hi]

theorem module_b_essential [Nonempty I] (ε : Finset I) : Essential (moduleFunction ε) b := by
  by_cases he : ε=univ
  · let i : I:=Classical.choice ‹Nonempty I›
    refine ⟨context ∅ {i},by simp [b],?_⟩
    rw [b,←context_insert_hub,insert_empty_eq,module_b_zero_cover]
    simp [he]
  · obtain ⟨i,hi⟩:=nonempty_iff_ne_empty.mpr
      (show univ\ε≠∅ from fun h => he (eq_univ_iff_forall.mpr
        (fun i => (sdiff_eq_empty_iff_subset.mp h) (mem_univ i))))
    let Y:=(univ\ε).erase i
    have hiε : i∉ε := (mem_sdiff.mp hi).2
    have hiY : i∉Y := by simp [Y]
    have hYi : insert i Y=univ\ε := insert_erase hi
    have hb0:=module_b_complement_zero ε
    have hd:=module_bi_delta ε i (context (∅ : Finset Bool) Y) (by simp [b]) (by simpa [u] using hiY)
    simp only [a,b,u,mem_context_hub,notMem_empty,not_false_eq_true,ite_false,hiε] at hd
    refine ⟨context (∅ : Finset Bool) Y,by simp [b],?_⟩
    rw [b,←context_insert_hub,insert_empty_eq]
    have hctx : insert (u i) (context (∅ : Finset Bool) Y)=context (∅ : Finset Bool) (univ\ε) := by
      rw [u,←context_insert,hYi]
    have hctxb : insert b (context (∅ : Finset Bool) (univ\ε))=context {true} (univ\ε) := by
      rw [b,←context_insert_hub,insert_empty_eq]
    have hctxbY : insert b (context (∅ : Finset Bool) Y)=context {true} Y := by
      rw [b,←context_insert_hub,insert_empty_eq]
    change delta (moduleFunction ε) b (u i) (context (∅ : Finset Bool) Y)= -1 at hd
    simp only [delta,hctx,hctxb,hctxbY] at hd
    linarith

theorem module_all_essential [Nonempty I] (ε : Finset I) (v : Hub I) :
    Essential (moduleFunction ε) v := by
  rcases v with e|i
  · cases e
    · exact module_a_essential ε
    · exact module_b_essential ε
  · exact module_u_essential ε i

theorem balancing_a_essential (i : I) : Essential (balancing i) a := by
  refine ⟨{b},by simp [a,b],?_⟩
  simp [balancing,a,b,u]

theorem family_connected [Nonempty I] : (essentialSpokeGraph (family (I:=I))).Connected := by
  let j₀ : Index I:=.inl ∅
  have hhub (v : Hub I) :
      (essentialSpokeGraph family).Adj (.inl v) (.inr j₀) := module_all_essential ∅ v
  have houter (j : Index I) :
      (essentialSpokeGraph family).Adj (.inl (a : Hub I)) (.inr j) := by
    cases j with
    | inl ε => exact module_a_essential ε
    | inr i => exact balancing_a_essential i
  have reach (v : Hub I⊕Index I) :
      (essentialSpokeGraph family).Reachable v (.inl (a : Hub I)) := by
    cases v with
    | inl v => exact (hhub v).reachable.trans (hhub a).reachable.symm
    | inr j => exact (houter j).reachable.symm
  exact ⟨fun x y => (reach x).trans (reach y).symm⟩

theorem construction_fullDimension [Nonempty I] : FullDimension (basePolytope (construction (I:=I))) := by
  apply finrank_vectorSpan_eq_of_connected_slacks construction_normalized.1
    construction_supermodular family_connected
  intro x y hxy
  exact essential_spoke_slack weights_pos hxy

namespace IntegerHelpers
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem conditional (P : Finset V → Prop) [∀ S,Decidable (P S)]
    {f : SetFunction V} (hf : IntegerValued f) :
    IntegerValued (fun S => if P S then f S else 0) := by
  intro S
  by_cases h : P S
  · simpa [h] using hf S
  · exact ⟨0,by simp [h]⟩

theorem constant (n : ℤ) : IntegerValued (fun _ : Finset V => (n : ℝ)) :=
  fun _ => ⟨n,rfl⟩

end IntegerHelpers

theorem pair_integer (A B C : ℤ) : IntegerValued (pair (A : ℝ) (B : ℝ) (C : ℝ)) := by
  exact ((IntegerHelpers.conditional (fun S : Finset Bool => false∈S) (IntegerHelpers.constant A)).add
    (IntegerHelpers.conditional (fun S : Finset Bool => true∈S) (IntegerHelpers.constant B))).add
    (IntegerHelpers.conditional (fun S : Finset Bool => false∈S∧true∈S) (IntegerHelpers.constant C))

theorem corner_integer (e : Bool) : IntegerValued (corner e) := by
  intro S
  rcases corner_values e S with h|h
  · exact ⟨0,by simpa using h⟩
  · exact ⟨1,by simpa using h⟩

theorem central_integer (ε : Finset I) : IntegerValued (central ε) := by
  have he : eta ε=((if ε=∅ then 1 else 0 : ℤ) : ℝ) := by
    unfold eta
    split_ifs <;> norm_num
  simpa only [central,he,Int.cast_sub,Int.cast_natCast,Int.cast_one] using
    pair_integer (if ε=∅ then 1 else 0) ((Fintype.card I : ℤ)-(ε.card : ℤ))
      ((ε.card : ℤ)-1)

theorem module_integer (ε : Finset I) : IntegerValued (moduleFunction ε) := by
  apply (boundaryLift_integerValued (central_integer ε)).add
  apply IntegerValued.finset_sum
  intro i hi
  simpa only [one_smul] using branchLift_integerValued i (corner_integer (decide (i∈ε)))

theorem family_integer (j : Index I) : IntegerValued (family j) := by
  cases j with
  | inl ε => exact module_integer ε
  | inr i => exact (balancing_boolean i).integerValued

theorem boundaryCentral_integer : IntegerValued (boundaryCentral (I:=I)) := by
  unfold boundaryCentral assembled
  have hz : IntegerValued (pair (0 : ℝ) 0 1) := by simpa using pair_integer 0 0 1
  apply (boundaryLift_integerValued hz).add
  apply IntegerValued.finset_sum
  intro i hi
  simpa only [one_smul,Int.cast_natCast] using
    branchLift_integerValued i
      (IntegerHelpers.conditional (fun S : Finset Bool => true∈S)
        (IntegerHelpers.constant (missCount i : ℤ)))

theorem construction_integer : IntegerValued (construction (I:=I)) := by
  unfold construction assembled
  apply (boundaryLift_integerValued boundaryCentral_integer).add
  apply IntegerValued.finset_sum
  intro j hj
  cases j with
  | inl ε => simpa only [weights,family,one_smul] using branchLift_integerValued (Sum.inl ε : Index I) (module_integer ε)
  | inr i => simpa only [weights,family,Int.cast_natCast] using
      (branchLift_integerValued (Sum.inr i : Index I) (balancing_boolean i).integerValued).int_smul (missCount i : ℤ)

/-- The construction is an actual integral, full-dimensional
Minkowski-indecomposable weak summand for arbitrary nonempty finite I. -/
theorem exponential_lattice_witness [Nonempty I] :
    LatticePolytope (basePolytope (construction (I:=I))) ∧
    MinkowskiIndecomposable (basePolytope (construction (I:=I))) ∧
    FullDimension (basePolytope (construction (I:=I))) ∧
    IsWeakMinkowskiSummand (basePolytope (construction (I:=I)))
      (graphicalZonotope (graph (I:=I) (J:=Index I))) := by
  refine ⟨construction_integer.basePolytope construction_normalized.1 construction_supermodular,
    construction_extreme.minkowskiIndecomposable,construction_fullDimension,?_⟩
  exact (isWeakMinkowskiSummand_graphical_iff construction_normalized.1
    construction_supermodular).mpr construction_graphical

end TwoHub
end GraphicalZonotopes
