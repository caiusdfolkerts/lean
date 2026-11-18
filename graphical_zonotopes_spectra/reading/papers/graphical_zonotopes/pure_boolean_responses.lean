module

public import Papers.GraphicalZonotopes.DisjointMintermModules
public import Papers.GraphicalZonotopes.BooleanResponseCoordinates

@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace BooleanModule
open Finset PowersetTransform
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

theorem rowLower_raw_coefficients (y : SetFunction H) :
    rowLowerEquiv (fun r => y (rowClique r))=
      (fun r : HubResponseRow H => delta (zeta y) r.1.1.1 r.1.1.2 r.2.1) := by
  funext r
  have hu : r.1.1.1∉r.2.1 := by
    intro hm
    exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) hm)
  have hv : r.1.1.2∉r.2.1 := by
    intro hm
    exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) hm)
  change lowerSum (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)
    (fun T => y (insert r.1.1.1 (insert r.1.1.2 T.1))) r.2=_
  rw [lowerSum_restriction _ (fun T : Finset H => y (insert r.1.1.1 (insert r.1.1.2 T))) r.2]
  exact (delta_zeta_reduced (ne_of_lt r.1.2.1) hu hv y).symm

theorem rowLower_edge_mul (q : OrientedEdge (⊤ : SimpleGraph H) → ℝ)
    (y : HubResponseRow H → ℝ) :
    rowLowerEquiv (fun r => q r.1*y r)=fun r => q r.1*rowLowerEquiv y r := by
  funext r
  exact congrFun ((lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)).map_smul
    (q r.1) (fun T => y ⟨r.1,T⟩)) r.2

theorem zeta_delta_coordinate (C : Finset H) :
    zeta (fun D : Finset H => if D=C then 1 else 0)=setMonomial C := by
  funext A
  by_cases hC : C⊆A <;> simp [zeta,setMonomial,hC]

/-- The raw response coefficient array of a disjoint-minterm module has one
clique block and the exact complete-multipartite pair indicator in that block. -/
theorem complementModule_response_coefficients {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) :
    rowLowerEquiv.symm (responseVector (complementModule C blocks))=
      fun r : HubResponseRow H =>
        if rowClique r=C ∧ Crosses blocks r.1.1.1 r.1.1.2 then 1 else 0 := by
  classical
  let q : OrientedEdge (⊤ : SimpleGraph H) → ℝ:=
    fun e => if Crosses blocks e.1.1 e.1.2 then 1 else 0
  let y : HubResponseRow H → ℝ:=fun r => if rowClique r=C then 1 else 0
  have he : (fun r : HubResponseRow H =>
      if rowClique r=C ∧ Crosses blocks r.1.1.1 r.1.1.2 then (1 : ℝ) else 0)=
      fun r => q r.1*y r := by
    funext r
    by_cases hc : rowClique r=C <;>
      by_cases he : Crosses blocks r.1.1.1 r.1.1.2 <;> simp [q,y,hc,he]
  rw [he]
  apply rowLowerEquiv.injective
  rw [rowLowerEquiv.apply_symm_apply,rowLower_edge_mul]
  have hmon : rowLowerEquiv y=
      fun r : HubResponseRow H => delta (setMonomial C) r.1.1.1 r.1.1.2 r.2.1 := by
    simpa only [y,zeta_delta_coordinate] using
      rowLower_raw_coefficients (fun D : Finset H => if D=C then 1 else 0)
  rw [hmon]
  funext r
  have hu : r.1.1.1∉r.2.1 := by
    intro hm
    exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) hm)
  have hv : r.1.1.2∉r.2.1 := by
    intro hm
    exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) hm)
  change negativeResponse (complementModule C blocks) r.1.1.1 r.1.1.2 r.2.1=
    q r.1*delta (setMonomial C) r.1.1.1 r.1.1.2 r.2.1
  rw [complementModule_negative h (ne_of_lt r.1.2.1) hu hv,
    delta_setMonomial (ne_of_lt r.1.2.1) hu hv]
  by_cases he : Crosses blocks r.1.1.1 r.1.1.2
  · obtain ⟨A,hA,B,hB,hAB,ha,hb⟩:=he
    have haC:=h.subsets A hA ha
    have hbC:=h.subsets B hB hb
    have hcross : Crosses blocks r.1.1.1 r.1.1.2 := ⟨A,hA,B,hB,hAB,ha,hb⟩
    simp only [q,hcross,one_mul,haC,hbC,true_and,ite_true]
  · simp only [q,he,zero_mul,false_and,ite_false]

def positivePairBlocks (u v : H) : Finset (Finset H):={{u},{v}}

theorem positivePairBlocks_family (C : Finset H) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u≠v) :
    ComplementFamily C (positivePairBlocks u v) := by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · simp [positivePairBlocks,huv]
  · intro B hB
    simp only [positivePairBlocks,mem_insert,mem_singleton] at hB
    rcases hB with rfl | rfl
    · simpa only [singleton_subset_iff] using hu
    · simpa only [singleton_subset_iff] using hv
  · intro B hB
    simp only [positivePairBlocks,mem_insert,mem_singleton] at hB
    rcases hB with rfl | rfl <;> exact singleton_nonempty _
  · intro A hA B hB hAB
    simp only [positivePairBlocks,mem_insert,mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact False.elim (hAB rfl)
    · simp [huv]
    · simp [huv.symm]
    · exact False.elim (hAB rfl)

theorem crosses_positivePairBlocks {u v : H} (huv : u≠v) (a b : H) :
    Crosses (positivePairBlocks u v) a b ↔
      (a=u ∧ b=v) ∨ (a=v ∧ b=u) := by
  classical
  constructor
  · rintro ⟨A,hA,B,hB,hAB,ha,hb⟩
    simp only [positivePairBlocks,mem_insert,mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact False.elim (hAB rfl)
    · exact Or.inl ⟨mem_singleton.mp ha,mem_singleton.mp hb⟩
    · exact Or.inr ⟨mem_singleton.mp ha,mem_singleton.mp hb⟩
    · exact False.elim (hAB rfl)
  · rintro (⟨ha,hb⟩ | ⟨ha,hb⟩)
    · subst a; subst b
      exact ⟨{u},by simp [positivePairBlocks],{v},by simp [positivePairBlocks],
        by simpa using huv,mem_singleton_self _,mem_singleton_self _⟩
    · subst a; subst b
      exact ⟨{v},by simp [positivePairBlocks],{u},by simp [positivePairBlocks],
        by simpa using huv.symm,mem_singleton_self _,mem_singleton_self _⟩

def positivePairModule (C : Finset H) (u v : H) : SetFunction H:=
  complementModule C (positivePairBlocks u v)

/-- The pure positive module of Lemma7.4, with every ambient hub retained. -/
theorem positivePairModule_coefficients (C : Finset H) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u<v) :
    rowLowerEquiv.symm (responseVector (positivePairModule C u v))=
      fun r : HubResponseRow H =>
        if rowClique r=C ∧ r.1.1.1=u ∧ r.1.1.2=v then 1 else 0 := by
  rw [positivePairModule,complementModule_response_coefficients
    (positivePairBlocks_family C hu hv (ne_of_lt huv))]
  funext r
  rw [crosses_positivePairBlocks (ne_of_lt huv)]
  have hn : ¬(r.1.1.1=v ∧ r.1.1.2=u) := by
    rintro ⟨ha,hb⟩
    have hh:=r.1.2.1
    rw [ha,hb] at hh
    exact (not_lt_of_ge huv.le) hh
  simp only [or_false,hn,and_assoc]

theorem positivePairModule_essential (C : Finset H) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u≠v) {a : H} (ha : a∈C) :
    Essential (positivePairModule C u v) a :=
  (positivePairBlocks_family C hu hv huv).essential ha

end BooleanModule
end GraphicalZonotopes
