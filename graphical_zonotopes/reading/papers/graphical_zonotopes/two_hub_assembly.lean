module

public import Papers.GraphicalZonotopes.TwoHubCircuit
public import Papers.GraphicalZonotopes.TwoHubGraph

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace TwoHub
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem boundaryCentral_normalized : TranslationNormalized (boundaryCentral (I:=I)) := by
  apply assembled_normalized_general
  · constructor
    · simp [Normalized,pair]
    · intro v
      cases v <;> simp [pair]
  · intro i
    simp

theorem boundaryCentral_ab (S : Finset (Hub I)) (ha : a∉S) (hb : b∉S) :
    delta boundaryCentral a b S=1 := by
  have hh : hubs S=∅ := by
    ext v
    cases v <;> simp_all [a,b]
  rw [boundaryCentral,a,b,delta_assembled_hubs,hh,delta_pair]
  have hd (i : I) : delta (fun X : Finset Bool => if true∈X then (missCount i : ℝ) else 0)
      false true ∅=0 := by simp [delta]
  simp only [hd,ite_self,mul_zero,sum_const_zero,add_zero]

theorem boundaryCentral_ai (i : I) (S : Finset (Hub I)) (hi : u i∉S) :
    delta boundaryCentral a (u i) S=0 := by
  rw [boundaryCentral,a,u,delta_assembled_spoke _ _ _ _ _ _ hi]
  simp

theorem boundaryCentral_bi (i : I) (S : Finset (Hub I)) (hb : b∉S) (hi : u i∉S) :
    delta boundaryCentral b (u i) S=(missCount i : ℝ) := by
  have hx : true∉hubs S := by simpa [b] using hb
  rw [boundaryCentral,b,u,delta_assembled_spoke _ _ _ _ _ _ hi]
  simp [hx]

theorem boundaryCentral_outer : OuterZero (boundaryCentral (I:=I)) := by
  intro i j hij S hi hj
  exact delta_assembled_outer _ _ _ i j hij S hi hj

theorem missing_sum (i : I) :
    (∑ ε : Finset I,if i∈ε then (0 : ℝ) else 1)=(missCount i : ℝ) := by
  have he : (∑ ε : Finset I,if i∈ε then (0 : ℝ) else 1)=
      ∑ ε∈univ.filter (fun ε : Finset I => i∉ε),(1 : ℝ) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro ε hε
    by_cases hi : i∈ε <;> simp [hi]
  rw [he]
  simp [missCount]

theorem family_outer_zero (j : Index I) : OuterZero (family j) := by
  cases j with
  | inl ε => exact module_outer_zero ε
  | inr i => exact balancing_outer_zero i

/-- The central coefficients match the exact negative responses on every
boundary edge and every conditioning set. -/
theorem central_compatible : Compatible (boundaryCentral (I:=I)) family weights := by
  have hab (S : Finset (Hub I)) (ha : a∉S) (hb : b∉S) :
      delta boundaryCentral a b S=
        ∑ j : Index I,weights j*negativeResponse (family j) a b S := by
    rw [boundaryCentral_ab S ha hb,response_sum_ab _ _ ha hb]
    rfl
  have hai (i : I) (S : Finset (Hub I)) (ha : a∉S) (hi : u i∉S) :
      delta boundaryCentral a (u i) S=
        ∑ j : Index I,weights j*negativeResponse (family j) a (u i) S := by
    rw [boundaryCentral_ai i S hi,response_sum_ai _ _ _ ha hi]
  have hbi (i : I) (S : Finset (Hub I)) (hb : b∉S) (hi : u i∉S) :
      delta boundaryCentral b (u i) S=
        ∑ j : Index I,weights j*negativeResponse (family j) b (u i) S := by
    rw [boundaryCentral_bi i S hb hi,response_sum_bi _ _ _ hb hi]
    by_cases ha : a∈S
    · simp [ha,weights]
    · simp only [ha,ite_false,weights,missing_sum]
  have hij (i j : I) (hne : i≠j) (S : Finset (Hub I)) (hi : u i∉S) (hj : u j∉S) :
      delta boundaryCentral (u i) (u j) S=
        ∑ k : Index I,weights k*negativeResponse (family k) (u i) (u j) S := by
    have hz : delta boundaryCentral (u i) (u j) S=0 := boundaryCentral_outer i j hne S hi hj
    rw [hz]
    simp only [family_outer_response _ _ _ hne S hi hj,mul_zero,sum_const_zero]
  have swap (x y : Hub I) (S : Finset (Hub I))
      (h : delta boundaryCentral x y S=
        ∑ j : Index I,weights j*negativeResponse (family j) x y S) :
      delta boundaryCentral y x S=
        ∑ j : Index I,weights j*negativeResponse (family j) y x S := by
    simpa only [negativeResponse,delta_comm y x] using h
  intro x y hxy S hx hy
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      cases x <;> cases y
      · exact False.elim (hxy rfl)
      · exact hab S hx hy
      · exact swap a b S (hab S hy hx)
      · exact False.elim (hxy rfl)
    | inr i =>
      cases x
      · exact hai i S hx hy
      · exact hbi i S hx hy
  | inr i =>
    cases y with
    | inl y =>
      cases y
      · exact swap a (u i) S (hai i S hy hx)
      · exact swap b (u i) S (hbi i S hy hx)
    | inr j => exact hij i j (fun he => hxy (congrArg Sum.inr he)) S hx hy

theorem construction_normalized : TranslationNormalized (construction (I:=I)) :=
  assembled_normalized_general boundaryCentral_normalized family family_empty weights

theorem construction_supermodular [Nonempty I] : Supermodular (construction (I:=I)) :=
  assembled_supermodular_general boundaryCentral family family_monotone weights
    (fun j => (weights_pos j).le) central_compatible

theorem construction_extreme [Nonempty I] : ExtremeSupermodular (construction (I:=I)) := by
  apply positive_circuit_extreme_general boundaryCentral_normalized family_empty family_monotone
    family_privateRigid (fun j => (weights_pos j).le) _ central_compatible unique_relation
  refine ⟨Sum.inr (Classical.choice ‹Nonempty I›),univ,?_⟩
  simp only [family,weights,(balancing_boolean _).full,mul_one]
  exact ne_of_gt (Nat.cast_pos.mpr (missCount_pos _) : (0 : ℝ)<_)

theorem construction_graphical : Graphical (graph (I:=I) (J:=Index I)) construction := by
  intro x y hxy hnon S hx hy
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          cases x <;> cases y <;> simp_all [graph,color]
        | inr i => cases x <;> simp_all [graph,color]
      | inr i =>
        cases y with
        | inl y => cases y <;> simp_all [graph,color]
        | inr j =>
          have hij : i≠j := fun he => hxy (by subst j; rfl)
          have hi : u i∉hubs S := by simpa [u] using hx
          have hj : u j∉hubs S := by simpa [u] using hy
          rw [construction,delta_assembled_hubs,boundaryCentral_outer i j hij _ hi hj]
          simp only [family_outer_zero _ i j hij _ hi hj,ite_self,mul_zero,sum_const_zero,add_zero]
    | inr j =>
      cases x with
      | inl x => cases x <;> simp_all [graph,color]
      | inr i => simp_all [graph,color]
  | inr i =>
    cases y with
    | inl y =>
      cases y with
      | inl y => cases y <;> simp_all [graph,color]
      | inr j => simp_all [graph,color]
    | inr j =>
      exact delta_assembled_outer _ _ _ i j
        (fun he => hxy (congrArg Sum.inr he)) S hx hy

end TwoHub
end GraphicalZonotopes
