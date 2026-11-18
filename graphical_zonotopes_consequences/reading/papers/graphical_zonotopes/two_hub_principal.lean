module

public import Papers.GraphicalZonotopes.TwoHubAttainment
public import Papers.GraphicalZonotopes.TwoHubCapacity
public import Papers.GraphicalZonotopes.PrincipalTargets

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset
open scoped BigOperators Pointwise

theorem maximum_dimension_upper (p b : ℕ) :
    maximumIndecomposableDimension (twoSingletonGraph p b)≤
      min (p+b+1) (2^p+2*p+1) := by
  rw [←maximum_dimension_model_eq]
  exact Capacity.maximum_dimension_upper p b

theorem maximum_dimension_upper_symmetric (p b : ℕ) :
    maximumIndecomposableDimension (twoSingletonGraph p b)≤
      min (p+b+1) (2^(min p b)+2*min p b+1) := by
  by_cases hpb : p≤b
  · simpa only [min_eq_left hpb] using maximum_dimension_upper p b
  · have hbp : b≤p:=by omega
    rw [maximum_dimension_swap]
    simpa only [min_eq_right hbp,Nat.add_comm b p] using maximum_dimension_upper b p

/-- The exact dimension formula of Theorem8.7, for all positive part
sizes, with no restriction to the explicit support pattern. -/
theorem maximum_dimension (p b : ℕ) (hp : 1≤p) (hb : 1≤b) :
    maximumIndecomposableDimension (twoSingletonGraph p b)=
      min (p+b+1) (2^(min p b)+2*min p b+1) :=
  le_antisymm (maximum_dimension_upper_symmetric p b) (all_attainment p b hp hb).dimension_le

theorem full_dimension_arithmetic (p b : ℕ) :
    p+b+1≤2^(min p b)+2*min p b+1 ↔ max p b≤2^(min p b)+min p b := by
  by_cases h : p≤b
  · simp only [min_eq_left h,max_eq_right h]
    omega
  · have hh : b≤p:=by omega
    simp only [min_eq_right hh,max_eq_left hh]
    omega

theorem supports_full_iff (p b : ℕ) (hp : 1≤p) (hb : 1≤b) :
    SupportsFullIndecomposable (twoSingletonGraph p b) ↔
      max p b≤2^(min p b)+min p b := by
  constructor
  · rintro ⟨Q,hQ,hi,hd,hw⟩
    have hm:=(dimension_le_maximum hQ hi hw).trans (maximum_dimension_upper_symmetric p b)
    rw [hd,twoSingleton_card] at hm
    have hn : p+b+1≤2^(min p b)+2*min p b+1:=by omega
    exact (full_dimension_arithmetic p b).mp hn
  · intro h
    obtain ⟨Q,hQ,hl,hi,hw,hd⟩:=(all_attainment p b hp hb).polytope
    refine ⟨Q,hQ,hi,?_,hw⟩
    change Module.finrank ℝ (vectorSpan ℝ Q)=_
    rw [hd,min_eq_left ((full_dimension_arithmetic p b).mpr h),twoSingleton_card]
    omega

/-- The dimension formula, exact full-dimensionality criterion, and lattice
attainment in the original coordinate model of the paper. -/
theorem two_singleton_classification : Targets.TwoSingletonClassification := by
  intro p b hp hb
  refine ⟨maximum_dimension p b hp hb,supports_full_iff p b hp hb,?_⟩
  obtain ⟨Q,hQ,hl,hi,hw,hd⟩:=(all_attainment p b hp hb).polytope
  exact ⟨Q,hl,hi,hw,hd⟩

theorem twoSingleton_cliqueFree (p b : ℕ) : (twoSingletonGraph p b).CliqueFree 5 := by
  intro S hS
  have hinj : Function.Injective (fun v : S => v.1.1) := by
    intro x y he
    by_contra hne
    have hxy:=hS.1 x.2 y.2 (fun h => hne (Subtype.ext h))
    exact hxy he
  have hc:=Fintype.card_le_of_injective (fun v : S => v.1.1) hinj
  simp only [Fintype.card_coe,Fintype.card_fin] at hc
  rw [hS.2] at hc
  omega

/-- The whole printed Theorem8.4: an actual lattice summand at the explicit
integral dilation, and stabilization at every larger fourth part. -/
theorem exponential_family (p : ℕ) (hp : 1≤p) :
    (twoSingletonGraph p (2^p+p)).CliqueFree 5 ∧
    (∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,2^p+p] i))→ℝ),
      LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=2^p+2*p+1 ∧
      IsMinkowskiSummand Q ((((p-1)*2^p+2 : ℕ) : ℝ) •
        graphicalZonotope (twoSingletonGraph p (2^p+p)))) ∧
    ∀ b : ℕ,2^p+p≤b →
      maximumIndecomposableDimension (twoSingletonGraph p b)=2^p+2*p+1 := by
  refine ⟨twoSingleton_cliqueFree _ _,(exponential_lattice_summand p hp).polytope,?_⟩
  intro b hb
  have hpb : p≤b:=(Nat.le_add_left p (2^p)).trans hb
  rw [maximum_dimension p b hp (by omega),min_eq_left hpb,min_eq_right (by omega)]

end GraphicalZonotopes.TwoHub
