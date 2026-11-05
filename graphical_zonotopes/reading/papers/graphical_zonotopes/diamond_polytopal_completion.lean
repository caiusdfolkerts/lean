module

public import Papers.GraphicalZonotopes.DiamondGeometricObstruction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- On every actual finite weak summand, ordinary polytopal and compact-convex
indecomposability agree. No full-dimension hypothesis is needed. -/
theorem minkowskiIndecomposable_iff_polytopal_of_weak_summand
    {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    MinkowskiIndecomposable Q ↔ PolytopalMinkowskiIndecomposable Q := by
  constructor
  · intro hi
    exact ⟨hi.1,fun P R hP hR he =>
      hi.2 P R hP.compact hR.compact hP.convex hR.convex he⟩
  · intro hi
    obtain ⟨a,ha,R,hR,hcR,hnR,he⟩ := hw
    have hzn : Normalized (a • graphFunction G) := by
      change a * graphFunction G ∅=0
      rw [graphFunction_normalized,mul_zero]
    have hzs : Supermodular (a • graphFunction G) :=
      (graphFunction_supermodular G).smul ha.le
    have hsum : Q+R=basePolytope (a • graphFunction G) := by
      rw [basePolytope_smul (graphFunction_normalized G)
        (graphFunction_supermodular G) ha.le,baseGraphFunction_eq_graphicalZonotope]
      exact he
    have hn := lowerSupport_normalized hQ.compact hi.1
    have hsm := summand_lowerSupport_supermodular hzn hzs hQ.compact hR hi.1 hnR hsum
    have hbody := summand_eq_basePolytope hzn hzs hQ.compact hR hQ.convex hi.1 hnR hsum
    exact (minkowskiIndecomposable_iff_polytopal
      ⟨lowerSupport Q,hn,hsm,hbody⟩).mpr hi

/-- The literal dimension supremum with ordinary polytopal decompositions. -/
def maximumPolytopalIndecomposableDimension (G : SimpleGraph V) : ℕ :=
  sSup {d : ℕ | ∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧
    PolytopalMinkowskiIndecomposable Q ∧
    IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
    Module.finrank ℝ (vectorSpan ℝ Q)=d}

/-- Equality of the two dimension invariants, for every finite graph. -/
theorem maximumIndecomposableDimension_eq_polytopal (G : SimpleGraph V) :
    maximumIndecomposableDimension G=maximumPolytopalIndecomposableDimension G := by
  unfold maximumIndecomposableDimension maximumPolytopalIndecomposableDimension
  congr 1
  ext d
  constructor
  · rintro ⟨Q,hQ,hi,hw,hd⟩
    exact ⟨Q,hQ,(minkowskiIndecomposable_iff_polytopal_of_weak_summand hQ hw).mp hi,hw,hd⟩
  · rintro ⟨Q,hQ,hi,hw,hd⟩
    exact ⟨Q,hQ,(minkowskiIndecomposable_iff_polytopal_of_weak_summand hQ hw).mpr hi,hw,hd⟩

/-- Allowing zero as a dilation factor adds no full-dimensional lattice
witness when there are at least two coordinates. -/
theorem not_fullLatticeSummandAt_zero (G : SimpleGraph V)
    (hn : 2≤Fintype.card V) : ¬FullLatticeSummandAt G 0 := by
  rintro ⟨Q,_,hi,hd,R,_,_,hnR,he⟩
  obtain ⟨r,hr⟩ := hnR
  have hpoint : ∀ q∈Q,q= -r := by
    intro q hq
    have hm : q+r∈(0 : ℝ) • graphicalZonotope G :=
      he ▸ (show q+r∈Q+R from ⟨q,hq,r,hr,rfl⟩)
    obtain ⟨z,_,hz⟩ := hm
    have hqr : q+r=0 := by simpa only [zero_smul] using hz.symm
    calc
      q=q+r-r := by abel
      _= -r := by rw [hqr];simp
  have hQ : Q={-r} := by
    ext q
    constructor
    · intro hq
      exact Set.mem_singleton_iff.mpr (hpoint q hq)
    · intro hq
      have heq := Set.mem_singleton_iff.mp hq
      obtain ⟨q₀,hq₀⟩ := hi.1
      simpa only [heq,hpoint q₀ hq₀] using hq₀
  change Module.finrank ℝ (vectorSpan ℝ Q)=Fintype.card V-1 at hd
  rw [hQ,_root_.vectorSpan_singleton,_root_.finrank_bot] at hd
  omega

namespace DiamondBook

/-- The entire diamond theorem with ordinary polytopal indecomposability
in both its dimension invariant and its literal geometric obstruction. -/
theorem paper_theorem_8_1_polytopal :
    (∀ k : ℕ,1≤k → maximumPolytopalIndecomposableDimension (twoSingletonGraph 2 k)=
      min (k+3) 9) ∧
    (∃ Q : Set (MultipartiteVertex 6 → ℝ),
      LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsMinkowskiSummand Q ((4 : ℝ) • graphicalZonotope (twoSingletonGraph 2 6)) ∧
      directionCount Q=25) ∧
    ¬∃ H : SimpleGraph (MultipartiteVertex 6),
      H≤twoSingletonGraph 2 6 ∧ IsThreeTree H ∧
      ∃ Q : Set (MultipartiteVertex 6 → ℝ), IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope H) := by
  obtain ⟨hm,⟨Q,hQ,hi,hd,hs,he⟩,ho⟩ := paper_theorem_8_1_literal
  refine ⟨?_,⟨Q,hQ,?_,hd,hs,he⟩,?_⟩
  · intro k hk
    rw [←maximumIndecomposableDimension_eq_polytopal]
    exact hm k hk
  · exact ⟨hi.1,fun P R hP hR heq =>
      hi.2 P R hP.compact hR.compact hP.convex hR.convex heq⟩
  · rintro ⟨H,hsub,htree,Q,hfin,hind,hfull,hweak⟩
    apply ho
    exact ⟨H,hsub,htree,Q,hfin,
      (minkowskiIndecomposable_iff_polytopal_of_weak_summand hfin hweak).mpr hind,
      hfull,hweak⟩

end DiamondBook
end GraphicalZonotopes
