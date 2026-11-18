module

public import Papers.GraphicalZonotopes.PathJoinGeometry
public import Papers.GraphicalZonotopes.PathJoinThreeTree
public import Papers.GraphicalZonotopes.ThreeTreeLatticeCoefficients
public import Papers.GraphicalZonotopes.ThreeTreeSlack

/-! # The sharp real lattice dilation for every two-hub path join -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped Classical
attribute [local instance] Classical.propDecidable
open scoped BigOperators Pointwise

/-- The lower bound concerns every actual lattice indecomposable summand,
not only the explicit Appendix B construction. The index n means m=n+2.
-/
theorem lattice_dilation_lower_bound (n : ℕ)
    {Q : Set (Vertex n → ℝ)} (hQ : LatticePolytope Q)
    (hi : MinkowskiIndecomposable Q) (hd : FullDimension Q)
    {a : ℝ} (ha : 0<a) (hsum : IsMinkowskiSummand Q (a • graphicalZonotope (graph n))) :
    (((n+2)/2 : ℕ) : ℝ)≤a := by
  classical
  have hG := graph_isThreeTree n
  have hcoeff := threeTree_lattice_four_coefficients (by omega : 4≤n+4) hG hQ hi hd ha hsum
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR ha.le he
  let f := lowerSupport Q
  let z := normalize f
  have hzn : TranslationNormalized z := normalize_translationNormalized hfn
  have hzs : Supermodular z := hfs.normalize
  have hzi : IntegerValued z := (hQ.lowerSupport_integerValued hi.1).normalize
  have hzg : Graphical (graph n) z := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hzy : CliqueSupported (graph n) (mobius z) :=
    (mobius_cliqueSupported_iff (graph n) z).mpr ⟨hzn,hzg⟩
  have hzb : ∀ u v,u≠v → (graph n).Adj u v → ∀ S,u∉S → v∉S → delta z u v S≤a := by
    intro u v huv hadj S hu hv
    rw [delta_normalize f huv hu hv]
    exact hbound u v huv hadj S hu hv
  have hb := threeTree_integral_slack_bound hG hzs hzi hzy hzb
    (graph_hubA.mpr (hubA_ne_hubB n))
  rw [tetrahedra_hub_filter] at hb
  have hsumlower : ((n+1 : ℕ) : ℝ)≤∑ C∈tetrahedra (graph n),|mobius z C| := by
    calc
      ((n+1 : ℕ) : ℝ)=((tetrahedra (graph n)).card : ℝ) := by rw [tetrahedra_count]
      _ = ∑ C∈tetrahedra (graph n),(1 : ℝ) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro C hC
        obtain ⟨k,hk,hvalue⟩ := hcoeff C hC
        have hc : C.card=4 := by
          have hC' := hC
          simp only [tetrahedra,mem_filter,mem_univ,true_and] at hC'
          exact hC'.1
        rw [mobius_four_normalize hc,hvalue]
        have hpos : (0 : ℤ)<abs k := abs_pos.mpr hk
        have hone : (1 : ℤ)≤abs k := by omega
        exact_mod_cast hone
  have hnat : 2*((n+2)/2)≤n+2 := Nat.mul_div_le n.succ.succ 2
  have hreal : (2 : ℝ)*(((n+2)/2 : ℕ) : ℝ)≤(n : ℝ)+2 := by exact_mod_cast hnat
  have hceil : ((((n+2)/2 : ℕ) : ℤ) : ℤ)≤
      Int.ceil ((1/2 : ℝ)*∑ C∈tetrahedra (graph n),|mobius z C|) := by
    have hx : ((((n+2)/2 : ℕ) : ℤ)-1)<
        Int.ceil ((1/2 : ℝ)*∑ C∈tetrahedra (graph n),|mobius z C|) :=
      Int.lt_ceil.mpr (by
        simp only [Int.cast_sub,Int.cast_natCast,Int.cast_one]
        norm_num only [Nat.cast_add,Nat.cast_one] at hsumlower
        linarith)
    omega
  have hc : (((n+2)/2 : ℕ) : ℝ)≤
      (Int.ceil ((1/2 : ℝ)*∑ C∈tetrahedra (graph n),|mobius z C|) : ℝ) := by
    have hh : (((((n+2)/2 : ℕ) : ℤ)) : ℝ)≤
        (Int.ceil ((1/2 : ℝ)*∑ C∈tetrahedra (graph n),|mobius z C|) : ℝ) := Int.cast_le.mpr hceil
    simpa only [Int.cast_natCast] using hh
  exact hc.trans hb

theorem full_lattice_summand_at (n : ℕ) :
    FullLatticeSummandAt (graph n) (((n+2)/2 : ℕ) : ℝ) := by
  refine ⟨polytope n,lattice n,indecomposable n,full_dimension n,complement n,?_,?_,?_,add_complement n⟩
  · exact (complement_lattice n).compact
  · exact (complement_lattice n).convex
  · exact basePolytope_nonempty (complement_normalized n) (complement_supermodular n)

/-- Corollary 9.4, the path-join assertion, including every real positive
dilation and every path length at least two. -/
theorem least_lattice_dilation (n : ℕ) :
    LeastFullLatticeDilation (graph n) (((n+2)/2 : ℕ) : ℝ) := by
  refine ⟨lt_of_lt_of_le zero_lt_one (dilation_ge_one n),full_lattice_summand_at n,?_⟩
  intro a ha hQ
  obtain ⟨Q,hQ,hi,hd,hs⟩ := hQ
  exact lattice_dilation_lower_bound n hQ hi hd ha hs

/-- Reindexing to the paper's unrestricted m≥2 convention is explicit. -/
theorem paper_path_join (m : ℕ) (hm : 2≤m) :
    LeastFullLatticeDilation (graph (m-2)) ((m/2 : ℕ) : ℝ) := by
  have h := least_lattice_dilation (m-2)
  simpa only [Nat.sub_add_cancel hm] using h

end GraphicalZonotopes.PathJoin
