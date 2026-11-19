module

public import Papers.GraphicalZonotopes.ConeCorrespondence
public import Papers.GraphicalZonotopes.LatticeSupport

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual Minkowski summation of compact convex sets in the standard real
coordinate space. -/
def IsMinkowskiSummand (Q Z : Set (V → ℝ)) : Prop :=
  ∃ R : Set (V → ℝ), IsCompact R ∧ Convex ℝ R ∧ R.Nonempty ∧ Q+R=Z

def IsWeakMinkowskiSummand (Q Z : Set (V → ℝ)) : Prop :=
  ∃ a : ℝ, 0<a ∧ IsMinkowskiSummand Q (a • Z)

/-- The exact fixed-dilation deformation criterion. The forward direction
quantifies over arbitrary genuine compact convex summands. -/
theorem isMinkowskiSummand_graphical_iff {G : SimpleGraph V} {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z) {a : ℝ} (ha : 0 ≤ a) :
    IsMinkowskiSummand (basePolytope z) (a • graphicalZonotope G) ↔
      Graphical G z ∧
      ∀ u v, u ≠ v → G.Adj u v → ∀ S, u ∉ S → v ∉ S → delta z u v S ≤ a := by
  classical
  have hTn : Normalized (a • graphFunction G) := by
    change a*graphFunction G ∅=0
    rw [graphFunction_normalized,mul_zero]
  have hTs : Supermodular (a • graphFunction G) := (graphFunction_supermodular G).smul ha
  constructor
  · rintro ⟨R,hR,hRc,hnR,hQR⟩
    have hbase : basePolytope z+R=basePolytope (a • graphFunction G) := by
      rw [basePolytope_smul (graphFunction_normalized G) (graphFunction_supermodular G) ha,
        baseGraphFunction_eq_graphicalZonotope]
      exact hQR
    have hQ := basePolytope_compact hn hs
    have hnQ := basePolytope_nonempty hn hs
    have hswap : R+basePolytope z=basePolytope (a • graphFunction G) := by
      rw [add_comm]
      exact hbase
    have hRs := summand_lowerSupport_supermodular hTn hTs hR hQ hnR hnQ hswap
    have hsum : z+lowerSupport R=a • graphFunction G := by
      rw [← lowerSupport_basePolytope hn hs,← lowerSupport_add hQ hR hnQ hnR,
        hbase,lowerSupport_basePolytope hTn hTs]
    have hrows : ∀ u v, u ≠ v → ∀ S, u ∉ S → v ∉ S →
        delta z u v S+delta (lowerSupport R) u v S =
          a*(if G.Adj u v then 1 else 0) := by
      intro u v huv S hu hv
      have h := congrArg (fun f => delta f u v S) hsum
      simpa only [delta_add,delta_smul,graphFunction_delta G huv hu hv] using h
    refine ⟨?_,?_⟩
    · intro u v huv hnon S hu hv
      have h := hrows u v huv S hu hv
      rw [if_neg hnon,mul_zero] at h
      have h1 := hs.elemental u v huv S hu hv
      have h2 := hRs.elemental u v huv S hu hv
      linarith
    · intro u v huv hedge S hu hv
      have h := hrows u v huv S hu hv
      rw [if_pos hedge,mul_one] at h
      have h2 := hRs.elemental u v huv S hu hv
      linarith
  · rintro ⟨hG,hub⟩
    let w := a • graphFunction G-z
    have hwn : Normalized w := by
      change a*graphFunction G ∅-z ∅=0
      rw [graphFunction_normalized,hn]
      ring
    have hws : Supermodular w := graphical_complement_supermodular hG ha hub
    exact ⟨basePolytope w,basePolytope_compact hwn hws,basePolytope_convex w,
      basePolytope_nonempty hwn hws,basePolytope_add_graphical_complement hn hs hG ha hub⟩

/-- The full graphical deformation cone agrees with genuine weak Minkowski
summands, with no bound imposed on the finite graph or its clique sizes. -/
theorem isWeakMinkowskiSummand_graphical_iff {G : SimpleGraph V} {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z) :
    IsWeakMinkowskiSummand (basePolytope z) (graphicalZonotope G) ↔ Graphical G z := by
  classical
  constructor
  · rintro ⟨a,ha,h⟩
    exact ((isMinkowskiSummand_graphical_iff hn hs ha.le).mp h).1
  · intro hG
    let A : ℝ := ∑ r : V × V × Finset V, |delta z r.1 r.2.1 r.2.2|
    have hA : 0 ≤ A := sum_nonneg (fun r _ => abs_nonneg _)
    refine ⟨A+1,by linarith,?_⟩
    apply (isMinkowskiSummand_graphical_iff hn hs (by linarith)).mpr
    refine ⟨hG,?_⟩
    intro u v huv hedge S hu hv
    have hbound : |delta z u v S| ≤ A := by
      exact single_le_sum (s := (univ : Finset (V × V × Finset V)))
        (f := fun r => |delta z r.1 r.2.1 r.2.2|)
        (fun r _ => abs_nonneg _) (mem_univ (u,v,S))
    exact (le_abs_self _).trans (hbound.trans (by linarith))

/-- A nonpoint lattice summand of an unweighted graphical zonotope cannot
occur below unit dilation. -/
theorem lattice_nonpoint_dilation_ge_one {G : SimpleGraph V}
    {Q R : Set (V → ℝ)} (hQ : LatticePolytope Q) (hnQ : Q.Nonempty)
    (hR : IsCompact R) (hnR : R.Nonempty)
    (hnpoint : ¬∃ p,Q={p}) {a : ℝ} (ha : 0<a)
    (he : Q+R=a • graphicalZonotope G) : 1 ≤ a := by
  let f := lowerSupport Q
  have hQcomp := hQ.compact
  have hTn : Normalized (a • graphFunction G) := by
    change a*graphFunction G ∅=0
    rw [graphFunction_normalized,mul_zero]
  have hTs := (graphFunction_supermodular G).smul ha.le
  have hbase : Q+R=basePolytope (a • graphFunction G) := by
    rw [basePolytope_smul (graphFunction_normalized G) (graphFunction_supermodular G) ha.le,
      baseGraphFunction_eq_graphicalZonotope]
    exact he
  have hfn : Normalized f := lowerSupport_normalized hQcomp hnQ
  have hfs : Supermodular f :=
    summand_lowerSupport_supermodular hTn hTs hQcomp hR hnQ hnR hbase
  have hQbase : Q=basePolytope f :=
    summand_eq_basePolytope hTn hTs hQcomp hR hQ.convex hnQ hnR hbase
  have hfnormne : normalize f ≠ 0 := by
    intro hz
    apply hnpoint
    refine ⟨fun v => f {v},?_⟩
    rw [hQbase]
    conv_lhs => rw [recover_normalize f]
    rw [hz,basePolytope_translate,basePolytope_zero]
    simp
  obtain ⟨u,v,huv,S,hu,hv,hpos⟩ := exists_positive_delta
    (normalize_translationNormalized hfn) hfs.normalize hfnormne
  rw [delta_normalize f huv hu hv] at hpos
  have hone := IntegerValued.positive_delta_ge_one
    (hQ.lowerSupport_integerValued hnQ) u v S hpos
  have hswap : R+Q=basePolytope (a • graphFunction G) := by rw [add_comm]; exact hbase
  have hRs := summand_lowerSupport_supermodular hTn hTs hR hQcomp hnR hnQ hswap
  have hsum : f+lowerSupport R=a • graphFunction G := by
    rw [← lowerSupport_add hQcomp hR hnQ hnR,hbase,lowerSupport_basePolytope hTn hTs]
  have hrow := congrArg (fun z => delta z u v S) hsum
  rw [delta_add,delta_smul,graphFunction_delta G huv hu hv] at hrow
  have hRδ := hRs.elemental u v huv S hu hv
  by_cases hedge : G.Adj u v
  · rw [if_pos hedge,mul_one] at hrow
    linarith
  · rw [if_neg hedge,mul_zero] at hrow
    linarith

end GraphicalZonotopes
