module

public import Papers.GraphicalZonotopes.Dilation
public import Papers.GraphicalZonotopes.ExposedSegments
public import Papers.GraphicalZonotopes.GraphModels

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A polytope is a finite convex hull in the actual coordinate space. -/
def IsFinitePolytope (Q : Set (V → ℝ)) : Prop :=
  ∃ s : Finset (V → ℝ), convexHull ℝ (s : Set (V → ℝ)) = Q

/-- The standard lower-base-polytope presentation of a generalized
permutahedron, including arbitrary translations. -/
def IsGeneralizedPermutahedron (Q : Set (V → ℝ)) : Prop :=
  ∃ z : SetFunction V, Normalized z ∧ Supermodular z ∧ Q = basePolytope z

theorem IsFinitePolytope.compact {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q) :
    IsCompact Q := by
  obtain ⟨s,rfl⟩ := hQ
  exact s.finite_toSet.isCompact_convexHull ℝ

theorem IsFinitePolytope.convex {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q) :
    Convex ℝ Q := by
  obtain ⟨s,rfl⟩ := hQ
  exact convex_convexHull ℝ _

theorem IsGeneralizedPermutahedron.finitePolytope {Q : Set (V → ℝ)}
    (hQ : IsGeneralizedPermutahedron Q) : IsFinitePolytope Q := by
  classical
  obtain ⟨z,hn,hs,rfl⟩ := hQ
  refine ⟨(greedyPoints_finite z).toFinset,?_⟩
  simpa only [Set.Finite.coe_toFinset] using (basePolytope_eq_convexHull hn hs).symm

/-- The traditional definition quantifies over polytope summands. The
compact-convex definition used by the geometric proof is equivalent on the
generalized permutahedra at issue here, as proved below. -/
def PolytopalMinkowskiIndecomposable (Q : Set (V → ℝ)) : Prop :=
  Q.Nonempty ∧ ∀ P R : Set (V → ℝ),IsFinitePolytope P → IsFinitePolytope R →
    P+R=Q → ∃ (a : ℝ) (t : V → ℝ),0≤a ∧ P=({t} : Set (V → ℝ))+a • Q

theorem minkowskiIndecomposable_iff_polytopal {Q : Set (V → ℝ)}
    (hQ : IsGeneralizedPermutahedron Q) :
    MinkowskiIndecomposable Q ↔ PolytopalMinkowskiIndecomposable Q := by
  constructor
  · intro h
    refine ⟨h.1,fun P R hP hR he => ?_⟩
    exact h.2 P R hP.compact hR.compact hP.convex hR.convex he
  · intro h
    obtain ⟨z,hn,hs,rfl⟩ := hQ
    refine ⟨h.1,?_⟩
    intro P R hP hR hcP hcR he
    obtain ⟨x,hx⟩ := h.1
    rw [← he] at hx
    obtain ⟨p,hp,r,hr,hpr⟩ := hx
    have hnP : P.Nonempty := ⟨p,hp⟩
    have hnR : R.Nonempty := ⟨r,hr⟩
    have hsgP := summand_lowerSupport_supermodular hn hs hP hR hnP hnR he
    have heR : R+P=basePolytope z := by rw [add_comm]; exact he
    have hsgR := summand_lowerSupport_supermodular hn hs hR hP hnR hnP heR
    have hgpP : IsGeneralizedPermutahedron P :=
      ⟨lowerSupport P,lowerSupport_normalized hP hnP,hsgP,
        summand_eq_basePolytope hn hs hP hR hcP hnP hnR he⟩
    have hgpR : IsGeneralizedPermutahedron R :=
      ⟨lowerSupport R,lowerSupport_normalized hR hnR,hsgR,
        summand_eq_basePolytope hn hs hR hP hcR hnR hnP heR⟩
    exact h.2 P R hgpP.finitePolytope hgpR.finitePolytope he

/-- The base-polytope presentation agrees with genuine weak Minkowski
summands of the ordinary permutahedral zonotope. This checks the geometric
meaning of the generalized-permutahedron predicate used in the targets. -/
theorem generalizedPermutahedron_iff_weak_complete {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q) :
    IsGeneralizedPermutahedron Q ↔
      IsWeakMinkowskiSummand Q (graphicalZonotope (⊤ : SimpleGraph V)) := by
  constructor
  · rintro ⟨z,hn,hs,rfl⟩
    apply (isWeakMinkowskiSummand_graphical_iff hn hs).mpr
    intro u v huv hnon
    exact False.elim (hnon huv)
  · rintro ⟨a,ha,R,hR,hRc,hnR,he⟩
    let z : SetFunction V := a • graphFunction (⊤ : SimpleGraph V)
    have hzn : Normalized z := by
      change a * graphFunction (⊤ : SimpleGraph V) ∅ = 0
      rw [graphFunction_normalized,mul_zero]
    have hzs : Supermodular z := (graphFunction_supermodular _).smul ha.le
    have hbody : Q+R = basePolytope z := by
      rw [show basePolytope z = a • graphicalZonotope (⊤ : SimpleGraph V) by
        rw [basePolytope_smul (graphFunction_normalized _)
          (graphFunction_supermodular _) ha.le,baseGraphFunction_eq_graphicalZonotope]]
      exact he
    obtain ⟨x,hx⟩ := basePolytope_nonempty hzn hzs
    rw [← hbody] at hx
    obtain ⟨p,hp,r,hr,hpr⟩ := hx
    have hnQ : Q.Nonempty := ⟨p,hp⟩
    refine ⟨lowerSupport Q,lowerSupport_normalized hQ.compact hnQ,?_,?_⟩
    · exact summand_lowerSupport_supermodular hzn hzs hQ.compact hR hnQ hnR hbody
    · exact summand_eq_basePolytope hzn hzs hQ.compact hR hQ.convex hnQ hnR hbody

theorem actualRootEdge_symm {Q : Set (V → ℝ)} {u v : V}
    (h : ActualRootEdge Q u v) : ActualRootEdge Q v u := by
  obtain ⟨huv,p,q,hface,a,ha,he⟩ := h
  refine ⟨Ne.symm huv,p,q,hface,-a,neg_ne_zero.mpr ha,?_⟩
  rw [he,neg_smul,smul_sub,smul_sub]
  abel

def actualDirectionGraph (Q : Set (V → ℝ)) : SimpleGraph V where
  Adj := ActualRootEdge Q
  symm := ⟨fun _ _ => actualRootEdge_symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def directionCount (Q : Set (V → ℝ)) : ℕ := (edgeFamily (actualDirectionGraph Q)).card

def maximumDirectionDegree (Q : Set (V → ℝ)) : ℕ := by
  classical
  exact (actualDirectionGraph Q).maxDegree

def FullDimension (Q : Set (V → ℝ)) : Prop :=
  Module.finrank ℝ (vectorSpan ℝ Q) = Fintype.card V - 1

def SupportsFullIndecomposable (G : SimpleGraph V) : Prop :=
  ∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧ MinkowskiIndecomposable Q ∧
    FullDimension Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G)

/-- The dimension invariant in the paper. Points do not change its value;
on an edgeless graph this supremum is zero. -/
def maximumIndecomposableDimension (G : SimpleGraph V) : ℕ :=
  sSup {d : ℕ | ∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧
    MinkowskiIndecomposable Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
    Module.finrank ℝ (vectorSpan ℝ Q) = d}

def maximumThreeTreeSupportDimension (G : SimpleGraph V) : ℕ :=
  sSup {d : ℕ | ∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧
    MinkowskiIndecomposable Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
    (∃ S : Finset V, ThreeTreeOn S (actualDirectionGraph Q)) ∧
    Module.finrank ℝ (vectorSpan ℝ Q) = d}

def EdgeMinimalSupporting (G : SimpleGraph V) : Prop :=
  SupportsFullIndecomposable G ∧
    ∀ H : SimpleGraph V, H < G → ¬SupportsFullIndecomposable H

def BooleanElemental (Q : Set (V → ℝ)) : Prop :=
  ∀ u v, u ≠ v → ∀ S : Finset V, u ∉ S → v ∉ S →
    delta (lowerSupport Q) u v S = 0 ∨ delta (lowerSupport Q) u v S = 1

def CentrallySymmetricUpToTranslation (Q : Set (V → ℝ)) : Prop :=
  ∃ t : V → ℝ, Q = ({t} : Set (V → ℝ)) + (-1 : ℝ) • Q

def FullLatticeSummandAt (G : SimpleGraph V) (a : ℝ) : Prop :=
  ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
    FullDimension Q ∧ IsMinkowskiSummand Q (a • graphicalZonotope G)

def LeastFullLatticeDilation (G : SimpleGraph V) (a : ℝ) : Prop :=
  0 < a ∧ FullLatticeSummandAt G a ∧
    ∀ b : ℝ, 0 < b → FullLatticeSummandAt G b → a ≤ b


end GraphicalZonotopes
