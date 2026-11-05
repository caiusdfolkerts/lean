module

public import PaperVerification.ToricNearFacetParity
public import PaperVerification.ToricNearFacetAdjoint
public import PaperVerification.ToricBundleFanInduction

@[expose] public section

/-!
# Applying the local support-coordinate proofs to the original polytopes

Reconstruction of a polytope from its actual support function does not
change its carrier, actual edges, or normal fan. These equalities eliminate
support-coordinate presentations from the hypotheses of the induction.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical Pointwise
open PaperVerification.ToricExchange

namespace LatticePolytope

variable {n : ℕ} (P Q : LatticePolytope n)

theorem smooth_iff_of_carrier_eq (h : P.carrier = Q.carrier) :
    P.Smooth ↔ Q.Smooth := by
  unfold Smooth IsEdge
  rw [h]

theorem edgesAtLeast_iff_of_carrier_eq (h : P.carrier = Q.carrier) (e : ℕ) :
    P.EdgesAtLeast e ↔ Q.EdgesAtLeast e := by
  unfold EdgesAtLeast IsEdge
  rw [h]

theorem normalFan_eq_of_carrier_eq (h : P.carrier = Q.carrier) :
    P.normalFan = Q.normalFan := by
  unfold normalFan normalCone
  rw [h]

theorem supportReconstruction_carrier («Σ» : SmoothCompleteFan n) (hpure : «Σ».IsPure)
    (hfan : «Σ».realCones = P.normalFan) :
    («Σ».supportLatticePolytope hpure P.integralSupport
      (P.integralSupport_isStrictSupport «Σ» hfan)).carrier = P.carrier := by
  rw [«Σ».supportLatticePolytope_carrier,
    P.fanPolytope_integralSupport_eq «Σ» hfan]

theorem supportReconstruction_edgesAtLeast («Σ» : SmoothCompleteFan n) (hpure : «Σ».IsPure)
    (hfan : «Σ».realCones = P.normalFan) {e : ℕ} (hbound : P.EdgesAtLeast e) :
    («Σ».supportLatticePolytope hpure P.integralSupport
      (P.integralSupport_isStrictSupport «Σ» hfan)).EdgesAtLeast e :=
  ((«Σ».supportLatticePolytope hpure P.integralSupport
    (P.integralSupport_isStrictSupport «Σ» hfan)).edgesAtLeast_iff_of_carrier_eq P
      (P.supportReconstruction_carrier «Σ» hpure hfan) e).mpr hbound

end LatticePolytope

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem integralSupport_sum_polytope_eq (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan) :
    «Σ».fanPolytope (fun u => ((P.integralSupport + Q.integralSupport) u : ℝ)) =
      P.minkowskiSum Q := by
  have he : (fun u => ((P.integralSupport + Q.integralSupport) u : ℝ)) =
      (fun u => (P.integralSupport u : ℝ)) +
        (fun u => (Q.integralSupport u : ℝ)) := by
    funext u
    simp
  rw [he, «Σ».fanPolytope_add hpure _ _
    (IsStrictSupport.isNef «Σ» (P.integralSupport_isStrictSupport «Σ» hfanP))
    (IsStrictSupport.isNef «Σ» (Q.integralSupport_isStrictSupport «Σ» hfanQ)),
    P.fanPolytope_integralSupport_eq «Σ» hfanP,
    Q.fanPolytope_integralSupport_eq «Σ» hfanQ]
  rfl

/-- The old-facet parity branch for the original input polytopes. Its
only recursive input is the unchanged theorem in smaller dimensions. -/
theorem polytope_near_facet_parity (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (u : Lattice n) (hu : u ∈ «Σ».rays)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q))
    (hslack : latticeSlack (P.integralSupport + Q.integralSupport) m u = 1)
    (IH : ∀ d : ℕ, d < n → ParityDimensionStatement d) (p : Lattice n) :
    ∃ x y : Lattice n,
      embed n x ∈ P.carrier ∧ embed n y ∈ Q.carrier ∧
      x + y = m ∧ SameParity x p := by
  have ha := P.integralSupport_isStrictSupport «Σ» hfanP
  have hb := Q.integralSupport_isStrictSupport «Σ» hfanQ
  have hedgesP := P.supportReconstruction_edgesAtLeast «Σ» hpure hfanP hboundP
  have hedgesQ := Q.supportReconstruction_edgesAtLeast «Σ» hpure hfanQ hboundQ
  have hm' : embed n m ∈ interior («Σ».fanPolytope
      (fun v => ((P.integralSupport + Q.integralSupport) v : ℝ))) := by
    rw [«Σ».integralSupport_sum_polytope_eq hpure P Q hfanP hfanQ]
    exact hm
  obtain ⟨x, y, hx, hy, hxy, hp⟩ := «Σ».near_facet_parity_decomposition hpure
    P.integralSupport Q.integralSupport ha hb hedgesP hedgesQ u hu m hm' hslack IH p
  exact ⟨x, y, (P.fanPolytope_integralSupport_eq «Σ» hfanP) ▸ hx,
    (Q.fanPolytope_integralSupport_eq «Σ» hfanQ) ▸ hy, hxy, hp⟩

/-- The old-facet adjoint branch retains the ambient interior condition
through the exact canonical slice identity. -/
theorem polytope_near_facet_adjoint (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1))
    (u : Lattice n) (hu : u ∈ «Σ».rays)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q))
    (hslack : latticeSlack (P.integralSupport + Q.integralSupport) m u = 1)
    (IH : ∀ d : ℕ, d < n → AdjointDimensionStatement d) :
    ∃ x y : Lattice n,
      embed n x ∈ P.carrier ∧ embed n y ∈ interior Q.carrier ∧ x + y = m := by
  have ha := P.integralSupport_isStrictSupport «Σ» hfanP
  have hb := Q.integralSupport_isStrictSupport «Σ» hfanQ
  have hedgesP := P.supportReconstruction_edgesAtLeast «Σ» hpure hfanP hboundP
  have hedgesQ := Q.supportReconstruction_edgesAtLeast «Σ» hpure hfanQ hboundQ
  have hm' : embed n m ∈ interior («Σ».fanPolytope
      (fun v => ((P.integralSupport + Q.integralSupport) v : ℝ))) := by
    rw [«Σ».integralSupport_sum_polytope_eq hpure P Q hfanP hfanQ]
    exact hm
  obtain ⟨x, y, hx, hy, hxy⟩ := «Σ».near_facet_adjoint_decomposition hpure
    P.integralSupport Q.integralSupport ha hb hedgesP hedgesQ u hu m hm' hslack IH
  rw [P.fanPolytope_integralSupport_eq «Σ» hfanP] at hx
  rw [Q.fanPolytope_integralSupport_eq «Σ» hfanQ] at hy
  exact ⟨x, y, hx, hy, hxy⟩

/-- An empty-focus primitive relation supplies its actual saturated
bundle coordinates internally. No split-bundle presentation is assumed. -/
theorem polytope_fiber_type_parity (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅)
    (IH : ∀ d : ℕ, d < n → ParityDimensionStatement d)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q)) (p : Lattice n) :
    ∃ x y : Lattice n,
      embed n x ∈ P.carrier ∧ embed n y ∈ Q.carrier ∧
      x + y = m ∧ SameParity x p :=
  R.bundleCoordinates.bundle_parity_decomposition hR hN hpure
    P Q hP hQ hfanP hfanQ hboundP hboundQ IH m hm p

theorem polytope_fiber_type_adjoint (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1))
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅)
    (IH : ∀ d : ℕ, d < n → ∀ A B : LatticePolytope d,
      A.Smooth → B.Smooth → A.SameNormalFan B →
      A.EdgesAtLeast (d + 1) → B.EdgesAtLeast (d + 1) →
      ∀ m : Lattice d, embed d m ∈ interior (A.minkowskiSum B) →
      ∃ x y : Lattice d,
        embed d x ∈ A.carrier ∧ embed d y ∈ interior B.carrier ∧ x + y = m)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q)) :
    ∃ x y : Lattice n,
      embed n x ∈ P.carrier ∧ embed n y ∈ interior Q.carrier ∧ x + y = m :=
  R.bundleCoordinates.bundle_adjoint_decomposition hR hN hpure
    P Q hP hQ hfanP hfanQ hboundP hboundQ IH m hm

end SmoothCompleteFan

end PaperVerification.ToricGeometry
