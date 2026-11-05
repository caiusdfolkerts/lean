module

public import Continuation.Divisor.ProjectiveComparison

/-! # Projectivity from an actual integral strict support function

The recovered positive integral edge and normal-cone arguments are
followed by an explicit convex-combination proof of primitive unit-step
membership. These data give a literal finite projective embedding of
the original fan scheme, with no projectivity hypothesis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace PaperVerification.ToricGeometry.SmoothCompleteFan
open Set
open scoped BigOperators Classical
variable {n : ℕ} («Σ» : SmoothCompleteFan n)
/-- All coordinate-ray faces have actual positive integral endpoints. -/
theorem support_polytope_coordinate_edges
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ))) (s : «Σ».fullCones) :
    ∃ lengths : Fin n → ℕ, ∀ i,
      0 < lengths i ∧
      («Σ».supportLatticePolytope hpure a ha).IsEdge
        («Σ».cartierPoint (fun u => (a u : ℝ)) s)
        (embed n («Σ».cartierLatticePoint a s +
          (lengths i : ℤ) • integralDualBasis («Σ».fullConeBasis s) i)) ∧
      («Σ».supportLatticePolytope hpure a ha).coordinateRayFace
        («Σ».cartierPoint (fun u => (a u : ℝ)) s) («Σ».cartierBasis s) i =
        segment ℝ («Σ».cartierPoint (fun u => (a u : ℝ)) s)
          (embed n («Σ».cartierLatticePoint a s +
            (lengths i : ℤ) • integralDualBasis («Σ».fullConeBasis s) i)) := by
  let P := «Σ».supportLatticePolytope hpure a ha
  have hvgen : «Σ».cartierLatticePoint a s ∈ P.generators :=
    Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩
  have horthant (x : Ambient n) (hx : x ∈ P.carrier) (j : Fin n) :
      0 ≤ («Σ».cartierBasis s).repr (x - embed n («Σ».cartierLatticePoint a s)) j := by
    rw [«Σ».embed_cartierLatticePoint]
    exact «Σ».cartierPoint_orthant s ((«Σ».supportLatticePolytope_carrier hpure a ha) ▸ hx) j
  have hex (i : Fin n) := P.coordinateRayFace_eq_integral_edge
    («Σ».cartierLatticePoint a s) hvgen (integralDualBasis («Σ».fullConeBasis s)) horthant i
    (by simpa only [P, cartierBasis, «Σ».embed_cartierLatticePoint,
      «Σ».supportLatticePolytope_carrier] using «Σ».exists_positive_axis_point ha s i)
  choose lengths hlengths using hex
  refine ⟨lengths, ?_⟩
  intro i
  simpa only [P, cartierBasis, «Σ».embed_cartierLatticePoint] using hlengths i

/-- The actual normal cone at each integral Cartier vertex is its full
original fan cone, with no rescaling or missing primitive ray. -/
theorem supportLatticePolytope_cartier_normalCone
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ))) (s : «Σ».fullCones) :
    («Σ».supportLatticePolytope hpure a ha).normalCone
      («Σ».cartierPoint (fun u => (a u : ℝ)) s) =
      (latticeRayCone (s : Finset (Lattice n)) : Set (Ambient n)) := by
  let P := «Σ».supportLatticePolytope hpure a ha
  obtain ⟨lengths, hlengths⟩ := «Σ».support_polytope_coordinate_edges hpure a ha s
  have hedges : ∀ i, 0 < lengths i ∧
      P.IsEdge (embed n («Σ».cartierLatticePoint a s))
        (embed n («Σ».cartierLatticePoint a s +
          (lengths i : ℤ) • integralDualBasis («Σ».fullConeBasis s) i)) := by
    intro i
    simpa only [«Σ».embed_cartierLatticePoint] using
      ⟨(hlengths i).1, (hlengths i).2.1⟩
  have horthant (x : Ambient n) (hx : x ∈ P.carrier) (j : Fin n) :
      0 ≤ («Σ».cartierBasis s).repr (x - embed n («Σ».cartierLatticePoint a s)) j := by
    rw [«Σ».embed_cartierLatticePoint]
    exact «Σ».cartierPoint_orthant s ((«Σ».supportLatticePolytope_carrier hpure a ha) ▸ hx) j
  have heq := P.normalCone_eq_latticeRayCone («Σ».cartierLatticePoint a s)
    (integralDualBasis («Σ».fullConeBasis s)) lengths hedges horthant
  simpa only [«Σ».embed_cartierLatticePoint, integralDualBasis_involutive,
    ← «Σ».fullConeBasis_ray_set] using heq


/-- Every first primitive lattice step is in the actual support polytope. -/
theorem supportLatticePolytope_unitStep
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (s : «Σ».fullCones) (i : Fin n) :
    embed n («Σ».cartierLatticePoint a s + integralDualBasis («Σ».fullConeBasis s) i) ∈
      («Σ».supportLatticePolytope «Σ».isPure a ha).carrier := by
  let P := «Σ».supportLatticePolytope «Σ».isPure a ha
  let z := «Σ».cartierLatticePoint a s
  let b := integralDualBasis («Σ».fullConeBasis s) i
  obtain ⟨lengths, hl⟩ := «Σ».support_polytope_coordinate_edges «Σ».isPure a ha s
  have hp := P.edge_endpoints_extreme (hl i).2.1
  have hv : embed n z ∈ P.carrier := by
    simpa only [z, «Σ».embed_cartierLatticePoint] using hp.1.1
  have hw : embed n (z + (lengths i : ℤ) • b) ∈ P.carrier := hp.2.1
  have hpos : (0 : ℝ) < lengths i := by exact_mod_cast (hl i).1
  have hge : (1 : ℝ) ≤ lengths i := by exact_mod_cast (Nat.succ_le_iff.mpr (hl i).1)
  have hi0 : 0 ≤ (lengths i : ℝ)⁻¹ := inv_nonneg.mpr hpos.le
  have hi1 : (lengths i : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hpos).mpr hge
  have hc : Convex ℝ P.carrier := by
    dsimp only [P]
    rw [«Σ».supportLatticePolytope_carrier]
    exact «Σ».convex_fanPolytope _
  have hm := hc hv hw (sub_nonneg.mpr hi1) hi0
    (show (1 - (lengths i : ℝ)⁻¹) + (lengths i : ℝ)⁻¹ = 1 by ring)
  have he : embed n (z + (lengths i : ℤ) • b) =
      embed n z + (lengths i : ℝ) • embed n b := by
    ext j
    simp [embed]
  have heq : (1 - (lengths i : ℝ)⁻¹) • embed n z +
      (lengths i : ℝ)⁻¹ • embed n (z + (lengths i : ℤ) • b) =
      embed n (z + b) := by
    rw [he, smul_add, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul,
      ← add_assoc, ← add_smul]
    have hs : (1 - (lengths i : ℝ)⁻¹) + (lengths i : ℝ)⁻¹ = 1 := by ring
    rw [hs, one_smul]
    ext j
    simp [embed]
  exact heq ▸ hm
end PaperVerification.ToricGeometry.SmoothCompleteFan

namespace Unimodular.Projectivity
open PaperVerification.ToricGeometry AlgebraicGeometry
variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
  (a : Lattice n → ℤ) (ha : F.IsStrictSupport (fun u => (a u : ℝ)))

/-- Concrete monomial chart data for every integral strict support function. -/
def strictSupportVertexData : VertexChartData F (F.supportLatticePolytope F.isPure a ha) where
  vertex := F.cartierLatticePoint a
  vertex_mem s := by
    rw [F.supportLatticePolytope_carrier, F.embed_cartierLatticePoint]
    exact F.cartierPoint_mem_of_nef (PaperVerification.ToricGeometry.SmoothCompleteFan.IsStrictSupport.isNef F ha) s
  hull := by
    rw [F.supportLatticePolytope_carrier,
      F.fanPolytope_eq_convexHull_cartier F.isPure _
        (PaperVerification.ToricGeometry.SmoothCompleteFan.IsStrictSupport.isNef F ha)]
    congr 2
    funext s
    exact (F.embed_cartierLatticePoint a s).symm
  normal s := by
    rw [F.embed_cartierLatticePoint]
    exact F.supportLatticePolytope_cartier_normalCone F.isPure a ha s
  unitStep_mem := F.supportLatticePolytope_unitStep a ha

variable (k : Type u) [Field k]
/-- A literal finite projective closed immersion of the original scheme. -/
def strictSupportProjectiveEmbedding :=
  (strictSupportVertexData F a ha).fanProjectiveEmbedding k

instance strictSupportProjectiveEmbedding_isClosedImmersion :
    IsClosedImmersion (strictSupportProjectiveEmbedding F a ha k) :=
  (strictSupportVertexData F a ha).fanProjectiveEmbedding_isClosedImmersion k

#print axioms strictSupportVertexData
#print axioms strictSupportProjectiveEmbedding_isClosedImmersion
end Unimodular.Projectivity
