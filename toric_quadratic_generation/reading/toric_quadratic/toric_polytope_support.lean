module
public import PaperVerification.ToricNefCone
public import PaperVerification.ToricNormalFan
public import Mathlib.LinearAlgebra.Matrix.Dual
@[expose] public section

/-!
# Integral strict support from a genuine lattice polytope

The support coefficients are negatives of actual minima over the polytope.
Every minimum occurs at a genuine lattice vertex, so those coefficients are
integers. Equality of the actual normal fans then supplies strict support on
every cone, including its lower-dimensional cones.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- The negative minimum of a primitive integral linear functional is an
integer, and its equality locus is its actual normal-cone incidence locus. -/
theorem exists_integral_support_value (u : Lattice n) :
    ∃ a : ℤ, ∀ x ∈ P.carrier,
      -(dotProductEquiv ℝ (Fin n) (embed n u)) x ≤ (a : ℝ) ∧
      (-(dotProductEquiv ℝ (Fin n) (embed n u)) x = (a : ℝ) ↔
        embed n u ∈ P.normalCone x) := by
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) (embed n u)
  obtain ⟨v, hv, hmin⟩ := P.exists_minimizing_vertex f
  obtain ⟨z, hz, hze⟩ := P.extreme_integral hv
  let a : ℤ := -(∑ i, u i * z i)
  have ha : (a : ℝ) = -f v := by
    rw [← hze]
    simp [a, f, dotProductEquiv, dotProduct, embed]
  refine ⟨a, ?_⟩
  intro x hx
  have hnormal : embed n u ∈ P.normalCone x ↔ ∀ y ∈ P.carrier, f x ≤ f y := by
    change (∀ y ∈ P.carrier, 0 ≤ f (y - x)) ↔ _
    simp only [map_sub, sub_nonneg]
  constructor
  · rw [ha]
    exact neg_le_neg (hmin x hx)
  · rw [ha, neg_inj, hnormal]
    constructor
    · intro he y hy
      rw [he]
      exact hmin y hy
    · intro he
      exact le_antisymm (he v hv.1) (hmin x hx)

/-- Canonical chosen integral support coefficients, defined by actual minima. -/
def integralSupport (u : Lattice n) : ℤ :=
  Classical.choose (P.exists_integral_support_value u)

theorem integralSupport_spec (u : Lattice n) (x : Ambient n) (hx : x ∈ P.carrier) :
    -(dotProductEquiv ℝ (Fin n) (embed n u)) x ≤ (P.integralSupport u : ℝ) ∧
    (-(dotProductEquiv ℝ (Fin n) (embed n u)) x = (P.integralSupport u : ℝ) ↔
      embed n u ∈ P.normalCone x) :=
  Classical.choose_spec (P.exists_integral_support_value u) x hx

/-- The normal fan of an actual lattice polytope has integral strict convex
support. This conclusion follows from literal equality of cone sets. -/
theorem integralSupport_isStrictSupport («Σ» : SmoothCompleteFan n)
    (hfan : «Σ».realCones = P.normalFan) :
    «Σ».IsStrictSupport (fun u => (P.integralSupport u : ℝ)) := by
  intro s hs
  have hmem : (latticeRayCone s : Set (Ambient n)) ∈ «Σ».realCones := ⟨s, hs, rfl⟩
  rw [hfan] at hmem
  obtain ⟨x, hx, hcone⟩ := hmem
  let ℓ : Ambient n →ₗ[ℝ] ℝ := -(dotProductEquiv ℝ (Fin n) x)
  have hpair (u : Lattice n) :
      ℓ (embed n u) = -(dotProductEquiv ℝ (Fin n) (embed n u)) x := by
    simp only [ℓ, LinearMap.neg_apply]
    congr 1
    change (∑ i, x i * embed n u i) = ∑ i, embed n u i * x i
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  refine ⟨ℓ, ?_, ?_⟩
  · intro u hu
    rw [hpair]
    apply (P.integralSupport_spec u x hx).2.mpr
    rw [← hcone]
    exact latticeRayCone_generator s hu
  · intro u hu hus
    rw [hpair]
    apply lt_of_le_of_ne (P.integralSupport_spec u x hx).1
    intro he
    have hnormal := (P.integralSupport_spec u x hx).2.mp he
    rw [← hcone] at hnormal
    exact hus ((«Σ».ray_mem_cone_iff hs hu).mp hnormal)

end LatticePolytope

end PaperVerification.ToricGeometry
