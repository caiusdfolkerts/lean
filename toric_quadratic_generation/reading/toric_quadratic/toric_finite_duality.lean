module

public import PaperVerification.ToricPrimitiveFinite
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

/-!
# Finite cone duality from a strictly positive normalizing functional

The finite generating vectors admit a common strictly positive functional.
Their normalized convex hull is compact. Separating a normalized candidate
from this finite hull proves the relevant dual-cone theorem directly from
Hahn--Banach, including the zero and empty-family cases.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

section FiniteDuality

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (v : ι → E) (H : E →ₗ[ℝ] ℝ) (hH : ∀ i, 0 < H (v i))

include hH

/-- In the dual of a finite inequality family, the zero slice of a strictly
positive normalizing functional consists only of the zero vector. -/
theorem finite_dual_zero_of_pairing_zero (c : E)
    (hc : ∀ f : E →ₗ[ℝ] ℝ, (∀ i, 0 ≤ f (v i)) → 0 ≤ f c)
    (hzero : H c = 0) : c = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff ℝ c).mp
  intro f
  obtain ⟨M, hM⟩ := (Set.finite_range (fun i => |f (v i)| / H (v i))).bddAbove
  have hbound (i : ι) : |f (v i)| ≤ M * H (v i) :=
    (div_le_iff₀ (hH i)).mp (hM (Set.mem_range_self i))
  have hplus : ∀ i, 0 ≤ (M • H + f) (v i) := by
    intro i
    have hb := hbound i
    have hf := neg_abs_le (f (v i))
    change 0 ≤ M * H (v i) + f (v i)
    linarith
  have hminus : ∀ i, 0 ≤ (M • H - f) (v i) := by
    intro i
    have hb := hbound i
    have hf := le_abs_self (f (v i))
    change 0 ≤ M * H (v i) - f (v i)
    linarith
  have hp := hc (M • H + f) hplus
  have hm := hc (M • H - f) hminus
  change 0 ≤ M * H c + f c at hp
  change 0 ≤ M * H c - f c at hm
  rw [hzero, mul_zero, zero_add] at hp
  rw [hzero, mul_zero, zero_sub] at hm
  linarith

theorem finite_dual_pairing_pos (c : E)
    (hc : ∀ f : E →ₗ[ℝ] ℝ, (∀ i, 0 ≤ f (v i)) → 0 ≤ f c)
    (hne : c ≠ 0) : 0 < H c := by
  have hnonneg := hc H (fun i => (hH i).le)
  exact lt_of_le_of_ne hnonneg (fun he =>
    hne (finite_dual_zero_of_pairing_zero v H hH c hc he.symm))

/-- Every nonzero point in the dual of the finite inequalities normalizes
into the actual convex hull of the normalized generating vectors. -/
theorem finite_dual_normalized_mem_convexHull (c : E)
    (hc : ∀ f : E →ₗ[ℝ] ℝ, (∀ i, 0 ≤ f (v i)) → 0 ≤ f c)
    (hne : c ≠ 0) :
    (H c)⁻¹ • c ∈ convexHull ℝ (Set.range (fun i => (H (v i))⁻¹ • v i)) := by
  have hcp := finite_dual_pairing_pos v H hH c hc hne
  by_contra hnot
  obtain ⟨f, t, hct, ht⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ (Set.range (fun i => (H (v i))⁻¹ • v i)))
    ((Set.finite_range (fun i => (H (v i))⁻¹ • v i)).isClosed_convexHull ℝ) hnot
  have hgenerators : ∀ i, 0 ≤ (f.toLinearMap - t • H) (v i) := by
    intro i
    have hi := ht ((H (v i))⁻¹ • v i)
      (subset_convexHull ℝ _ (Set.mem_range_self i))
    have he : f ((H (v i))⁻¹ • v i) = f (v i) / H (v i) := by
      simp only [map_smul, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [he] at hi
    change 0 ≤ f (v i) - t * H (v i)
    exact (sub_pos.mpr ((lt_div_iff₀ (hH i)).mp hi)).le
  have hdual := hc (f.toLinearMap - t • H) hgenerators
  have he : f ((H c)⁻¹ • c) = f c / H c := by
    simp only [map_smul, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [he] at hct
  have hlt := (div_lt_iff₀ hcp).mp hct
  change 0 ≤ f c - t * H c at hdual
  linarith

/-- The needed finite conic bipolar theorem, with the strictly positive
normalizing functional explicitly justified by the mathematical application. -/
theorem mem_finite_cone_of_nonnegative_on_dual (c : E)
    (hc : ∀ f : E →ₗ[ℝ] ℝ, (∀ i, 0 ≤ f (v i)) → 0 ≤ f c) :
    c ∈ PointedCone.hull ℝ (Set.range v) := by
  by_cases hzero : c = 0
  · subst c
    exact Submodule.zero_mem _
  · let C := PointedCone.hull ℝ (Set.range v)
    have hnorm := finite_dual_normalized_mem_convexHull v H hH c hc hzero
    have hsub : convexHull ℝ (Set.range (fun i => (H (v i))⁻¹ • v i)) ⊆ C := by
      apply convexHull_min
      · rintro _ ⟨i, rfl⟩
        exact PointedCone.smul_mem C (inv_nonneg.mpr (hH i).le)
          (PointedCone.subset_hull (Set.mem_range_self i))
      · exact C.convex
    have hcp := finite_dual_pairing_pos v H hH c hc hzero
    have hscaled := PointedCone.smul_mem C hcp.le (hsub hnorm)
    simpa only [smul_smul, mul_inv_cancel₀ (ne_of_gt hcp), one_smul] using hscaled

end FiniteDuality

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Coefficients representing an arbitrary linear functional on the finite
ray coefficient space. Values away from actual rays are irrelevant and zero. -/
def functionalCoefficients (f : «Σ».RaySpace →ₗ[ℝ] ℝ) (v : Lattice n) : ℝ :=
  if hv : v ∈ «Σ».rays then f (Pi.single ⟨v, hv⟩ 1) else 0

theorem rayPairing_functionalCoefficients (f : «Σ».RaySpace →ₗ[ℝ] ℝ) (c : «Σ».RaySpace) :
    «Σ».rayPairing («Σ».functionalCoefficients f) c = f c := by
  have he := congrArg f ((Pi.basisFun ℝ «Σ».rays).sum_repr c)
  simpa [rayPairing, functionalCoefficients, map_sum, map_smul, smul_eq_mul,
    Pi.basisFun_repr, Pi.basisFun_apply] using he

/-- Nefness detects precisely the nonnegative linear functionals on the
finite canonical primitive family. -/
theorem isNef_functionalCoefficients_iff (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (f : «Σ».RaySpace →ₗ[ℝ] ℝ) :
    «Σ».IsNef («Σ».functionalCoefficients f) ↔
      ∀ Q : «Σ».primitiveCollections, 0 ≤ f («Σ».canonicalPrimitive Q).vector := by
  rw [«Σ».isNef_iff_canonicalPrimitive_nonneg hpure H hH]
  apply forall_congr'
  intro Q
  rw [← («Σ».canonicalPrimitive Q).vector_pairing,
    «Σ».rayPairing_functionalCoefficients]

/-- An effective relation is nonnegative on every linear functional
nonnegative on the actual finite primitive family. -/
theorem effective_nonnegative_on_finite_dual (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    {c : «Σ».RaySpace} (hc : c ∈ «Σ».effectiveCone) :
    ∀ f : «Σ».RaySpace →ₗ[ℝ] ℝ,
      (∀ Q : «Σ».primitiveCollections, 0 ≤ f («Σ».canonicalPrimitive Q).vector) → 0 ≤ f c := by
  intro f hf
  have hnef := («Σ».isNef_functionalCoefficients_iff hpure H hH f).mpr hf
  have h := hc.2 («Σ».functionalCoefficients f) hnef
  rwa [«Σ».rayPairing_functionalCoefficients] at h

/-- The genuine dual effective cone is generated by the finite primitive
relation family. This is proved, not inserted into a fan or nef definition. -/
theorem effectiveCone_eq_primitive_hull (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ))) :
    «Σ».effectiveCone = PointedCone.hull ℝ
      (Set.range (fun Q : «Σ».primitiveCollections => («Σ».canonicalPrimitive Q).vector)) := by
  apply le_antisymm
  · intro c hc
    exact mem_finite_cone_of_nonnegative_on_dual
      (fun Q : «Σ».primitiveCollections => («Σ».canonicalPrimitive Q).vector)
      («Σ».rayPairing (fun v => (H v : ℝ)))
      (fun Q => by
        rw [(«Σ».canonicalPrimitive Q).vector_pairing]
        exact («Σ».canonicalPrimitive Q).degree_pos_of_strictSupport hH)
      c («Σ».effective_nonnegative_on_finite_dual hpure H hH hc)
  · apply Submodule.span_le.mpr
    rintro _ ⟨Q, rfl⟩
    exact («Σ».canonicalPrimitive Q).vector_effective

end SmoothCompleteFan

end PaperVerification.ToricGeometry
