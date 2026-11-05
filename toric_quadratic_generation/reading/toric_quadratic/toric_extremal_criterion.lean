module

public import PaperVerification.ToricFiniteDuality
public import PaperVerification.ToricVertexCone

@[expose] public section

/-!
# Extremal primitive rays detect all nef inequalities

The compact normalized primitive hull has genuine extreme points. Each such
point is one of the normalized primitive vectors, and its nonnegative ray is
a Mathlib face of the actual dual effective cone. Taking the convex hull of
these extreme points proves the criterion using only extremal primitive
relations. Together with the proved replacement theorem this gives the
contractible-relation corner criterion.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical
open PaperVerification.ToricVertexCone

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

def normalizedPrimitive (H : Lattice n → ℤ) (Q : «Σ».primitiveCollections) : «Σ».RaySpace :=
  ((«Σ».canonicalPrimitive Q).degree (fun v => (H v : ℝ)))⁻¹ •
    («Σ».canonicalPrimitive Q).vector

def primitiveBase (H : Lattice n → ℤ) : Set «Σ».RaySpace :=
  convexHull ℝ (Set.range («Σ».normalizedPrimitive H))

theorem effective_height_pos (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    {c : «Σ».RaySpace} (hc : c ∈ «Σ».effectiveCone) (hne : c ≠ 0) :
    0 < «Σ».rayPairing (fun v => (H v : ℝ)) c := by
  exact finite_dual_pairing_pos
    (fun Q : «Σ».primitiveCollections => («Σ».canonicalPrimitive Q).vector)
    («Σ».rayPairing (fun v => (H v : ℝ)))
    (fun Q => by
      rw [(«Σ».canonicalPrimitive Q).vector_pairing]
      exact («Σ».canonicalPrimitive Q).degree_pos_of_strictSupport hH)
    c («Σ».effective_nonnegative_on_finite_dual hpure H hH hc) hne

theorem effective_normalized_mem_base (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    {c : «Σ».RaySpace} (hc : c ∈ «Σ».effectiveCone) (hne : c ≠ 0) :
    («Σ».rayPairing (fun v => (H v : ℝ)) c)⁻¹ • c ∈ «Σ».primitiveBase H := by
  have h := finite_dual_normalized_mem_convexHull
    (fun Q : «Σ».primitiveCollections => («Σ».canonicalPrimitive Q).vector)
    («Σ».rayPairing (fun v => (H v : ℝ)))
    (fun Q => by rw [(«Σ».canonicalPrimitive Q).vector_pairing]
                 exact («Σ».canonicalPrimitive Q).degree_pos_of_strictSupport hH)
    c («Σ».effective_nonnegative_on_finite_dual hpure H hH hc) hne
  change («Σ».rayPairing (fun v => (H v : ℝ)) c)⁻¹ • c ∈
    convexHull ℝ (Set.range (fun Q : «Σ».primitiveCollections =>
      ((«Σ».canonicalPrimitive Q).degree (fun v => (H v : ℝ)))⁻¹ •
        («Σ».canonicalPrimitive Q).vector))
  simpa only [PrimitiveRelation.vector_pairing] using h

/-- A genuine extreme point of the normalized base gives an actual
extremal ray of the dual effective cone. -/
theorem primitive_extremal_of_normalized_extreme (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (R : «Σ».PrimitiveRelation)
    (hR : (R.degree (fun v => (H v : ℝ)))⁻¹ • R.vector ∈
      («Σ».primitiveBase H).extremePoints ℝ) : R.IsExtremal := by
  let F := «Σ».rayPairing (fun v => (H v : ℝ))
  have hFr : 0 < F R.vector := by
    rw [show F R.vector = R.degree (fun v => (H v : ℝ)) from R.vector_pairing _]
    exact R.degree_pos_of_strictSupport hH
  have hR' : (F R.vector)⁻¹ • R.vector ∈ («Σ».primitiveBase H).extremePoints ℝ := by
    simpa only [F, R.vector_pairing] using hR
  refine ⟨Submodule.span_le.mpr ?_, ?_⟩
  · rintro _ rfl
    exact R.vector_effective
  · intro c d α hc hd hα hsum
    by_cases hc0 : c = 0
    · subst c
      exact Submodule.zero_mem _
    obtain ⟨t, ht, he⟩ := PointedCone.mem_hull_singleton.mp hsum
    by_cases hd0 : d = 0
    · apply PointedCone.mem_hull_singleton.mpr
      refine ⟨α⁻¹ * t, mul_nonneg (inv_nonneg.mpr hα.le) ht, ?_⟩
      have hh := congrArg (fun z : «Σ».RaySpace => α⁻¹ • z) he
      simpa only [hd0, add_zero, smul_smul, inv_mul_cancel₀ (ne_of_gt hα), one_smul] using hh
    have hFc : 0 < F c := «Σ».effective_height_pos hpure H hH hc hc0
    have hFd : 0 < F d := «Σ».effective_height_pos hpure H hH hd hd0
    have hcn := «Σ».effective_normalized_mem_base hpure H hH hc hc0
    have hdn := «Σ».effective_normalized_mem_base hpure H hH hd hd0
    have hFt : t * F R.vector = α * F c + F d := by
      have hh := congrArg F he
      simpa only [map_add, map_smul, smul_eq_mul] using hh
    let D : ℝ := α * F c + F d
    have hD : 0 < D := add_pos (mul_pos hα hFc) hFd
    have htpos : 0 < t := by nlinarith
    let p : ℝ := α * F c / D
    let q : ℝ := F d / D
    have hp : 0 < p := div_pos (mul_pos hα hFc) hD
    have hq : 0 < q := div_pos hFd hD
    have hpq : p + q = 1 := by
      dsimp [p, q]
      rw [← add_div]
      exact div_self (ne_of_gt hD)
    have hpc : p * (F c)⁻¹ = D⁻¹ * α := by
      dsimp [p]
      field_simp
    have hqd : q * (F d)⁻¹ = D⁻¹ := by
      dsimp [q]
      field_simp
    have hDr : D⁻¹ * t = (F R.vector)⁻¹ := by
      rw [show D = t * F R.vector from hFt.symm]
      field_simp
    have hcombo : p • ((F c)⁻¹ • c) + q • ((F d)⁻¹ • d) =
        (F R.vector)⁻¹ • R.vector := by
      calc
        p • ((F c)⁻¹ • c) + q • ((F d)⁻¹ • d) = D⁻¹ • (α • c + d) := by
          simp only [smul_smul, smul_add, hpc, hqd]
        _ = D⁻¹ • (t • R.vector) := by rw [← he]
        _ = (F R.vector)⁻¹ • R.vector := by rw [smul_smul, hDr]
    have hnorm : (F c)⁻¹ • c = (F R.vector)⁻¹ • R.vector :=
      hR'.2 hcn hdn ⟨p, q, hp, hq, hpq, hcombo⟩
    apply PointedCone.mem_hull_singleton.mpr
    refine ⟨F c * (F R.vector)⁻¹,
      mul_nonneg hFc.le (inv_nonneg.mpr hFr.le), ?_⟩
    have hh := congrArg (fun z : «Σ».RaySpace => F c • z) hnorm
    simpa only [smul_smul, mul_inv_cancel₀ (ne_of_gt hFc), one_smul] using hh.symm

/-- The convex hull of the actual extreme points is the whole normalized
primitive base, including the empty-base case. -/
theorem primitiveBase_hull_extremePoints (H : Lattice n → ℤ) :
    convexHull ℝ ((«Σ».primitiveBase H).extremePoints ℝ) = «Σ».primitiveBase H := by
  let s := Finset.univ.image («Σ».normalizedPrimitive H)
  have he : (s : Set «Σ».RaySpace) = Set.range («Σ».normalizedPrimitive H) := by
    simp [s]
  have h := finite_hull_eq_hull_extremePoints s
  simpa only [he, primitiveBase] using h

/-- All actual nef inequalities are detected by primitive relations spanning
genuine extremal effective rays. -/
theorem isNef_iff_extremal_primitive_nonneg (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (a : Lattice n → ℝ) :
    «Σ».IsNef a ↔ ∀ R : «Σ».PrimitiveRelation, R.IsExtremal → 0 ≤ R.degree a := by
  constructor
  · intro ha R hR
    exact R.degree_nonneg_of_nef ha
  · intro ha
    apply («Σ».isNef_iff_canonicalPrimitive_nonneg hpure H hH a).mpr
    intro Q
    let R := «Σ».canonicalPrimitive Q
    let f := «Σ».rayPairing a
    have hnonneg : ∀ x ∈ («Σ».primitiveBase H).extremePoints ℝ, 0 ≤ f x := by
      intro x hx
      obtain ⟨S, hS⟩ := extremePoints_convexHull_subset hx
      subst x
      have hsext := «Σ».primitive_extremal_of_normalized_extreme hpure H hH
        («Σ».canonicalPrimitive S) hx
      have hdeg := ha («Σ».canonicalPrimitive S) hsext
      have hheight := («Σ».canonicalPrimitive S).degree_pos_of_strictSupport hH
      change 0 ≤ f ((«Σ».normalizedPrimitive H) S)
      simp only [normalizedPrimitive, map_smul, smul_eq_mul,
        PrimitiveRelation.vector_pairing, f]
      exact mul_nonneg (inv_nonneg.mpr hheight.le) hdeg
    have hmem : «Σ».normalizedPrimitive H Q ∈ «Σ».primitiveBase H :=
      subset_convexHull ℝ _ (Set.mem_range_self Q)
    have hconv : Convex ℝ {x : «Σ».RaySpace | 0 ≤ f x} :=
      (convex_Ici (0 : ℝ)).linear_preimage f
    have hbase : «Σ».primitiveBase H ⊆ {x : «Σ».RaySpace | 0 ≤ f x} := by
      rw [← «Σ».primitiveBase_hull_extremePoints H]
      exact convexHull_min hnonneg hconv
    have hvalue := hbase hmem
    have hheight := R.degree_pos_of_strictSupport hH
    change 0 ≤ f («Σ».normalizedPrimitive H Q) at hvalue
    have hvalue' : 0 ≤ (R.degree (fun v => (H v : ℝ)))⁻¹ * R.degree a := by
      simpa only [normalizedPrimitive, map_smul, smul_eq_mul, f,
        PrimitiveRelation.vector_pairing, R] using hvalue
    exact nonneg_of_mul_nonneg_right hvalue' (inv_pos.mpr hheight)

/-- The numerical contractible-relation bound forces genuine nefness after
every selected cone-divisor subtraction. This is the support-function core
of the corner-box criterion. -/
theorem nef_sub_cone_selection_of_contractible_degrees (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (a : Lattice n → ℝ) (side : ℝ) (hside : 0 ≤ side)
    (hdegree : ∀ R : «Σ».PrimitiveRelation, R.IsCombinatoriallyContractible →
      side * R.fiberDimension ≤ R.degree a)
    {s t : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (ht : t ⊆ s) :
    «Σ».IsNef (a - side • (fun v => if v ∈ t then 1 else 0)) := by
  apply («Σ».isNef_iff_extremal_primitive_nonneg hpure H hH _).mpr
  intro R hR
  exact R.degree_sub_corner_selection_nonneg hs ht a side hside
    (hdegree R (R.combinatoriallyContractible_of_extremal hR))

end SmoothCompleteFan

end PaperVerification.ToricGeometry
