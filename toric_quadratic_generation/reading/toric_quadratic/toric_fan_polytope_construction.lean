module

public import PaperVerification.ToricFanPolytopes
public import PaperVerification.ToricOrthantEdges
public import PaperVerification.ToricNormalConeRealization
public import PaperVerification.ToricNormalConeAverages

@[expose] public section

/-!
# An integral strictly convex support function gives its genuine polytope

The generators are literal integral Cartier points. Positive feasible points
on each dual basis ray prove full dimension and identify the actual edges;
none of these conclusions is stored as an assumption in the construction.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical
open PaperVerification.ToricExchange

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem fullCones_nonempty (hpure : «Σ».IsPure) : «Σ».fullCones.Nonempty := by
  obtain ⟨t, ht, hzero⟩ := «Σ».complete 0
  obtain ⟨s, hs, hts, hscard⟩ := hpure t ht
  exact ⟨s, Finset.mem_filter.mpr ⟨hs, hscard⟩⟩

/-- The actual integral solution of the primitive active equations. -/
def cartierLatticePoint (a : Lattice n → ℤ) (s : «Σ».fullCones) : Lattice n :=
  -∑ i, a («Σ».fullConeBasis s i) • integralDualBasis («Σ».fullConeBasis s) i

theorem embed_cartierLatticePoint (a : Lattice n → ℤ) (s : «Σ».fullCones) :
    embed n («Σ».cartierLatticePoint a s) = «Σ».cartierPoint (fun u => (a u : ℝ)) s := by
  simp only [cartierLatticePoint, cartierPoint, map_neg, map_sum,
    embed_int_smul, integralBasisReal_apply]

theorem cartierPoint_support_eq_of_mem (a : Lattice n → ℝ) (s : «Σ».fullCones)
    {u : Lattice n} (hu : u ∈ (s : Finset (Lattice n))) :
    (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s) = -a u := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ((«Σ».fullConeBasis_ray_set s) ▸ hu)
  exact «Σ».cartierPoint_active a s i

/-- Strict support means literal strict inequality at every inactive ray
of the actual Cartier point. -/
theorem cartierPoint_support_lt_of_not_mem {a : Lattice n → ℝ}
    (ha : «Σ».IsStrictSupport a) (s : «Σ».fullCones)
    {u : Lattice n} (hu : u ∈ «Σ».rays) (hus : u ∉ (s : Finset (Lattice n))) :
    -a u < (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s) := by
  obtain ⟨ℓ, he, hlt⟩ := ha s («Σ».fullCones_mem s)
  let q : Ambient n →ₗ[ℝ] ℝ := -(dotProductEquiv ℝ (Fin n) («Σ».cartierPoint a s))
  have hq (z : Lattice n) :
      q (embed n z) = -(dotProductEquiv ℝ (Fin n) (embed n z)) («Σ».cartierPoint a s) := by
    change -(«Σ».cartierPoint a s ⬝ᵥ embed n z) =
      -(embed n z ⬝ᵥ «Σ».cartierPoint a s)
    rw [dotProduct_comm]
  have hℓq : ℓ = q := by
    apply (integralBasisReal («Σ».fullConeBasis s)).ext
    intro i
    have hi : «Σ».fullConeBasis s i ∈ (s : Finset (Lattice n)) := by
      rw [«Σ».fullConeBasis_ray_set]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    rw [integralBasisReal_apply, he _ hi, hq,
      «Σ».cartierPoint_support_eq_of_mem a s hi, neg_neg]
  have h := hlt u hu hus
  rw [hℓq, hq] at h
  linarith

theorem cartierPoint_orthant {a : Lattice n → ℝ} (s : «Σ».fullCones)
    {x : Ambient n} (hx : x ∈ «Σ».fanPolytope a) (i : Fin n) :
    0 ≤ («Σ».cartierBasis s).repr (x - «Σ».cartierPoint a s) i := by
  rw [← «Σ».activeRay_dual s i, map_sub, «Σ».cartierPoint_active]
  exact sub_nonneg.mpr (hx («Σ».activeRay s i) («Σ».activeRay s i).property)

/-- Every dual coordinate ray has a strictly positive feasible initial
segment. A finite common perturbation handles all inactive facets. -/
theorem exists_positive_axis_point {a : Lattice n → ℝ}
    (ha : «Σ».IsStrictSupport a) (s : «Σ».fullCones) (i : Fin n) :
    ∃ ε : ℝ, 0 < ε ∧
      «Σ».cartierPoint a s + ε • «Σ».cartierBasis s i ∈ «Σ».fanPolytope a := by
  let v := «Σ».cartierPoint a s
  let e := «Σ».cartierBasis s i
  let I := «Σ».rays \ (s : Finset (Lattice n))
  let f : Lattice n → ℝ := fun u => a u + (dotProductEquiv ℝ (Fin n) (embed n u)) v
  let g : Lattice n → ℝ := fun u => (dotProductEquiv ℝ (Fin n) (embed n u)) e
  have hf (u : Lattice n) (hu : u ∈ I) : 0 < f u := by
    obtain ⟨hur, hus⟩ := Finset.mem_sdiff.mp hu
    have h := «Σ».cartierPoint_support_lt_of_not_mem ha s hur hus
    dsimp [f, v]
    linarith
  obtain ⟨ε, hε, hsmall⟩ := finite_strict_perturbation I f g hf
  refine ⟨ε, hε, ?_⟩
  intro u hu
  by_cases hus : u ∈ (s : Finset (Lattice n))
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ((«Σ».fullConeBasis_ray_set s) ▸ hus)
    have heq := «Σ».cartierPoint_active a s j
    have hpair : (dotProductEquiv ℝ (Fin n) (embed n («Σ».fullConeBasis s j))) e =
        if i = j then 1 else 0 := by
      rw [show «Σ».fullConeBasis s j = («Σ».activeRay s j : Lattice n) from rfl,
        «Σ».activeRay_dual]
      exact Module.Basis.repr_self_apply _ _ _
    change -a («Σ».fullConeBasis s j) ≤ _
    rw [map_add, map_smul, hpair]
    change -a («Σ».fullConeBasis s j) ≤
      (dotProductEquiv ℝ (Fin n) (embed n («Σ».fullConeBasis s j))) v +
        ε * (if i = j then 1 else 0)
    change (dotProductEquiv ℝ (Fin n) (embed n («Σ».fullConeBasis s j))) v =
      -a («Σ».fullConeBasis s j) at heq
    rw [heq]
    split_ifs <;> nlinarith
  · have h := hsmall u (Finset.mem_sdiff.mpr ⟨hu, hus⟩)
    dsimp [f, g] at h
    rw [map_add, map_smul]
    change -a u ≤ (dotProductEquiv ℝ (Fin n) (embed n u)) v + ε * g u
    dsimp [g]
    linarith

/-- The actual halfspace polytope has full affine span. This includes
dimension zero and does not presume a previously constructed polytope. -/
theorem affineSpan_fanPolytope_eq_top (hpure : «Σ».IsPure)
    {a : Lattice n → ℝ} (ha : «Σ».IsStrictSupport a) :
    affineSpan ℝ («Σ».fanPolytope a) = ⊤ := by
  obtain ⟨s, hs⟩ := «Σ».fullCones_nonempty hpure
  let s' : «Σ».fullCones := ⟨s, hs⟩
  let v := «Σ».cartierPoint a s'
  let b := «Σ».cartierBasis s'
  let A := affineSpan ℝ («Σ».fanPolytope a)
  have hv : v ∈ A := subset_affineSpan ℝ _
    («Σ».cartierPoint_mem_of_nef (IsStrictSupport.isNef «Σ» ha) s')
  have hb (i : Fin n) : b i ∈ A.direction := by
    obtain ⟨ε, hε, hpoint⟩ := «Σ».exists_positive_axis_point ha s' i
    have hd := AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ _ hpoint) hv
    have hd' : ε • b i ∈ A.direction := by
      simpa only [v, b, A, vsub_eq_sub, add_sub_cancel_left] using hd
    have hh := A.direction.smul_mem ε⁻¹ hd'
    simpa only [smul_smul, inv_mul_cancel₀ hε.ne', one_smul] using hh
  have hdir (x : Ambient n) : x ∈ A.direction := by
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ (fun i _ => A.direction.smul_mem _ (hb i))
  apply top_unique
  intro x hx
  have hh := AffineSubspace.vadd_mem_of_mem_direction (hdir (x - v)) hv
  simpa only [vadd_eq_add, sub_add_cancel] using hh

def supportGenerators (a : Lattice n → ℤ) : Finset (Lattice n) :=
  Finset.univ.image («Σ».cartierLatticePoint a)

theorem supportGenerators_nonempty (hpure : «Σ».IsPure) (a : Lattice n → ℤ) :
    («Σ».supportGenerators a).Nonempty := by
  obtain ⟨s, hs⟩ := «Σ».fullCones_nonempty hpure
  exact ⟨«Σ».cartierLatticePoint a ⟨s, hs⟩,
    Finset.mem_image.mpr ⟨⟨s, hs⟩, Finset.mem_univ _, rfl⟩⟩

theorem embed_supportGenerators (a : Lattice n → ℤ) :
    (embed n) '' («Σ».supportGenerators a : Set (Lattice n)) =
      Set.range («Σ».cartierPoint (fun u => (a u : ℝ))) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨s, («Σ».embed_cartierLatticePoint a s).symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨«Σ».cartierLatticePoint a s,
      Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩,
      «Σ».embed_cartierLatticePoint a s⟩

/-- A literal full-dimensional lattice polytope, generated by its
integral Cartier points. Smoothness is proved separately below. -/
def supportLatticePolytope (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ))) : LatticePolytope n where
  generators := «Σ».supportGenerators a
  nonempty := «Σ».supportGenerators_nonempty hpure a
  fullDimensional := by
    rw [«Σ».embed_supportGenerators,
      ← «Σ».fanPolytope_eq_convexHull_cartier hpure _ (IsStrictSupport.isNef «Σ» ha)]
    exact «Σ».affineSpan_fanPolytope_eq_top hpure ha

theorem supportLatticePolytope_carrier (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ))) :
    («Σ».supportLatticePolytope hpure a ha).carrier =
      «Σ».fanPolytope (fun u => (a u : ℝ)) := by
  change convexHull ℝ ((embed n) '' («Σ».supportGenerators a : Set (Lattice n))) = _
  rw [«Σ».embed_supportGenerators,
    ← «Σ».fanPolytope_eq_convexHull_cartier hpure _ (IsStrictSupport.isNef «Σ» ha)]

end PaperVerification.ToricGeometry.SmoothCompleteFan
