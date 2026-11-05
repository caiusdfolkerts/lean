module

public import PaperVerification.ToricFanPolytopes
public import PaperVerification.ToricQuotientStarCovering

@[expose] public section

/-!
# Exact nef face hulls over an actual fan cone

Even when nef support collapses some edges, the face cut out by a cone is
the convex hull of Cartier points of full cones containing it. Small
perturbations of the cone's interior normal prove the minimizing property,
so no assumption that the nef polytope retains the original normal fan is
needed.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

def supportFace (a : Lattice n → ℝ) (F : Finset (Lattice n)) : Set (Ambient n) :=
  {x ∈ «Σ».fanPolytope a | ∀ u ∈ F,
    (dotProductEquiv ℝ (Fin n) (embed n u)) x = -a u}

def fullConesOver (F : Finset (Lattice n)) : Finset «Σ».fullCones :=
  Finset.univ.filter (fun s => F ⊆ (s : Finset (Lattice n)))

theorem cartierPoint_support_eq (a : Lattice n → ℝ) (s : «Σ».fullCones)
    {u : Lattice n} (hu : u ∈ (s : Finset (Lattice n))) :
    (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s) = -a u := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ((«Σ».fullConeBasis_ray_set s) ▸ hu)
  exact «Σ».cartierPoint_active a s i

theorem convex_supportFace (a : Lattice n → ℝ) (F : Finset (Lattice n)) :
    Convex ℝ («Σ».supportFace a F) := by
  intro x hx y hy r t hr ht hrt
  refine ⟨«Σ».convex_fanPolytope a hx.1 hy.1 hr ht hrt, ?_⟩
  intro u hu
  rw [map_add, map_smul, map_smul, hx.2 u hu, hy.2 u hu]
  change r * -a u + t * -a u = -a u
  rw [← add_mul, hrt, one_mul]

/-- Equality in genuine supporting primitive halfspaces cuts out an
actual extreme face of the original halfspace polytope. -/
theorem supportFace_isExtreme (a : Lattice n → ℝ)
    (F : Finset (Lattice n)) (hF : F ⊆ «Σ».rays) :
    IsExtreme ℝ («Σ».fanPolytope a) («Σ».supportFace a F) := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  intro x hx y hy z hz hseg
  obtain ⟨r, t, hr, ht, hrt, he⟩ := hseg
  refine ⟨hx, ?_⟩
  intro u hu
  have hxu := hx u (hF hu)
  have hyu := hy u (hF hu)
  have hzu := hz.2 u hu
  have hlin := congrArg (dotProductEquiv ℝ (Fin n) (embed n u) : Ambient n → ℝ) he
  simp only [map_add, map_smul, smul_eq_mul] at hlin
  have hxnon := mul_nonneg hr.le (sub_nonneg.mpr hxu)
  have hynon := mul_nonneg ht.le (sub_nonneg.mpr hyu)
  have htotal :
      r * ((dotProductEquiv ℝ (Fin n) (embed n u)) x + a u) +
        t * ((dotProductEquiv ℝ (Fin n) (embed n u)) y + a u) = 0 := by
    calc
      _ = (r * ((dotProductEquiv ℝ (Fin n) (embed n u)) x) +
        t * ((dotProductEquiv ℝ (Fin n) (embed n u)) y)) + (r + t) * a u := by ring
      _ = 0 := by rw [hlin, hzu, hrt]; ring
  have hzero : r * ((dotProductEquiv ℝ (Fin n) (embed n u)) x + a u) = 0 := by
    nlinarith only [hxnon, hynon, htotal]
  have hz := (mul_eq_zero.mp hzero).resolve_left hr.ne'
  linarith

theorem cartierPoint_mem_supportFace {a : Lattice n → ℝ} (ha : «Σ».IsNef a)
    (F : Finset (Lattice n)) (s : «Σ».fullConesOver F) :
    «Σ».cartierPoint a s ∈ «Σ».supportFace a F := by
  refine ⟨«Σ».cartierPoint_mem_of_nef ha s, ?_⟩
  intro u hu
  exact «Σ».cartierPoint_support_eq a s ((Finset.mem_filter.mp s.property).2 hu)

/-- A normal in a full fan cone is minimized at that cone's actual
Cartier point on the whole nef polytope. -/
theorem cartierPoint_minimizes_normal (a : Lattice n → ℝ) (s : «Σ».fullCones)
    (u : Ambient n) (hu : u ∈ latticeRayCone (s : Finset (Lattice n)))
    (x : Ambient n) (hx : x ∈ «Σ».fanPolytope a) :
    (dotProductEquiv ℝ (Fin n) u) («Σ».cartierPoint a s) ≤
      (dotProductEquiv ℝ (Fin n) u) x := by
  let d := «Σ».fullConeBasis s
  let B := «Σ».cartierBasis s
  rw [«Σ».fullConeBasis_ray_set s] at hu
  have hcoords := ((mem_latticeRayCone_basis_iff d Finset.univ u).mp hu).1
  apply linear_le_of_basis_coordinates B (dotProductEquiv ℝ (Fin n) u)
    («Σ».cartierPoint a s) x
  · intro i
    have hp := integralDualBasis_real_repr (integralDualBasis d) u i
    rw [integralDualBasis_involutive] at hp
    have hi := hcoords i
    rw [hp] at hi
    exact hi
  · intro i
    rw [← «Σ».activeRay_dual s i, map_sub, «Σ».cartierPoint_active]
    exact sub_nonneg.mpr (hx («Σ».activeRay s i) («Σ».activeRay s i).property)

/-- Equation (1) restricted to the face indexed by any actual cone. This
also applies at nef endpoints and to lower-dimensional restriction polytopes. -/
theorem supportFace_eq_convexHull_cartier (hpure : «Σ».IsPure)
    (a : Lattice n → ℝ) (ha : «Σ».IsNef a)
    (F : Finset (Lattice n)) (hF : F ∈ «Σ».cones) :
    «Σ».supportFace a F = convexHull ℝ
      (Set.range (fun s : «Σ».fullConesOver F => «Σ».cartierPoint a s)) := by
  apply Set.Subset.antisymm
  · intro x hx
    apply mem_finite_convexHull_of_lower_support
    intro f
    obtain ⟨ε, hε, t, ht, hFt, hut⟩ :=
      «Σ».exists_small_perturbation_in_containing_cone hF (dualVector f)
    obtain ⟨s, hs, hts, hscard⟩ := hpure t ht
    let s' : «Σ».fullCones := ⟨s, Finset.mem_filter.mpr ⟨hs, hscard⟩⟩
    let s'' : «Σ».fullConesOver F :=
      ⟨s', Finset.mem_filter.mpr ⟨Finset.mem_univ s', hFt.trans hts⟩⟩
    let w : Ambient n := ∑ u ∈ F, embed n u
    have hnormal : w + ε • dualVector f ∈ latticeRayCone s :=
      latticeRayCone_mono hts hut
    have hmin := «Σ».cartierPoint_minimizes_normal a s' (w + ε • dualVector f)
      hnormal x hx.1
    have hcface := «Σ».cartierPoint_mem_supportFace ha F s''
    let q : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) w
    have hwvalue (y : Ambient n) (hy : y ∈ «Σ».supportFace a F) :
        q y = -∑ u ∈ F, a u := by
      change (dotProductEquiv ℝ (Fin n) (∑ u ∈ F, embed n u)) y = _
      calc
        _ = ∑ u ∈ F, (dotProductEquiv ℝ (Fin n) (embed n u)) y := by
          rw [map_sum, LinearMap.sum_apply]
        _ = ∑ u ∈ F, -a u := Finset.sum_congr rfl (fun u hu => hy.2 u hu)
        _ = _ := Finset.sum_neg_distrib a
    have hpair (y : Ambient n) :
        (dotProductEquiv ℝ (Fin n) (w + ε • dualVector f)) y = q y + ε * f y := by
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
      have hf : (dotProductEquiv ℝ (Fin n) (dualVector f)) y = f y := by
        change (∑ i, dualVector f i * y i) = f y
        simpa only [Pi.zero_apply, sub_zero] using
          dualVector_pairing f (0 : Ambient n) y
      rw [hf]
      rfl
    rw [hpair, hpair, hwvalue x hx, hwvalue _ hcface] at hmin
    refine ⟨s'', ?_⟩
    nlinarith
  · exact convexHull_min
      (by rintro _ ⟨s, rfl⟩; exact «Σ».cartierPoint_mem_supportFace ha F s)
      («Σ».convex_supportFace a F)

end PaperVerification.ToricGeometry.SmoothCompleteFan
