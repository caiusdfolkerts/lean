module

public import PaperVerification.ToricCompleteWalls
public import PaperVerification.ToricEdgeWallSupport

@[expose] public section

/-!
# Positive genuine wall slacks imply strict support

For a fixed fan ray, minimize its pairing with the finitely many actual
Cartier points. A negative coordinate in the minimizing cone would allow
crossing the corresponding wall and strictly lowering that pairing. Thus
the minimum is attained on a cone containing the ray. This proves all
global support inequalities and their strictness without a local-to-global
convexity theorem or a cone-of-curves assertion.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped Classical BigOperators

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

def wallSlack (a : Lattice n→ℝ) (s : «Σ».fullCones) (u : Lattice n) : ℝ :=
  a u + (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s)

/-- Slacks are tested only at the actual new ray of two adjacent full
cones in the given fan. -/
def HasPositiveWallSlacks (a : Lattice n→ℝ) : Prop :=
  ∀ s t : «Σ».fullCones,(s.val∩t.val).card=n-1 →
    ∀ u∈t.val,u∉s.val → 0<«Σ».wallSlack a s u

theorem eq_cartierPoint_of_active_pairings (a : Lattice n→ℝ) (s : «Σ».fullCones)
    (x : Ambient n)
    (hx : ∀ u∈s.val,(dotProductEquiv ℝ (Fin n) (embed n u)) x = -a u) :
    x=«Σ».cartierPoint a s := by
  apply («Σ».cartierBasis s).repr.injective
  ext i
  have hi : («Σ».activeRay s i : Lattice n)∈s.val := by
    rw [«Σ».fullConeBasis_ray_set]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  calc
    («Σ».cartierBasis s).repr x i =
        (dotProductEquiv ℝ (Fin n) (embed n («Σ».activeRay s i))) x :=
      («Σ».activeRay_dual s i x).symm
    _ = -a («Σ».activeRay s i) := hx _ hi
    _ = (dotProductEquiv ℝ (Fin n) (embed n («Σ».activeRay s i)))
        («Σ».cartierPoint a s) := («Σ».cartierPoint_active a s i).symm
    _ = («Σ».cartierBasis s).repr («Σ».cartierPoint a s) i := «Σ».activeRay_dual s i _

/-- The actual displacement of Cartier points across a smooth wall is
the primitive dual direction multiplied by the literal wall slack. -/
theorem cartierPoint_across_wall (a : Lattice n→ℝ) (s t : «Σ».fullCones)
    (j : Fin n) (w : Lattice n)
    (ht : t.val=insert w ((Finset.univ.erase j).image («Σ».fullConeBasis s)))
    (hwj : («Σ».fullConeBasis s).repr w j = -1) :
    «Σ».cartierPoint a t = «Σ».cartierPoint a s + «Σ».wallSlack a s w • «Σ».cartierBasis s j := by
  symm
  apply «Σ».eq_cartierPoint_of_active_pairings a t
  intro u hu
  rw [ht] at hu
  rcases Finset.mem_insert.mp hu with hu | hu
  · subst u
    rw [map_add,map_smul]
    change _ + «Σ».wallSlack a s w *
      (dotProductEquiv ℝ (Fin n) (embed n w))
        (integralBasisReal (integralDualBasis («Σ».fullConeBasis s)) j) = _
    rw [pairing_integral_dual_basis,hwj]
    simp only [Int.cast_neg,Int.cast_one,wallSlack]
    ring
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    have his : «Σ».fullConeBasis s i∈s.val := by
      rw [«Σ».fullConeBasis_ray_set]
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
    rw [map_add,map_smul,«Σ».cartierPoint_support_eq_of_mem a s his]
    change -a _ + «Σ».wallSlack a s w *
      (dotProductEquiv ℝ (Fin n) (embed n («Σ».fullConeBasis s i)))
        (integralBasisReal (integralDualBasis («Σ».fullConeBasis s)) j) = _
    rw [pairing_integral_dual_basis,Module.Basis.repr_self_apply,
      if_neg (Finset.mem_erase.mp hi).1]
    simp

theorem exists_negative_coordinate_of_ray_not_mem_full (s : «Σ».fullCones)
    (u : Lattice n) (hu : u∈«Σ».rays) (hus : u∉s.val) :
    ∃ j : Fin n,(«Σ».fullConeBasis s).repr u j<0 := by
  by_contra hn
  push_neg at hn
  have hcone : embed n u∈latticeRayCone s.val := by
    rw [«Σ».fullConeBasis_ray_set s]
    apply (mem_latticeRayCone_basis_iff («Σ».fullConeBasis s) Finset.univ (embed n u)).mpr
    refine ⟨?_,?_⟩
    · intro j
      rw [integralBasisReal_repr]
      exact_mod_cast hn j
    · intro j hj
      exact (hj (Finset.mem_univ j)).elim
  exact hus ((«Σ».ray_mem_cone_iff («Σ».fullCones_mem s) hu).mp hcone)

/-- Any cone not containing the chosen fan ray has a genuine adjacent
cone with strictly smaller Cartier pairing against that ray. -/
theorem exists_smaller_cartier_pairing (hpure : «Σ».IsPure) (a : Lattice n→ℝ)
    (ha : «Σ».HasPositiveWallSlacks a) (s : «Σ».fullCones)
    (u : Lattice n) (hu : u∈«Σ».rays) (hus : u∉s.val) :
    ∃ t : «Σ».fullCones,
      (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a t) <
        (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s) := by
  obtain ⟨j,huj⟩ := «Σ».exists_negative_coordinate_of_ray_not_mem_full s u hu hus
  obtain ⟨t,w,ht,hwj,hmeet,hwt,hws⟩ := «Σ».exists_full_opposite_wall hpure s j
  have hcard : (s.val∩t.val).card=n-1 := by
    rw [hmeet,basis_wall_card]
  have hslack := ha s t hcard w hwt hws
  refine ⟨t,?_⟩
  rw [«Σ».cartierPoint_across_wall a s t j w ht hwj,map_add,map_smul]
  change _+«Σ».wallSlack a s w *
      (dotProductEquiv ℝ (Fin n) (embed n u))
        (integralBasisReal (integralDualBasis («Σ».fullConeBasis s)) j) < _
  rw [pairing_integral_dual_basis]
  exact add_lt_of_neg_right _ (mul_neg_of_pos_of_neg hslack (by exact_mod_cast huj))

theorem cartier_pairing_ge_of_positive_wallSlacks (hpure : «Σ».IsPure)
    (a : Lattice n→ℝ) (ha : «Σ».HasPositiveWallSlacks a)
    (u : Lattice n) (hu : u∈«Σ».rays) (s : «Σ».fullCones) :
    -a u≤(dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s) := by
  obtain ⟨s₀,hs₀⟩ := «Σ».fullCones_nonempty hpure
  letI : Nonempty «Σ».fullCones := ⟨⟨s₀,hs₀⟩⟩
  obtain ⟨t,ht,hmin⟩ := (Finset.univ : Finset «Σ».fullCones).exists_min_image
    (fun t=>(dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a t))
    Finset.univ_nonempty
  have hut : u∈t.val := by
    by_contra hut
    obtain ⟨q,hq⟩ := «Σ».exists_smaller_cartier_pairing hpure a ha t u hu hut
    exact (not_lt_of_ge (hmin q (Finset.mem_univ q))) hq
  have hvalue := «Σ».cartierPoint_support_eq_of_mem a t hut
  rw [← hvalue]
  exact hmin s (Finset.mem_univ s)

theorem cartier_pairing_gt_of_positive_wallSlacks (hpure : «Σ».IsPure)
    (a : Lattice n→ℝ) (ha : «Σ».HasPositiveWallSlacks a)
    (u : Lattice n) (hu : u∈«Σ».rays) (s : «Σ».fullCones) (hus : u∉s.val) :
    -a u<(dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s) := by
  obtain ⟨t,ht⟩ := «Σ».exists_smaller_cartier_pairing hpure a ha s u hu hus
  exact («Σ».cartier_pairing_ge_of_positive_wallSlacks hpure a ha u hu t).trans_lt ht

/-- Full-cone strict inequalities imply strict support on every face.
A small linear perturbation makes the other rays of a containing full
cone strict, while preserving all already strict inactive inequalities. -/
theorem strictSupport_of_full_cartier_inequalities (hpure : «Σ».IsPure)
    (a : Lattice n→ℝ)
    (ha : ∀ (s : «Σ».fullCones) (u : Lattice n),u∈«Σ».rays → u∉s.val →
      -a u<(dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s)) :
    «Σ».IsStrictSupport a := by
  intro F hF
  obtain ⟨s,hs,hFs,hcard⟩ := hpure F hF
  let s' : «Σ».fullCones := ⟨s,Finset.mem_filter.mpr ⟨hs,hcard⟩⟩
  let b := «Σ».fullConeBasis s'
  let B := integralBasisReal b
  have hs_basis : s = Finset.univ.image b := «Σ».fullConeBasis_ray_set s'
  let ℓ : Ambient n→ₗ[ℝ]ℝ := -(dotProductEquiv ℝ (Fin n) («Σ».cartierPoint a s'))
  have hℓ (u : Lattice n) : ℓ (embed n u) =
      -(dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s') := by
    change -(«Σ».cartierPoint a s' ⬝ᵥ embed n u) =
      -(embed n u ⬝ᵥ «Σ».cartierPoint a s')
    exact congrArg (fun r : ℝ => -r)
      (dotProduct_comm («Σ».cartierPoint a s') (embed n u))
  let I := Finset.univ.filter (fun i : Fin n=>b i∉F)
  let h : Ambient n→ₗ[ℝ]ℝ := ∑ i∈I,B.coord i
  have hh (j : Fin n) : h (embed n (b j)) = if b j∈F then 0 else 1 := by
    simp only [h,B,LinearMap.sum_apply,Module.Basis.coord_apply,integralBasisReal_repr,
      Module.Basis.repr_self_apply]
    by_cases hj : b j∈F <;> simp [I,hj]
  let J := «Σ».rays\s
  let f : Lattice n→ℝ := fun u=>a u-ℓ (embed n u)
  let g : Lattice n→ℝ := fun u=>h (embed n u)
  have hf (u : Lattice n) (hu : u∈J) : 0<f u := by
    obtain ⟨hur,hus⟩ := Finset.mem_sdiff.mp hu
    have ht := ha s' u hur hus
    dsimp [f]
    rw [hℓ]
    linarith
  obtain ⟨ε,hε,hsmall⟩ := finite_strict_perturbation J f g hf
  refine ⟨ℓ-ε • h,?_,?_⟩
  · intro u hu
    have hus := hFs hu
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp (hs_basis ▸ hus)
    rw [LinearMap.sub_apply,LinearMap.smul_apply,hℓ,hh,if_pos hu,
      «Σ».cartierPoint_support_eq_of_mem a s' (hFs hu)]
    simp
  · intro u hur huF
    by_cases hus : u∈s
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp (hs_basis ▸ hus)
      rw [LinearMap.sub_apply,LinearMap.smul_apply,hℓ,hh,if_neg huF,
        «Σ».cartierPoint_support_eq_of_mem a s' hus]
      simp only [neg_neg,smul_eq_mul,mul_one]
      linarith
    · have hz := hsmall u (Finset.mem_sdiff.mpr ⟨hur,hus⟩)
      dsimp [f,g] at hz
      change ℓ (embed n u)-ε*h (embed n u)<a u
      linarith

/-- Positive actual wall slacks suffice for the entire strict support
condition, including every lower-dimensional cone. -/
theorem strictSupport_of_positive_wallSlacks (hpure : «Σ».IsPure)
    (a : Lattice n→ℝ) (ha : «Σ».HasPositiveWallSlacks a) : «Σ».IsStrictSupport a :=
  «Σ».strictSupport_of_full_cartier_inequalities hpure a
    (fun s u hu hus=>«Σ».cartier_pairing_gt_of_positive_wallSlacks hpure a ha u hu s hus)

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.cartierPoint_across_wall
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.strictSupport_of_positive_wallSlacks
