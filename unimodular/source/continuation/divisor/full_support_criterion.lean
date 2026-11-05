module

public import Continuation.Divisor.Geometry

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ToricGeometry.SmoothCompleteFan
open Set
open scoped Classical BigOperators
variable {n : ℕ} («Σ» : SmoothCompleteFan n)

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


end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.strictSupport_of_full_cartier_inequalities
