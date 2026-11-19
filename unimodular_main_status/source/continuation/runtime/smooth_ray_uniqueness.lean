module

public import Continuation.Runtime.SmoothConeFamily

/-!
# Primitive ray sets are determined by their smooth cones

The primitive integral generators of a smooth cone are intrinsic. The
proof works directly with integer basis coordinates: subtracting a
positive coordinate generator leaves another lattice point of the cone,
and a primitive basis vector cannot split into two nonzero such points.
This supplies the exact common-ray equality needed after identifying
affine-chart overlaps by the valuative criterion.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PaperVerification.ToricGeometry

open scoped Classical

variable {n : ℕ}

/-- The real cone contains precisely the integral vectors with the
stated nonnegative integer coordinates and zero free coordinates. -/
theorem embed_mem_latticeRayCone_basis_iff
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) (m : Lattice n) :
    embed n m ∈ latticeRayCone (I.image b) ↔
      (∀ i, 0 ≤ b.repr m i) ∧ (∀ i ∉ I, b.repr m i = 0) := by
  rw [mem_latticeRayCone_basis_iff]
  simp only [integralBasisReal_repr, Int.cast_nonneg_iff, Int.cast_eq_zero]

/-- A primitive vector in one basis must be one of the primitive
generators of any other basis-subset presentation of the same cone. -/
theorem basisRay_mem_of_cone_eq
    (b c : Module.Basis (Fin n) ℤ (Lattice n)) (I J : Finset (Fin n))
    (hcone : latticeRayCone (I.image b) = latticeRayCone (J.image c))
    (i : Fin n) (hi : i ∈ I) : b i ∈ J.image c := by
  have hbi : embed n (b i) ∈ latticeRayCone (J.image c) := by
    rw [← hcone]
    exact latticeRayCone_generator _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  obtain ⟨hpos, hzero⟩ := (embed_mem_latticeRayCone_basis_iff c J (b i)).mp hbi
  have hpositive : ∃ j, 0 < c.repr (b i) j := by
    by_contra h
    push_neg at h
    have hz : c.repr (b i) = 0 := by
      ext j
      exact le_antisymm (h j) (hpos j)
    exact b.ne_zero i (c.repr.injective (by simpa using hz))
  obtain ⟨j, hj⟩ := hpositive
  have hjJ : j ∈ J := by
    by_contra h
    rw [hzero j h] at hj
    exact (lt_irrefl 0) hj
  have hcj : embed n (c j) ∈ latticeRayCone (I.image b) := by
    rw [hcone]
    exact latticeRayCone_generator _ (Finset.mem_image.mpr ⟨j, hjJ, rfl⟩)
  have hrest : embed n (b i - c j) ∈ latticeRayCone (I.image b) := by
    rw [hcone, embed_mem_latticeRayCone_basis_iff]
    constructor
    · intro q
      simp only [map_sub, Finsupp.sub_apply, Module.Basis.repr_self, Finsupp.single_apply]
      by_cases hjq : j = q
      · subst q
        simp only [if_pos rfl]
        omega
      · simp only [if_neg hjq, sub_zero]
        exact hpos q
    · intro q hq
      have hjq : j ≠ q := fun h => hq (h ▸ hjJ)
      simp [hzero q hq, hjq]
  have hcjpos := (embed_mem_latticeRayCone_basis_iff b I (c j)).mp hcj |>.1
  have hrestpos := (embed_mem_latticeRayCone_basis_iff b I (b i - c j)).mp hrest |>.1
  have hother (q : Fin n) (hqi : q ≠ i) : b.repr (c j) q = 0 := by
    have hq := hrestpos q
    simp only [map_sub, Finsupp.sub_apply, Module.Basis.repr_self,
      Finsupp.single_apply, if_neg (Ne.symm hqi), zero_sub] at hq
    exact le_antisymm (neg_nonneg.mp hq) (hcjpos q)
  have hinez : b.repr (c j) i ≠ 0 := by
    intro h
    apply c.ne_zero j
    apply b.repr.injective
    ext q
    by_cases hqi : q = i
    · subst q
      simpa using h
    · simpa using hother q hqi
  have hione : b.repr (c j) i = 1 := by
    have hu := hrestpos i
    simp only [map_sub, Finsupp.sub_apply, Module.Basis.repr_self,
      Finsupp.single_apply, if_pos rfl] at hu
    have hl := hcjpos i
    omega
  refine Finset.mem_image.mpr ⟨j, hjJ, ?_⟩
  apply b.repr.injective
  ext q
  by_cases hqi : q = i
  · subst q
    simpa using hione
  · simp [hother q hqi, hqi, Ne.symm hqi]

/-- Equal smooth real cones have exactly equal primitive lattice rays. -/
theorem smooth_raysets_eq_of_cone_eq
    {s t : Finset (Lattice n)}
    (hs : ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)), s = I.image b)
    (ht : ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)), t = I.image b)
    (h : latticeRayCone s = latticeRayCone t) : s = t := by
  obtain ⟨b, I, rfl⟩ := hs
  obtain ⟨c, J, rfl⟩ := ht
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact basisRay_mem_of_cone_eq b c I J h i hi
  · intro v hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    exact basisRay_mem_of_cone_eq c b J I h.symm j hj

/-- Within a fixed smooth cone, a listed primitive ray belongs to a
subcone on a subset exactly when it belongs to that subset. -/
theorem smooth_ray_mem_subcone_iff
    {s t : Finset (Lattice n)}
    (hs : ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)), s = I.image b)
    (hts : t ⊆ s) {v : Lattice n} (hv : v ∈ s) :
    embed n v ∈ latticeRayCone t ↔ v ∈ t := by
  obtain ⟨b, I, rfl⟩ := hs
  let J := basisRayIndices b t
  have hJ : J.image b = t := image_basisRayIndices b t
    (hts.trans (Finset.image_subset_image (Finset.subset_univ I)))
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
  constructor
  · intro h
    rw [← hJ, embed_mem_latticeRayCone_basis_iff] at h
    have hiJ : i ∈ J := by
      by_contra hn
      have hzero := h.2 i hn
      simpa using hzero
    rw [← hJ]
    exact Finset.mem_image.mpr ⟨i, hiJ, rfl⟩
  · exact latticeRayCone_generator t

/-- If the geometric intersection is a coordinate face on both sides,
then its rays are literally the common primitive rays. -/
theorem common_coordinate_faces_eq_intersection
    {s t r q : Finset (Lattice n)}
    (hs : ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)), s = I.image b)
    (ht : ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)), t = I.image b)
    (hrs : r ⊆ s) (hqt : q ⊆ t)
    (hr : latticeRayCone r = latticeRayCone s ⊓ latticeRayCone t)
    (hq : latticeRayCone q = latticeRayCone s ⊓ latticeRayCone t) :
    r = s ∩ t := by
  have sub_smooth {a d : Finset (Lattice n)}
      (ha : ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)), a = I.image b)
      (hda : d ⊆ a) :
      ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)), d = I.image b := by
    obtain ⟨b, I, rfl⟩ := ha
    exact ⟨b, basisRayIndices b d,
      (image_basisRayIndices b d
        (hda.trans (Finset.image_subset_image (Finset.subset_univ I)))).symm⟩
  have hrq : r = q := smooth_raysets_eq_of_cone_eq
    (sub_smooth hs hrs) (sub_smooth ht hqt) (hr.trans hq.symm)
  apply Finset.Subset.antisymm
  · intro v hv
    exact Finset.mem_inter.mpr ⟨hrs hv, hqt (hrq ▸ hv)⟩
  · intro v hv
    apply (smooth_ray_mem_subcone_iff hs hrs (Finset.mem_inter.mp hv).1).mp
    rw [hr]
    exact ⟨latticeRayCone_generator s (Finset.mem_inter.mp hv).1,
      latticeRayCone_generator t (Finset.mem_inter.mp hv).2⟩

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.smooth_raysets_eq_of_cone_eq
#print axioms PaperVerification.ToricGeometry.common_coordinate_faces_eq_intersection
