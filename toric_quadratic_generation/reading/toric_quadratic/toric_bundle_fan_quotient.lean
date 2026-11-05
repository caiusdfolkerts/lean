module

public import PaperVerification.ToricBundleFanCoordinates


@[expose] public section
/-!
# Actual cones in a saturated quotient

The fan intersection property descends through a smooth cone.  The proof
lifts two equal quotient vectors and adds nonnegative combinations of the
common cone rays to make the lifts equal.  Smoothness descends through the
explicit integral quotient basis from `ToricBundleFanCoordinates`.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem finiteRayCone_image_linear {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (s : Finset E) (f : E →ₗ[ℝ] F) :
    finiteRayCone (s.image f) = (finiteRayCone s).map f := by
  rw [finiteRayCone_eq_hull, finiteRayCone_eq_hull]
  change Submodule.span (Nonneg ℝ) ((s.image f : Finset F) : Set F) =
    Submodule.map (f : E →ₗ[Nonneg ℝ] F) (Submodule.span (Nonneg ℝ) (s : Set E))
  rw [Finset.coe_image]
  exact Submodule.span_image (f : E →ₗ[Nonneg ℝ] F)

variable {n : ℕ}

theorem latticeRayCone_image_quotient
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) :
    latticeRayCone (s.image (coneQuotientLattice b I)) =
      (latticeRayCone s).map (coneQuotientReal b I) := by
  unfold latticeRayCone
  rw [← finiteRayCone_image_linear]
  congr 1
  simp only [Finset.image_image]
  ext x
  simp only [Finset.mem_image, Function.comp_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, coneQuotient_compatible b I v⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, (coneQuotient_compatible b I v).symm⟩

theorem coneQuotient_zero_on_cone
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    {x : Ambient n} (hx : x ∈ latticeRayCone (I.image b)) :
    coneQuotientReal b I x = 0 := by
  have hcoord := (mem_latticeRayCone_basis_iff b I x).mp hx
  change quotientCoordinateFinEquiv ℝ I
    (basisProjection (integralBasisReal b) I x) = 0
  rw [(basisProjection_eq_zero_iff (integralBasisReal b) I x).mpr hcoord.2, map_zero]

/-- Two lifts of one quotient vector become identical after adding vectors
in the same actual cone on the deleted basis rays. -/
theorem coneQuotient_common_lift
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    {x y : Ambient n} (hxy : coneQuotientReal b I x = coneQuotientReal b I y) :
    ∃ a ∈ latticeRayCone (I.image b), ∃ c ∈ latticeRayCone (I.image b),
      x + a = y + c := by
  let β := integralBasisReal b
  let d : Fin n → ℝ := fun i => β.repr (y - x) i
  have hproj : basisProjection β I (y - x) = 0 := by
    apply (quotientCoordinateFinEquiv ℝ I).injective
    change coneQuotientReal b I (y - x) = quotientCoordinateFinEquiv ℝ I 0
    rw [map_sub, hxy, sub_self, map_zero]
  have hsum : (∑ i ∈ I, d i • β i) = y - x := by
    have h := basisSection_projection_decomposition β I (y - x)
    rw [hproj, map_zero, zero_add] at h
    exact h
  let a := ∑ i ∈ I, max (d i) 0 • β i
  let c := ∑ i ∈ I, (max (d i) 0 - d i) • β i
  have ha : a ∈ latticeRayCone (I.image b) := by
    rw [latticeRayCone_basis]
    exact Submodule.sum_mem _ (fun i hi => PointedCone.smul_mem _
      (le_max_right _ _) (finiteRayCone_generator _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)))
  have hc : c ∈ latticeRayCone (I.image b) := by
    rw [latticeRayCone_basis]
    exact Submodule.sum_mem _ (fun i hi => PointedCone.smul_mem _
      (sub_nonneg.mpr (le_max_left _ _))
      (finiteRayCone_generator _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)))
  have hac : a - c = y - x := by
    change (∑ i ∈ I, max (d i) 0 • β i) -
      (∑ i ∈ I, (max (d i) 0 - d i) • β i) = _
    rw [← Finset.sum_sub_distrib]
    simp only [← sub_smul, sub_sub_cancel]
    exact hsum
  refine ⟨a, ha, c, hc, ?_⟩
  calc
    x + a = x + (a - c) + c := by abel
    _ = x + (y - x) + c := by rw [hac]
    _ = y + c := by abel

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n)

/-- Projecting genuine cones containing a common smooth cone preserves
their genuine geometric intersections. -/
theorem coneQuotient_intersection
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    {s t : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones)
    (hIs : I.image b ⊆ s) (hIt : I.image b ⊆ t) :
    (latticeRayCone s).map (coneQuotientReal b I) ⊓
      (latticeRayCone t).map (coneQuotientReal b I) =
        (latticeRayCone (s ∩ t)).map (coneQuotientReal b I) := by
  apply le_antisymm
  · rintro z ⟨⟨x, hx, hxz⟩, ⟨y, hy, hyz⟩⟩
    obtain ⟨a, ha, c, hc, he⟩ := coneQuotient_common_lift b I (hxz.trans hyz.symm)
    have has : a ∈ latticeRayCone s := latticeRayCone_mono hIs ha
    have hct : c ∈ latticeRayCone t := latticeRayCone_mono hIt hc
    have hboth : x + a ∈ latticeRayCone (s ∩ t) := by
      rw [← «Σ».intersection s hs t ht]
      refine ⟨Submodule.add_mem _ hx has, ?_⟩
      rw [he]
      exact Submodule.add_mem _ hy hct
    refine ⟨x + a, hboth, ?_⟩
    change coneQuotientReal b I x = z at hxz
    change coneQuotientReal b I (x + a) = z
    rw [map_add, coneQuotient_zero_on_cone b I ha, add_zero, hxz]
  · rintro z ⟨x, hx, rfl⟩
    exact ⟨⟨x, latticeRayCone_mono Finset.inter_subset_left hx, rfl⟩,
      ⟨x, latticeRayCone_mono Finset.inter_subset_right hx, rfl⟩⟩

end SmoothCompleteFan

/-- Removing the rays killed by the quotient does not change the image cone. -/
theorem latticeRayCone_quotient_sdiff
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) :
    latticeRayCone ((s \ I.image b).image (coneQuotientLattice b I)) =
      (latticeRayCone s).map (coneQuotientReal b I) := by
  rw [← latticeRayCone_image_quotient]
  apply le_antisymm
  · exact latticeRayCone_mono (Finset.image_subset_image Finset.sdiff_subset)
  · rw [latticeRayCone, finiteRayCone_eq_hull]
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    by_cases hwI : w ∈ I.image b
    · rw [coneQuotientLattice_of_mem b I hwI, map_zero]
      exact Submodule.zero_mem _
    · exact latticeRayCone_generator _ (Finset.mem_image.mpr
        ⟨w, Finset.mem_sdiff.mpr ⟨hw, hwI⟩, rfl⟩)

theorem basis_image_card_eq {b c : Module.Basis (Fin n) ℤ (Lattice n)}
    {I J : Finset (Fin n)} (hIJ : I.image b = J.image c) : I.card = J.card := by
  have h := congrArg Finset.card hIJ
  simpa only [Finset.card_image_of_injective _ b.injective,
    Finset.card_image_of_injective _ c.injective] using h

/-- A full integral basis of the quotient, constructed from any full basis
containing the deleted rays. -/
def coneQuotientBasis (b c : Module.Basis (Fin n) ℤ (Lattice n))
    (I J : Finset (Fin n)) (hIJ : I.image b = J.image c) :
    Module.Basis (Fin (n - I.card)) ℤ (Lattice (n - I.card)) :=
  ((descendedQuotientBasis b c I J
      (by simpa only [Finset.ext_iff, Finset.mem_image] using hIJ)).map
    (quotientCoordinateFinEquiv ℤ I)).reindex
    (Fintype.equivFinOfCardEq (by
      rw [complementaryIndex_card, basis_image_card_eq hIJ]))

theorem coneQuotientBasis_range (b c : Module.Basis (Fin n) ℤ (Lattice n))
    (I J : Finset (Fin n)) (hIJ : I.image b = J.image c)
    (j : ComplementaryIndex J) :
    coneQuotientLattice b I (c j) ∈
      (Finset.univ : Finset (Fin (n - I.card))).image (coneQuotientBasis b c I J hIJ) := by
  let e : ComplementaryIndex J ≃ Fin (n - I.card) :=
    Fintype.equivFinOfCardEq (by rw [complementaryIndex_card, basis_image_card_eq hIJ])
  refine Finset.mem_image.mpr ⟨e j, Finset.mem_univ _, ?_⟩
  simp only [coneQuotientBasis, Module.Basis.reindex_apply, Module.Basis.map_apply]
  change quotientCoordinateFinEquiv ℤ I
    (descendedQuotientBasis b c I J
      (by simpa only [Finset.ext_iff, Finset.mem_image] using hIJ) (e.symm (e j))) = _
  rw [e.symm_apply_apply, descendedQuotientBasis_apply]
  rfl

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n)

/-- Smoothness survives in the saturated quotient, with an actual integral
basis of the target lattice. -/
theorem coneQuotient_smooth
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (hIs : I.image b ⊆ s) :
    ∃ (β : Module.Basis (Fin (n - I.card)) ℤ (Lattice (n - I.card)))
      (K : Finset (Fin (n - I.card))),
      (s \ I.image b).image (coneQuotientLattice b I) = K.image β := by
  obtain ⟨c, L, hL⟩ := «Σ».smooth s hs
  let J := basisRayIndices c (I.image b)
  have hJ : J.image c = I.image b := image_basisRayIndices c _ (by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hL ▸ hIs hv)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  let β := coneQuotientBasis b c I J hJ.symm
  let T := (s \ I.image b).image (coneQuotientLattice b I)
  have hT : T ⊆ Finset.univ.image β := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hwS, hwF⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hL ▸ hwS)
    have hiJ : i ∉ J := by
      intro hij
      exact hwF (hJ ▸ Finset.mem_image.mpr ⟨i, hij, rfl⟩)
    exact coneQuotientBasis_range b c I J hJ.symm ⟨i, hiJ⟩
  exact ⟨β, basisRayIndices β T, (image_basisRayIndices β T hT).symm⟩

theorem coneQuotient_nonzero_ray
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (hIs : I.image b ⊆ s)
    {v : Lattice n} (hv : v ∈ s \ I.image b) : coneQuotientLattice b I v ≠ 0 := by
  obtain ⟨β, K, hK⟩ := «Σ».coneQuotient_smooth b I hs hIs
  have hmem : coneQuotientLattice b I v ∈ K.image β :=
    hK ▸ Finset.mem_image.mpr ⟨v, hv, rfl⟩
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hmem
  rw [← he]
  exact β.ne_zero j

end SmoothCompleteFan

end PaperVerification.ToricGeometry
