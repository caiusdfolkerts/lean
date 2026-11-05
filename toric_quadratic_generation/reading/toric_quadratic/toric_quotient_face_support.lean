module

public import PaperVerification.ToricQuotientFaceCoordinates
public import PaperVerification.ToricAdjointSupport

@[expose] public section

/-!
# Support functions on the actual saturated quotient star

Every projected star ray has one actual primitive lift. Restriction support
is the original coefficient plus the value of the chosen affine origin on
that lift. The linear support functions factor through the saturated
quotient, proving both nefness and strict support on the actual quotient
fan. The affine image of its polytope is proved to be the original face.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones)

theorem exists_starRayLift
    (u : («Σ».completeQuotientStarFan b I hF).rays) :
    ∃ v : Lattice n, ∃ s ∈ «Σ».cones, I.image b ⊆ s ∧
      v ∈ s \ I.image b ∧ coneQuotientLattice b I v = u := by
  obtain ⟨t, ht, hut⟩ := ((«Σ».completeQuotientStarFan b I hF).mem_rays_iff u).mp u.property
  obtain ⟨s, hs, hFs, hts⟩ := («Σ».mem_quotientStarCones b I t).mp ht
  rw [hts] at hut
  obtain ⟨v, hv, hvu⟩ := Finset.mem_image.mp hut
  exact ⟨v, s, hs, hFs, hv, hvu⟩

def starRayLift (u : («Σ».completeQuotientStarFan b I hF).rays) : Lattice n :=
  Classical.choose («Σ».exists_starRayLift b I hF u)

theorem starRayLift_spec (u : («Σ».completeQuotientStarFan b I hF).rays) :
    ∃ s ∈ «Σ».cones, I.image b ⊆ s ∧
      «Σ».starRayLift b I hF u ∈ s \ I.image b ∧
      coneQuotientLattice b I («Σ».starRayLift b I hF u) = u :=
  Classical.choose_spec («Σ».exists_starRayLift b I hF u)

theorem projected_starRay_mem {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones)
    (hFs : I.image b ⊆ s) {v : Lattice n} (hv : v ∈ s \ I.image b) :
    coneQuotientLattice b I v ∈ («Σ».completeQuotientStarFan b I hF).rays := by
  apply ((«Σ».completeQuotientStarFan b I hF).mem_rays_iff _).mpr
  refine ⟨(s \ I.image b).image (coneQuotientLattice b I), ?_,
    Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
  exact («Σ».mem_quotientStarCones b I _).mpr ⟨s, hs, hFs, rfl⟩

theorem starRayLift_projected {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones)
    (hFs : I.image b ⊆ s) {v : Lattice n} (hv : v ∈ s \ I.image b) :
    «Σ».starRayLift b I hF ⟨coneQuotientLattice b I v,
      «Σ».projected_starRay_mem b I hF hs hFs hv⟩ = v := by
  obtain ⟨t, ht, hFt, hwt, hwp⟩ := «Σ».starRayLift_spec b I hF
    ⟨coneQuotientLattice b I v, «Σ».projected_starRay_mem b I hF hs hFs hv⟩
  exact «Σ».coneQuotient_injective_star_rays b I ht hs hFt hFs hwt hv hwp

/-- The actual restriction coefficient on each quotient primitive ray.
Values outside the ray set are irrelevant and are fixed to zero. -/
def faceSupport (a : Lattice n → ℝ) : Lattice (n - I.card) → ℝ := fun u =>
  if hu : u ∈ («Σ».completeQuotientStarFan b I hF).rays then
    a («Σ».starRayLift b I hF ⟨u, hu⟩) +
      (dotProductEquiv ℝ (Fin n) (embed n («Σ».starRayLift b I hF ⟨u, hu⟩)))
        (quotientFaceOrigin a b I)
  else 0

theorem faceSupport_lift (a : Lattice n → ℝ)
    (u : («Σ».completeQuotientStarFan b I hF).rays) :
    «Σ».faceSupport b I hF a u = a («Σ».starRayLift b I hF u) +
      (dotProductEquiv ℝ (Fin n) (embed n («Σ».starRayLift b I hF u)))
        (quotientFaceOrigin a b I) := by
  simp only [faceSupport, dif_pos u.property]

theorem faceSupport_projected (a : Lattice n → ℝ)
    {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (hFs : I.image b ⊆ s)
    {v : Lattice n} (hv : v ∈ s \ I.image b) :
    «Σ».faceSupport b I hF a (coneQuotientLattice b I v) =
      a v + (dotProductEquiv ℝ (Fin n) (embed n v)) (quotientFaceOrigin a b I) := by
  have h := «Σ».faceSupport_lift b I hF a
    ⟨coneQuotientLattice b I v, «Σ».projected_starRay_mem b I hF hs hFs hv⟩
  rw [«Σ».starRayLift_projected b I hF hs hFs hv] at h
  exact h

theorem quotientFaceMap_pairing (a : Lattice n → ℝ)
    (u : Lattice n) (x : Ambient (n - I.card)) :
    (dotProductEquiv ℝ (Fin n) (embed n u)) (quotientFaceMap a b I x) =
      (dotProductEquiv ℝ (Fin n) (embed n u)) (quotientFaceOrigin a b I) +
      (dotProductEquiv ℝ (Fin (n - I.card)) (embed (n - I.card)
        (coneQuotientLattice b I u))) x := by
  rw [quotientFaceMap_apply, map_add, faceTangentReal_pairing, coneQuotient_compatible]

/-- Original linear support, shifted by the affine origin, factors through
the normal quotient. -/
theorem face_linear_support_factors (a : Lattice n → ℝ)
    (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (he : ∀ i ∈ I, ℓ (embed n (b i)) = a (b i)) :
    ∀ u : Ambient n,
      ((ℓ + dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)).comp
        (coneQuotientSectionReal b I)) (coneQuotientReal b I u) =
      ℓ u + (dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)) u := by
  intro u
  apply linear_face_factorization b I
    (ℓ + dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)) ?_ u
  intro i hi
  simp only [LinearMap.add_apply, integralBasisReal_apply, he i hi]
  have hp : (dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)) (embed n (b i)) =
      -a (b i) := by
    have hcomm : (dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)) (embed n (b i)) =
        (dotProductEquiv ℝ (Fin n) (embed n (b i))) (quotientFaceOrigin a b I) := by
      change quotientFaceOrigin a b I ⬝ᵥ embed n (b i) =
        embed n (b i) ⬝ᵥ quotientFaceOrigin a b I
      exact dotProduct_comm _ _
    rw [hcomm, normal_pairing_eq_dual_coordinate,
      quotientFaceOrigin_coordinate, if_pos hi]
  rw [hp, add_neg_cancel]

/-- Nefness restricts to the genuine saturated quotient-star fan. -/
theorem faceSupport_isNef (a : Lattice n → ℝ) (ha : «Σ».IsNef a) :
    («Σ».completeQuotientStarFan b I hF).IsNef («Σ».faceSupport b I hF a) := by
  intro t ht
  obtain ⟨s, hs, hFs, hts⟩ := («Σ».mem_quotientStarCones b I t).mp ht
  obtain ⟨ℓ, he, hle⟩ := ha s hs
  let L := ℓ + dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)
  let q := L.comp (coneQuotientSectionReal b I)
  have hfactor (v : Lattice n) : q (embed (n - I.card) (coneQuotientLattice b I v)) =
      ℓ (embed n v) + (dotProductEquiv ℝ (Fin n) (embed n v)) (quotientFaceOrigin a b I) := by
    rw [← coneQuotient_compatible]
    have h := face_linear_support_factors b I a ℓ
      (fun i hi => he _ (hFs (Finset.mem_image.mpr ⟨i, hi, rfl⟩))) (embed n v)
    change q (coneQuotientReal b I (embed n v)) =
      ℓ (embed n v) + quotientFaceOrigin a b I ⬝ᵥ embed n v at h
    change q (coneQuotientReal b I (embed n v)) =
      ℓ (embed n v) + embed n v ⬝ᵥ quotientFaceOrigin a b I
    rw [dotProduct_comm (embed n v) (quotientFaceOrigin a b I)]
    exact h
  refine ⟨q, ?_, ?_⟩
  · intro u hu
    rw [hts] at hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    rw [hfactor, he v (Finset.mem_sdiff.mp hv).1,
      «Σ».faceSupport_projected b I hF a hs hFs hv]
  · intro u hu
    let u' : («Σ».completeQuotientStarFan b I hF).rays := ⟨u, hu⟩
    obtain ⟨s', hs', hFs', hv, hproj⟩ := «Σ».starRayLift_spec b I hF u'
    have hvray := «Σ».ray_mem_of_mem_cone hs' (Finset.mem_sdiff.mp hv).1
    have hbound := hle («Σ».starRayLift b I hF u') hvray
    have hsupp := «Σ».faceSupport_lift b I hF a u'
    have hfactor' := hfactor («Σ».starRayLift b I hF u')
    rw [hproj] at hfactor'
    exact hfactor'.trans_le ((add_le_add hbound le_rfl).trans_eq hsupp.symm)

/-- Strict support restricts as well: no extra quotient-ray coincidence is
assumed, since uniqueness of actual primitive lifts was proved above. -/
theorem faceSupport_isStrictSupport (a : Lattice n → ℝ)
    (ha : «Σ».IsStrictSupport a) :
    («Σ».completeQuotientStarFan b I hF).IsStrictSupport («Σ».faceSupport b I hF a) := by
  intro t ht
  obtain ⟨s, hs, hFs, hts⟩ := («Σ».mem_quotientStarCones b I t).mp ht
  obtain ⟨ℓ, he, hlt⟩ := ha s hs
  let L := ℓ + dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)
  let q := L.comp (coneQuotientSectionReal b I)
  have hfactor (v : Lattice n) : q (embed (n - I.card) (coneQuotientLattice b I v)) =
      ℓ (embed n v) + (dotProductEquiv ℝ (Fin n) (embed n v)) (quotientFaceOrigin a b I) := by
    rw [← coneQuotient_compatible]
    have h := face_linear_support_factors b I a ℓ
      (fun i hi => he _ (hFs (Finset.mem_image.mpr ⟨i, hi, rfl⟩))) (embed n v)
    change q (coneQuotientReal b I (embed n v)) =
      ℓ (embed n v) + quotientFaceOrigin a b I ⬝ᵥ embed n v at h
    change q (coneQuotientReal b I (embed n v)) =
      ℓ (embed n v) + embed n v ⬝ᵥ quotientFaceOrigin a b I
    rw [dotProduct_comm (embed n v) (quotientFaceOrigin a b I)]
    exact h
  refine ⟨q, ?_, ?_⟩
  · intro u hu
    rw [hts] at hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    rw [hfactor, he v (Finset.mem_sdiff.mp hv).1,
      «Σ».faceSupport_projected b I hF a hs hFs hv]
  · intro u hu hut
    let u' : («Σ».completeQuotientStarFan b I hF).rays := ⟨u, hu⟩
    obtain ⟨s', hs', hFs', hv, hproj⟩ := «Σ».starRayLift_spec b I hF u'
    have hvray := «Σ».ray_mem_of_mem_cone hs' (Finset.mem_sdiff.mp hv).1
    have hvnot : «Σ».starRayLift b I hF u' ∉ s := by
      intro hvs
      apply hut
      rw [hts]
      exact Finset.mem_image.mpr ⟨«Σ».starRayLift b I hF u',
        Finset.mem_sdiff.mpr ⟨hvs, (Finset.mem_sdiff.mp hv).2⟩, hproj⟩
    have hbound := hlt («Σ».starRayLift b I hF u') hvray hvnot
    have hsupp := «Σ».faceSupport_lift b I hF a u'
    have hfactor' := hfactor («Σ».starRayLift b I hF u')
    rw [hproj] at hfactor'
    exact hfactor'.trans_lt ((add_lt_add_of_lt_of_le hbound le_rfl).trans_eq hsupp.symm)

/-- A full cone of the quotient star is the projection of a full original
cone containing the deleted cone. The dimension assertion is a consequence
of the already proved injectivity of primitive ray projection. -/
theorem exists_fullCone_lift
    (t : («Σ».completeQuotientStarFan b I hF).fullCones) :
    ∃ s : «Σ».fullCones, I.image b ⊆ (s : Finset (Lattice n)) ∧
      (t : Finset (Lattice (n - I.card))) =
        ((s : Finset (Lattice n)) \ I.image b).image (coneQuotientLattice b I) := by
  obtain ⟨s, hs, hFs, hts⟩ := («Σ».mem_quotientStarCones b I t).mp
    ((«Σ».completeQuotientStarFan b I hF).fullCones_mem t)
  have hcard := («Σ».completeQuotientStarFan b I hF).fullCones_card t
  have himage : ((s \ I.image b).image (coneQuotientLattice b I)).card =
      (s \ I.image b).card := by
    apply Finset.card_image_of_injOn
    intro v hv w hw he
    exact «Σ».coneQuotient_injective_star_rays b I hs hs hFs hFs hv hw he
  have hIcard : (I.image b).card = I.card := Finset.card_image_of_injective I b.injective
  have hIs : I.card ≤ s.card := by
    rw [← hIcard]
    exact Finset.card_le_card hFs
  have hIn : I.card ≤ n := hIs.trans («Σ».card_cone_le hs)
  rw [hts, himage, Finset.card_sdiff_of_subset hFs, hIcard] at hcard
  have hsn : s.card = n := by omega
  exact ⟨⟨s, Finset.mem_filter.mpr ⟨hs, hsn⟩⟩, hFs, hts⟩

/-- The quotient Cartier point maps to the original Cartier point in every
full lifted chart. This is an equality of actual vectors. -/
theorem quotientFaceMap_cartierPoint (a : Lattice n → ℝ)
    (t : («Σ».completeQuotientStarFan b I hF).fullCones)
    (s : «Σ».fullCones) (hFs : I.image b ⊆ (s : Finset (Lattice n)))
    (hts : (t : Finset (Lattice (n - I.card))) =
      ((s : Finset (Lattice n)) \ I.image b).image (coneQuotientLattice b I)) :
    quotientFaceMap a b I
        ((«Σ».completeQuotientStarFan b I hF).cartierPoint («Σ».faceSupport b I hF a) t) =
      «Σ».cartierPoint a s := by
  let x := («Σ».completeQuotientStarFan b I hF).cartierPoint («Σ».faceSupport b I hF a) t
  have hactive (u : Lattice n) (hu : u ∈ (s : Finset (Lattice n))) :
      (dotProductEquiv ℝ (Fin n) (embed n u)) (quotientFaceMap a b I x) = -a u := by
    by_cases huF : u ∈ I.image b
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp huF
      exact quotientFaceMap_active a b I x i hi
    · have hut : coneQuotientLattice b I u ∈ (t : Finset (Lattice (n - I.card))) := by
        rw [hts]
        exact Finset.mem_image.mpr ⟨u, Finset.mem_sdiff.mpr ⟨hu, huF⟩, rfl⟩
      have hq := («Σ».completeQuotientStarFan b I hF).cartierPoint_support_eq
        («Σ».faceSupport b I hF a) t hut
      rw [«Σ».faceSupport_projected b I hF a («Σ».fullCones_mem s) hFs
        (Finset.mem_sdiff.mpr ⟨hu, huF⟩)] at hq
      rw [quotientFaceMap_pairing]
      change _ + (dotProductEquiv ℝ (Fin (n - I.card))
        (embed (n - I.card) (coneQuotientLattice b I u))) x = _
      rw [hq]
      ring
  apply (integralBasisReal (integralDualBasis («Σ».fullConeBasis s))).ext_elem
  intro i
  rw [← normal_pairing_eq_dual_coordinate, ← normal_pairing_eq_dual_coordinate]
  have hi : «Σ».fullConeBasis s i ∈ (s : Finset (Lattice n)) := by
    rw [«Σ».fullConeBasis_ray_set]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  rw [hactive _ hi, «Σ».cartierPoint_support_eq a s hi]

/-- The exact saturated face dictionary, including nef degenerate faces.
No extra inequality is discarded: containment in the original polytope is
proved first on all quotient Cartier points and then on their convex hull. -/
theorem quotientFaceMap_image_fanPolytope (hpure : «Σ».IsPure)
    (a : Lattice n → ℝ) (ha : «Σ».IsNef a) :
    quotientFaceMap a b I ''
      («Σ».completeQuotientStarFan b I hF).fanPolytope («Σ».faceSupport b I hF a) =
      «Σ».supportFace a (I.image b) := by
  let Ψ := «Σ».completeQuotientStarFan b I hF
  have hΨpure : Ψ.IsPure := «Σ».completeQuotientStarFan_isPure hpure b I hF
  have hΨnef : Ψ.IsNef («Σ».faceSupport b I hF a) :=
    «Σ».faceSupport_isNef b I hF a ha
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    have hcontain : Ψ.fanPolytope («Σ».faceSupport b I hF a) ⊆
        quotientFaceMap a b I ⁻¹' «Σ».supportFace a (I.image b) := by
      rw [Ψ.fanPolytope_eq_convexHull_cartier hΨpure _ hΨnef]
      apply convexHull_min
      · rintro z ⟨t, rfl⟩
        obtain ⟨s, hFs, hts⟩ := «Σ».exists_fullCone_lift b I hF t
        change quotientFaceMap a b I
          (Ψ.cartierPoint («Σ».faceSupport b I hF a) t) ∈ «Σ».supportFace a (I.image b)
        rw [«Σ».quotientFaceMap_cartierPoint b I hF a t s hFs hts]
        exact ⟨«Σ».cartierPoint_mem_of_nef ha s,
          fun u hu => «Σ».cartierPoint_support_eq a s (hFs hu)⟩
      · exact Convex.affine_preimage _ («Σ».convex_supportFace a (I.image b))
    exact hcontain hy
  · intro x hx
    have hactive : ∀ i ∈ I,
        (dotProductEquiv ℝ (Fin n) (embed n (b i))) x = -a (b i) :=
      fun i hi => hx.2 _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    obtain ⟨y, rfl⟩ := (mem_range_quotientFaceMap_iff a b I x).mpr hactive
    refine ⟨y, ?_, rfl⟩
    intro u hu
    let u' : Ψ.rays := ⟨u, hu⟩
    obtain ⟨s, hs, hFs, hv, hproj⟩ := «Σ».starRayLift_spec b I hF u'
    have hvray := «Σ».ray_mem_of_mem_cone hs (Finset.mem_sdiff.mp hv).1
    have hbound := hx.1 («Σ».starRayLift b I hF u') hvray
    rw [quotientFaceMap_pairing, hproj] at hbound
    have hsupp := «Σ».faceSupport_lift b I hF a u'
    change -«Σ».faceSupport b I hF a u ≤ _
    rw [hsupp]
    linarith

/-- Integral restriction coefficients use the actual integral affine
origin and the actual primitive lifts. -/
def faceSupportLattice (a : Lattice n → ℤ) : Lattice (n - I.card) → ℤ := fun u =>
  if hu : u ∈ («Σ».completeQuotientStarFan b I hF).rays then
    a («Σ».starRayLift b I hF ⟨u, hu⟩) +
      ∑ i, («Σ».starRayLift b I hF ⟨u, hu⟩) i * quotientFaceOriginLattice a b I i
  else 0

theorem faceSupportLattice_cast (a : Lattice n → ℤ) :
    (fun u => («Σ».faceSupportLattice b I hF a u : ℝ)) =
      «Σ».faceSupport b I hF (fun u => (a u : ℝ)) := by
  funext u
  by_cases hu : u ∈ («Σ».completeQuotientStarFan b I hF).rays
  · simp only [faceSupportLattice, faceSupport, dif_pos hu, Int.cast_add]
    rw [← embed_quotientFaceOrigin, normalRay_pairing_lattice]
  · simp only [faceSupportLattice, faceSupport, dif_neg hu, Int.cast_zero]

theorem quotientFaceIntegralChart_image_fanPolytope (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsNef (fun u => (a u : ℝ))) :
    (quotientFaceIntegralChart a b I).realMap ''
      («Σ».completeQuotientStarFan b I hF).fanPolytope
        (fun u => («Σ».faceSupportLattice b I hF a u : ℝ)) =
      «Σ».supportFace (fun u => (a u : ℝ)) (I.image b) := by
  rw [quotientFaceIntegralChart_realMap, «Σ».faceSupportLattice_cast]
  exact «Σ».quotientFaceMap_image_fanPolytope b I hF hpure _ ha

end PaperVerification.ToricGeometry.SmoothCompleteFan
