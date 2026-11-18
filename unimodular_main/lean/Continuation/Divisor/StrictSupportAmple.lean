module

public import Continuation.Divisor.Geometry

/-!
# Strict toric support gives intrinsic ampleness

A Cartier character for a maximal cone has nonvanishing open exactly
that cone's actual affine chart. This is proved by localizing the actual
semigroup algebra at the character whose zero face is the common cone.
Thus the usual affine-nonvanishing definition of ampleness follows from
strict support, without assuming projectivity.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u
namespace Unimodular.NefBig

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricSchemes PaperVerification.ToricCharacters
open PaperVerification.ToricGeometry
open scoped Classical BigOperators

section OpenImage
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (j : X ⟶ Y) [IsOpenImmersion j]

lemma imageTop_nonempty : Nonempty (j ''ᵁ (⊤ : X.Opens)) :=
  openImmersion_image_nonempty j ⊤

lemma opensRange_nonempty : Nonempty j.opensRange := by
  simpa only [j.image_top_eq_opensRange] using imageTop_nonempty j

lemma imageSection_value (a : Γ(X, ⊤)) :
    letI := opensRange_nonempty j
    Y.germToFunctionField j.opensRange ((IsOpenImmersion.ΓIsoTop j).hom a) =
      openImmersionGlobalToFunctionField j a := by
  letI := opensRange_nonempty j
  letI := imageTop_nonempty j
  change Y.germToFunctionField j.opensRange
      (Y.presheaf.map (eqToHom j.image_top_eq_opensRange.symm).op
        ((j.appIso ⊤).inv a)) = _
  rw [germToFunctionField_restrict]
  exact (openImmersionRegularToFunctionField_eq_germ_image j ⊤ a).symm

lemma imageSection_basicOpen (a : Γ(X, ⊤)) :
    Y.basicOpen ((IsOpenImmersion.ΓIsoTop j).hom a) = j ''ᵁ X.basicOpen a := by
  change Y.basicOpen (Y.presheaf.map
    (eqToHom j.image_top_eq_opensRange.symm).op ((j.appIso ⊤).inv a)) = _
  rw [Y.basicOpen_res_eq]
  exact (Scheme.image_basicOpen j a).symm
end OpenImage

section ZeroFace
variable {n : ℕ}

/-- The face where an actual semigroup character is zero on the rays. -/
def characterVanishingFace (s : Finset (Lattice n)) (z : Lattice n) : Finset (Lattice n) :=
  s.filter (fun u => PaperVerification.ToricGeometry.integerPairing u z = 0)

lemma characterVanishingFace_subset (s : Finset (Lattice n)) (z : Lattice n) :
    characterVanishingFace s z ⊆ s := Finset.filter_subset _ _

lemma characterVanishingFace_negative (s : Finset (Lattice n)) (z : Lattice n) :
    -z ∈ dualConeMonoid (characterVanishingFace s z) := by
  intro u hu
  have hz := (Finset.mem_filter.mp hu).2
  simp only [PaperVerification.ToricGeometry.integerPairing, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  change 0 ≤ -PaperVerification.ToricGeometry.integerPairing u z
  rw [hz, neg_zero]

lemma characterVanishingFace_clear (s : Finset (Lattice n)) (z : Lattice n)
    (hz : z ∈ dualConeMonoid s) (m : Lattice n)
    (hm : m ∈ dualConeMonoid (characterVanishingFace s z)) :
    ∃ N : ℕ, m + N • z ∈ dualConeMonoid s := by
  let N := s.sup (fun u => (-PaperVerification.ToricGeometry.integerPairing u m).toNat)
  refine ⟨N, ?_⟩
  intro u hu
  have he : PaperVerification.ToricGeometry.integerPairing u (m + N • z) =
      PaperVerification.ToricGeometry.integerPairing u m + (N : ℤ) * PaperVerification.ToricGeometry.integerPairing u z := by
    simp [PaperVerification.ToricGeometry.integerPairing, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul,
      mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul,
      mul_assoc, mul_left_comm, mul_comm]
  rw [he]
  by_cases hzero : PaperVerification.ToricGeometry.integerPairing u z = 0
  · rw [hzero, mul_zero, add_zero]
    exact hm u (Finset.mem_filter.mpr ⟨hu, hzero⟩)
  · have hpos : 1 ≤ PaperVerification.ToricGeometry.integerPairing u z := by have := hz u hu; omega
    have hle : (-PaperVerification.ToricGeometry.integerPairing u m).toNat ≤ N := by
      exact Finset.le_sup (f := fun v =>
        (-PaperVerification.ToricGeometry.integerPairing v m).toNat) hu
    have hleZ : (((-PaperVerification.ToricGeometry.integerPairing u m).toNat : ℕ) : ℤ) ≤ (N : ℤ) := by
      exact_mod_cast hle
    have hself := Int.self_le_toNat (-PaperVerification.ToricGeometry.integerPairing u m)
    have hN : (0 : ℤ) ≤ N := Int.natCast_nonneg _
    nlinarith

lemma characterVanishingFace_localization (k : Type u) [CommSemiring k]
    (s : Finset (Lattice n)) (z : Lattice n) (hz : z ∈ dualConeMonoid s) :
    (Submonoid.powers (chartCharacter k (dualConeMonoid s) z hz)).IsLocalizationMap
      (monoidChartInclusion k (dualConeMonoid_antitone
        (characterVanishingFace_subset s z))) :=
  monoidChartInclusion_isLocalizationMap k
    (dualConeMonoid_antitone (characterVanishingFace_subset s z)) z hz
    (characterVanishingFace_negative s z) (characterVanishingFace_clear s z hz)
end ZeroFace

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
  (k : Type u) [Field k] (a : Lattice n → ℤ)

lemma cartierDifference_mem_cone (ha : F.IsNef (fun u => (a u : ℝ)))
    (s t : F.fullCones) :
    F.cartierLatticePoint a s - F.cartierLatticePoint a t ∈ dualConeMonoid t.val := by
  intro u hu
  rw [integerPairing_sub, F.cartierLatticePoint_pairing a t u hu]
  have h := F.cartierPoint_mem_of_nef ha s u (F.ray_mem_of_mem_cone (F.fullCones_mem t) hu)
  rw [← F.embed_cartierLatticePoint a s, PaperVerification.ToricGeometry.SmoothCompleteFan.normalRay_pairing_lattice] at h
  change -(a u : ℝ) ≤
    (PaperVerification.ToricGeometry.integerPairing u (F.cartierLatticePoint a s) : ℝ) at h
  have hZ : -a u ≤ PaperVerification.ToricGeometry.integerPairing u
      (F.cartierLatticePoint a s) :=
    (Int.cast_le (R := ℝ)).mp (by simpa only [Int.cast_neg] using h)
  exact sub_nonneg.mpr hZ

lemma cartierDifference_zeroFace (ha : F.IsStrictSupport (fun u => (a u : ℝ)))
    (s t : F.fullCones) :
    characterVanishingFace t.val
      (F.cartierLatticePoint a s - F.cartierLatticePoint a t) = t.val ∩ s.val := by
  ext u
  simp only [characterVanishingFace, Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨hut, hz⟩
    refine ⟨hut, ?_⟩
    by_contra hus
    have h := F.cartierPoint_support_lt_of_not_mem ha s
      (F.ray_mem_of_mem_cone (F.fullCones_mem t) hut) hus
    rw [← F.embed_cartierLatticePoint a s, PaperVerification.ToricGeometry.SmoothCompleteFan.normalRay_pairing_lattice] at h
    have hz' : PaperVerification.ToricGeometry.integerPairing u (F.cartierLatticePoint a s) = -a u := by
      rw [integerPairing_sub, F.cartierLatticePoint_pairing a t u hut] at hz
      omega
    have hZ : -a u < PaperVerification.ToricGeometry.integerPairing u (F.cartierLatticePoint a s) := by
      apply (Int.cast_lt (R := ℝ)).mp
      change -((a u : ℤ) : ℝ) <
        (PaperVerification.ToricGeometry.integerPairing u (F.cartierLatticePoint a s) : ℝ) at h
      simpa only [Int.cast_neg] using h
    omega
  · rintro ⟨hut, hus⟩
    refine ⟨hut, ?_⟩
    rw [integerPairing_sub, F.cartierLatticePoint_pairing a s u hus,
      F.cartierLatticePoint_pairing a t u hut, sub_self]

lemma cartierDifference_basicOpen_range
    (ha : F.IsStrictSupport (fun u => (a u : ℝ))) (s t : F.fullCones) :
    (PrimeSpectrum.basicOpen (chartCharacter k (dualConeMonoid t.val)
      (F.cartierLatticePoint a s - F.cartierLatticePoint a t)
        (cartierDifference_mem_cone F a (PaperVerification.ToricGeometry.SmoothCompleteFan.IsStrictSupport.isNef F ha) s t))).carrier =
      Set.range (coneChartFaceMap k (Finset.inter_subset_left : t.val ∩ s.val ⊆ t.val)) := by
  let z := F.cartierLatticePoint a s - F.cartierLatticePoint a t
  let hz := cartierDifference_mem_cone F a (PaperVerification.ToricGeometry.SmoothCompleteFan.IsStrictSupport.isNef F ha) s t
  have htransport (q : Finset (Lattice n))
      (hq : q = characterVanishingFace t.val z) (hqt : q ⊆ t.val) :
      (Submonoid.powers (chartCharacter k (dualConeMonoid t.val) z hz)).IsLocalizationMap
        (monoidChartInclusion k (dualConeMonoid_antitone hqt)) := by
    subst q
    exact characterVanishingFace_localization k t.val z hz
  have hloc := htransport (t.val ∩ s.val)
    (cartierDifference_zeroFace F a ha s t).symm Finset.inter_subset_left
  letI : IsOpenImmersion (monoidChartSpecMap k
      (dualConeMonoid_antitone (Finset.inter_subset_left : t.val ∩ s.val ⊆ t.val))) := by
    change IsOpenImmersion (coneChartFaceMap k
      (Finset.inter_subset_left : t.val ∩ s.val ⊆ t.val))
    exact F.coneChartFaceMap_isOpenImmersion k t.val (t.val ∩ s.val)
      (F.fullCones_mem t) Finset.inter_subset_left
  exact (congrArg (fun U : (coneChart k t.val).Opens => U.carrier)
    (monoidChartSpecMap_opensRange_of_isLocalizationMap k _ z hz hloc)).symm

lemma localCoefficient_cartierCharacter (ha : F.IsNef (fun u => (a u : ℝ)))
    (s t : F.fullCones)
    (q : Γ((F.fanCartierCocycle k F.isPure a).sheaf, ⊤))
    (hq : (F.fanCartierCocycle k F.isPure a).toCartierData.sectionValue ⊤ q =
      (F.rationalCharacter k (F.cartierLatticePoint a s) : (F.fanScheme k).functionField)) :
    (F.fanCartierCocycle k F.isPure a).localCoefficient (ULift.up t) q =
      (IsOpenImmersion.ΓIsoTop (F.fanChartMap k (F.fullConeIndex t))).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid t.val)))).inv
          (chartCharacter k (dualConeMonoid t.val)
            (F.cartierLatticePoint a s - F.cartierLatticePoint a t)
              (cartierDifference_mem_cone F a ha s t))) := by
  letI := F.coneChart_isIntegral k (F.fullConeIndex t)
  letI : Nonempty (F.fullChartOpen k t) := by
    change Nonempty (F.fanChartMap k (F.fullConeIndex t)).opensRange
    exact opensRange_nonempty (F.fanChartMap k (F.fullConeIndex t))
  letI : Nonempty ((F.fanCartierCocycle k F.isPure a).openSet (ULift.up t)) := by
    change Nonempty (F.fullChartOpen k t)
    infer_instance
  have hcoeff :
      (F.fanScheme k).germToFunctionField (F.fullChartOpen k t)
        ((F.fanCartierCocycle k F.isPure a).localCoefficient (ULift.up t) q) =
      (F.fanCartierCocycle k F.isPure a).toCartierData.sectionValue ⊤ q /
        (F.rationalCharacter k (F.cartierLatticePoint a t) :
          (F.fanScheme k).functionField) :=
    (F.fanCartierCocycle k F.isPure a).localCoefficient_value (ULift.up t) q
  let χ : monoidChartAlgebra k (dualConeMonoid t.val) :=
    chartCharacter k (dualConeMonoid t.val)
      (F.cartierLatticePoint a s - F.cartierLatticePoint a t)
      (cartierDifference_mem_cone F a ha s t)
  let f : Γ(coneChart k (F.fullConeIndex t).val, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of
      (monoidChartAlgebra k (dualConeMonoid t.val)))).inv χ
  letI := opensRange_nonempty (F.fanChartMap k (F.fullConeIndex t))
  have himage :
      (F.fanScheme k).germToFunctionField (F.fullChartOpen k t)
        ((IsOpenImmersion.ΓIsoTop (F.fanChartMap k (F.fullConeIndex t))).hom f) =
      F.chartRationalMap k (F.fullConeIndex t) χ := by
    change (F.fanScheme k).germToFunctionField
        (F.fanChartMap k (F.fullConeIndex t)).opensRange
        ((IsOpenImmersion.ΓIsoTop (F.fanChartMap k (F.fullConeIndex t))).hom f) =
      openImmersionGlobalToFunctionField (F.fanChartMap k (F.fullConeIndex t)) f
    exact imageSection_value (F.fanChartMap k (F.fullConeIndex t)) f
  apply (F.fanScheme k).germToFunctionField_injective (F.fullChartOpen k t)
  rw [hcoeff, hq]
  change _ = (F.fanScheme k).germToFunctionField (F.fullChartOpen k t)
    ((IsOpenImmersion.ΓIsoTop (F.fanChartMap k (F.fullConeIndex t))).hom f)
  have hchar : F.chartRationalMap k (F.fullConeIndex t) χ =
      (F.rationalCharacter k (F.cartierLatticePoint a s - F.cartierLatticePoint a t) :
        (F.fanScheme k).functionField) :=
    F.chartRationalMap_character k (F.fullConeIndex t)
      (F.cartierLatticePoint a s - F.cartierLatticePoint a t)
      (cartierDifference_mem_cone F a ha s t)
  rw [himage, hchar, F.rationalCharacter_sub k]
  rfl

/-- The Cartier section for a full cone vanishes exactly off its actual
chart. This is the geometric step from strict support to ampleness. -/
theorem cartierCharacter_nonvanishingOpen
    (ha : F.IsStrictSupport (fun u => (a u : ℝ))) (s : F.fullCones)
    (q : Γ((F.fanCartierCocycle k F.isPure a).sheaf, ⊤))
    (hq : (F.fanCartierCocycle k F.isPure a).toCartierData.sectionValue ⊤ q =
      (F.rationalCharacter k (F.cartierLatticePoint a s) : (F.fanScheme k).functionField)) :
    (F.fanCartierCocycle k F.isPure a).nonvanishingOpen q = F.fullChartOpen k s := by
  let C := F.fanCartierCocycle k F.isPure a
  apply le_antisymm
  · intro x hx
    obtain ⟨t, ht⟩ := Opens.mem_iSup.mp hx
    letI := F.coneChart_isIntegral k (F.fullConeIndex t.down)
    change x ∈ (F.fanScheme k).basicOpen
      ((F.fanCartierCocycle k F.isPure a).localCoefficient (ULift.up t.down) q) at ht
    rw [localCoefficient_cartierCharacter F k a (PaperVerification.ToricGeometry.SmoothCompleteFan.IsStrictSupport.isNef F ha) s t.down q hq,
      imageSection_basicOpen] at ht
    obtain ⟨y, hy, hyx⟩ := ht
    have hys : y ∈ Set.range (coneChartFaceMap k
        (Finset.inter_subset_left : t.down.val ∩ s.val ⊆ t.down.val)) := by
      rw [← cartierDifference_basicOpen_range F k a ha s t.down]
      change y ∈ (Spec (CommRingCat.of
        (monoidChartAlgebra k (dualConeMonoid t.down.val)))).basicOpen _ at hy
      rw [basicOpen_eq_of_affine] at hy
      exact hy
    obtain ⟨z, hz⟩ := hys
    refine ⟨coneChartFaceMap k Finset.inter_subset_right z, ?_⟩
    let r : F.ConeIndex := ⟨t.down.val ∩ s.val,
      F.downward t.down.val (F.fullCones_mem t.down) _ Finset.inter_subset_left⟩
    have hs' := congrArg (fun f => f z)
      (F.fanChartMap_naturality k (s := r) (t := F.fullConeIndex s) Finset.inter_subset_right)
    have ht' := congrArg (fun f => f z)
      (F.fanChartMap_naturality k (s := r) (t := F.fullConeIndex t.down) Finset.inter_subset_left)
    simp only [Scheme.Hom.comp_apply] at hs' ht'
    change F.fanChartMap k (F.fullConeIndex t.down) y = x at hyx
    exact hs'.trans (ht'.symm.trans
      ((congrArg (fun y => F.fanChartMap k (F.fullConeIndex t.down) y) hz).trans hyx))
  · intro x hx
    apply (C.mem_nonvanishingOpen_iff_rational (ULift.up s) q x hx).mpr
    rw [hq]
    exact ⟨Units.ne_zero _, by simp only [C, PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartierCocycle,
      div_self (Units.ne_zero _)]; exact (regularAtSubring _ _).one_mem⟩

/-- Strict integral support gives the intrinsic affine-nonvanishing
criterion for an ample Cartier line bundle. -/
theorem fanCartier_isAmple_of_strictSupport
    (ha : F.IsStrictSupport (fun u => (a u : ℝ))) :
    (F.fanCartierCocycle k F.isPure a).IsAmple := by
  let C := F.fanCartierCocycle k F.isPure a
  have hcompact : CompactSpace (F.fanScheme k) := by
    letI : Finite (F.fanSchemeOpenCover k).I₀ :=
      inferInstanceAs (Finite F.ConeIndex)
    letI : ∀ s : (F.fanSchemeOpenCover k).I₀,
        CompactSpace ((F.fanSchemeOpenCover k).X s) := fun s => by
      change CompactSpace (Spec (CommRingCat.of
        (monoidChartAlgebra k (dualConeMonoid s.val))))
      infer_instance
    exact Scheme.OpenCover.compactSpace (F.fanSchemeOpenCover k)
  refine ⟨hcompact, ?_⟩
  intro x
  obtain ⟨s, hs⟩ := F.fullChartOpen_cover k F.isPure x
  obtain ⟨q, hq⟩ := fanCartier_global_generators F k a (PaperVerification.ToricGeometry.SmoothCompleteFan.IsStrictSupport.isNef F ha) (ULift.up s)
  refine ⟨1, zero_lt_one, C.sectionPow 1 q, ?_, ?_⟩
  · rw [C.nonvanishingOpen_sectionPow 1 zero_lt_one,
      cartierCharacter_nonvanishingOpen F k a ha s q hq]
    exact hs
  · rw [C.nonvanishingOpen_sectionPow 1 zero_lt_one,
      cartierCharacter_nonvanishingOpen F k a ha s q hq]
    letI : IsAffine (coneChart k (F.fullConeIndex s).val) := by
      change IsAffine (Spec (CommRingCat.of
        (monoidChartAlgebra k (dualConeMonoid (F.fullConeIndex s).val))))
      infer_instance
    exact isAffineOpen_opensRange (F.fanChartMap k (F.fullConeIndex s))

#print axioms cartierCharacter_nonvanishingOpen
#print axioms fanCartier_isAmple_of_strictSupport

end Unimodular.NefBig
