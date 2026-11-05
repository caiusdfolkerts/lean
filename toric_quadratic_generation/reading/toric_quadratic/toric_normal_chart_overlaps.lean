module

public import PaperVerification.ToricChartOpenImmersions
public import PaperVerification.ToricNormalConeFaces
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# A weight difference cuts out the actual common normal-cone chart

For two lattice points supporting actual fan cones, their difference is
nonnegative on the first cone and zero precisely on its common rays with
the second. Inverting this literal character therefore gives exactly the
common-face chart. This identifies actual projective chart overlaps with
actual fan gluing overlaps.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory
open scoped BigOperators Classical

variable {n : ℕ}

def characterZeroFace (s : Finset (Lattice n)) (z : Lattice n) : Finset (Lattice n) :=
  s.filter (fun u=>integerPairing u z=0)

theorem characterZeroFace_subset (s : Finset (Lattice n)) (z : Lattice n) :
    characterZeroFace s z⊆s := Finset.filter_subset _ _

theorem negative_character_mem_zeroFace (s : Finset (Lattice n)) (z : Lattice n) :
    -z∈dualConeMonoid (characterZeroFace s z) := by
  intro u hu
  have hz := (Finset.mem_filter.mp hu).2
  simp only [integerPairing,Pi.neg_apply,mul_neg,Finset.sum_neg_distrib]
  change 0≤-integerPairing u z
  rw [hz,neg_zero]

theorem character_clears_zeroFace (s : Finset (Lattice n)) (z : Lattice n)
    (hz : z∈dualConeMonoid s) (m : Lattice n)
    (hm : m∈dualConeMonoid (characterZeroFace s z)) :
    ∃ N : ℕ,m+N • z∈dualConeMonoid s := by
  let N := s.sup (fun u=>(-integerPairing u m).toNat)
  refine ⟨N,?_⟩
  intro u hu
  have he : integerPairing u (m+N • z)=
      integerPairing u m+(N : ℤ)*integerPairing u z := by
    simp [integerPairing,Pi.add_apply,Pi.smul_apply,nsmul_eq_mul,
      mul_add,Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul,mul_assoc,mul_left_comm,mul_comm]
  rw [he]
  by_cases hzero : integerPairing u z=0
  · rw [hzero,mul_zero,add_zero]
    exact hm u (Finset.mem_filter.mpr ⟨hu,hzero⟩)
  · have hpos : 1≤ integerPairing u z := by have := hz u hu;omega
    have hle : (-integerPairing u m).toNat≤N :=
      Finset.le_sup (f := fun u => (-integerPairing u m).toNat) hu
    have hleZ : (((-integerPairing u m).toNat : ℕ) : ℤ)≤(N : ℤ) := by exact_mod_cast hle
    have hself := Int.self_le_toNat (-integerPairing u m)
    have hN : (0 : ℤ)≤N := Int.natCast_nonneg _
    nlinarith

theorem characterZeroFace_isLocalizationMap (k : Type*) [CommSemiring k]
    (s : Finset (Lattice n)) (z : Lattice n) (hz : z∈dualConeMonoid s) :
    (Submonoid.powers (chartCharacter k (dualConeMonoid s) z hz)).IsLocalizationMap
      (monoidChartInclusion k (dualConeMonoid_antitone (characterZeroFace_subset s z))) :=
  monoidChartInclusion_isLocalizationMap k
    (dualConeMonoid_antitone (characterZeroFace_subset s z)) z hz
    (negative_character_mem_zeroFace s z) (character_clears_zeroFace s z hz)

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n) (P : LatticePolytope n)

include «Σ» in
theorem vertex_difference_mem_dualCone (v w : Lattice n)
    (hw : embed n w∈P.carrier) (s : Finset (Lattice n))
    (hs : P.normalCone (embed n v)=(latticeRayCone s : Set (Ambient n))) :
    w-v∈dualConeMonoid s := by
  intro u hu
  have hucone : embed n u∈P.normalCone (embed n v) :=
    hs.symm ▸ latticeRayCone_generator s hu
  have h := hucone (embed n w) hw
  change 0≤∑ i,(u i : ℝ)*((w i : ℝ)-(v i : ℝ)) at h
  change 0≤∑ i,u i*(w i-v i)
  exact_mod_cast h

theorem normal_cone_common_rays_eq_characterZeroFace
    (v w : Lattice n) (hv : embed n v∈P.carrier) (hw : embed n w∈P.carrier)
    (s t : Finset (Lattice n)) (hs : s∈«Σ».cones) (ht : t∈«Σ».cones)
    (hvs : P.normalCone (embed n v)=(latticeRayCone s : Set (Ambient n)))
    (hwt : P.normalCone (embed n w)=(latticeRayCone t : Set (Ambient n))) :
    s∩t=characterZeroFace s (w-v) := by
  ext u
  simp only [Finset.mem_inter,characterZeroFace,Finset.mem_filter]
  constructor
  · rintro ⟨hus,hut⟩
    refine ⟨hus,?_⟩
    have hu : embed n u∈P.normalCone (embed n v)∩P.normalCone (embed n w) :=
      ⟨hvs.symm ▸ latticeRayCone_generator s hus,hwt.symm ▸ latticeRayCone_generator t hut⟩
    have hzero := ((P.mem_normalCone_inter_iff _ _ hv hw _).mp hu).2
    change (∑ i,(u i : ℝ)*((w i : ℝ)-(v i : ℝ)))=0 at hzero
    change (∑ i,u i*(w i-v i))=0
    exact_mod_cast hzero
  · rintro ⟨hus,hzero⟩
    refine ⟨hus,?_⟩
    have hur : u∈«Σ».rays := («Σ».mem_rays_iff u).mpr ⟨s,hs,hus⟩
    apply («Σ».ray_mem_cone_iff ht hur).mp
    change embed n u∈(latticeRayCone t : Set (Ambient n))
    rw [← hwt]
    apply ((P.mem_normalCone_inter_iff _ _ hv hw _).mpr
      ⟨hvs.symm ▸ latticeRayCone_generator s hus,?_⟩).2
    change (∑ i,(u i : ℝ)*((w i : ℝ)-(v i : ℝ)))=0
    change (∑ i,u i*(w i-v i))=0 at hzero
    exact_mod_cast hzero

/-- The common-face inclusion has exactly the principal open image
defined by the actual difference of the two vertex weights. -/
theorem normal_chart_intersection_range (k : Type*) [CommRing k]
    (v w : Lattice n) (hv : embed n v∈P.carrier) (hw : embed n w∈P.carrier)
    (s t : Finset (Lattice n)) (hs : s∈«Σ».cones) (ht : t∈«Σ».cones)
    (hvs : P.normalCone (embed n v)=(latticeRayCone s : Set (Ambient n)))
    (hwt : P.normalCone (embed n w)=(latticeRayCone t : Set (Ambient n))) :
    Set.range (coneChartFaceMap k (Finset.inter_subset_left : s∩t⊆s))=
      ((PrimeSpectrum.basicOpen (chartCharacter k (dualConeMonoid s) (w-v)
        («Σ».vertex_difference_mem_dualCone P v w hw s hvs))).carrier :
          Set (coneChart k s)) := by
  have hz := «Σ».vertex_difference_mem_dualCone P v w hw s hvs
  have heq := «Σ».normal_cone_common_rays_eq_characterZeroFace P v w hv hw s t hs ht hvs hwt
  have hloc_transport (q : Finset (Lattice n))
      (hq : q=characterZeroFace s (w-v)) (hqs : q⊆s) :
      (Submonoid.powers (chartCharacter k (dualConeMonoid s) (w-v) hz)).IsLocalizationMap
        (monoidChartInclusion k (dualConeMonoid_antitone hqs)) := by
    subst q
    exact characterZeroFace_isLocalizationMap k s (w-v) hz
  have hloc := hloc_transport (s∩t) heq Finset.inter_subset_left
  letI : IsOpenImmersion (monoidChartSpecMap k
      (dualConeMonoid_antitone (Finset.inter_subset_left : s∩t⊆s))) :=
    monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
      (dualConeMonoid_antitone (Finset.inter_subset_left : s∩t⊆s)) (w-v) hz hloc
  exact congrArg (fun U : TopologicalSpace.Opens
      (PrimeSpectrum (monoidChartAlgebra k (dualConeMonoid s))) => U.carrier)
    (monoidChartSpecMap_opensRange_of_isLocalizationMap k _ (w-v) hz hloc)

end SmoothCompleteFan

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.normal_chart_intersection_range
