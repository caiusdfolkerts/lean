module

public import PaperVerification.ToricSmoothChartAlgebra
public import PaperVerification.ToricFanPolytopeConstruction
public import PaperVerification.ToricAdjointSupport

@[expose] public section

/-!
# Exact intersection of the actual principal character modules

Each affine semigroup chart is a genuine subalgebra of the Laurent
algebra. Its Cartier module is its image under multiplication by the
actual Cartier character. Their intersection is proved to be exactly
the module supported on all integral points of the support polytope.
No global-section or scheme dictionary is assumed by this statement.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set AddMonoidAlgebra
open PaperVerification.ToricCharacters
open scoped BigOperators Classical

def integerPairing {n : ℕ} (u m : Lattice n) : ℤ := ∑ j, u j * m j

theorem integerPairing_add {n : ℕ} (u m p : Lattice n) :
    integerPairing u (m + p) = integerPairing u m + integerPairing u p := by
  simp only [integerPairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem integerPairing_sub {n : ℕ} (u m p : Lattice n) :
    integerPairing u (m - p) = integerPairing u m - integerPairing u p := by
  simp only [integerPairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

def dualConeMonoid {n : ℕ} (s : Finset (Lattice n)) : AddSubmonoid (Lattice n) where
  carrier := {m | ∀ u ∈ s, 0 ≤ integerPairing u m}
  zero_mem' := by intro u hu; simp [integerPairing]
  add_mem' := by
    intro m p hm hp u hu
    rw [integerPairing_add]
    exact add_nonneg (hm u hu) (hp u hu)

/-- Smoothness gives the actual free semigroup coordinates of the
dual cone, including its unrestricted Laurent directions. -/
theorem dualConeMonoid_basis_eq {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    dualConeMonoid (I.image b) = coordinateConeMonoid (integralDualBasis b) I := by
  ext m
  change (∀ u ∈ I.image b, 0 ≤ integerPairing u m) ↔
    ∀ i ∈ I, 0 ≤ (integralDualBasis b).repr m i
  constructor
  · intro h i hi
    have hh := h (b i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    simpa only [integerPairing, integralDualBasis_repr, mul_comm] using hh
  · intro h u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    simpa only [integerPairing, integralDualBasis_repr, mul_comm] using h i hi

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem cartierLatticePoint_pairing (a : Lattice n → ℤ) (s : «Σ».fullCones)
    (u : Lattice n) (hu : u ∈ (s : Finset (Lattice n))) :
    integerPairing u («Σ».cartierLatticePoint a s) = -a u := by
  have h := «Σ».cartierPoint_support_eq_of_mem (fun v => (a v : ℝ)) s hu
  rw [← «Σ».embed_cartierLatticePoint a s, normalRay_pairing_lattice] at h
  exact_mod_cast h

theorem cartier_translate_dualCone (a : Lattice n → ℤ) (s : «Σ».fullCones) :
    (fun m => «Σ».cartierLatticePoint a s + m) ''
      (dualConeMonoid (s : Finset (Lattice n)) : Set (Lattice n)) =
        {m | ∀ u ∈ (s : Finset (Lattice n)), -a u ≤ integerPairing u m} := by
  ext m
  constructor
  · rintro ⟨w, hw, rfl⟩ u hu
    rw [integerPairing_add, «Σ».cartierLatticePoint_pairing a s u hu]
    exact le_add_of_nonneg_right (hw u hu)
  · intro hm
    refine ⟨m - «Σ».cartierLatticePoint a s, ?_, by abel⟩
    intro u hu
    rw [integerPairing_sub, «Σ».cartierLatticePoint_pairing a s u hu]
    exact sub_nonneg.mpr (hm u hu)

def fanIntegralExponents (a : Lattice n → ℤ) : Set (Lattice n) :=
  {m | embed n m ∈ «Σ».fanPolytope (fun u => (a u : ℝ))}

theorem integral_exponents_eq_chart_intersection (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) :
    «Σ».fanIntegralExponents a =
      ⋂ s : «Σ».fullCones, (fun m => «Σ».cartierLatticePoint a s + m) ''
        (dualConeMonoid (s : Finset (Lattice n)) : Set (Lattice n)) := by
  ext m
  simp only [Set.mem_iInter, «Σ».cartier_translate_dualCone, Set.mem_setOf_eq]
  constructor
  · intro hm s u hu
    have h := hm u («Σ».ray_mem_of_mem_cone («Σ».fullCones_mem s) hu)
    rw [normalRay_pairing_lattice] at h
    change -(a u : ℝ) ≤ (integerPairing u m : ℝ) at h
    exact_mod_cast h
  · intro hm u hu
    obtain ⟨t, ht, hut⟩ := («Σ».mem_rays_iff u).mp hu
    obtain ⟨s, hs, hts, hscard⟩ := hpure t ht
    let s' : «Σ».fullCones := ⟨s, Finset.mem_filter.mpr ⟨hs, hscard⟩⟩
    have h := hm s' u (hts hut)
    rw [normalRay_pairing_lattice]
    change -(a u : ℝ) ≤ (integerPairing u m : ℝ)
    exact_mod_cast h

variable (k : Type*) [CommSemiring k]

/-- The local principal module, defined by actual multiplication in the
Laurent algebra of the actual semigroup chart ring. -/
def cartierChartCharacterModule (a : Lattice n → ℤ) (s : «Σ».fullCones) :
    Submodule k (AddMonoidAlgebra k (Lattice n)) :=
  ((monoidChartAlgebra k (dualConeMonoid (s : Finset (Lattice n)))).toSubmodule).map
    (characterTranslation k («Σ».cartierLatticePoint a s)).toLinearMap

/-- Exact global compatibility at the character-module level. This is
the algebraic computation needed after identifying a toric line bundle's
actual global sections with these local principal modules. -/
theorem iInf_cartierChartCharacterModule (hpure : «Σ».IsPure) (a : Lattice n → ℤ) :
    (⨅ s : «Σ».fullCones, «Σ».cartierChartCharacterModule k a s) =
      characterModule k («Σ».fanIntegralExponents a) := by
  rw [«Σ».integral_exponents_eq_chart_intersection hpure a]
  exact intersection_principal_character_modules k
    (fun s : «Σ».fullCones => dualConeMonoid (s : Finset (Lattice n)))
    («Σ».cartierLatticePoint a)

/-- Every genuine smooth cone has the proved polynomial/Laurent chart
algebra, with its actual ray set and a chosen integral basis extension. -/
theorem smooth_chart_algebra (s : Finset (Lattice n)) (hs : s ∈ «Σ».cones) :
    ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)),
      s = I.image b ∧ Nonempty
        (monoidChartAlgebra k (dualConeMonoid s) ≃ₐ[k]
          MvPolynomial I (AddMonoidAlgebra k (FreeCoordinate I → ℤ))) := by
  obtain ⟨b, I, hI⟩ := «Σ».smooth s hs
  refine ⟨b, I, hI, ?_⟩
  rw [hI, dualConeMonoid_basis_eq]
  exact ⟨smoothChartAlgebraEquiv k (integralDualBasis b) I⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.iInf_cartierChartCharacterModule
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.smooth_chart_algebra
