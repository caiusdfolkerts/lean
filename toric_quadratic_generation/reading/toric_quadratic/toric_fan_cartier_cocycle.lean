module

public import PaperVerification.ToricFanCharacters
public import PaperVerification.ToricCartierCocycle

@[expose] public section

/-!
# Actual Cartier sheaves from integral fan support coefficients

For every integral coefficient function the full smooth charts give
genuine rational character generators. Their ratios are units on the
actual scheme overlaps. These data construct an invertible fractional
sheaf using the proved rational Cartier cocycle construction.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

def fullConeIndex (s : «Σ».fullCones) : «Σ».ConeIndex := ⟨s.val, «Σ».fullCones_mem s⟩

def fullChartOpen (s : «Σ».fullCones) : («Σ».fanScheme k).Opens :=
  («Σ».fanChartMap k («Σ».fullConeIndex s)).opensRange

theorem fullChartOpen_cover (hpure : «Σ».IsPure) (x : «Σ».fanScheme k) :
    ∃ s : «Σ».fullCones, x ∈ «Σ».fullChartOpen k s := by
  obtain ⟨t, y, hy⟩ := «Σ».fanChartMap_jointly_surjective k x
  obtain ⟨s, hs, hts, hcard⟩ := hpure t.val t.property
  let s' : «Σ».fullCones := ⟨s, Finset.mem_filter.mpr ⟨hs, hcard⟩⟩
  have hts' : t.val ⊆ («Σ».fullConeIndex s').val := hts
  refine ⟨s', coneChartFaceMap k hts' y, ?_⟩
  exact (congrArg (fun f : coneChart k t.val ⟶ «Σ».fanScheme k => f y)
    («Σ».fanChartMap_naturality k hts')).trans hy

theorem chartRationalMap_mem_regularAt (s : «Σ».ConeIndex)
    (f : monoidChartAlgebra k (dualConeMonoid s.val)) (x : coneChart k s.val) :
    «Σ».chartRationalMap k s f ∈ regularAtSubring («Σ».fanScheme k) («Σ».fanChartMap k s x) := by
  letI := «Σ».coneChart_isIntegral k s
  exact openImmersionGlobalToFunctionField_mem_regularAt («Σ».fanChartMap k s)
    ((Scheme.ΓSpecIso (CommRingCat.of
      (monoidChartAlgebra k (dualConeMonoid s.val)))).inv f) x

/-- The actual rational transition function is regular at each point of
the actual overlap. Interchanging s and t proves its inverse regular. -/
theorem cartier_rational_transition_regular (a : Lattice n → ℤ)
    (s t : «Σ».fullCones) (x : «Σ».fanScheme k)
    (hxs : x ∈ «Σ».fullChartOpen k s) (hxt : x ∈ «Σ».fullChartOpen k t) :
    ((«Σ».rationalCharacter k («Σ».cartierLatticePoint a s) : («Σ».fanScheme k).functionField) /
      («Σ».rationalCharacter k («Σ».cartierLatticePoint a t) : («Σ».fanScheme k).functionField)) ∈
        regularAtSubring («Σ».fanScheme k) x := by
  obtain ⟨ys, hys⟩ := hxs
  obtain ⟨yt, hyt⟩ := hxt
  obtain ⟨z, hzs, hzt⟩ := («Σ».fanChartMap_eq_iff k
    («Σ».fullConeIndex s) («Σ».fullConeIndex t) ys yt).mp (hys.trans hyt.symm)
  let l : «Σ».ConeIndex :=
    ⟨s.val ∩ t.val, «Σ».downward s.val («Σ».fullCones_mem s) _ Finset.inter_subset_left⟩
  have hlx : «Σ».fanChartMap k l z = x := by
    rw [← «Σ».fanChartMap_naturality k
      (show l.val ⊆ («Σ».fullConeIndex s).val from Finset.inter_subset_left)]
    change «Σ».fanChartMap k («Σ».fullConeIndex s)
      (coneChartFaceMap k Finset.inter_subset_left z) = x
    rw [hzs, hys]
  let m := «Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t
  have hm : m ∈ dualConeMonoid l.val :=
    («Σ».cartier_difference_mem_overlap a s t).1
  have hregular := «Σ».chartRationalMap_mem_regularAt k l
    (chartCharacter k (dualConeMonoid l.val) m hm) z
  rw [«Σ».chartRationalMap_character k l m hm, hlx] at hregular
  simpa only [m, «Σ».rationalCharacter_sub k, Units.val_div_eq_div_val] using hregular

/-- The rational cocycle is built from ordinary integral ray coefficients;
local freeness and the actual sheaf condition are proved downstream. -/
def fanCartierCocycle (hpure : «Σ».IsPure) (a : Lattice n → ℤ) :
    RationalCartierCocycle («Σ».fanScheme k) where
  index := ULift.{u} «Σ».fullCones
  openSet i := «Σ».fullChartOpen k i.down
  covers x := by
    obtain ⟨s, hs⟩ := «Σ».fullChartOpen_cover k hpure x
    exact ⟨⟨s⟩, hs⟩
  generator i := «Σ».rationalCharacter k («Σ».cartierLatticePoint a i.down)
  transition i j x hxi hxj :=
    «Σ».cartier_rational_transition_regular k a i.down j.down x hxi hxj

/-- The genuine invertible fractional sheaf associated to the integral
Cartier data on the fan. -/
def fanCartierData (hpure : «Σ».IsPure) (a : Lattice n → ℤ) :
    CartierData («Σ».fanScheme k) :=
  («Σ».fanCartierCocycle k hpure a).toCartierData

end PaperVerification.ToricGeometry.SmoothCompleteFan
