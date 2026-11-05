module

public import PaperVerification.ToricFanCartierFrames

@[expose] public section

/-! # Regular constants and the overlap equations of actual Cartier frames -/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

def rationalScalar : k →+* («Σ».fanScheme k).functionField :=
  («Σ».torusRationalMap k).comp (algebraMap k (AddMonoidAlgebra k (Lattice n)))

def rationalScalarUnit (c : kˣ) : («Σ».fanScheme k).functionFieldˣ :=
  Units.map («Σ».rationalScalar k) c

theorem rationalScalar_mem_regularAt (c : k) (x : «Σ».fanScheme k) :
    «Σ».rationalScalar k c ∈ regularAtSubring («Σ».fanScheme k) x := by
  obtain ⟨s,y,rfl⟩ := «Σ».fanChartMap_jointly_surjective k x
  have h := «Σ».chartRationalMap_mem_regularAt k s
    (algebraMap k (monoidChartAlgebra k (dualConeMonoid s.val)) c) y
  rw [«Σ».chartRationalMap_eq_torusRationalMap k s] at h
  exact h

theorem torusRationalMap_single (m : Lattice n) (c : k) :
    «Σ».torusRationalMap k (AddMonoidAlgebra.single m c) =
      «Σ».rationalScalar k c *
        («Σ».rationalCharacter k m : («Σ».fanScheme k).functionField) := by
  change «Σ».torusRationalMap k (AddMonoidAlgebra.single m c) =
    «Σ».torusRationalMap k (algebraMap k (AddMonoidAlgebra k (Lattice n)) c) *
      «Σ».torusRationalMap k (AddMonoidAlgebra.single m 1)
  rw [← map_mul]
  congr 1
  simp

theorem characterDifference_regular_of_frameFactors
    (D : CartierData («Σ».fanScheme k)) (s t : «Σ».ConeIndex)
    (es : D.sheaf.restrict («Σ».fanChartMap k s) ≅
      SheafOfModules.unit (coneChart k s.val).ringCatSheaf)
    (et : D.sheaf.restrict («Σ».fanChartMap k t) ≅
      SheafOfModules.unit (coneChart k t.val).ringCatSheaf)
    (cs ct : kˣ) (ms mt : Lattice n)
    (hs : letI := «Σ».coneChart_isIntegral k s
      D.chartFrameRationalGenerator («Σ».fanChartMap k s) es =
        («Σ».rationalScalarUnit k cs : («Σ».fanScheme k).functionField) *
          («Σ».rationalCharacter k ms : («Σ».fanScheme k).functionField))
    (ht : letI := «Σ».coneChart_isIntegral k t
      D.chartFrameRationalGenerator («Σ».fanChartMap k t) et =
        («Σ».rationalScalarUnit k ct : («Σ».fanScheme k).functionField) *
          («Σ».rationalCharacter k mt : («Σ».fanScheme k).functionField))
    (x : «Σ».fanScheme k)
    (hxs : x∈(«Σ».fanChartMap k s).opensRange)
    (hxt : x∈(«Σ».fanChartMap k t).opensRange) :
    («Σ».rationalCharacter k (ms-mt) : («Σ».fanScheme k).functionField) ∈
      regularAtSubring («Σ».fanScheme k) x := by
  letI := «Σ».coneChart_isIntegral k s
  letI := «Σ».coneChart_isIntegral k t
  have hratio := D.chartFrameRatio_regularAt («Σ».fanChartMap k s)
    («Σ».fanChartMap k t) es et x hxs hxt
  have hconst := «Σ».rationalScalar_mem_regularAt k ((ct / cs : kˣ) : k) x
  have h := (regularAtSubring («Σ».fanScheme k) x).mul_mem hratio hconst
  rw [hs,ht] at h
  have he :
      ((«Σ».rationalScalarUnit k cs : («Σ».fanScheme k).functionField) *
        («Σ».rationalCharacter k ms : («Σ».fanScheme k).functionField) /
        ((«Σ».rationalScalarUnit k ct : («Σ».fanScheme k).functionField) *
          («Σ».rationalCharacter k mt : («Σ».fanScheme k).functionField))) *
          «Σ».rationalScalar k ((ct/cs : kˣ) : k) =
      («Σ».rationalCharacter k (ms-mt) : («Σ».fanScheme k).functionField) := by
    have hcs : «Σ».rationalScalar k (cs:k) ≠ 0 :=
      Units.ne_zero («Σ».rationalScalarUnit k cs)
    have hct : «Σ».rationalScalar k (ct:k) ≠ 0 :=
      Units.ne_zero («Σ».rationalScalarUnit k ct)
    simp only [«Σ».rationalCharacter_sub k ms mt,Units.val_div_eq_div_val]
    change ((«Σ».rationalScalar k (cs:k) *
        («Σ».rationalCharacter k ms : («Σ».fanScheme k).functionField)) /
        («Σ».rationalScalar k (ct:k) *
          («Σ».rationalCharacter k mt : («Σ».fanScheme k).functionField))) *
        «Σ».rationalScalar k ((ct:k)/(cs:k)) =
      («Σ».rationalCharacter k ms : («Σ».fanScheme k).functionField) /
        («Σ».rationalCharacter k mt : («Σ».fanScheme k).functionField)
    rw [map_div₀]
    field_simp [hcs,hct,Units.ne_zero] <;> ring
  simpa only [he] using h

/-- On every common ray, actual chart frames normalized by scalar units
have equal integral character pairings. This is obtained from regularity
of both transition directions on the genuine overlap chart. -/
theorem frameCharacter_pairing_eq
    (D : CartierData («Σ».fanScheme k)) (s t : «Σ».ConeIndex)
    (es : D.sheaf.restrict («Σ».fanChartMap k s) ≅
      SheafOfModules.unit (coneChart k s.val).ringCatSheaf)
    (et : D.sheaf.restrict («Σ».fanChartMap k t) ≅
      SheafOfModules.unit (coneChart k t.val).ringCatSheaf)
    (cs ct : kˣ) (ms mt : Lattice n)
    (hs : letI := «Σ».coneChart_isIntegral k s
      D.chartFrameRationalGenerator («Σ».fanChartMap k s) es =
        («Σ».rationalScalarUnit k cs : («Σ».fanScheme k).functionField) *
          («Σ».rationalCharacter k ms : («Σ».fanScheme k).functionField))
    (ht : letI := «Σ».coneChart_isIntegral k t
      D.chartFrameRationalGenerator («Σ».fanChartMap k t) et =
        («Σ».rationalScalarUnit k ct : («Σ».fanScheme k).functionField) *
          («Σ».rationalCharacter k mt : («Σ».fanScheme k).functionField))
    (v : Lattice n) (hvs : v∈s.val) (hvt : v∈t.val) :
    integerPairing v ms=integerPairing v mt := by
  let q : «Σ».ConeIndex := ⟨s.val∩t.val,«Σ».downward s.val s.property _ Finset.inter_subset_left⟩
  have hregular (x : «Σ».fanScheme k) (hx : x∈(«Σ».fanChartMap k q).opensRange) :
      («Σ».rationalCharacter k (ms-mt) : («Σ».fanScheme k).functionField) ∈
        regularAtSubring («Σ».fanScheme k) x := by
    obtain ⟨z,rfl⟩ := hx
    apply «Σ».characterDifference_regular_of_frameFactors k D s t es et cs ct ms mt hs ht
    · refine ⟨coneChartFaceMap k Finset.inter_subset_left z,?_⟩
      exact congrArg (fun f=>f z) («Σ».fanChartMap_naturality k Finset.inter_subset_left)
    · refine ⟨coneChartFaceMap k Finset.inter_subset_right z,?_⟩
      exact congrArg (fun f=>f z) («Σ».fanChartMap_naturality k Finset.inter_subset_right)
  have h₁ : ms-mt ∈ dualConeMonoid q.val :=
    («Σ».rationalCharacter_mem_chartRange_iff k q (ms-mt)).mp
      ((«Σ».mem_chartRationalMap_range_iff k q _).mpr hregular)
  have hregular' (x : «Σ».fanScheme k) (hx : x∈(«Σ».fanChartMap k q).opensRange) :
      («Σ».rationalCharacter k (mt-ms) : («Σ».fanScheme k).functionField) ∈
        regularAtSubring («Σ».fanScheme k) x := by
    obtain ⟨z,rfl⟩ := hx
    apply «Σ».characterDifference_regular_of_frameFactors k D t s et es ct cs mt ms ht hs
    · refine ⟨coneChartFaceMap k Finset.inter_subset_right z,?_⟩
      exact congrArg (fun f=>f z) («Σ».fanChartMap_naturality k Finset.inter_subset_right)
    · refine ⟨coneChartFaceMap k Finset.inter_subset_left z,?_⟩
      exact congrArg (fun f=>f z) («Σ».fanChartMap_naturality k Finset.inter_subset_left)
  have h₂ : mt-ms ∈ dualConeMonoid q.val :=
    («Σ».rationalCharacter_mem_chartRange_iff k q (mt-ms)).mp
      ((«Σ».mem_chartRationalMap_range_iff k q _).mpr hregular')
  have hv : v∈q.val := Finset.mem_inter.mpr ⟨hvs,hvt⟩
  have ha := h₁ v hv
  have hb := h₂ v hv
  rw [integerPairing_sub] at ha hb
  omega

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.frameCharacter_pairing_eq
