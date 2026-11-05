module

public import PaperVerification.ToricFanScheme
public import PaperVerification.ToricChartFactorization
public import Mathlib.AlgebraicGeometry.Properties

@[expose] public section

/-!
# Integrality and the dense torus of the glued fan scheme

The actual affine chart rings are domains. Their zero prime ideals agree
under all face restrictions, and yield a generic point of the glued
scheme. Reducedness is local on the proved affine open cover. Together
these prove integrality and density of the actual zero-cone chart.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

theorem coneChart_isIntegral (s : «Σ».ConeIndex) : IsIntegral (coneChart k s.val) := by
  letI := «Σ».chartRing_isDomain k s.val s.property
  exact inferInstanceAs
    (IsIntegral (Spec (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s.val)))))

def fanChartGenericPoint (s : «Σ».ConeIndex) : coneChart k s.val := by
  letI := «Σ».chartRing_isDomain k s.val s.property
  exact ⟨⊥, inferInstance⟩

theorem fanChartGenericPoint_isGenericPoint (s : «Σ».ConeIndex) :
    IsGenericPoint («Σ».fanChartGenericPoint k s) Set.univ := by
  letI := «Σ».chartRing_isDomain k s.val s.property
  change closure ({(⟨⊥, inferInstance⟩ :
    PrimeSpectrum (monoidChartAlgebra k (dualConeMonoid s.val)))} :
    Set (PrimeSpectrum (monoidChartAlgebra k (dualConeMonoid s.val)))) = Set.univ
  rw [PrimeSpectrum.closure_singleton]
  exact PrimeSpectrum.zeroLocus_bot

@[simp] theorem fanChartGenericPoint_faceMap {s t : «Σ».ConeIndex}
    (hst : s.val ⊆ t.val) :
    coneChartFaceMap k hst («Σ».fanChartGenericPoint k s) = «Σ».fanChartGenericPoint k t := by
  apply PrimeSpectrum.ext
  change Ideal.comap (monoidChartInclusion k (dualConeMonoid_antitone hst)).toRingHom ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _
    (monoidChartInclusion_injective k (dualConeMonoid_antitone hst))

def fanGenericPoint : «Σ».fanScheme k :=
  «Σ».torusOpenMap k («Σ».fanChartGenericPoint k «Σ».zeroConeIndex)

@[simp] theorem fanChartMap_genericPoint (s : «Σ».ConeIndex) :
    «Σ».fanChartMap k s («Σ».fanChartGenericPoint k s) = «Σ».fanGenericPoint k := by
  have hface := «Σ».fanChartGenericPoint_faceMap k
    (s := «Σ».zeroConeIndex) (t := s) (Finset.empty_subset s.val)
  have h := congrArg
    (fun f : coneChart k (∅ : Finset (Lattice n)) ⟶ «Σ».fanScheme k =>
      f («Σ».fanChartGenericPoint k «Σ».zeroConeIndex))
    («Σ».torusOpenMap_chart k s)
  exact (congrArg (fun z : coneChart k s.val => «Σ».fanChartMap k s z) hface).symm.trans h

theorem fanGenericPoint_isGenericPoint : IsGenericPoint («Σ».fanGenericPoint k) Set.univ := by
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro x hx
  obtain ⟨s, y, rfl⟩ := «Σ».fanChartMap_jointly_surjective k x
  have hclosed : IsClosed ((«Σ».fanChartMap k s) ⁻¹' closure {«Σ».fanGenericPoint k}) :=
    isClosed_closure.preimage («Σ».fanChartMap k s).continuous
  have hmem : «Σ».fanChartGenericPoint k s ∈
      («Σ».fanChartMap k s) ⁻¹' closure {«Σ».fanGenericPoint k} := by
    change «Σ».fanChartMap k s («Σ».fanChartGenericPoint k s) ∈ closure {«Σ».fanGenericPoint k}
    rw [«Σ».fanChartMap_genericPoint]
    exact subset_closure (Set.mem_singleton _)
  exact ((«Σ».fanChartGenericPoint_isGenericPoint k s).mem_closed_set_iff hclosed).mp hmem
    (Set.mem_univ y)

instance fanScheme_irreducibleSpace : IrreducibleSpace («Σ».fanScheme k) :=
  (irreducibleSpace_def _).mpr («Σ».fanGenericPoint_isGenericPoint k).isIrreducible

instance fanScheme_isReduced : IsReduced («Σ».fanScheme k) := by
  letI (i : («Σ».fanSchemeOpenCover k).I₀) :
      IsReduced ((«Σ».fanSchemeOpenCover k).X i) := by
    let s : «Σ».ConeIndex := i
    change IsReduced (coneChart k s.val)
    letI := «Σ».coneChart_isIntegral k s
    infer_instance
  exact IsReduced.of_openCover («Σ».fanScheme k) («Σ».fanSchemeOpenCover k)

instance fanScheme_isIntegral : IsIntegral («Σ».fanScheme k) :=
  isIntegral_of_irreducibleSpace_of_isReduced («Σ».fanScheme k)

/-- The actual open zero-cone chart is dense in the actual glued scheme. -/
theorem torusOpenMap_denseRange : DenseRange («Σ».torusOpenMap k) := by
  intro x
  have hsub : ({«Σ».fanGenericPoint k} : Set («Σ».fanScheme k)) ⊆
      Set.range («Σ».torusOpenMap k) := by
    rintro y rfl
    exact ⟨«Σ».fanChartGenericPoint k «Σ».zeroConeIndex, rfl⟩
  have hcl := closure_mono hsub
  rw [(«Σ».fanGenericPoint_isGenericPoint k).def] at hcl
  exact hcl (Set.mem_univ x)

end PaperVerification.ToricGeometry.SmoothCompleteFan
