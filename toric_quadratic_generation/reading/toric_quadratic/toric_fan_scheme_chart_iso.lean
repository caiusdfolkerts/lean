module

public import PaperVerification.ToricFanSchemeIntegral
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

@[expose] public section

/-!
# An actual scheme isomorphism from compatible affine fan charts

The hypotheses below concern literal open immersions of the already
constructed cone schemes. Agreement is tested on the actual dense torus,
and overlap ranges are required to equal the actual common-face chart.
The resulting map is constructed by the genuine fan colimit. Its point
injectivity, open-immersion property, and surjectivity are proved, giving
an actual scheme isomorphism.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PaperVerification.ToricCharacters
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

theorem coneChart_zeroFace_isDominant (s : «Σ».ConeIndex) :
    IsDominant (coneChartFaceMap k (Finset.empty_subset s.val)) := by
  refine ⟨?_⟩
  intro x
  have hg : «Σ».fanChartGenericPoint k s∈
      Set.range (coneChartFaceMap k (Finset.empty_subset s.val)) := by
    exact ⟨«Σ».fanChartGenericPoint k «Σ».zeroConeIndex,
      «Σ».fanChartGenericPoint_faceMap k
        (s := «Σ».zeroConeIndex) (t := s) (Finset.empty_subset s.val)⟩
  have hsub : ({«Σ».fanChartGenericPoint k s} : Set (coneChart k s.val))⊆
      Set.range (coneChartFaceMap k (Finset.empty_subset s.val)) :=
    Set.singleton_subset_iff.mpr hg
  have hcl := closure_mono hsub
  rw [(«Σ».fanChartGenericPoint_isGenericPoint k s).def] at hcl
  exact hcl (Set.mem_univ x)

section ChartFamily

variable {J : Type*} (s : J → Finset (Lattice n)) (hs : ∀ j,s j∈«Σ».cones)
    (hcover : ∀ t∈«Σ».cones,∃ j,t⊆s j)
    {Y : Scheme.{u}} [Y.IsSeparated]
    (f : ∀ j,coneChart k (s j)⟶Y)
    [∀ j,IsOpenImmersion (f j)]
    (hT : ∀ i j,
      coneChartFaceMap k (Finset.empty_subset (s i))≫f i=
        coneChartFaceMap k (Finset.empty_subset (s j))≫f j)

include hs hT in
theorem chartFamily_commonFace_agree (i j : J) :
    coneChartFaceMap k (Finset.inter_subset_left : s i∩s j⊆s i)≫f i=
      coneChartFaceMap k (Finset.inter_subset_right : s i∩s j⊆s j)≫f j := by
  let t : «Σ».ConeIndex := ⟨s i∩s j,«Σ».downward (s i) (hs i) _ Finset.inter_subset_left⟩
  letI := «Σ».coneChart_isIntegral k t
  letI := «Σ».coneChart_zeroFace_isDominant k t
  apply ext_of_isDominant (coneChartFaceMap k (Finset.empty_subset t.val))
  simpa only [← Category.assoc,coneChartFaceMap_comp] using hT i j

def chartFamilyChoice (t : «Σ».ConeIndex) : J :=
  Classical.choose (hcover t.val t.property)

theorem chartFamilyChoice_subset (t : «Σ».ConeIndex) :
    t.val⊆s («Σ».chartFamilyChoice s hcover t) :=
  Classical.choose_spec (hcover t.val t.property)

def chartFamilyMap (t : «Σ».ConeIndex) : coneChart k t.val⟶Y :=
  coneChartFaceMap k («Σ».chartFamilyChoice_subset s hcover t)≫
    f («Σ».chartFamilyChoice s hcover t)

include hs hT in
theorem chartFamilyMap_torus (t : «Σ».ConeIndex) (j : J) :
    coneChartFaceMap k (Finset.empty_subset t.val)≫
      «Σ».chartFamilyMap k s hcover f t=
        coneChartFaceMap k (Finset.empty_subset (s j))≫f j := by
  simpa only [chartFamilyMap,← Category.assoc,coneChartFaceMap_comp] using
    hT («Σ».chartFamilyChoice s hcover t) j

include hs hT in
theorem chartFamilyMap_naturality {t q : «Σ».ConeIndex} (htq : t.val⊆q.val) :
    coneChartFaceMap k htq≫«Σ».chartFamilyMap k s hcover f q=
      «Σ».chartFamilyMap k s hcover f t := by
  letI := «Σ».coneChart_isIntegral k t
  letI := «Σ».coneChart_zeroFace_isDominant k t
  apply ext_of_isDominant (coneChartFaceMap k (Finset.empty_subset t.val))
  rw [← Category.assoc,coneChartFaceMap_comp,
    «Σ».chartFamilyMap_torus k s hs hcover f hT q («Σ».chartFamilyChoice s hcover t)]
  unfold chartFamilyMap
  rw [← Category.assoc,coneChartFaceMap_comp]

def chartFamilyCocone : Cocone («Σ».coneDiagram k) where
  pt := Y
  «ι» := {
    app := «Σ».chartFamilyMap k s hcover f
    naturality := by
      intro t q h
      change coneChartFaceMap k (leOfHom h)≫«Σ».chartFamilyMap k s hcover f q=
        «Σ».chartFamilyMap k s hcover f t≫𝟙 Y
      exact («Σ».chartFamilyMap_naturality k s hs hcover f hT (leOfHom h)).trans
        (Category.comp_id _).symm }

def chartFamilyDesc : «Σ».fanScheme k⟶Y :=
  colimit.desc («Σ».coneDiagram k) («Σ».chartFamilyCocone k s hs hcover f hT)

@[reassoc] theorem fanChartMap_chartFamilyDesc (t : «Σ».ConeIndex) :
    «Σ».fanChartMap k t≫«Σ».chartFamilyDesc k s hs hcover f hT=
      «Σ».chartFamilyMap k s hcover f t :=
  colimit.ι_desc («Σ».chartFamilyCocone k s hs hcover f hT) t

@[reassoc] theorem familyChart_chartFamilyDesc (j : J) :
    «Σ».fanChartMap k ⟨s j,hs j⟩≫«Σ».chartFamilyDesc k s hs hcover f hT=f j := by
  rw [«Σ».fanChartMap_chartFamilyDesc]
  let t : «Σ».ConeIndex := ⟨s j,hs j⟩
  letI := «Σ».coneChart_isIntegral k t
  letI := «Σ».coneChart_zeroFace_isDominant k t
  apply ext_of_isDominant (coneChartFaceMap k (Finset.empty_subset t.val))
  exact «Σ».chartFamilyMap_torus k s hs hcover f hT t j

include hcover in
theorem familyCharts_cover_fanScheme (x : «Σ».fanScheme k) :
    ∃ j y,«Σ».fanChartMap k ⟨s j,hs j⟩ y=x := by
  obtain ⟨t,y,rfl⟩ := «Σ».fanChartMap_jointly_surjective k x
  let j := «Σ».chartFamilyChoice s hcover t
  let ht := «Σ».chartFamilyChoice_subset s hcover t
  refine ⟨j,coneChartFaceMap k ht y,?_⟩
  exact congrArg (fun g : coneChart k t.val⟶«Σ».fanScheme k => g y)
    («Σ».fanChartMap_naturality k (s := t) (t := ⟨s j,hs j⟩) ht)

theorem chartFamilyDesc_injective
    (hoverlap : ∀ i j,
      Set.range (coneChartFaceMap k (Finset.inter_subset_left : s i∩s j⊆s i))=
        (f i) ⁻¹' Set.range (f j)) :
    Function.Injective («Σ».chartFamilyDesc k s hs hcover f hT) := by
  intro x y hxy
  obtain ⟨i,xi,rfl⟩ := «Σ».familyCharts_cover_fanScheme k s hs hcover x
  obtain ⟨j,yj,rfl⟩ := «Σ».familyCharts_cover_fanScheme k s hs hcover y
  have h : f i xi=f j yj := by
    simpa only [← Scheme.Hom.comp_apply,«Σ».familyChart_chartFamilyDesc] using hxy
  have hxi : xi∈Set.range
      (coneChartFaceMap k (Finset.inter_subset_left : s i∩s j⊆s i)) := by
    rw [hoverlap]
    exact ⟨yj,h.symm⟩
  obtain ⟨z,hzi⟩ := hxi
  have hzj : coneChartFaceMap k (Finset.inter_subset_right : s i∩s j⊆s j) z=yj := by
    apply (f j).isOpenEmbedding.injective
    calc
      f j (coneChartFaceMap k (Finset.inter_subset_right : s i∩s j⊆s j) z)=
          f i (coneChartFaceMap k (Finset.inter_subset_left : s i∩s j⊆s i) z) :=
        congrArg (fun g=>g z) («Σ».chartFamily_commonFace_agree k s hs f hT i j).symm
      _ = f j yj := by rw [hzi,h]
  exact («Σ».fanChartMap_eq_iff k ⟨s i,hs i⟩ ⟨s j,hs j⟩ xi yj).mpr ⟨z,hzi,hzj⟩

theorem chartFamilyDesc_isOpenImmersion
    (hoverlap : ∀ i j,
      Set.range (coneChartFaceMap k (Finset.inter_subset_left : s i∩s j⊆s i))=
        (f i) ⁻¹' Set.range (f j)) :
    IsOpenImmersion («Σ».chartFamilyDesc k s hs hcover f hT) := by
  apply IsOpenImmersion.of_openCover_source _ («Σ».fanSchemeOpenCover k)
    («Σ».chartFamilyDesc_injective k s hs hcover f hT hoverlap)
  intro t
  change IsOpenImmersion («Σ».fanChartMap k t≫_)
  rw [«Σ».fanChartMap_chartFamilyDesc]
  unfold chartFamilyMap
  letI := «Σ».coneChartFaceMap_isOpenImmersion k _ _
    (hs («Σ».chartFamilyChoice s hcover t)) («Σ».chartFamilyChoice_subset s hcover t)
  infer_instance

theorem chartFamilyDesc_surjective (hY : ∀ y : Y,∃ j x,f j x=y) :
    Function.Surjective («Σ».chartFamilyDesc k s hs hcover f hT) := by
  intro y
  obtain ⟨j,x,rfl⟩ := hY y
  refine ⟨«Σ».fanChartMap k ⟨s j,hs j⟩ x,?_⟩
  rw [← Scheme.Hom.comp_apply,«Σ».familyChart_chartFamilyDesc]

/-- The actual fan colimit is isomorphic to the separated target once
its literal chart maps have the proved common-face overlaps and cover. -/
def chartFamilyIso
    (hoverlap : ∀ i j,
      Set.range (coneChartFaceMap k (Finset.inter_subset_left : s i∩s j⊆s i))=
        (f i) ⁻¹' Set.range (f j))
    (hY : ∀ y : Y,∃ j x,f j x=y) : «Σ».fanScheme k≅Y := by
  let F := «Σ».chartFamilyDesc k s hs hcover f hT
  letI : IsOpenImmersion F := «Σ».chartFamilyDesc_isOpenImmersion k s hs hcover f hT hoverlap
  letI : Surjective F := ⟨«Σ».chartFamilyDesc_surjective k s hs hcover f hT hY⟩
  letI : IsIso F := (isIso_iff_isOpenImmersion_and_surjective F).mpr ⟨inferInstance,inferInstance⟩
  exact asIso F

end ChartFamily

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.chartFamilyIso
