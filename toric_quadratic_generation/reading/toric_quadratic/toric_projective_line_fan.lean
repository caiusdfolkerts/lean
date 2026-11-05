module

public import PaperVerification.ToricFanNoetherian
public import PaperVerification.ToricFanConstruction
public import Mathlib.Algebra.Polynomial.AlgebraMap

@[expose] public section

/-!
# The actual two-chart projective line

The complete rank-one fan has the primitive rays `1` and `-1`. Its scheme
is the actual gluing of the two affine polynomial charts along their common
Laurent chart. The algebra equivalences below identify the coordinate on
each affine chart with the corresponding primitive character.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory
open scoped Classical BigOperators

def projectiveLineRay (negative : Bool) : Lattice 1 :=
  fun _ => if negative then -1 else 1

def projectiveLineBasis (negative : Bool) : Module.Basis (Fin 1) ℤ (Lattice 1) :=
  if negative then (Pi.basisFun ℤ (Fin 1)).map (LinearEquiv.neg ℤ)
  else Pi.basisFun ℤ (Fin 1)

theorem projectiveLineBasis_apply (negative : Bool) (i : Fin 1) :
    projectiveLineBasis negative i = projectiveLineRay negative := by
  cases negative <;> ext j <;>
    simp [projectiveLineBasis,projectiveLineRay,Pi.basisFun_apply,
      Subsingleton.elim i j]

theorem projectiveLineBasis_rays (negative : Bool) :
    Finset.univ.image (projectiveLineBasis negative) = {projectiveLineRay negative} := by
  ext z
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_singleton]
  constructor
  · rintro ⟨i,rfl⟩
    exact projectiveLineBasis_apply negative i
  · rintro rfl
    exact ⟨0,projectiveLineBasis_apply negative 0⟩

theorem projectiveLineRay_ne : projectiveLineRay false ≠ projectiveLineRay true := by
  intro h
  have hh := congrFun h (0 : Fin 1)
  norm_num [projectiveLineRay] at hh

theorem mem_finiteRayCone_singleton_iff {E : Type*} [AddCommGroup E]
    [Module ℝ E] (v x : E) :
    x∈finiteRayCone {v} ↔ ∃ a : ℝ, 0≤a ∧ a • v=x := by
  constructor
  · rintro ⟨c,hc,hx⟩
    exact ⟨c v,hc v (Finset.mem_singleton_self v),by simpa only [Finset.sum_singleton] using hx⟩
  · rintro ⟨a,ha,hx⟩
    exact ⟨fun _ => a,fun _ _ => ha,by simpa only [Finset.sum_singleton] using hx⟩

theorem mem_projectiveLineCone (negative : Bool) (x : Ambient 1) :
    x∈latticeRayCone {projectiveLineRay negative} ↔
      0≤(if negative then -x 0 else x 0) := by
  rw [latticeRayCone,Finset.image_singleton,mem_finiteRayCone_singleton_iff]
  cases negative
  · constructor
    · rintro ⟨a,ha,hx⟩
      have h := congrFun hx (0 : Fin 1)
      have ha0 : a=x 0 := by simpa [embed,projectiveLineRay] using h
      simpa only [ha0, Bool.false_eq_true, ite_false] using ha
    · intro hx
      refine ⟨x 0,hx,?_⟩
      ext i
      have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
      simp [embed,projectiveLineRay,hi]
  · constructor
    · rintro ⟨a,ha,hx⟩
      have h := congrFun hx (0 : Fin 1)
      simp [embed,projectiveLineRay] at h
      change 0≤-x 0
      linarith
    · intro hx
      refine ⟨-x 0,hx,?_⟩
      ext i
      have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
      simp [embed,projectiveLineRay,hi]

theorem projectiveLineCone_inter :
    latticeRayCone {projectiveLineRay false} ⊓
      latticeRayCone {projectiveLineRay true} = ⊥ := by
  ext x
  simp only [Submodule.mem_inf,mem_projectiveLineCone,Bool.false_eq_true,
    if_false,if_true,Submodule.mem_bot]
  constructor
  · intro h
    ext i
    have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
    simp only [hi,Pi.zero_apply]
    linarith [h.1,h.2]
  · rintro rfl
    simp

theorem projectiveLineBasis_inter (a b : Bool) :
    latticeRayCone (Finset.univ.image (projectiveLineBasis a)) ⊓
      latticeRayCone (Finset.univ.image (projectiveLineBasis b)) =
        latticeRayCone ((Finset.univ.image (projectiveLineBasis a)) ∩
          (Finset.univ.image (projectiveLineBasis b))) := by
  rw [projectiveLineBasis_rays,projectiveLineBasis_rays]
  cases a <;> cases b
  · simp
  · have h : ({projectiveLineRay false} : Finset (Lattice 1)) ∩
        {projectiveLineRay true} = ∅ := by
      ext v
      simp only [Finset.mem_inter,Finset.mem_singleton,Finset.notMem_empty,iff_false]
      rintro ⟨rfl,hv⟩
      exact projectiveLineRay_ne hv
    rw [h,latticeRayCone_empty,projectiveLineCone_inter]
  · rw [inf_comm,Finset.inter_comm]
    have h : ({projectiveLineRay false} : Finset (Lattice 1)) ∩
        {projectiveLineRay true} = ∅ := by
      ext v
      simp only [Finset.mem_inter,Finset.mem_singleton,Finset.notMem_empty,iff_false]
      rintro ⟨rfl,hv⟩
      exact projectiveLineRay_ne hv
    rw [h,latticeRayCone_empty,projectiveLineCone_inter]
  · simp

theorem projectiveLineBasis_cover (x : Ambient 1) :
    ∃ negative : Bool,
      x∈latticeRayCone (Finset.univ.image (projectiveLineBasis negative)) := by
  by_cases hx : 0≤x 0
  · exact ⟨false,by simpa only [projectiveLineBasis_rays,mem_projectiveLineCone,
      Bool.false_eq_true,ite_false] using hx⟩
  · exact ⟨true,by simpa only [projectiveLineBasis_rays,mem_projectiveLineCone,
      ite_true] using
      neg_nonneg.mpr (le_of_not_ge hx)⟩

/-- The fan is proved smooth and complete by its actual real cones. -/
def projectiveLineFan : SmoothCompleteFan 1 :=
  fanOfBasisFamily projectiveLineBasis projectiveLineBasis_inter projectiveLineBasis_cover

theorem projectiveLineFan_isPure : projectiveLineFan.IsPure :=
  fanOfBasisFamily_isPure projectiveLineBasis projectiveLineBasis_inter projectiveLineBasis_cover

theorem projectiveLineRayCone_mem (negative : Bool) :
    {projectiveLineRay negative} ∈ projectiveLineFan.cones := by
  apply (mem_basisFamilyCones projectiveLineBasis _).mpr
  exact ⟨negative,by simpa only [projectiveLineBasis_rays] using
    (Finset.Subset.refl {projectiveLineRay negative})⟩

theorem mem_projectiveLineFan_cones (s : Finset (Lattice 1)) :
    s∈projectiveLineFan.cones ↔
      s=∅ ∨ s={projectiveLineRay false} ∨ s={projectiveLineRay true} := by
  rw [show projectiveLineFan.cones=basisFamilyCones projectiveLineBasis from rfl,
    mem_basisFamilyCones]
  simp only [projectiveLineBasis_rays,Finset.subset_singleton_iff]
  constructor
  · rintro ⟨b,h⟩
    rcases h with h|h
    · exact Or.inl h
    · cases b
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · rintro (h|h|h)
    · exact ⟨false,Or.inl h⟩
    · exact ⟨false,Or.inr h⟩
    · exact ⟨true,Or.inr h⟩

theorem mem_projectiveLineDualCone (negative : Bool) (m : Lattice 1) :
    m∈dualConeMonoid {projectiveLineRay negative} ↔
      0≤(if negative then -m 0 else m 0) := by
  change (∀ u∈({projectiveLineRay negative} : Finset (Lattice 1)),
    0≤ integerPairing u m) ↔ _
  cases negative <;> simp [integerPairing,projectiveLineRay]

/-- Exact natural-number coordinates on the actual dual semigroup. -/
def projectiveLineSemigroupEquiv (negative : Bool) :
    dualConeMonoid {projectiveLineRay negative} ≃+ ℕ where
  toFun m := (if negative then -m.val 0 else m.val 0).toNat
  invFun a := ⟨fun _ => if negative then -(a : ℤ) else a,by
    rw [mem_projectiveLineDualCone]
    cases negative <;> simp⟩
  left_inv m := by
    apply Subtype.ext
    have hm := (mem_projectiveLineDualCone negative m.val).mp m.property
    ext i
    have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
    cases negative <;> simp only [hi,if_false,if_true] at hm ⊢
    · exact Int.toNat_of_nonneg hm
    · rw [Int.toNat_of_nonneg hm,neg_neg]
  right_inv a := by cases negative <;> simp
  map_add' m p := by
    have hm := (mem_projectiveLineDualCone negative m.val).mp m.property
    have hp := (mem_projectiveLineDualCone negative p.val).mp p.property
    cases negative
    · exact Int.toNat_add hm hp
    · change (-(m.val 0 + p.val 0)).toNat = (-m.val 0).toNat + (-p.val 0).toNat
      rw [neg_add]
      exact Int.toNat_add (by simpa using hm) (by simpa using hp)

variable (k : Type*) [Field k]

/-- Each affine chart is the actual affine line. -/
def projectiveLineChartRingEquiv (negative : Bool) :
    monoidChartAlgebra k (dualConeMonoid {projectiveLineRay negative}) ≃ₐ[k]
      Polynomial k :=
  (monoidChartAlgebraEquiv k _).symm.trans
    ((AddMonoidAlgebra.domCongr k k (projectiveLineSemigroupEquiv negative)).trans
      (Polynomial.toFinsuppIsoAlg k).symm)

/-- The usual two affine lines with inverted transition coordinate, as an
actual scheme obtained by the already verified common-face gluing. -/
abbrev projectiveLineScheme : Scheme := projectiveLineFan.fanScheme k

def projectiveLineChart (negative : Bool) :
    coneChart k {projectiveLineRay negative} ⟶ projectiveLineScheme k :=
  projectiveLineFan.fanChartMap k
    ⟨{projectiveLineRay negative},projectiveLineRayCone_mem negative⟩

instance projectiveLineChart_isOpenImmersion (negative : Bool) :
    IsOpenImmersion (projectiveLineChart k negative) :=
  projectiveLineFan.fanChartMap_isOpenImmersion k
    ⟨{projectiveLineRay negative},projectiveLineRayCone_mem negative⟩

instance projectiveLineScheme_isIntegral : IsIntegral (projectiveLineScheme k) :=
  inferInstanceAs (IsIntegral (projectiveLineFan.fanScheme k))

instance projectiveLineScheme_isNoetherian : IsNoetherian (projectiveLineScheme k) :=
  inferInstanceAs (IsNoetherian (projectiveLineFan.fanScheme k))

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLineBasis_inter
#print axioms PaperVerification.ToricGeometry.projectiveLineChartRingEquiv
