module

public import ToricPower.RelativeAugmentationSingles
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.Algebra.Homology.Opposite

/-!
# Exact augmented Hom rows of a projective resolution

The positive coefficient cohomology of a projective resolution is the
only additional condition needed for its entire augmented Hom row to be
exact. Degree zero follows from the actual cokernel universal property
of the projective augmentation. Extension from natural chain degrees to
integer cochain degrees is tracked through the canonical indexing isos.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CochainComplex HomologicalComplex

namespace ToricPower

universe u v r
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The same projective resolution, in actual nonpositive cochain degrees. -/
def projectiveCochain {Z : C} (P : ProjectiveResolution Z) : CochainComplex C ℤ :=
  P.complex.extend ComplexShape.embeddingDownNat

instance {Z : C} (P : ProjectiveResolution Z) : (projectiveCochain P).IsStrictlyLE 0 := by
  unfold projectiveCochain
  infer_instance

/-- Its literal augmentation to degree zero. -/
def projectiveCochainAugmentation {Z : C} (P : ProjectiveResolution Z) :
    projectiveCochain P ⟶ (CochainComplex.singleFunctor C 0).obj Z :=
  extendMap P.π ComplexShape.embeddingDownNat ≫
    (extendSingleIso ComplexShape.embeddingDownNat Z 0 0 rfl).hom

/-- The degree-zero component is exactly the original projective
augmentation, after the canonical indexing isomorphisms. -/
theorem projectiveCochainAugmentation_zero {Z : C} (P : ProjectiveResolution Z) :
    (projectiveCochainAugmentation P).f 0 ≫ (singleObjXSelf (.up ℤ) 0 Z).hom =
      (P.complex.extendXIso ComplexShape.embeddingDownNat (show
        ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) by rfl)).hom ≫ P.π.f 0 ≫
        (singleObjXSelf (.down ℕ) 0 Z).hom := by
  simp only [projectiveCochainAugmentation, HomologicalComplex.comp_f,
    extendMap_f _ _ (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) by rfl),
    extendSingleIso_hom_f, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]

instance {Z : C} (P : ProjectiveResolution Z) :
    Epi ((projectiveCochainAugmentation P).f 0) := by
  have : Epi ((projectiveCochainAugmentation P).f 0 ≫
      (singleObjXSelf (.up ℤ) 0 Z).hom) := by
    rw [projectiveCochainAugmentation_zero]
    infer_instance
  exact (epi_comp_iff_of_isIso ((projectiveCochainAugmentation P).f 0)
    (singleObjXSelf (.up ℤ) 0 Z).hom).mp this

/-- Transport exact coefficient factorizations through a genuine
extension of complex shapes. -/
theorem extend_rightHom_factor
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (K : HomologicalComplex C c) (e : c.Embedding c')
    {i j k : ι} {i' j' k' : ι'} (hi : e.f i = i') (hj : e.f j = j')
    (hk : e.f k = k') (Y : C)
    (hf : ∀ u : K.X j ⟶ Y, K.d i j ≫ u = 0 →
      ∃ v : K.X k ⟶ Y, K.d j k ≫ v = u)
    (u : (K.extend e).X j' ⟶ Y) (hu : (K.extend e).d i' j' ≫ u = 0) :
    ∃ v : (K.extend e).X k' ⟶ Y, (K.extend e).d j' k' ≫ v = u := by
  have closed : K.d i j ≫ (K.extendXIso e hj).inv ≫ u = 0 := by
    rw [K.extend_d_eq e hi hj] at hu
    have h := congrArg (fun z => (K.extendXIso e hi).inv ≫ z) hu
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, comp_zero] using h
  obtain ⟨v, hv⟩ := hf _ closed
  refine ⟨(K.extendXIso e hk).hom ≫ v, ?_⟩
  rw [K.extend_d_eq e hj hk]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, hv,
    Iso.hom_inv_id_assoc]

/-- The ordinary scalar-linear coefficient complex of a resolution. -/
def projectiveCoefficientComplex (R : Type r) [CommRing R] [Linear R C]
    {Z : C} (P : ProjectiveResolution Z) (Y : C) : CochainComplex (ModuleCat.{v} R) ℕ :=
  (((linearYoneda R C).obj Y).mapHomologicalComplex (.up ℕ)).obj P.complex.op

/-- Positive exactness plus the proved cokernel universal property
gives every augmented coefficient row, including the degree-zero edge. -/
theorem projectiveCochain_augmentationHomExact
    (R : Type r) [CommRing R] [Linear R C]
    {Z : C} (P : ProjectiveResolution Z) (Y : C)
    (h : ∀ n : ℕ, (projectiveCoefficientComplex R P Y).ExactAt (n+1)) :
    AugmentationHomExact (projectiveCochain P) Z Y (projectiveCochainAugmentation P) := by
  constructor
  · intro q hq u hu
    obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hq
    apply extend_rightHom_factor P.complex ComplexShape.embeddingDownNat
      (i := n+2) (j := n+1) (k := n)
      (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) Y ?_ u hu
    intro v hv
    have hn := h n
    rw [HomologicalComplex.exactAt_iff' _ n (n+1) (n+2) (by simp) (by simp)] at hn
    exact (ShortComplex.moduleCat_exact_iff _).mp hn v hv
  · intro u hu
    let e₀ := P.complex.extendXIso ComplexShape.embeddingDownNat
      (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) by rfl)
    let e₁ := P.complex.extendXIso ComplexShape.embeddingDownNat
      (show ComplexShape.embeddingDownNat.f 1 = (-1 : ℤ) by rfl)
    have closed : P.complex.d 1 0 ≫ e₀.inv ≫ u = 0 := by
      change (P.complex.extend ComplexShape.embeddingDownNat).d (-1) 0 ≫ u = 0 at hu
      rw [P.complex.extend_d_eq ComplexShape.embeddingDownNat
        (show ComplexShape.embeddingDownNat.f 1 = (-1 : ℤ) by rfl)
        (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) by rfl)] at hu
      have hv := congrArg (fun z => e₁.inv ≫ z) hu
      simpa only [e₀, e₁, Category.assoc, Iso.inv_hom_id_assoc, comp_zero] using hv
    obtain ⟨g, hg⟩ := CokernelCofork.IsColimit.desc' P.isColimitCokernelCofork
      (e₀.inv ≫ u) closed
    change ((ChainComplex.single₀ C).obj Z).X 0 ⟶ Y at g
    change P.π.f 0 ≫ g = e₀.inv ≫ u at hg
    refine ⟨(singleObjXSelf (.down ℕ) 0 Z).inv ≫ g, ?_⟩
    rw [← Category.assoc, projectiveCochainAugmentation_zero]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, hg]
    exact e₀.hom_inv_id_assoc u

end ToricPower
