module

public import PaperVerification.ToricMonomialPrimeFaces
public import PaperVerification.ToricSmoothMonoidFaces
public import PaperVerification.ToricChartActions
public import PaperVerification.ToricOrbitChartMaps
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

@[expose] public section

/-!
# Actual invariant prime closed subschemes of smooth affine charts

An arbitrary integral affine quotient with its genuine equivariant
torus action has a monomial prime kernel. The actual smooth basis then
identifies this kernel with the literal coordinate-face orbit quotient.
The final statement is equality of actual scheme ideal sheaves.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open AddMonoidAlgebra AlgebraicGeometry CategoryTheory Opposite MonoidalCategory MonObj
open scoped Classical

variable (k : Type u) [Field k] {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n))

local notation "s" => Finset.univ.image b
local notation "S" => dualConeMonoid s
local notation "R" => monoidChartAlgebra k S
local notation "F" => (algSpec (CommRingCat.of k) :
  (CommAlgCat k)ᵒᵖ ⥤ Over (Spec (CommRingCat.of k)))
local notation "G" => splitTorusOver k (Lattice n)

local instance fullChart_algSpec_torusAction :
    ModObj G ((F).obj (op (CommAlgCat.of k R))) := by
  change ModObj G (monoidChartSchemeOver k S)
  exact monoidChartScheme_torusAction k S

theorem invariant_fullCone_ringKernel
    (B : CommAlgCat.{u} k) [IsDomain B]
    [ModObj G ((F).obj (op B))]
    (q : R→ₐ[k]B) [IsModHom G ((F).map (CommAlgCat.ofHom q).op)] :
    ∃ I : Finset (Fin n),
      RingHom.ker q.toRingHom=
        RingHom.ker (orbitQuotientAlgebraMap k b I s
          (Finset.image_subset_image (Finset.subset_univ I))).toRingHom := by
  let e := monoidChartAlgebraEquiv k S
  let q' := q.comp e.toAlgHom
  let f₀ : (F).obj (op B) ⟶ monoidChartSchemeOver k S :=
    (F).map (CommAlgCat.ofHom q).op
  letI : IsModHom G f₀ :=
    inferInstanceAs (IsModHom G ((F).map (CommAlgCat.ofHom q).op))
  have hspec : (F).map (CommAlgCat.ofHom q').op=
      f₀≫(monoidChartSchemeOverIso k S).hom := by
    change (F).map (CommAlgCat.ofHom q').op =
      (F).map (CommAlgCat.ofHom q).op ≫
        (F).map (CommAlgCat.ofHom e.toAlgHom).op
    exact (F).map_comp (CommAlgCat.ofHom q).op (CommAlgCat.ofHom e.toAlgHom).op
  letI : IsModHom G ((F).map (CommAlgCat.ofHom q').op) :=
    hspec.symm ▸ (inferInstance : IsModHom G (f₀≫(monoidChartSchemeOverIso k S).hom))
  let P := RingHom.ker q'.toRingHom
  letI : P.IsPrime := RingHom.ker_isPrime q'.toRingHom
  have hP : IsMonomialIdeal k P := fun f hf m=>equivariant_kernel_component k S B q' hf m
  let J := survivingCharacterFace k P
  let I := fullDualForbiddenCoordinates b J
  have hJ : J=orbitCharacterFace s (I.image b) :=
    fullDual_additiveFace_eq_orbitFace b J (survivingCharacterFace_isAdditiveFace k P)
  have hker := monomialPrime_eq_face_kernel k P hP
  change P=RingHom.ker (additiveFaceRetraction k J
    (survivingCharacterFace_isAdditiveFace k P)).toRingHom at hker
  have hfaceKernel (J₁ J₂ : AddSubmonoid S)
      (h₁ : IsAdditiveFace J₁) (h₂ : IsAdditiveFace J₂) (h : J₁ = J₂) :
      RingHom.ker (additiveFaceRetraction k J₁ h₁).toRingHom =
        RingHom.ker (additiveFaceRetraction k J₂ h₂).toRingHom := by
    cases h
    rfl
  have hker := hker.trans (hfaceKernel J (orbitCharacterFace s (I.image b))
    (survivingCharacterFace_isAdditiveFace k P)
    (orbitCharacterFace_isAdditiveFace s (I.image b)
      (Finset.image_subset_image (Finset.subset_univ I))) hJ)
  refine ⟨I,?_⟩
  ext f
  rw [RingHom.mem_ker,RingHom.mem_ker]
  change q f = 0 ↔ orbitQuotientAlgebraMap k b I s
    (Finset.image_subset_image (Finset.subset_univ I)) f = 0
  have hz : q f=0 ↔
      additiveFaceRetraction k (orbitCharacterFace s (I.image b))
        (orbitCharacterFace_isAdditiveFace s (I.image b)
          (Finset.image_subset_image (Finset.subset_univ I))) (e.symm f)=0 := by
    have he := Iff.of_eq
      (congrArg (fun K : Ideal (AddMonoidAlgebra k S)=>e.symm f∈K) hker)
    change q (e (e.symm f)) = 0 ↔
      additiveFaceRetraction k (orbitCharacterFace s (I.image b))
        (orbitCharacterFace_isAdditiveFace s (I.image b)
          (Finset.image_subset_image (Finset.subset_univ I))) (e.symm f) = 0 at he
    simpa only [AlgEquiv.apply_symm_apply] using he
  rw [hz]
  let e₁ := AddMonoidAlgebra.domCongr k k (orbitQuotientSemigroupEquiv b I s)
  let e₂ := monoidChartAlgebraEquiv k (dualConeMonoid (orbitQuotientCone b I s))
  let z : AddMonoidAlgebra k (orbitCharacterFace s (I.image b)) :=
    additiveFaceRetraction k (orbitCharacterFace s (I.image b))
      (orbitCharacterFace_isAdditiveFace s (I.image b)
        (Finset.image_subset_image (Finset.subset_univ I))) (e.symm f)
  change z = 0 ↔ e₂ (e₁ z) = 0
  constructor
  · intro h
    rw [h,map_zero,map_zero]
  · intro h
    apply e₁.injective
    apply e₂.injective
    simpa only [map_zero] using h

end PaperVerification.ToricGeometry

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory MonObj
open PaperVerification.ToricCharacters PaperVerification.ToricGeometry
open scoped Classical

/-- Equal affine coordinate kernels give equal actual scheme ideal
sheaves through the proved ΓSpec natural isomorphisms. -/
theorem specMap_kernel_eq_of_ringKernel_eq
    {A B C : CommRingCat.{u}} (f : A⟶B) (g : A⟶C)
    (h : RingHom.ker f.hom=RingHom.ker g.hom) :
    (Spec.map f).ker=(Spec.map g).ker := by
  rw [Scheme.ker_of_isAffine,Scheme.ker_of_isAffine]
  congr 1
  ext a
  have hf : (Spec.map f).appTop a=0 ↔ f ((Scheme.ΓSpecIso A).hom a)=0 := by
    have he := congrArg (fun φ=>φ a) (Scheme.ΓSpecIso_naturality f)
    constructor
    · intro hz
      simpa only [ConcreteCategory.comp_apply,hz,map_zero] using he.symm
    · intro hz
      apply (Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv.injective
      change (Scheme.ΓSpecIso B).hom ((Spec.map f).appTop a) =
        (Scheme.ΓSpecIso B).hom 0
      simpa only [ConcreteCategory.comp_apply,hz,map_zero] using he
  have hg : (Spec.map g).appTop a=0 ↔ g ((Scheme.ΓSpecIso A).hom a)=0 := by
    have he := congrArg (fun φ=>φ a) (Scheme.ΓSpecIso_naturality g)
    constructor
    · intro hz
      simpa only [ConcreteCategory.comp_apply,hz,map_zero] using he.symm
    · intro hz
      apply (Scheme.ΓSpecIso C).commRingCatIsoToRingEquiv.injective
      change (Scheme.ΓSpecIso C).hom ((Spec.map g).appTop a) =
        (Scheme.ΓSpecIso C).hom 0
      simpa only [ConcreteCategory.comp_apply,hz,map_zero] using he
  rw [RingHom.mem_ker,RingHom.mem_ker,hf,hg]
  simpa only [RingHom.mem_ker] using
    Iff.of_eq (congrArg (fun I : Ideal A=>(Scheme.ΓSpecIso A).hom a∈I) h)

variable (k : Type u) [Field k] {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n))

local notation "s" => Finset.univ.image b
local notation "S" => dualConeMonoid s
local notation "R" => monoidChartAlgebra k S
local notation "F" => (algSpec (CommRingCat.of k) :
  (CommAlgCat k)ᵒᵖ ⥤ Over (Spec (CommRingCat.of k)))
local notation "G" => splitTorusOver k (Lattice n)

local instance fullChart_algSpec_torusAction :
    ModObj G ((F).obj (op (CommAlgCat.of k R))) := by
  change ModObj G (monoidChartSchemeOver k S)
  exact monoidChartScheme_torusAction k S

theorem invariant_fullCone_Spec_kernel
    (B : CommAlgCat.{u} k) [IsDomain B]
    [ModObj G ((F).obj (op B))]
    (q : R→ₐ[k]B) [IsModHom G ((F).map (CommAlgCat.ofHom q).op)] :
    ∃ I : Finset (Fin n),
      (Spec.map (CommRingCat.ofHom q.toRingHom)).ker=
        (orbitQuotientChartMap k b I s
          (Finset.image_subset_image (Finset.subset_univ I))).ker := by
  obtain ⟨I,hI⟩ := invariant_fullCone_ringKernel k b B q
  exact ⟨I,specMap_kernel_eq_of_ringKernel_eq _ _ hI⟩

/-- Every actual invariant integral closed subscheme of a full smooth
chart is exactly one of its coordinate-face orbit closures. The source
is any integral scheme with an actual group-scheme action; affineness,
the coordinate quotient, and character stability are all derived. -/
theorem invariant_integral_closed_fullChart_kernel
    (Y : Over (Spec (CommRingCat.of k))) [IsIntegral Y.left]
    [ModObj G Y]
    (f : Y⟶monoidChartSchemeOver k S)
    [IsClosedImmersion f.left] [IsModHom G f] :
    ∃ I : Finset (Fin n),f.left.ker=
      (orbitQuotientChartMap k b I s
        (Finset.image_subset_image (Finset.subset_univ I))).ker := by
  letI : IsAffine (monoidChartSchemeOver k S).left := by
    change IsAffine (Spec (CommRingCat.of R))
    infer_instance
  letI : Y.left.Over (Spec (CommRingCat.of k)) := OverClass.fromOver Y
  letI : IsAffine Y.left := (IsClosedImmersion.isAffine_surjective_of_isAffine f.left).1
  let ρ : CommRingCat.of k ⟶ Γ(Y.left,⊤) :=
    (Spec.fullyFaithful.preimage (Y.left.isoSpec.inv ≫ Y.hom)).unop
  letI : Algebra k Γ(Y.left,⊤) := ρ.hom.toAlgebra
  let B : CommAlgCat.{u} k := CommAlgCat.of k Γ(Y.left,⊤)
  have hρ : Spec.map ρ = Y.left.isoSpec.inv ≫ Y.hom :=
    Spec.fullyFaithful.map_preimage (Y.left.isoSpec.inv ≫ Y.hom)
  let e : Y≅(F).obj (op B) := Over.isoMk Y.left.isoSpec (by
    change Y.left.isoSpec.hom ≫ Spec.map ρ = Y.hom
    rw [hρ,Iso.hom_inv_id_assoc])
  letI : IsMonHom (Iso.refl G).hom := by
    change IsMonHom (𝟙 G)
    infer_instance
  letI : ModObj G ((F).obj (op B)) := ModObj.ofIso (Iso.refl G) e
  letI : IsModHom G e.hom := by
    refine ⟨?_⟩
    change γ[G,Y]≫e.hom=
      (G◁e.hom)≫((𝟙 G⊗ₘe.inv)≫γ[G,Y]≫e.hom)
    simp only [id_tensorHom,← Category.assoc,← whiskerLeft_comp,Iso.hom_inv_id,
      whiskerLeft_id,Category.id_comp]
  let f₀ : Y ⟶ (F).obj (op (CommAlgCat.of k R)) := f
  letI : IsModHom G f₀ := inferInstanceAs (IsModHom G f)
  let q : R→ₐ[k]B :=
    ((algSpec.fullyFaithful («R» := CommRingCat.of k)).preimage
      (X := op B) (Y := op (CommAlgCat.of k R)) (e.inv≫f₀)).unop.hom
  have hq : (F).map (CommAlgCat.ofHom q).op=e.inv≫f₀ :=
    (algSpec.fullyFaithful («R» := CommRingCat.of k)).map_preimage (e.inv≫f₀)
  letI : IsModHom G ((F).map (CommAlgCat.ofHom q).op) := by
    rw [hq]
    infer_instance
  obtain ⟨I,hI⟩ := invariant_fullCone_Spec_kernel k b B q
  refine ⟨I,?_⟩
  have hleft := congrArg (fun g=>g.left) hq
  change Spec.map (CommRingCat.ofHom q.toRingHom)=e.inv.left≫f.left at hleft
  let e₀ := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  have hcomp : (e.inv.left ≫ f.left).ker = f.left.ker :=
    Scheme.Hom.ker_comp_of_isIso e₀.inv f.left
  have hker : (Spec.map (CommRingCat.ofHom q.toRingHom)).ker =
      (e.inv.left ≫ f.left).ker :=
    congrArg (fun g : ((F).obj (op B)).left ⟶ (monoidChartSchemeOver k S).left => g.ker) hleft
  exact hcomp.symm.trans (hker.symm.trans hI)

/-- The ideal equality yields an actual local scheme isomorphism over
the original chart, using the universal property of closed immersions. -/
theorem invariant_integral_closed_fullChart_exists_faceIso
    (Y : Over (Spec (CommRingCat.of k))) [IsIntegral Y.left]
    [ModObj G Y]
    (f : Y⟶monoidChartSchemeOver k S)
    [IsClosedImmersion f.left] [IsModHom G f] :
    ∃ I : Finset (Fin n),
      ∃ e : Y.left≅coneChart k (orbitQuotientCone b I s),
        e.hom≫orbitQuotientChartMap k b I s
          (Finset.image_subset_image (Finset.subset_univ I))=f.left := by
  obtain ⟨I,hI⟩ := invariant_integral_closed_fullChart_kernel k b Y f
  let g : coneChart k (orbitQuotientCone b I s) ⟶
      (monoidChartSchemeOver k S).left := orbitQuotientChartMap k b I s
    (Finset.image_subset_image (Finset.subset_univ I))
  letI : IsClosedImmersion g := inferInstanceAs
    (IsClosedImmersion (orbitQuotientChartMap k b I s
      (Finset.image_subset_image (Finset.subset_univ I))))
  letI := IsClosedImmersion.isIso_lift g f.left hI.symm
  exact ⟨I,asIso (IsClosedImmersion.lift g f.left hI.symm.le),
    IsClosedImmersion.lift_fac _ _ _⟩

theorem invariant_integral_closed_fullChart_kernel_of_basis
    (s₀ : Finset (Lattice n)) (hs : s₀=Finset.univ.image b)
    (Y : Over (Spec (CommRingCat.of k))) [IsIntegral Y.left]
    [ModObj G Y]
    (f : Y⟶monoidChartSchemeOver k (dualConeMonoid s₀))
    [IsClosedImmersion f.left] [IsModHom G f] :
    ∃ I : Finset (Fin n),f.left.ker=
      (orbitQuotientChartMap k b I s₀
        (by rw [hs]; exact Finset.image_subset_image (Finset.subset_univ I))).ker := by
  subst s₀
  exact invariant_integral_closed_fullChart_kernel k b Y f

theorem invariant_integral_closed_fullChart_faceIso_of_basis
    (s₀ : Finset (Lattice n)) (hs : s₀=Finset.univ.image b)
    (Y : Over (Spec (CommRingCat.of k))) [IsIntegral Y.left]
    [ModObj G Y]
    (f : Y⟶monoidChartSchemeOver k (dualConeMonoid s₀))
    [IsClosedImmersion f.left] [IsModHom G f] :
    ∃ I : Finset (Fin n),∃ e : Y.left≅coneChart k (orbitQuotientCone b I s₀),
      e.hom≫orbitQuotientChartMap k b I s₀
        (by rw [hs]; exact Finset.image_subset_image (Finset.subset_univ I))=f.left := by
  subst s₀
  exact invariant_integral_closed_fullChart_exists_faceIso k b Y f

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.invariant_integral_closed_fullChart_kernel
