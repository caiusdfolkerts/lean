module

public import ToricPower.ProjectiveSectionsFromResolution
public import ToricPower.LinearHomComplexExact
public import ToricPower.ShortExactAcyclicKernel

/-! # The genuine kernel comparison for projective section complexes

Canonical scalar sections commute with every actual coefficient map.
The short exact open/closed sequence can therefore be tested using the
complete signed projective Hom complex, without altering its coefficients.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex

namespace ToricPower

universe u v
variable (R : Type v) [CommRing R]
  {A : Type u} [Category.{v} A] [Abelian A] [Linear R A]
  {Z M N : A} {V : ModuleCat.{v} R}

theorem singleCoefficientSection_naturality
    (a : V ⟶ ((linearCoyoneda R A).obj (op Z)).obj M) (g : M ⟶ N) :
    singleCoefficientSection R a ≫
        (((linearCoyoneda R A).obj (op Z)).mapHomologicalComplex (.up ℤ)).map
          ((CochainComplex.singleFunctor A 0).map g) =
      singleCoefficientSection R (a ≫ ((linearCoyoneda R A).obj (op Z)).map g) := by
  have natural :
      (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map
          (((linearCoyoneda R A).obj (op Z)).map g) ≫
        (HomologicalComplex.singleMapHomologicalComplex
          ((linearCoyoneda R A).obj (op Z)) (.up ℤ) 0).inv.app N =
      (HomologicalComplex.singleMapHomologicalComplex
        ((linearCoyoneda R A).obj (op Z)) (.up ℤ) 0).inv.app M ≫
        (((linearCoyoneda R A).obj (op Z)).mapHomologicalComplex (.up ℤ)).map
          ((CochainComplex.singleFunctor A 0).map g) := by
    simpa only [Functor.comp_map] using
      (HomologicalComplex.singleMapHomologicalComplex
        ((linearCoyoneda R A).obj (op Z)) (.up ℤ) 0).inv.naturality g
  simp only [singleCoefficientSection,CategoryTheory.Functor.map_comp,
    Category.assoc,natural]

theorem scalarProjectiveSectionMap_naturality (P : ProjectiveResolution Z)
    (a : V ⟶ ((linearCoyoneda R A).obj (op Z)).obj M) (g : M ⟶ N) :
    scalarProjectiveSectionMap R P a ≫
        (projectiveCoefficientComplexFunctor R (𝟭 A) P).map
          ((CochainComplex.singleFunctor A 0).map g) =
      scalarProjectiveSectionMap R P (a ≫ ((linearCoyoneda R A).obj (op Z)).map g) := by
  rw [scalarProjectiveSectionMap, Category.assoc,
    ← (projectiveCoefficientComplexUnit R (𝟭 A) P).naturality,
    ← Category.assoc]
  simp only [ordinaryProjectiveCoefficients,Functor.id_comp]
  rw [singleCoefficientSection_naturality]
  rfl

/-- Exact canonical scalar comparisons for the middle and right terms
force the actual projective section complex of the kernel to be acyclic. -/
theorem projectiveSectionKernel_acyclic (P : ProjectiveResolution Z)
    (S : ShortComplex A) (hS : S.ShortExact)
    (a : V ⟶ ((linearCoyoneda R A).obj (op Z)).obj S.X₂)
    (b : V ⟶ ((linearCoyoneda R A).obj (op Z)).obj S.X₃)
    (same : a ≫ ((linearCoyoneda R A).obj (op Z)).map S.g = b)
    [QuasiIso (scalarProjectiveSectionMap R P a)]
    [QuasiIso (scalarProjectiveSectionMap R P b)] :
    ((projectiveCoefficientComplexFunctor R (𝟭 A) P).obj
      ((CochainComplex.singleFunctor A 0).obj S.X₁)).Acyclic := by
  haveI : QuasiIso (scalarProjectiveSectionMap R P a ≫
      (projectiveCoefficientComplexFunctor R (𝟭 A) P).map
        ((CochainComplex.singleFunctor A 0).map S.g)) := by
    rw [scalarProjectiveSectionMap_naturality, same]
    infer_instance
  haveI : QuasiIso ((projectiveCoefficientComplexFunctor R (𝟭 A) P).map
      ((CochainComplex.singleFunctor A 0).map S.g)) :=
    quasiIso_of_comp_left (scalarProjectiveSectionMap R P a) _
  let T := (S.map (CochainComplex.singleFunctor A 0)).map
    ((𝟭 A).mapHomologicalComplex (.up ℤ))
  have hT : T.ShortExact :=
    (hS.map_of_exact (CochainComplex.singleFunctor A 0)).map_of_exact _
  letI (i : ℤ) : Projective ((projectiveCochain P).X i) := by
    unfold projectiveCochain
    infer_instance
  have hU := linearHomComplex_map_shortExact R (projectiveCochain P) T hT
  haveI : QuasiIso (T.map (linearHomComplexFunctor R (projectiveCochain P))).g :=
    inferInstanceAs (QuasiIso ((projectiveCoefficientComplexFunctor R (𝟭 A) P).map
      ((CochainComplex.singleFunctor A 0).map S.g)))
  exact shortExact_acyclic_left_of_quasiIso_g
    (T.map (linearHomComplexFunctor R (projectiveCochain P))) hU

end ToricPower

end
