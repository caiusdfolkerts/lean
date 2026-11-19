module
public import Mathlib

/-! Multiplication in the associated graded of Koszul homology. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
open scoped BigOperators DirectSum
universe u v w
open Classical Finset MvPolynomial CategoryTheory
set_option backward.isDefEq.respectTransparency false
section
open Category Limits Module ExteriorAlgebra
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R)
noncomputable def koszulComplex.dAlternating (n : ℕ) : M [⋀^Fin (n + 1)]→ₗ[R] ⋀[R]^n M := AlternatingMap.alternatizeUncurryFin (φ.smulRight (exteriorPower.ιMulti R n))
noncomputable def koszulComplex.d (n : ℕ) : ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M := exteriorPower.alternatingMapLinearEquiv (koszulComplex.dAlternating φ n)
lemma koszulComplex.d_comp_eq_zero (n : ℕ) : koszulComplex.d φ n ∘ₗ koszulComplex.d φ (n + 1) = 0 := by sorry
noncomputable def koszulComplex : ChainComplex (ModuleCat R) ℕ := ChainComplex.of (fun n ↦ ModuleCat.of R (⋀[R]^n M))
    (fun n ↦ ModuleCat.ofHom (koszulComplex.d φ n))
    (fun n ↦ by rw [← ModuleCat.ofHom_comp, koszulComplex.d_comp_eq_zero, ModuleCat.ofHom_zero])
end
namespace CommAlg.Koszul
open TensorProduct
variable {R : Type u} {V : Type} [CommRing R] [Fintype V] [LinearOrder V]
abbrev familyCoefficientComplex (x : V → R) (M : ModuleCat.{u} R) : ChainComplex (ModuleCat.{u} R) ℕ := (((CategoryTheory.MonoidalCategory.tensoringRight (ModuleCat R)).obj
  M).mapHomologicalComplex (ComplexShape.down ℕ)).obj (koszulComplex (Fintype.linearCombination R x))
def coefficientCoordinates (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) : (familyCoefficientComplex x M).X i ≃ₗ[R] (Set.powersetCard V i →₀ M) :=
  TensorProduct.equivFinsuppOfBasisLeft ((Pi.basisFun R V).exteriorPower i)
def coordinateDifferential (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) :
    (Set.powersetCard V (i + 1) →₀ M) →ₗ[R] (Set.powersetCard V i →₀ M) :=
  let δ : (familyCoefficientComplex.{u} x M).X (i + 1) →ₗ[R]
      (familyCoefficientComplex.{u} x M).X i := ((familyCoefficientComplex.{u} x M).d (i + 1) i).hom
  (coefficientCoordinates.{u} x M i).toLinearMap.comp
    (δ.comp (coefficientCoordinates.{u} x M (i + 1)).symm.toLinearMap)
end CommAlg.Koszul
namespace FourPapers.Universal
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
def IsSimplicialPoset (P : Type*) [PartialOrder P] [OrderBot P] : Prop := ∀ p : P, ∃ n : ℕ, Nonempty (Set.Iic p ≃o Finset (Fin n))
def faceVertices (p : P) : Finset P := univ.filter fun a => IsAtom a ∧ a ≤ p
theorem faceVertices_mono : Monotone (faceVertices : P → Finset P) := by sorry
theorem existsUnique_subface (hs : IsSimplicialPoset P) (p : P) (s : Finset P) (hsu : s ⊆ faceVertices p) : ∃! x : Set.Iic p, faceVertices x.val = s := by sorry
def faceRank (p : P) : ℕ := (faceVertices p).card
abbrev NonzeroFace (P : Type*) [Preorder P] [OrderBot P] := {p : P // p ≠ ⊥}
def faceMeetBelow (hs : IsSimplicialPoset P) (p q w : P) (hpw : p ≤ w) (hqw : q ≤ w) : P := ((existsUnique_subface hs w (faceVertices p ∩ faceVertices q)
  (Finset.inter_subset_left.trans (faceVertices_mono hpw))).choose).val
def IsMinimalCommonUpper (p q w : P) : Prop := p ≤ w ∧ q ≤ w ∧ ∀ v, p ≤ v → q ≤ v → v ≤ w → v = w
def minimalCommonUppers (p q : P) : Finset P := univ.filter (IsMinimalCommonUpper p q)
variable (K : Type*) [CommRing K]
abbrev FacePolynomial := MvPolynomial (NonzeroFace P) K
def faceSymbol (p : P) : FacePolynomial (P := P) K :=
  if hp : p = ⊥ then 1 else X ⟨p, hp⟩
def faceRelations (hs : IsSimplicialPoset P) : Set (FacePolynomial (P := P) K) := {f | (∃ (p q w : P) (hpw : p ≤ w) (hqw : q ≤ w), f = faceSymbol K p * faceSymbol K q -
  faceSymbol K (faceMeetBelow hs p q w hpw hqw) * ∑ u ∈ minimalCommonUppers p q, faceSymbol K u) ∨ (∃ p q, (¬ ∃ w, p ≤ w ∧ q ≤ w) ∧ f = faceSymbol K p * faceSymbol K q)}
def faceIdeal (hs : IsSimplicialPoset P) : Ideal (FacePolynomial (P := P) K) := Ideal.span (faceRelations K hs)
abbrev FaceRing (hs : IsSimplicialPoset P) := FacePolynomial (P := P) K ⧸ faceIdeal K hs
def barycentricIdeal : Ideal (FacePolynomial (P := P) K) := Ideal.span {f | ∃ p q : NonzeroFace P, ¬ p.val ≤ q.val ∧ ¬ q.val ≤ p.val ∧ f = X p * X q}
abbrev BarycentricRing := FacePolynomial (P := P) K ⧸ barycentricIdeal (P := P) K
def faceRingGenerator (hs : IsSimplicialPoset P) (p : P) : FaceRing K hs := Ideal.Quotient.mk (faceIdeal K hs) (faceSymbol K p)
def barycentricGenerator (p : P) : BarycentricRing (P := P) K := Ideal.Quotient.mk (barycentricIdeal K) (faceSymbol K p)
def faceRankParameter (hs : IsSimplicialPoset P) (i : ℕ) : FaceRing K hs := ∑ p ∈ univ.filter (fun p : P => faceRank p = i), faceRingGenerator K hs p
def barycentricRankParameter (i : ℕ) : BarycentricRing (P := P) K := ∑ p ∈ univ.filter (fun p : P => faceRank p = i), barycentricGenerator K p
end
section
variable {V : Type*} [Fintype V]
def rankWeight (d r : ℕ) : ℤ := (r : ℤ) * (2 * (d : ℤ) - r)
end
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
section
variable (K : Type*) [CommRing K]
def BarycentricAllowed (a : NonzeroFace P →₀ ℕ) : Prop := ∀ p ∈ a.support, ∀ q ∈ a.support, p.val ≤ q.val ∨ q.val ≤ p.val
end
abbrev StandardFaceIndex (P : Type*) [PartialOrder P] [OrderBot P] := {a : NonzeroFace P →₀ ℕ // BarycentricAllowed a}
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
def faceRingMonomial (a : NonzeroFace P →₀ ℕ) : FaceRing K hs := Ideal.Quotient.mk (faceIdeal K hs) (monomial a 1)
def standardFaceBasis : Module.Basis (StandardFaceIndex P) K (FaceRing K hs) := by sorry
@[simp] theorem standardFaceBasis_apply (a : StandardFaceIndex P) :
    standardFaceBasis K hs a = faceRingMonomial K hs a.val := by sorry
def standardRankWeight (d : ℕ) (a : StandardFaceIndex P) : ℤ := a.val.sum (fun F n => (n : ℤ) * rankWeight d (faceRank F.val))
end
section
variable {I K M N : Type*} [CommRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
def canonicalBasisEquiv (b : Module.Basis I K M) (c : Module.Basis I K N) : M ≃ₗ[K] N := b.repr.trans c.repr.symm
end
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P] (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
def barycentricGlobalStandardBasis : Module.Basis (StandardFaceIndex P) K (BarycentricRing (P := P) K) := by sorry
def canonicalOriginalComparison : BarycentricRing (P := P) K ≃ₗ[K] FaceRing K hs := canonicalBasisEquiv (barycentricGlobalStandardBasis K) (standardFaceBasis K hs)
end
variable {I V K M N : Type*} [CommRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K) (hs : IsSimplicialPoset P)
theorem barycentricGlobalStandardBasis_monomial (a : StandardFaceIndex P) : Ideal.Quotient.mk (barycentricIdeal (P := P) K) (monomial a.val 1) = barycentricGlobalStandardBasis
  K a := by sorry
end FourPapers.Universal
namespace FourPapers.FilteredHomology
variable {K : Type*} [CommRing K]
structure Filtration (M : Type*) [AddCommGroup M] [Module K M] where
  level : ℕ → Submodule K M
  zero : level 0 = ⊥
  mono : Monotone level
  exhaustive : ∀ x : M, ∃ n, x ∈ level n
variable {X Y Z : Type*} [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z]
def Preserves (F : Filtration (K := K) X) (G : Filtration (K := K) Y) (f : X →ₗ[K] Y) : Prop := ∀ n x, x ∈ F.level n → f x ∈ G.level n
def LiftsCycles (F : Filtration (K := K) X) (G : Filtration (K := K) Y) (f : X →ₗ[K] Y) : Prop := ∀ n x, x ∈ F.level (n + 1) → f x ∈ G.level n → ∃ z, z ∈ F.level (n + 1) ∧ f z
  = 0 ∧ x - z ∈ F.level n
def lowerInLevel (F : Filtration (K := K) X) (n : ℕ) : Submodule K (F.level (n + 1)) := (F.level n).comap (F.level (n + 1)).subtype
abbrev Grade (F : Filtration (K := K) X) (n : ℕ) := F.level (n + 1) ⧸ lowerInLevel F n
def levelMap (F : Filtration (K := K) X) (G : Filtration (K := K) Y) (f : X →ₗ[K] Y) (hf : Preserves F G f) (n : ℕ) : F.level n →ₗ[K] G.level n := (f.domRestrict
  _).codRestrict _ (fun x => hf n x.val x.property)
def gradeMap (F : Filtration (K := K) X) (G : Filtration (K := K) Y) (f : X →ₗ[K] Y) (hf : Preserves F G f) (n : ℕ) : Grade F n →ₗ[K] Grade G n := Submodule.mapQ _ _ (levelMap
  F G f hf (n + 1)) (fun x hx => hf n x.val hx)
theorem gradeMap_comp (F : Filtration (K := K) X) (G : Filtration (K := K) Y) (H : Filtration (K := K) Z) (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hf : Preserves F G f) (hg :
  Preserves G H g) (hfg : g.comp f = 0) (n : ℕ) : (gradeMap G H g hg n).comp (gradeMap F G f hf n) = 0 := by sorry
def boundaryMap (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) : X →ₗ[K] LinearMap.ker g := f.codRestrict _ (fun x => LinearMap.congr_fun hfg x)
abbrev Homology (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) := LinearMap.ker g ⧸ LinearMap.range (boundaryMap f g hfg)
def homologyClass (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) : LinearMap.ker g →ₗ[K] Homology f g hfg := (LinearMap.range (boundaryMap f g hfg)).mkQ
def cycleLevel (F : Filtration (K := K) Y) (g : Y →ₗ[K] Z) (n : ℕ) : Submodule K (LinearMap.ker g) := (F.level n).comap (LinearMap.ker g).subtype
def homologyLevel (F : Filtration (K := K) Y) (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) (n : ℕ) : Submodule K (Homology f g hfg) := (cycleLevel F g n).map
  (homologyClass f g hfg)
def homologyFiltration (F : Filtration (K := K) Y) (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z)
    (hfg : g.comp f = 0) : Filtration (K := K) (Homology f g hfg) where
  level := homologyLevel F f g hfg
  zero := by simp [homologyLevel, cycleLevel, F.zero]
  mono := fun _ _ h => Submodule.map_mono (Submodule.comap_mono (F.mono h))
  exhaustive x := by
    obtain ⟨z, rfl⟩ := (LinearMap.range (boundaryMap f g hfg)).mkQ_surjective x
    obtain ⟨n, hn⟩ := F.exhaustive z.val
    exact ⟨n, z, hn, rfl⟩
variable (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
  (H : Filtration (K := K) Z) (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z)
  (hf : Preserves F G f) (hg : Preserves G H g) (hfg : g.comp f = 0) (n : ℕ)
abbrev GradedHomology := Homology (gradeMap F G f hf n) (gradeMap G H g hg n) (gradeMap_comp F G H f g hf hg hfg n)
def cycleToLevel : cycleLevel G g (n + 1) →ₗ[K] G.level (n + 1) := (((LinearMap.ker g).subtype).comp (cycleLevel G g (n + 1)).subtype).codRestrict _ (fun z => z.property)
def cycleToGradeCycle : cycleLevel G g (n + 1) →ₗ[K] LinearMap.ker (gradeMap G H g hg n) :=
  (((lowerInLevel G n).mkQ).comp (cycleToLevel G g n)).codRestrict _ (by
    intro z
    change Submodule.Quotient.mk (levelMap G H g hg (n + 1) (cycleToLevel G g n z)) = 0
    have he : levelMap G H g hg (n + 1) (cycleToLevel G g n z) = 0 := Subtype.ext z.val.property
    rw [he]
    exact Submodule.Quotient.mk_zero _)
def leadingHomologyClass : cycleLevel G g (n + 1) →ₗ[K] GradedHomology F G H f g hf hg hfg n := (homologyClass _ _ (gradeMap_comp F G H f g hf hg hfg n)).comp
  (cycleToGradeCycle G H g hg n)
def filteredHomologyClass : cycleLevel G g (n + 1) →ₗ[K] Grade (homologyFiltration G f g hfg) n := (lowerInLevel (homologyFiltration G f g hfg) n).mkQ.comp (((homologyClass f
  g hfg).comp (cycleLevel G g (n + 1)).subtype).codRestrict _ (fun z => ⟨z.val, z.property, rfl⟩))
theorem leadingHomologyClass_surjective (lift : LiftsCycles G H g) : Function.Surjective (leadingHomologyClass F G H f g hf hg hfg n) := by sorry
theorem filteredHomologyClass_surjective : Function.Surjective (filteredHomologyClass G f g hfg n) := by sorry
theorem leading_filtered_kernel_eq (lift : LiftsCycles F G f) : LinearMap.ker (leadingHomologyClass F G H f g hf hg hfg n) = LinearMap.ker (filteredHomologyClass G f g hfg n)
  := by sorry
def associatedHomologyEquiv (liftf : LiftsCycles F G f) (liftg : LiftsCycles G H g) : Grade (homologyFiltration G f g hfg) n ≃ₗ[K] GradedHomology F G H f g hf hg hfg n :=
  ((filteredHomologyClass G f g hfg n).quotKerEquivOfSurjective (filteredHomologyClass_surjective G f g hfg n)).symm |>.trans ((Submodule.quotEquivOfEq _ _
  (leading_filtered_kernel_eq F G H f g hf hg hfg n liftf).symm).trans ((leadingHomologyClass F G H f g hf hg hfg n).quotKerEquivOfSurjective (leadingHomologyClass_surjective
  F G H f g hf hg hfg n liftg)))
end FourPapers.FilteredHomology
namespace FourPapers.Universal
open FourPapers.FilteredHomology
variable {K : Type*} [CommRing K] {X Y Z X' Y' Z' : Type*}
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z]
  [AddCommGroup X'] [Module K X'] [AddCommGroup Y'] [Module K Y'] [AddCommGroup Z'] [Module K Z']
variable (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0)
  (f' : X' →ₗ[K] Y') (g' : Y' →ₗ[K] Z') (hfg' : g'.comp f' = 0)
  (e : Y ≃ₗ[K] Y') (hcycles : ∀ y, g' (e y) = 0 ↔ g y = 0)
  (hboundaries : ∀ y, (∃ x', f' x' = e y) ↔ ∃ x, f x = y)
def middleCycleEquiv : LinearMap.ker g ≃ₗ[K] LinearMap.ker g' where
  toFun y := ⟨e y.val, (hcycles y.val).mpr y.property⟩
  invFun y := ⟨e.symm y.val, (hcycles (e.symm y.val)).mp
    (by rw [LinearEquiv.apply_symm_apply]; exact y.property)⟩
  left_inv y := Subtype.ext (e.symm_apply_apply y.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add e x.val y.val)
  map_smul' a y := Subtype.ext (map_smul e a y.val)
section
include hboundaries
theorem middleCycleEquiv_boundaries : (LinearMap.range (boundaryMap f g hfg)).map (middleCycleEquiv g g' e hcycles).toLinearMap = LinearMap.range (boundaryMap f' g' hfg') :=
  by sorry
end
def middleHomologyEquiv : Homology f g hfg ≃ₗ[K] Homology f' g' hfg' := Submodule.Quotient.equiv _ _ (middleCycleEquiv g g' e hcycles) (middleCycleEquiv_boundaries f g hfg f'
  g' hfg' e hcycles hboundaries)
end FourPapers.Universal
namespace FourPapers.FilteredHomology
variable {K X Y Z X' Y' Z' : Type*} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z] [AddCommGroup X'] [Module K X']
  [AddCommGroup Y'] [Module K Y'] [AddCommGroup Z'] [Module K Z']
def levelEquiv (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
    (e : X ≃ₗ[K] Y) (he : ∀ n x, e x ∈ G.level n ↔ x ∈ F.level n) (n : ℕ) :
    F.level n ≃ₗ[K] G.level n where
  toFun x := ⟨e x.val, (he n x.val).mpr x.property⟩
  invFun y := ⟨e.symm y.val, (he n (e.symm y.val)).mp
    (by simpa only [LinearEquiv.apply_symm_apply] using y.property)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (e.map_add x.val y.val)
  map_smul' a x := Subtype.ext (e.map_smul a x.val)
theorem levelEquiv_lower (F : Filtration (K := K) X) (G : Filtration (K := K) Y) (e : X ≃ₗ[K] Y) (he : ∀ n x, e x ∈ G.level n ↔ x ∈ F.level n) (n : ℕ) : (lowerInLevel F n).map
  (levelEquiv F G e he (n + 1)).toLinearMap = lowerInLevel G n := by sorry
def gradeEquiv (F : Filtration (K := K) X) (G : Filtration (K := K) Y) (e : X ≃ₗ[K] Y) (he : ∀ n x, e x ∈ G.level n ↔ x ∈ F.level n) (n : ℕ) : Grade F n ≃ₗ[K] Grade G n :=
  Submodule.Quotient.equiv _ _ (levelEquiv F G e he (n + 1)) (levelEquiv_lower F G e he n)
def chainHomologyEquiv
    (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0)
    (f' : X' →ₗ[K] Y') (g' : Y' →ₗ[K] Z') (hfg' : g'.comp f' = 0)
    (a : X ≃ₗ[K] X') (b : Y ≃ₗ[K] Y') (c : Z ≃ₗ[K] Z')
    (hab : ∀ x, f' (a x) = b (f x)) (hbc : ∀ y, g' (b y) = c (g y)) :
    Homology f g hfg ≃ₗ[K] Homology f' g' hfg' := FourPapers.Universal.middleHomologyEquiv f g hfg f' g' hfg' b
    (by intro y; rw [hbc]; exact c.map_eq_zero_iff)
    (by
      intro y
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨a.symm x, b.injective ?_⟩
        rw [← hab, LinearEquiv.apply_symm_apply, hx]
      · rintro ⟨x, hx⟩
        exact ⟨a x, by rw [hab, hx]⟩)
end FourPapers.FilteredHomology
namespace FourPapers.Universal
section
open FourPapers.FilteredHomology
variable {K I J X Y : Type*} [CommRing K] [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y]
def basisFiltration (b : Module.Basis I K X) (w : I → ℕ) : Filtration (K := K) X where
  level n := Submodule.span K (b '' {i | w i < n})
  zero := by simp
  mono := by
    intro m n hmn
    apply Submodule.span_mono
    exact Set.image_mono (fun i hi => hi.trans_le hmn)
  exhaustive x := by
    refine ⟨(b.repr x).support.sup w + 1, ?_⟩
    rw [b.mem_span_image]
    intro i hi
    exact Nat.lt_succ_of_le (Finset.le_sup (f := w) hi)
end
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
def koszulExteriorWeight (d : ℕ) {i : ℕ} (s : Set.powersetCard (Fin d) i) : ℤ := ∑ j ∈ s.val, rankWeight d (j.val + 1)
abbrev OriginalKoszulIndex (P : Type*) [PartialOrder P] [OrderBot P] (d i : ℕ) := Σ _ : Set.powersetCard (Fin d) i, StandardFaceIndex P
def originalKoszulWeight (d : ℕ) {i : ℕ} (a : OriginalKoszulIndex P d i) : ℤ := standardRankWeight d a.2 + koszulExteriorWeight d a.1
end
section
open CommAlg
section
variable {K B B' : Type u} {C : Type} [CommRing K] [CommRing B] [CommRing B']
  [Algebra K B] [Algebra K B'] [Fintype C] [LinearOrder C]
def parameterKoszulDifferential (γ : C → B) (i : ℕ) : (Set.powersetCard C (i + 1) →₀ B) →ₗ[K] (Set.powersetCard C i →₀ B) := (Koszul.coordinateDifferential γ (ModuleCat.of B
  B) i).restrictScalars K
theorem parameterKoszulDifferential_comp (γ : C → B) (i : ℕ) : (parameterKoszulDifferential (K := K) γ i).comp (parameterKoszulDifferential (K := K) γ (i + 1)) = 0 := by sorry
def parameterKoszulComplex (γ : C → B) : ChainComplex (ModuleCat.{u} K) ℕ := ChainComplex.of (fun i => ModuleCat.of K (Set.powersetCard C i →₀ B)) (fun i => ModuleCat.ofHom
  (parameterKoszulDifferential (K := K) γ i)) (fun i => ModuleCat.hom_ext (parameterKoszulDifferential_comp (K := K) γ i))
end
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
abbrev originalKoszulComplex : ChainComplex (ModuleCat.{u} K) ℕ := parameterKoszulComplex (K := K) (fun i : Fin d => faceRankParameter K hs (i.val + 1))
abbrev barycentricKoszulComplex : ChainComplex (ModuleCat.{u} K) ℕ := parameterKoszulComplex (K := K) (fun i : Fin d => barycentricRankParameter (P := P) K (i.val + 1))
end
section
open FourPapers.FilteredHomology
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ)
def originalKoszulBasis (i : ℕ) : Module.Basis (OriginalKoszulIndex P d i) K (Set.powersetCard (Fin d) i →₀ FaceRing K hs) := Finsupp.basis (fun _ => standardFaceBasis K hs)
def barycentricKoszulBasis (i : ℕ) : Module.Basis (OriginalKoszulIndex P d i) K (Set.powersetCard (Fin d) i →₀ BarycentricRing (P := P) K) := Finsupp.basis (fun _ =>
  barycentricGlobalStandardBasis K)
def originalKoszulFiltration (i : ℕ) : Filtration (K := K) (Set.powersetCard (Fin d) i →₀ FaceRing K hs) := basisFiltration (originalKoszulBasis K hs d i) (fun a =>
  (originalKoszulWeight d a).toNat)
def barycentricKoszulFiltration (i : ℕ) : Filtration (K := K) (Set.powersetCard (Fin d) i →₀ BarycentricRing (P := P) K) := basisFiltration (barycentricKoszulBasis (P := P) K
  d i) (fun a => (originalKoszulWeight d a).toNat)
def canonicalKoszulCoefficientEquiv (i : ℕ) : (Set.powersetCard (Fin d) i →₀ BarycentricRing (P := P) K) ≃ₗ[K] (Set.powersetCard (Fin d) i →₀ FaceRing K hs) :=
  Finsupp.mapRange.linearEquiv (canonicalOriginalComparison K hs)
end
section
open CommAlg FourPapers.FilteredHomology
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K)
theorem barycentricKoszulDifferential_preserves (d i : ℕ) : Preserves (barycentricKoszulFiltration (P := P) K d (i + 1)) (barycentricKoszulFiltration (P := P) K d i)
  (parameterKoszulDifferential (K := K) (fun j : Fin d => barycentricRankParameter K (j.val + 1)) i) := by sorry
theorem barycentricKoszulDifferential_liftsCycles (d i : ℕ) : LiftsCycles (barycentricKoszulFiltration (P := P) K d (i + 1)) (barycentricKoszulFiltration (P := P) K d i)
  (parameterKoszulDifferential (K := K) (fun j : Fin d => barycentricRankParameter K (j.val + 1)) i) := by sorry
end
open FourPapers.FilteredHomology
section
variable {K : Type u} [CommRing K]
abbrev complexIncoming (C : ChainComplex (ModuleCat.{u} K) ℕ) (i : ℕ) := (C.d (i + 1) i).hom
abbrev complexOutgoing (C : ChainComplex (ModuleCat.{u} K) ℕ) (i : ℕ) := (C.d i (i - 1)).hom
theorem complexIncomingOutgoing (C : ChainComplex (ModuleCat.{u} K) ℕ) (i : ℕ) : (complexOutgoing C i).comp (complexIncoming C i) = 0 := by sorry
abbrev complexKernelHomology (C : ChainComplex (ModuleCat.{u} K) ℕ) (i : ℕ) := Homology (complexIncoming C i) (complexOutgoing C i) (complexIncomingOutgoing C i)
variable {P : Type u} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
abbrev originalKoszulHomology (i : ℕ) := complexKernelHomology (originalKoszulComplex K hs d) i
def originalKoszulHomologyFiltration (i : ℕ) : Filtration (K := K) (originalKoszulHomology K hs d i) := homologyFiltration (originalKoszulFiltration K hs d i) (complexIncoming
  (originalKoszulComplex K hs d) i) (complexOutgoing (originalKoszulComplex K hs d) i) (complexIncomingOutgoing (originalKoszulComplex K hs d) i)
section
include hrank
theorem originalIncoming_preserves (i : ℕ) : Preserves (originalKoszulFiltration K hs d (i + 1)) (originalKoszulFiltration K hs d i) (complexIncoming (originalKoszulComplex K
  hs d) i) := by sorry
theorem originalOutgoing_preserves (i : ℕ) : Preserves (originalKoszulFiltration K hs d i) (originalKoszulFiltration K hs d (i - 1)) (complexOutgoing (originalKoszulComplex K
  hs d) i) := by sorry
theorem originalIncoming_liftsCycles (i : ℕ) : LiftsCycles (originalKoszulFiltration K hs d (i + 1)) (originalKoszulFiltration K hs d i) (complexIncoming
  (originalKoszulComplex K hs d) i) := by sorry
theorem originalOutgoing_liftsCycles (i : ℕ) : LiftsCycles (originalKoszulFiltration K hs d i) (originalKoszulFiltration K hs d (i - 1)) (complexOutgoing
  (originalKoszulComplex K hs d) i) := by sorry
end
def originalKoszulAssociatedHomology (i n : ℕ) : Grade (originalKoszulHomologyFiltration K hs d i) n ≃ₗ[K] GradedHomology (originalKoszulFiltration K hs d (i + 1))
  (originalKoszulFiltration K hs d i) (originalKoszulFiltration K hs d (i - 1)) (complexIncoming (originalKoszulComplex K hs d) i) (complexOutgoing (originalKoszulComplex K hs
  d) i) (originalIncoming_preserves K hs d hrank i) (originalOutgoing_preserves K hs d hrank i) (complexIncomingOutgoing (originalKoszulComplex K hs d) i) n :=
  associatedHomologyEquiv _ _ _ _ _ _ _ _ n (originalIncoming_liftsCycles K hs d hrank i) (originalOutgoing_liftsCycles K hs d hrank i)
end
variable {K X Y X' Y' : Type u} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup X'] [Module K X'] [AddCommGroup Y'] [Module K Y']
variable {P : Type u} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
theorem canonicalKoszulCoefficientEquiv_filtered (i n : ℕ) (x : Set.powersetCard (Fin d) i →₀ BarycentricRing (P := P) K) : canonicalKoszulCoefficientEquiv K hs d i x ∈
  (originalKoszulFiltration K hs d i).level n ↔ x ∈ (barycentricKoszulFiltration (P := P) K d i).level n := by sorry
def koszulGradeComparison (hrank : ∀ p : P, faceRank p ≤ d) (i n : ℕ) : Grade (barycentricKoszulFiltration (P := P) K d i) n ≃ₗ[K] Grade (originalKoszulFiltration K hs d i) n
  := by sorry
def canonicalKoszulGradeComparison (i n : ℕ) : Grade (barycentricKoszulFiltration (P := P) K d i) n ≃ₗ[K] Grade (originalKoszulFiltration K hs d i) n := gradeEquiv _ _
  (canonicalKoszulCoefficientEquiv K hs d i) (canonicalKoszulCoefficientEquiv_filtered K hs d i) n
theorem koszulGradeComparison_eq_canonical (i n : ℕ) : koszulGradeComparison K hs d hrank i n = canonicalKoszulGradeComparison K hs d i n := by sorry
theorem barycentricIncoming_preserves (i : ℕ) : Preserves (barycentricKoszulFiltration (P := P) K d (i + 1)) (barycentricKoszulFiltration (P := P) K d i) (complexIncoming
  (barycentricKoszulComplex (P := P) K d) i) := by sorry
theorem barycentricOutgoing_preserves (i : ℕ) : Preserves (barycentricKoszulFiltration (P := P) K d i) (barycentricKoszulFiltration (P := P) K d (i - 1)) (complexOutgoing
  (barycentricKoszulComplex (P := P) K d) i) := by sorry
abbrev originalGradedKoszulHomology (i n : ℕ) := GradedHomology (originalKoszulFiltration K hs d (i + 1)) (originalKoszulFiltration K hs d i) (originalKoszulFiltration K hs d
  (i - 1)) (complexIncoming (originalKoszulComplex K hs d) i) (complexOutgoing (originalKoszulComplex K hs d) i) (originalIncoming_preserves K hs d hrank i)
  (originalOutgoing_preserves K hs d hrank i) (complexIncomingOutgoing (originalKoszulComplex K hs d) i) n
abbrev barycentricGradedKoszulHomology (i n : ℕ) := GradedHomology (barycentricKoszulFiltration (P := P) K d (i + 1)) (barycentricKoszulFiltration (P := P) K d i)
  (barycentricKoszulFiltration (P := P) K d (i - 1)) (complexIncoming (barycentricKoszulComplex (P := P) K d) i) (complexOutgoing (barycentricKoszulComplex (P := P) K d) i)
  (barycentricIncoming_preserves K d i) (barycentricOutgoing_preserves K d i) (complexIncomingOutgoing (barycentricKoszulComplex (P := P) K d) i) n
def koszulGradedHomologyComparison (i n : ℕ) : barycentricGradedKoszulHomology (P := P) K d i n ≃ₗ[K] originalGradedKoszulHomology K hs d hrank i n := by sorry
theorem koszulGradedHomologyComparison_formula (i n : ℕ) : ∃ hin hout, koszulGradedHomologyComparison K hs d hrank i n = chainHomologyEquiv _ _ _ _ _ _ (koszulGradeComparison
  K hs d hrank (i + 1) n) (koszulGradeComparison K hs d hrank i n) (koszulGradeComparison K hs d hrank (i - 1) n) hin hout := by sorry
def originalAssociatedBarycentricHomology (i n : ℕ) : Grade (originalKoszulHomologyFiltration K hs d i) n ≃ₗ[K] barycentricGradedKoszulHomology (P := P) K d i n :=
  (originalKoszulAssociatedHomology K hs d hrank i n).trans (koszulGradedHomologyComparison K hs d hrank i n).symm
end FourPapers.Universal
namespace FourPapers.FilteredHomology
variable {K X Y Z : Type*} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]
def PreservesPair (F : Filtration (K := K) X) (G : Filtration (K := K) Y) (H : Filtration (K := K) Z) (p : X →ₗ[K] Y →ₗ[K] Z) : Prop := ∀ r s x y, x ∈ F.level (r + 1) → y ∈
  G.level (s + 1) → p x y ∈ H.level (r + s + 1)
variable (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
  (H : Filtration (K := K) Z) (p : X →ₗ[K] Y →ₗ[K] Z) (hp : PreservesPair F G H p)
def levelBilinearProduct (r s : ℕ) :
    F.level (r + 1) →ₗ[K] G.level (s + 1) →ₗ[K] H.level (r + s + 1) where
  toFun x :=
    { toFun := fun y => ⟨p x.val y.val, hp r s x.val y.val x.property y.property⟩
      map_add' y z := Subtype.ext (map_add (p x.val) y.val z.val)
      map_smul' c y := Subtype.ext (map_smul (p x.val) c y.val) }
  map_add' x z := by
    ext y
    exact LinearMap.congr_fun (map_add p x.val z.val) y.val
  map_smul' c x := by
    ext y
    exact LinearMap.congr_fun (map_smul p c x.val) y.val
def levelBilinearClass (r s : ℕ) : F.level (r + 1) →ₗ[K] G.level (s + 1) →ₗ[K] Grade H (r + s) := (levelBilinearProduct F G H p hp r s).compr₂ (lowerInLevel H (r + s)).mkQ
theorem levelBilinearClass_left_lower (r s : ℕ) : lowerInLevel F r ≤ LinearMap.ker (levelBilinearClass F G H p hp r s) := by sorry
theorem levelBilinearClass_right_lower (r s : ℕ) : lowerInLevel G s ≤ LinearMap.ker (levelBilinearClass F G H p hp r s).flip := by sorry
def gradeBilinearProduct (r s : ℕ) : Grade F r →ₗ[K] Grade G s →ₗ[K] Grade H (r + s) := (levelBilinearClass F G H p hp r s).liftQ₂ _ _ (levelBilinearClass_left_lower F G H p
  hp r s) (levelBilinearClass_right_lower F G H p hp r s)
end FourPapers.FilteredHomology
namespace FourPapers.Universal
section
open CliffordAlgebra
variable {K B C : Type*} [CommRing K] [CommRing B] [Algebra K B] [Fintype C]
abbrev CoefficientExterior (B C : Type*) [CommRing B] := ExteriorAlgebra B (C → B)
end
section
open CommAlg CliffordAlgebra
open FourPapers.FilteredHomology
variable {K B : Type u} {C : Type} [CommRing K] [CommRing B] [Algebra K B]
  [Fintype C] [LinearOrder C]
def coefficientExteriorBasis : Module.Basis (Finset C) B (CoefficientExterior B C) := (Pi.basisFun B C).ExteriorAlgebra
def coefficientExteriorLift (i : ℕ) : (Set.powersetCard C i →₀ B) →ₗ[K] CoefficientExterior B C := ((coefficientExteriorBasis (B := B) (C := C)).repr.symm.toLinearMap.comp
  (Finsupp.lmapDomain B B Subtype.val)).restrictScalars K
def coefficientExteriorProjection (i : ℕ) : CoefficientExterior B C →ₗ[K] (Set.powersetCard C i →₀ B) := ((Finsupp.lsubtypeDomain {F : Finset C | F.card = i}).comp
  (coefficientExteriorBasis (B := B) (C := C)).repr.toLinearMap).restrictScalars K
abbrev coefficientExteriorOutgoing (γ : C → B) (i : ℕ) := ((parameterKoszulComplex (K := K) γ).d i (i - 1)).hom
theorem coefficientExteriorIncomingOutgoing (γ : C → B) (i : ℕ) : (coefficientExteriorOutgoing (K := K) γ i).comp (parameterKoszulDifferential (K := K) γ i) = 0 := by sorry
abbrev CoefficientKoszulHomology (γ : C → B) (i : ℕ) := Homology (parameterKoszulDifferential (K := K) γ i) (coefficientExteriorOutgoing (K := K) γ i)
  (coefficientExteriorIncomingOutgoing γ i)
end
set_option backward.isDefEq.respectTransparency.types false
open FourPapers.FilteredHomology
section
variable {K B : Type u} {C : Type} [CommRing K] [CommRing B] [Algebra K B]
  [Fintype C] [LinearOrder C]
def coefficientKoszulProduct (i j : ℕ) : (Set.powersetCard C i →₀ B) →ₗ[K] (Set.powersetCard C j →₀ B) →ₗ[K] (Set.powersetCard C (i + j) →₀ B) := ((LinearMap.mul K
  (CoefficientExterior B C)).compl₁₂ (coefficientExteriorLift (K := K) i) (coefficientExteriorLift (K := K) j)).compr₂ (coefficientExteriorProjection (K := K) (i + j))
theorem coefficientKoszulProduct_cycle (γ : C → B) (i j : ℕ) (x : Set.powersetCard C i →₀ B) (y : Set.powersetCard C j →₀ B) (hx : coefficientExteriorOutgoing (K := K) γ i x =
  0) (hy : coefficientExteriorOutgoing (K := K) γ j y = 0) : coefficientExteriorOutgoing (K := K) γ (i + j) (coefficientKoszulProduct (K := K) i j x y) = 0 := by sorry
def coefficientKoszulCycleProduct (γ : C → B) (i j : ℕ) :
    LinearMap.ker (coefficientExteriorOutgoing (K := K) γ i) →ₗ[K] LinearMap.ker (coefficientExteriorOutgoing (K := K) γ j) →ₗ[K]
        LinearMap.ker (coefficientExteriorOutgoing (K := K) γ (i + j)) where
  toFun x :=
    { toFun := fun y => ⟨coefficientKoszulProduct (K := K) i j x.val y.val, coefficientKoszulProduct_cycle γ i j x.val y.val x.property y.property⟩
      map_add' y z := Subtype.ext (map_add (coefficientKoszulProduct (K := K) i j x.val) y.val z.val)
      map_smul' c y := Subtype.ext (map_smul (coefficientKoszulProduct (K := K) i j x.val) c y.val) }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact LinearMap.congr_fun (map_add (coefficientKoszulProduct (K := K) i j) x.val z.val) y.val
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact LinearMap.congr_fun (map_smul (coefficientKoszulProduct (K := K) i j) c x.val) y.val
def coefficientKoszulCycleProductClass (γ : C → B) (i j : ℕ) : LinearMap.ker (coefficientExteriorOutgoing (K := K) γ i) →ₗ[K] LinearMap.ker (coefficientExteriorOutgoing (K :=
  K) γ j) →ₗ[K] CoefficientKoszulHomology (K := K) γ (i + j) := (coefficientKoszulCycleProduct (K := K) γ i j).compr₂ (homologyClass (parameterKoszulDifferential (K := K) γ (i
  + j)) (coefficientExteriorOutgoing (K := K) γ (i + j)) (coefficientExteriorIncomingOutgoing γ (i + j)))
theorem coefficientKoszulCycleProductClass_left_boundary (γ : C → B) (i j : ℕ) : LinearMap.range (boundaryMap (parameterKoszulDifferential (K := K) γ i)
  (coefficientExteriorOutgoing (K := K) γ i) (coefficientExteriorIncomingOutgoing γ i)) ≤ LinearMap.ker (coefficientKoszulCycleProductClass (K := K) γ i j) := by sorry
theorem coefficientKoszulCycleProductClass_right_boundary (γ : C → B) (i j : ℕ) : LinearMap.range (boundaryMap (parameterKoszulDifferential (K := K) γ j)
  (coefficientExteriorOutgoing (K := K) γ j) (coefficientExteriorIncomingOutgoing γ j)) ≤ LinearMap.ker (coefficientKoszulCycleProductClass (K := K) γ i j).flip := by sorry
def coefficientKoszulHomologyProduct (γ : C → B) (i j : ℕ) : CoefficientKoszulHomology (K := K) γ i →ₗ[K] CoefficientKoszulHomology (K := K) γ j →ₗ[K]
  CoefficientKoszulHomology (K := K) γ (i + j) := (coefficientKoszulCycleProductClass (K := K) γ i j).liftQ₂ _ _ (coefficientKoszulCycleProductClass_left_boundary γ i j)
  (coefficientKoszulCycleProductClass_right_boundary γ i j)
end
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ)
theorem originalKoszulProduct_filtered (hrank : ∀ p : P, faceRank p ≤ d) (i j r s : ℕ) (x : Set.powersetCard (Fin d) i →₀ FaceRing K hs) (y : Set.powersetCard (Fin d) j →₀
  FaceRing K hs) (hx : x ∈ (originalKoszulFiltration K hs d i).level (r + 1)) (hy : y ∈ (originalKoszulFiltration K hs d j).level (s + 1)) : coefficientKoszulProduct (K := K)
  i j x y ∈ (originalKoszulFiltration K hs d (i + j)).level (r + s + 1) := by sorry
theorem barycentricKoszulProduct_filtered (hrank : ∀ p : P, faceRank p ≤ d) (i j r s : ℕ) (x : Set.powersetCard (Fin d) i →₀ BarycentricRing (P := P) K) (y : Set.powersetCard
  (Fin d) j →₀ BarycentricRing (P := P) K) (hx : x ∈ (barycentricKoszulFiltration (P := P) K d i).level (r + 1)) (hy : y ∈ (barycentricKoszulFiltration (P := P) K d j).level
  (s + 1)) : coefficientKoszulProduct (K := K) i j x y ∈ (barycentricKoszulFiltration (P := P) K d (i + j)).level (r + s + 1) := by sorry
end FourPapers.Universal
namespace FourPapers.FilteredHomology
set_option backward.isDefEq.respectTransparency.types false
variable {K Y Z : Type*} [CommRing K] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]
theorem cycleToGradeCycle_surjective (G : Filtration (K := K) Y) (H : Filtration (K := K) Z) (g : Y →ₗ[K] Z) (hg : Preserves G H g) (lift : LiftsCycles G H g) (n : ℕ) :
  Function.Surjective (cycleToGradeCycle G H g hg n) := by sorry
end FourPapers.FilteredHomology
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency.types false
open FourPapers.FilteredHomology
section
variable {K B : Type u} {C : Type} [CommRing K] [CommRing B] [Algebra K B]
  [Fintype C] [LinearOrder C]
variable (γ : C → B) (F : ∀ i : ℕ, Filtration (K := K) (Set.powersetCard C i →₀ B))
abbrev coefficientHomologyFiltration (i : ℕ) := homologyFiltration (F i) (parameterKoszulDifferential (K := K) γ i) (coefficientExteriorOutgoing (K := K) γ i)
  (coefficientExteriorIncomingOutgoing γ i)
variable (hp : ∀ i j, PreservesPair (F i) (F j) (F (i + j))
  (coefficientKoszulProduct (K := K) i j))
section
include hp
theorem coefficientKoszulHomologyProduct_filtered (i j : ℕ) : PreservesPair (coefficientHomologyFiltration γ F i) (coefficientHomologyFiltration γ F j)
  (coefficientHomologyFiltration γ F (i + j)) (coefficientKoszulHomologyProduct (K := K) γ i j) := by sorry
end
def coefficientHomologyGradeProduct (i j r s : ℕ) : Grade (coefficientHomologyFiltration γ F i) r →ₗ[K] Grade (coefficientHomologyFiltration γ F j) s →ₗ[K] Grade
  (coefficientHomologyFiltration γ F (i + j)) (r + s) := gradeBilinearProduct _ _ _ (coefficientKoszulHomologyProduct (K := K) γ i j)
  (coefficientKoszulHomologyProduct_filtered γ F hp i j) r s
def coefficientFilteredCycleProduct (i j r s : ℕ) :
    cycleLevel (F i) (coefficientExteriorOutgoing (K := K) γ i) (r + 1) →ₗ[K]
      cycleLevel (F j) (coefficientExteriorOutgoing (K := K) γ j) (s + 1) →ₗ[K]
        cycleLevel (F (i + j)) (coefficientExteriorOutgoing (K := K) γ (i + j)) (r + s + 1) where
  toFun x :=
    { toFun := fun y => ⟨coefficientKoszulCycleProduct (K := K) γ i j x.val y.val, hp i j r s x.val.val y.val.val x.property y.property⟩
      map_add' y z := by
        apply Subtype.ext
        exact map_add (coefficientKoszulCycleProduct (K := K) γ i j x.val) y.val z.val
      map_smul' c y := by
        apply Subtype.ext
        exact map_smul (coefficientKoszulCycleProduct (K := K) γ i j x.val) c y.val }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact LinearMap.congr_fun (map_add (coefficientKoszulCycleProduct (K := K) γ i j) x.val z.val) y.val
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact LinearMap.congr_fun (map_smul (coefficientKoszulCycleProduct (K := K) γ i j) c x.val) y.val
variable (hD : ∀ i, Preserves (F (i + 1)) (F i) (parameterKoszulDifferential (K := K) γ i))
  (hL : ∀ i, LiftsCycles (F (i + 1)) (F i) (parameterKoszulDifferential (K := K) γ i))
section
include hD
theorem coefficientOutgoing_preserves (i : ℕ) : Preserves (F i) (F (i - 1)) (coefficientExteriorOutgoing (K := K) γ i) := by sorry
end
section
include hL
theorem coefficientOutgoing_lifts (i : ℕ) : LiftsCycles (F i) (F (i - 1)) (coefficientExteriorOutgoing (K := K) γ i) := by sorry
end
abbrev coefficientGradedKoszulHomology (i r : ℕ) := GradedHomology (F (i + 1)) (F i) (F (i - 1)) (parameterKoszulDifferential (K := K) γ i) (coefficientExteriorOutgoing (K :=
  K) γ i) (hD i) (coefficientOutgoing_preserves γ F hD i) (coefficientExteriorIncomingOutgoing γ i) r
abbrev coefficientGradeCycles (i r : ℕ) := LinearMap.ker (gradeMap (F i) (F (i - 1)) (coefficientExteriorOutgoing (K := K) γ i) (coefficientOutgoing_preserves γ F hD i) r)
def coefficientGradedCycleProduct (i j r s : ℕ) :
    coefficientGradeCycles γ F hD i r →ₗ[K] coefficientGradeCycles γ F hD j s →ₗ[K] coefficientGradeCycles γ F hD (i + j) (r + s) where
  toFun x :=
    { toFun := fun y => ⟨gradeBilinearProduct (F i) (F j) (F (i + j))
        (coefficientKoszulProduct (K := K) i j) (hp i j) r s x.val y.val, by
        obtain ⟨x, rfl⟩ := cycleToGradeCycle_surjective (F i) (F (i - 1))
          (coefficientExteriorOutgoing (K := K) γ i) (coefficientOutgoing_preserves γ F hD i)
          (coefficientOutgoing_lifts γ F hL i) r x
        obtain ⟨y, rfl⟩ := cycleToGradeCycle_surjective (F j) (F (j - 1))
          (coefficientExteriorOutgoing (K := K) γ j) (coefficientOutgoing_preserves γ F hD j)
          (coefficientOutgoing_lifts γ F hL j) s y
        exact (cycleToGradeCycle (F (i + j)) (F (i + j - 1))
          (coefficientExteriorOutgoing (K := K) γ (i + j))
          (coefficientOutgoing_preserves γ F hD (i + j)) (r + s)
          (coefficientFilteredCycleProduct γ F hp i j r s x y)).property⟩
      map_add' y z := by
        apply Subtype.ext
        exact map_add (gradeBilinearProduct _ _ _ _ (hp i j) r s x.val) y.val z.val
      map_smul' c y := by
        apply Subtype.ext
        exact map_smul (gradeBilinearProduct _ _ _ _ (hp i j) r s x.val) c y.val }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact LinearMap.congr_fun (map_add (gradeBilinearProduct _ _ _ _ (hp i j) r s) x.val z.val) y.val
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact LinearMap.congr_fun (map_smul (gradeBilinearProduct _ _ _ _ (hp i j) r s) c x.val) y.val
def coefficientGradedCycleProductClass (i j r s : ℕ) : coefficientGradeCycles γ F hD i r →ₗ[K] coefficientGradeCycles γ F hD j s →ₗ[K] coefficientGradedKoszulHomology γ F hD
  (i + j) (r + s) := (coefficientGradedCycleProduct γ F hp hD hL i j r s).compr₂ (homologyClass _ _ _)
theorem coefficientGradedCycleProductClass_left_zero (i j r s : ℕ) (x : coefficientGradeCycles γ F hD i r) (y : coefficientGradeCycles γ F hD j s) (hx : (homologyClass _ _ _ x
  : coefficientGradedKoszulHomology γ F hD i r) = 0) : coefficientGradedCycleProductClass γ F hp hD hL i j r s x y = 0 := by sorry
theorem coefficientGradedCycleProductClass_right_zero (i j r s : ℕ) (x : coefficientGradeCycles γ F hD i r) (y : coefficientGradeCycles γ F hD j s) (hy : (homologyClass _ _ _
  y : coefficientGradedKoszulHomology γ F hD j s) = 0) : coefficientGradedCycleProductClass γ F hp hD hL i j r s x y = 0 := by sorry
def coefficientGradedHomologyProduct (i j r s : ℕ) :
    coefficientGradedKoszulHomology γ F hD i r →ₗ[K] coefficientGradedKoszulHomology γ F hD j s →ₗ[K]
        coefficientGradedKoszulHomology γ F hD (i + j) (r + s) := (coefficientGradedCycleProductClass γ F hp hD hL i j r s).liftQ₂ _ _
    (by
      rintro x ⟨a, rfl⟩
      apply LinearMap.ext
      intro y
      apply coefficientGradedCycleProductClass_left_zero γ F hp hD hL i j r s _ y
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨a, rfl⟩)
    (by
      rintro y ⟨a, rfl⟩
      apply LinearMap.ext
      intro x
      apply coefficientGradedCycleProductClass_right_zero γ F hp hD hL i j r s x _
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨a, rfl⟩)
end
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
theorem parameterKoszulComplex_incoming_eq {B : Type u} {C : Type} [CommRing B] [Algebra K B] [Fintype C] [LinearOrder C] (γ : C → B) (i : ℕ) : complexIncoming
  (parameterKoszulComplex (K := K) γ) i = parameterKoszulDifferential (K := K) γ i := by sorry
section
variable {X Y Z : Type*} [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z]
theorem gradeMap_eq_of_eq (F : Filtration (K := K) X) (G : Filtration (K := K) Y) (f f' : X →ₗ[K] Y) (hf : Preserves F G f) (hf' : Preserves F G f') (h : f = f') (n : ℕ) :
  gradeMap F G f hf n = gradeMap F G f' hf' n := by sorry
def homologyIncomingNormalization (f f' : X →ₗ[K] Y) (g : Y →ₗ[K] Z)
    (hfg : g.comp f = 0) (hfg' : g.comp f' = 0) (h : f = f') :
    Homology f g hfg ≃ₗ[K] Homology f' g hfg' := Submodule.quotEquivOfEq _ _ (by subst f'; rfl)
end
section
variable {B : Type u} {C : Type} [CommRing B] [Algebra K B] [Fintype C] [LinearOrder C] (γ : C → B)
def parameterHomologyNormalization (i : ℕ) : CoefficientKoszulHomology (K := K) γ i ≃ₗ[K] complexKernelHomology (parameterKoszulComplex (K := K) γ) i :=
  homologyIncomingNormalization K (parameterKoszulDifferential (K := K) γ i) (complexIncoming (parameterKoszulComplex (K := K) γ) i) (complexOutgoing (parameterKoszulComplex
  (K := K) γ) i) (coefficientExteriorIncomingOutgoing γ i) (complexIncomingOutgoing (parameterKoszulComplex (K := K) γ) i) (parameterKoszulComplex_incoming_eq K γ i).symm
variable (F : ∀ i, Filtration (K := K) (Set.powersetCard C i →₀ B))
theorem parameterHomologyNormalization_filtered (i n : ℕ) (x : CoefficientKoszulHomology (K := K) γ i) : parameterHomologyNormalization K γ i x ∈ (homologyFiltration (F i)
  (complexIncoming (parameterKoszulComplex (K := K) γ) i) (complexOutgoing (parameterKoszulComplex (K := K) γ) i) (complexIncomingOutgoing (parameterKoszulComplex (K := K) γ)
  i)).level n ↔ x ∈ (coefficientHomologyFiltration γ F i).level n := by sorry
def parameterHomologyGradeNormalization (i n : ℕ) : Grade (coefficientHomologyFiltration γ F i) n ≃ₗ[K] Grade (homologyFiltration (F i) (complexIncoming
  (parameterKoszulComplex (K := K) γ) i) (complexOutgoing (parameterKoszulComplex (K := K) γ) i) (complexIncomingOutgoing (parameterKoszulComplex (K := K) γ) i)) n :=
  gradeEquiv _ _ (parameterHomologyNormalization K γ i) (parameterHomologyNormalization_filtered K γ F i) n
variable (hD : ∀ i, Preserves (F (i + 1)) (F i) (parameterKoszulDifferential (K := K) γ i))
  (hI : ∀ i, Preserves (F (i + 1)) (F i)
    (complexIncoming (parameterKoszulComplex (K := K) γ) i))
  (hO : ∀ i, Preserves (F i) (F (i - 1))
    (complexOutgoing (parameterKoszulComplex (K := K) γ) i))
def parameterGradedHomologyNormalization (i n : ℕ) : coefficientGradedKoszulHomology γ F hD i n ≃ₗ[K] GradedHomology (F (i + 1)) (F i) (F (i - 1)) (complexIncoming
  (parameterKoszulComplex (K := K) γ) i) (complexOutgoing (parameterKoszulComplex (K := K) γ) i) (hI i) (hO i) (complexIncomingOutgoing (parameterKoszulComplex (K := K) γ) i)
  n := homologyIncomingNormalization K (gradeMap (F (i + 1)) (F i) (parameterKoszulDifferential (K := K) γ i) (hD i) n) (gradeMap (F (i + 1)) (F i) (complexIncoming
  (parameterKoszulComplex (K := K) γ) i) (hI i) n) (gradeMap (F i) (F (i - 1)) (complexOutgoing (parameterKoszulComplex (K := K) γ) i) (hO i) n) (gradeMap_comp (F (i + 1)) (F
  i) (F (i - 1)) (parameterKoszulDifferential (K := K) γ i) (complexOutgoing (parameterKoszulComplex (K := K) γ) i) (hD i) (hO i) (coefficientExteriorIncomingOutgoing γ i) n)
  (gradeMap_comp (F (i + 1)) (F i) (F (i - 1)) (complexIncoming (parameterKoszulComplex (K := K) γ) i) (complexOutgoing (parameterKoszulComplex (K := K) γ) i) (hI i) (hO i)
  (complexIncomingOutgoing (parameterKoszulComplex (K := K) γ) i) n) (gradeMap_eq_of_eq K (F (i + 1)) (F i) (parameterKoszulDifferential (K := K) γ i) (complexIncoming
  (parameterKoszulComplex (K := K) γ) i) (hD i) (hI i) (parameterKoszulComplex_incoming_eq K γ i).symm n)
end
def barycentricCoefficientGradedHomologyEquiv (i n : ℕ) : coefficientGradedKoszulHomology (fun k : Fin d => barycentricRankParameter (P := P) K (k.val + 1))
  (barycentricKoszulFiltration (P := P) K d) (barycentricKoszulDifferential_preserves K d) i n ≃ₗ[K] barycentricGradedKoszulHomology (P := P) K d i n :=
  parameterGradedHomologyNormalization K (fun k : Fin d => barycentricRankParameter (P := P) K (k.val + 1)) (barycentricKoszulFiltration (P := P) K d)
  (barycentricKoszulDifferential_preserves K d) (barycentricIncoming_preserves K d) (barycentricOutgoing_preserves K d) i n
def barycentricGradedKoszulHomologyProduct (i j r s : ℕ) : barycentricGradedKoszulHomology (P := P) K d i r →ₗ[K] barycentricGradedKoszulHomology (P := P) K d j s →ₗ[K]
  barycentricGradedKoszulHomology (P := P) K d (i + j) (r + s) := ((coefficientGradedHomologyProduct (fun k : Fin d => barycentricRankParameter (P := P) K (k.val + 1))
  (barycentricKoszulFiltration (P := P) K d) (barycentricKoszulProduct_filtered K d hrank) (barycentricKoszulDifferential_preserves K d)
  (barycentricKoszulDifferential_liftsCycles K d) i j r s).compl₁₂ (barycentricCoefficientGradedHomologyEquiv (P := P) K d i r).symm.toLinearMap
  (barycentricCoefficientGradedHomologyEquiv (P := P) K d j s).symm.toLinearMap).compr₂ (barycentricCoefficientGradedHomologyEquiv (P := P) K d (i + j) (r + s)).toLinearMap
def originalCoefficientHomologyGradeEquiv (i n : ℕ) : Grade (coefficientHomologyFiltration (fun k : Fin d => faceRankParameter K hs (k.val + 1)) (originalKoszulFiltration K hs
  d) i) n ≃ₗ[K] Grade (originalKoszulHomologyFiltration K hs d i) n := parameterHomologyGradeNormalization K (fun k : Fin d => faceRankParameter K hs (k.val + 1))
  (originalKoszulFiltration K hs d) i n
def originalAssociatedHomologyProduct (i j r s : ℕ) : Grade (originalKoszulHomologyFiltration K hs d i) r →ₗ[K] Grade (originalKoszulHomologyFiltration K hs d j) s →ₗ[K] Grade
  (originalKoszulHomologyFiltration K hs d (i + j)) (r + s) := ((coefficientHomologyGradeProduct (fun k : Fin d => faceRankParameter K hs (k.val + 1))
  (originalKoszulFiltration K hs d) (originalKoszulProduct_filtered K hs d hrank) i j r s).compl₁₂ (originalCoefficientHomologyGradeEquiv K hs d i r).symm.toLinearMap
  (originalCoefficientHomologyGradeEquiv K hs d j s).symm.toLinearMap).compr₂ (originalCoefficientHomologyGradeEquiv K hs d (i + j) (r + s)).toLinearMap
theorem originalAssociatedBarycentricHomology_multiplicative (i j r s : ℕ) (x : Grade (originalKoszulHomologyFiltration K hs d i) r) (y : Grade
  (originalKoszulHomologyFiltration K hs d j) s) : originalAssociatedBarycentricHomology K hs d hrank (i + j) (r + s) (originalAssociatedHomologyProduct K hs d hrank i j r s x
  y) = barycentricGradedKoszulHomologyProduct K d hrank i j r s (originalAssociatedBarycentricHomology K hs d hrank i r x) (originalAssociatedBarycentricHomology K hs d hrank
  j s y) := by sorry
end FourPapers.Universal
