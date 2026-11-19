module

public import ToricPower.DualDiagonalFramedResolution
public import ToricPower.DualDiagonalTopCellClass
public import ToricPower.TopHomologyFunctor
public import ToricPower.DualDiagonalBoundaryScalar

/-!
# The genuine affine top quotient on every Laurent generator

The weight inclusions below enter the original ring-linear dual complex
through its proved full-character complex isomorphism. Their induced
top classes are the fixed ambient classes. In particular, no actual
top-cell monomial generator becomes zero in the specified top quotient.
This is a calculation of the original quotient, not a choice of new
coordinates made to force nonvanishing.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (k : Type) [Field k] (A : Fin s → Fin n → ℤ)
  (S T : Set (Fin s)) (frames : ∀ q, DiagonalCellFrames A S T q)

local notation "R" => DiagonalChartRing k A S T
local notation "K" => diagonalFramedDualComplex k A S T frames
local notation "F" => ModuleCat.restrictScalars (algebraMap k R)
local notation "L" => diagonalFramedDualScalarComplex k A S T frames

/-- The original ring-linear quotient followed by the actual boundary
module frame. -/
def diagonalFramedDualTopQuotient :
    (K).X n ⟶ dualDiagonalBoundaryModule A S T k :=
  (K).pOpcycles n ≫
    ((K).isoHomologyι n (n+1) (by simp)
      (diagonalFramedDualComplex_top_differential k A S T frames)).inv ≫
        (diagonalFramedDualTopModuleIso k A S T frames).hom

/-- A character fiber enters the actual scalar restriction of the
original dual complex, with its original differential. -/
def diagonalFramedDualWeightInclusion (u : Fin n → ℤ) :
    dualDiagonalWeightComplex A S T u k ⟶ L :=
  ModuleDirectSum.complexInclusion k (fun v => dualDiagonalWeightComplex A S T v k) u ≫
    (diagonalFramedDualAllWeightIso k A S T frames).inv

/-- The specified inclusion retains the literal original Laurent
generator, including its total character and normalized cell. -/
theorem diagonalFramedDualWeightInclusion_generator
    (u : Fin n → ℤ) (q : ℕ) (i : DualDiagonalWeightIndex A S T u q) (a : k) :
    (diagonalFramedDualWeightInclusion k A S T frames u).f q
        ((translatedWeightCellularCoordinates A (dualDiagonalWeightAllowed A S T u)
          (dualDiagonalWeightAllowed_map A S T u) k q).symm (Finsupp.single i a)) =
      (diagonalFramedDualScalarCoordinates k A S T frames q).symm
        (Finsupp.single (⟨u,i⟩ : DualDiagonalAllWeightIndex A S T q) a) := by
  change (diagonalFramedDualScalarCoordinates k A S T frames q).symm
      (dualDiagonalAllWeightCoordinates k A S T q
        ((ModuleDirectSum.complexInclusion k (fun v => dualDiagonalWeightComplex A S T v k) u).f q
          ((translatedWeightCellularCoordinates A (dualDiagonalWeightAllowed A S T u)
            (dualDiagonalWeightAllowed_map A S T u) k q).symm (Finsupp.single i a)))) = _
  apply congrArg (diagonalFramedDualScalarCoordinates k A S T frames q).symm
  exact ModuleDirectSum.complexCoordinates_inclusion_generator k
    (fun u => dualDiagonalWeightComplex A S T u k)
    (fun u q => DualDiagonalWeightIndex A S T u q)
    (fun u q => translatedWeightCellularCoordinates A (dualDiagonalWeightAllowed A S T u)
      (dualDiagonalWeightAllowed_map A S T u) k q) q u i a

/-- The scalar top quotient agrees with its specified character
component and the fixed ambient orientation. -/
@[reassoc]
theorem diagonalFramedDualWeightInclusion_topClass
    (u : Fin n → ℤ) (nonempty : (dualDiagonalStrip A S T u).Nonempty) :
    HomologicalComplex.homologyMap
        (diagonalFramedDualWeightInclusion k A S T frames u) n ≫
      (((K).sc n).mapHomologyIso F).hom ≫
        (diagonalFramedDualTopScalarIso k A S T frames).hom =
      (dualDiagonalWeightTopClassIso A S T u k nonempty).hom ≫
        ModuleCat.ofHom (Finsupp.lsingle
          (⟨u,nonempty⟩ : DualDiagonalBoundaryWeight A S T) :
          k →ₗ[k] DualDiagonalBoundaryWeight A S T →₀ k) := by
  simp only [diagonalFramedDualWeightInclusion, HomologicalComplex.homologyMap_comp,
    diagonalFramedDualTopScalarIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_assoc]
  change HomologicalComplex.homologyMap
      (ModuleDirectSum.complexInclusion k (fun v => dualDiagonalWeightComplex A S T v k) u) n ≫
      HomologicalComplex.homologyMap (diagonalFramedDualAllWeightIso k A S T frames).inv n ≫
      HomologicalComplex.homologyMap (diagonalFramedDualAllWeightIso k A S T frames).hom n ≫
      (dualDiagonalAllWeightTopIso k A S T).hom = _
  rw [← Category.assoc (HomologicalComplex.homologyMap
      (diagonalFramedDualAllWeightIso k A S T frames).inv n),
    ← HomologicalComplex.homologyMap_comp, Iso.inv_hom_id,
    HomologicalComplex.homologyMap_id, Category.id_comp]
  exact dualDiagonalAllWeightTopIso_inclusion k A S T u nonempty

/-- The cochain quotient itself has the same specified weight
coordinates, before passing to homology. -/
@[reassoc]
theorem diagonalFramedDualWeightInclusion_topQuotient
    (u : Fin n → ℤ) (nonempty : (dualDiagonalStrip A S T u).Nonempty) :
    (diagonalFramedDualWeightInclusion k A S T frames u).f n ≫
        (F).map (diagonalFramedDualTopQuotient k A S T frames) ≫
        (dualDiagonalBoundaryRestrictionIso A S T k).hom =
      dualDiagonalWeightTopFunctional A S T u k nonempty ≫
        ModuleCat.ofHom (Finsupp.lsingle
          (⟨u,nonempty⟩ : DualDiagonalBoundaryWeight A S T) :
          k →ₗ[k] DualDiagonalBoundaryWeight A S T →₀ k) := by
  let outgoing := diagonalFramedDualComplex_top_differential k A S T frames
  have quotient := map_topHomologyQuotient F K n outgoing
  have natural := topHomologyQuotient_natural
    (dualDiagonalWeightComplex A S T u k) n
    (dualDiagonalWeightComplex_outgoing A S T u k)
    (mapComplex_top_differential F K n outgoing)
    (diagonalFramedDualWeightInclusion k A S T frames u)
  change (diagonalFramedDualWeightInclusion k A S T frames u).f n ≫
      (F).map ((K).pOpcycles n ≫
        ((K).isoHomologyι n (n+1) (by simp) outgoing).inv ≫
          (diagonalFramedDualTopModuleIso k A S T frames).hom) ≫
        (dualDiagonalBoundaryRestrictionIso A S T k).hom = _
  rw [← Category.assoc ((K).pOpcycles n)
    ((K).isoHomologyι n (n+1) (by simp) outgoing).inv
    (diagonalFramedDualTopModuleIso k A S T frames).hom, Functor.map_comp]
  have frame : (F).map (diagonalFramedDualTopModuleIso k A S T frames).hom ≫
      (dualDiagonalBoundaryRestrictionIso A S T k).hom =
      (diagonalFramedDualTopScalarIso k A S T frames).hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    rfl
  rw [Category.assoc, frame]
  have quotient' := congrArg (fun g => g ≫ (((K).sc n).mapHomologyIso F).hom) quotient
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at quotient'
  rw [quotient']
  calc
    _ = (dualDiagonalWeightComplex A S T u k).pOpcycles n ≫
        ((dualDiagonalWeightComplex A S T u k).isoHomologyι n (n+1) (by simp)
          (dualDiagonalWeightComplex_outgoing A S T u k)).inv ≫
        HomologicalComplex.homologyMap
          (diagonalFramedDualWeightInclusion k A S T frames u) n ≫
        (((K).sc n).mapHomologyIso F).hom ≫
        (diagonalFramedDualTopScalarIso k A S T frames).hom := by
      simpa only [Category.assoc] using congrArg
        (fun g => g ≫ (((K).sc n).mapHomologyIso F).hom ≫
          (diagonalFramedDualTopScalarIso k A S T frames).hom) natural
    _ = _ := by
      rw [diagonalFramedDualWeightInclusion_topClass]
      rfl

/-- Its full coefficient is supported at exactly the original total
character and is the fixed ambient scalar of that actual top cell. -/
theorem diagonalFramedDualTopQuotient_weight_generator
    (u : Fin n → ℤ) (i : DualDiagonalStripCell A S T u n)
    (nonempty : (dualDiagonalStrip A S T u).Nonempty) :
    (diagonalFramedDualTopQuotient k A S T frames)
      ((diagonalFramedDualWeightInclusion k A S T frames u).f n
        ((dualDiagonalWeightCoordinates A S T u k n).symm (Finsupp.single i 1))) =
      Finsupp.single (⟨u,nonempty⟩ : DualDiagonalBoundaryWeight A S T)
        (dualDiagonalWeightTopFunctional A S T u k nonempty
          ((dualDiagonalWeightCoordinates A S T u k n).symm (Finsupp.single i 1))) :=
  ConcreteCategory.congr_hom
    (diagonalFramedDualWeightInclusion_topQuotient k A S T frames u nonempty)
    ((dualDiagonalWeightCoordinates A S T u k n).symm (Finsupp.single i 1))

/-- Each actual characteristic-cell generator of each full weight has
nonzero image under the original ring-linear top quotient. -/
theorem diagonalFramedDualTopQuotient_weight_generator_ne_zero
    (u : Fin n → ℤ) (i : DualDiagonalStripCell A S T u n) :
    (diagonalFramedDualTopQuotient k A S T frames)
      ((diagonalFramedDualWeightInclusion k A S T frames u).f n
        ((dualDiagonalWeightCoordinates A S T u k n).symm (Finsupp.single i 1))) ≠ 0 := by
  have nonempty : (dualDiagonalStrip A S T u).Nonempty := ⟨_, i.property⟩
  intro zero
  rw [diagonalFramedDualTopQuotient_weight_generator k A S T frames u i nonempty] at zero
  exact dualDiagonalWeightTopFunctional_single_ne_zero A S T u k i nonempty
    (Finsupp.single_eq_zero.mp zero)

/-- In the original free module basis, every actual top-cell monomial
has nonzero image under the specified ring-linear top quotient. -/
theorem diagonalFramedDualTopQuotient_monomial_ne_zero
    (c : NormalizedCell A n) (p : rayCharacterMonoid A S × rayCharacterMonoid A T) :
    (diagonalFramedDualTopQuotient k A S T frames)
      ((diagonalFramedDualCoordinates k A S T frames n).symm
        (Finsupp.single c (AddMonoidAlgebra.single p 1))) ≠ 0 := by
  let x := (frames n).dualCell c p
  have h := diagonalFramedDualTopQuotient_weight_generator_ne_zero k A S T frames x.1
    (dualDiagonalWeightCellEquiv A S T x.1 n x.2)
  rw [dualDiagonalWeightCoordinates_symm_single,
    diagonalFramedDualWeightInclusion_generator] at h
  change (diagonalFramedDualTopQuotient k A S T frames)
    ((diagonalFramedDualScalarCoordinates k A S T frames n).symm
      (Finsupp.single ((frames n).dualCell c p) 1)) ≠ 0 at h
  rw [diagonalFramedDualScalarCoordinates_symm_single] at h
  exact h

/-- The full image of each original monomial basis vector has one
literal total weight and one nonzero ambient scalar. -/
theorem diagonalFramedDualTopQuotient_monomial_value
    (c : NormalizedCell A n) (p : rayCharacterMonoid A S × rayCharacterMonoid A T) :
    ∃ (w : DualDiagonalBoundaryWeight A S T) (a : k),
      w.val = (frames n).dualWeight c p ∧ a ≠ 0 ∧
      (diagonalFramedDualTopQuotient k A S T frames)
        ((diagonalFramedDualCoordinates k A S T frames n).symm
          (Finsupp.single c (AddMonoidAlgebra.single p 1))) = Finsupp.single w a := by
  let x := (frames n).dualCell c p
  let i := dualDiagonalWeightCellEquiv A S T x.1 n x.2
  have nonempty : (dualDiagonalStrip A S T x.1).Nonempty := ⟨_, i.property⟩
  refine ⟨⟨x.1, nonempty⟩,
    dualDiagonalWeightTopFunctional A S T x.1 k nonempty
      ((dualDiagonalWeightCoordinates A S T x.1 k n).symm (Finsupp.single i 1)),
    rfl, dualDiagonalWeightTopFunctional_single_ne_zero A S T x.1 k i nonempty, ?_⟩
  have value := diagonalFramedDualTopQuotient_weight_generator k A S T frames x.1 i nonempty
  rw [dualDiagonalWeightCoordinates_symm_single,
    diagonalFramedDualWeightInclusion_generator] at value
  change (diagonalFramedDualTopQuotient k A S T frames)
    ((diagonalFramedDualScalarCoordinates k A S T frames n).symm
      (Finsupp.single ((frames n).dualCell c p) 1)) = _ at value
  rw [diagonalFramedDualScalarCoordinates_symm_single] at value
  dsimp only [i] at value ⊢
  simpa only [dualDiagonalWeightCoordinates_symm_single] using value

end ToricPower.IntegralArrangement

end
