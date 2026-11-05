module

public import Recovery.Unimodular.ProductLatticeCoordinates
public import Recovery.Unimodular.ProductMatroidCoordinates
public import Recovery.Unimodular.ProductIntrinsic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set TauCeti.Toric

namespace Unimodular.OriginalComponents

open ComponentLattice LatticeCoordinates

variable {n : ℕ} {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {ι : N →+ V}

abbrev ImageSystem (b : Module.Basis (Fin n) ℤ N) (U : Set N) := latticeEquiv b '' U

theorem imageLabel_vectors (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) (u : U) :
    embed (imageLabelEquiv b U u).val = realEquiv hι b (ι u.val) :=
  (coordinates_commute hι b u.val).symm

def componentIndexEquiv (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) :
    MatroidComponents.Component (VectorMatroid.ofFamily (K := ℝ) (fun u : U => ι u.val)) ≃
      Components (ImageSystem b U) :=
  MatroidCoordinates.componentEquiv (fun u : U => ι u.val)
    (fun u : ImageSystem b U => embed u.val) (realEquiv hι b) (imageLabelEquiv b U)
    (imageLabel_vectors hι b U)

@[simp] theorem componentIndexEquiv_apply (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (U : Set N) (u : U) :
    componentIndexEquiv hι b U
      (MatroidComponents.component (VectorMatroid.ofFamily (K := ℝ) (fun u : U => ι u.val)) u) =
    MatroidComponents.component (represented (ImageSystem b U)) (imageLabelEquiv b U u) :=
  MatroidCoordinates.componentEquiv_component _ _ _ _ _ u

abbrev OriginalLineComponents (ι : N →+ V) (U : Set N) :=
  MatroidComponents.Component (LineMatroid.matroid (K := ℝ) (fun u : U => ι u.val))

/-- The coordinate component labels are rigorously identified with the
connected components of the original, literal line matroid in V. -/
def originalLineIndex (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0) :
    Components (ImageSystem b U) ≃ OriginalLineComponents ι U :=
  (componentIndexEquiv hι b U).symm.trans
    (LineMatroid.componentEquiv (K := ℝ) (fun u : U => ι u.val) hnz)

@[simp] theorem originalLineIndex_apply (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0) (u : U) :
    originalLineIndex hι b U hnz
        (MatroidComponents.component (represented (ImageSystem b U)) (imageLabelEquiv b U u)) =
      MatroidComponents.component (LineMatroid.matroid (K := ℝ) (fun u : U => ι u.val))
        (LineMatroid.projection (K := ℝ) (fun u : U => ι u.val) u) := by
  change (LineMatroid.componentEquiv (K := ℝ) (fun u : U => ι u.val) hnz)
    ((componentIndexEquiv hι b U).symm
      (MatroidComponents.component (represented (ImageSystem b U)) (imageLabelEquiv b U u))) = _
  rw [← componentIndexEquiv_apply hι b U u, Equiv.symm_apply_apply,
    LineMatroid.componentEquiv_component]

/-- Original vectors whose literal line belongs to the specified canonical
component. No coordinate vectors occur in the carrier. -/
def originalPart (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0) (c : Components (ImageSystem b U)) : Set N :=
  Subtype.val '' {u : U |
    MatroidComponents.component (LineMatroid.matroid (K := ℝ) (fun u : U => ι u.val))
      (LineMatroid.projection (K := ℝ) (fun u : U => ι u.val) u) =
        originalLineIndex hι b U hnz c}

theorem originalPart_image (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0) (c : Components (ImageSystem b U)) :
    latticeEquiv b '' originalPart hι b U hnz c = part (ImageSystem b U) c := by
  ext x
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨imageLabelEquiv b U u, ?_, rfl⟩
    apply (originalLineIndex hι b U hnz).injective
    rw [originalLineIndex_apply]
    exact hu
  · rintro ⟨v, hv, rfl⟩
    let u := (imageLabelEquiv b U).symm v
    have he : imageLabelEquiv b U u = v := (imageLabelEquiv b U).apply_symm_apply v
    refine ⟨u.val, ⟨u, ?_, rfl⟩, congrArg Subtype.val he⟩
    have hh := originalLineIndex_apply hι b U hnz u
    rw [he] at hh
    change MatroidComponents.component (represented (ImageSystem b U)) v = c at hv
    rw [hv] at hh
    exact hh.symm

/-- The coordinate factor lattice is the exact image of the integer span
of the original component vectors. Thus the integral direct summands are
intrinsic to the original configuration, not to the selected coordinates. -/
theorem original_integer_span_map (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0)
    (c : Components (ImageSystem b U)) :
    (Submodule.span ℤ (originalPart hι b U hnz c)).map (latticeEquiv b).toLinearMap =
      latticeSpan (ImageSystem b U) c := by
  rw [Submodule.map_span]
  change Submodule.span ℤ (latticeEquiv b '' originalPart hι b U hnz c) = _
  rw [originalPart_image]
  rfl

theorem original_real_span_map (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0)
    (c : Components (ImageSystem b U)) :
    (Submodule.span ℝ (ι '' originalPart hι b U hnz c)).map (realEquiv hι b).toLinearMap =
      realSpan (ImageSystem b U) c := by
  rw [Submodule.map_span, Set.image_image]
  have he : (fun x : N => realEquiv hι b (ι x)) = fun x => embed (latticeEquiv b x) :=
    funext (coordinates_commute hι b)
  change Submodule.span ℝ ((fun x : N => realEquiv hι b (ι x)) ''
    originalPart hι b U hnz c) = _
  rw [he, ← Set.image_image, originalPart_image]
  change Submodule.span ℝ (embed '' (Subtype.val '' _)) = _
  rw [Set.image_image]
  rfl

def originalEmbedding (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0) (c : Components (ImageSystem b U)) :
    Submodule.span ℤ (originalPart hι b U hnz c) →+
      Submodule.span ℝ (ι '' originalPart hι b U hnz c) where
  toFun x := ⟨ι x.val, by
    have hle : Submodule.span ℤ (originalPart hι b U hnz c) ≤
        ((Submodule.span ℝ (ι '' originalPart hι b U hnz c)).restrictScalars ℤ).comap
          ι.toIntLinearMap := by
      apply Submodule.span_le.mpr
      intro y hy
      exact Submodule.subset_span ⟨y, hy, rfl⟩
    exact hle x.property⟩
  map_zero' := Subtype.ext ι.map_zero
  map_add' x y := Subtype.ext (ι.map_add x.val y.val)

@[simp] theorem originalEmbedding_coe (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0)
    (c : Components (ImageSystem b U)) (x : Submodule.span ℤ (originalPart hι b U hnz c)) :
    (originalEmbedding hι b U hnz c x : V) = ι x.val := rfl

/-- An actual integral linear equivalence from the original canonical
sublattice to the corresponding coordinate factor. -/
def factorIntegralEquiv (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0) (c : Components (ImageSystem b U)) :
    Submodule.span ℤ (originalPart hι b U hnz c) ≃ₗ[ℤ] latticeSpan (ImageSystem b U) c :=
  (Submodule.equivMapOfInjective (latticeEquiv b).toLinearMap (latticeEquiv b).injective _).trans
    (LinearEquiv.ofEq _ _ (original_integer_span_map hι b U hnz c))

def factorRealEquiv (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0) (c : Components (ImageSystem b U)) :
    Submodule.span ℝ (ι '' originalPart hι b U hnz c) ≃ₗ[ℝ] realSpan (ImageSystem b U) c :=
  (Submodule.equivMapOfInjective (realEquiv hι b).toLinearMap (realEquiv hι b).injective _).trans
    (LinearEquiv.ofEq _ _ (original_real_span_map hι b U hnz c))

@[simp] theorem factorIntegralEquiv_coe (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0)
    (c : Components (ImageSystem b U)) (x : Submodule.span ℤ (originalPart hι b U hnz c)) :
    (factorIntegralEquiv hι b U hnz c x : Lattice n) = latticeEquiv b x.val := by
  simp only [factorIntegralEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    Submodule.coe_equivMapOfInjective_apply]
  rfl

@[simp] theorem factorRealEquiv_coe (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0)
    (c : Components (ImageSystem b U))
    (x : Submodule.span ℝ (ι '' originalPart hι b U hnz c)) :
    (factorRealEquiv hι b U hnz c x : Ambient n) = realEquiv hι b x.val := by
  simp only [factorRealEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    Submodule.coe_equivMapOfInjective_apply]
  rfl

theorem factorEquivs_compatible (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0)
    (c : Components (ImageSystem b U)) (x : Submodule.span ℤ (originalPart hι b U hnz c)) :
    factorRealEquiv hι b U hnz c (originalEmbedding hι b U hnz c x) =
      componentEmbedding (ImageSystem b U) c (factorIntegralEquiv hι b U hnz c x) := by
  apply Subtype.ext
  simp only [factorRealEquiv_coe, originalEmbedding_coe, componentEmbedding_coe,
    factorIntegralEquiv_coe]
  exact coordinates_commute hι b x.val

theorem originalFactor_isIntegralLattice (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0)
    (c : Components (ImageSystem b U))
    (hc : IsIntegralLattice (componentEmbedding (ImageSystem b U) c)) :
    IsIntegralLattice (originalEmbedding hι b U hnz c) :=
  (isIntegralLattice_congr (factorIntegralEquiv hι b U hnz c).toAddEquiv
    (factorRealEquiv hι b U hnz c) (factorEquivs_compatible hι b U hnz c)).mpr hc

end Unimodular.OriginalComponents

#print axioms Unimodular.OriginalComponents.componentIndexEquiv
#print axioms Unimodular.OriginalComponents.originalLineIndex_apply
#print axioms Unimodular.OriginalComponents.originalPart_image
#print axioms Unimodular.OriginalComponents.original_integer_span_map
#print axioms Unimodular.OriginalComponents.original_real_span_map
#print axioms Unimodular.OriginalComponents.factorEquivs_compatible
#print axioms Unimodular.OriginalComponents.originalFactor_isIntegralLattice
#check "UNIMODULAR_ORIGINAL_COMPONENTS_EOF_V1"
