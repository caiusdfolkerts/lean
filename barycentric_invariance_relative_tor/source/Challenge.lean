module
public import Mathlib
/-! Theorem 1.2 for relative pairs: the associated graded of each homogeneous Tor module is computed by the reduced cohomology of the rank-selected pairs. -/
@[expose] public section
namespace PalomarBarycentricTor
/-- Canonical cancellation and scalar-action laws used by the actual complexes. -/
theorem natRightCancelAdd : IsRightCancelAdd ℕ := by infer_instance
def naturalDown : ComplexShape ℕ := @ComplexShape.down ℕ _ natRightCancelAdd _
def naturalUp : ComplexShape ℕ := @ComplexShape.up ℕ _ natRightCancelAdd _
attribute [reducible] naturalDown naturalUp
theorem coefficientSMulComm {K : Type*} [CommRing K] : SMulCommClass K K K := by infer_instance
theorem functionScalarTower {V K : Type*} [CommRing K] : IsScalarTower K K (V → K) := by infer_instance
theorem exteriorScalarComm {V K : Type*} [CommRing K] : SMulCommClass K K (ExteriorAlgebra K (V → K)) := by infer_instance
theorem tensorPreservesZero {R : Type*} [CommRing R] (M : ModuleCat R) : ((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat R)).flip.obj M).PreservesZeroMorphisms := by infer_instance
attribute [instance 2200] natRightCancelAdd coefficientSMulComm functionScalarTower exteriorScalarComm tensorPreservesZero
end PalomarBarycentricTor
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
noncomputable def koszulComplex : HomologicalComplex (ModuleCat R) PalomarBarycentricTor.naturalDown := ChainComplex.of (fun n ↦ ModuleCat.of R (⋀[R]^n M))
    (fun n ↦ ModuleCat.ofHom (koszulComplex.d φ n))
    (fun n ↦ by rw [← ModuleCat.ofHom_comp, koszulComplex.d_comp_eq_zero, ModuleCat.ofHom_zero])
lemma koszulComplex.X_eq_exteriorPower (i : ℕ) : (koszulComplex φ).X i = ModuleCat.of R (⋀[R]^i M) := by sorry
lemma koszulComplex.d_eq_d (i : ℕ) : (koszulComplex φ).d (i + 1) i = ModuleCat.ofHom (koszulComplex.d φ i) := by sorry
end
namespace koszulComplex
open Category Limits Module ExteriorAlgebra
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) {N : Type v} [AddCommGroup N] [Module R N]
noncomputable def ofList (l : List R) := koszulComplex (Fintype.linearCombination R l.get)
lemma map_d_comm (f : M →ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ) (i : ℕ) : ModuleCat.ofHom.{max v u, u} (exteriorPower.map (i + 1) f) ≫ ModuleCat.ofHom.{max v u, u} (koszulComplex.d φ' i) =
  ModuleCat.ofHom.{max v u, u} (koszulComplex.d φ i) ≫ ModuleCat.ofHom.{max v u, u} (exteriorPower.map i f) := by sorry
noncomputable def map (f : M →ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ) : koszulComplex φ ⟶ koszulComplex φ' := ChainComplex.ofHom
    (fun i ↦ ModuleCat.ofHom (exteriorPower.map i f))
    (fun i ↦ by simpa [d_eq_d] using! map_d_comm φ f φ' h i)
section
variable {L : Type v} [AddCommGroup L] [Module R L]
noncomputable def isoOfEquiv (f : M ≃ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ) : koszulComplex φ ≅ koszulComplex φ' where
  hom := koszulComplex.map φ f φ' h
  inv := koszulComplex.map φ' f.symm φ ((f.comp_toLinearMap_symm_eq φ' φ).mpr h.symm)
  hom_inv_id := by
    ext i x
    change exteriorPower.map i f.symm.toLinearMap (exteriorPower.map i f.toLinearMap x) = x
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
    simp
  inv_hom_id := by
    ext i x
    change exteriorPower.map i f.toLinearMap (exteriorPower.map i f.symm.toLinearMap x) = x
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
    simp
end
section
variable (φ : M →ₗ[R] R)
noncomputable def zeroHomologyLinearEquivAux : (koszulComplex φ).homology 0 ≃ₗ[R] (⋀[R]^0 M) ⧸ (koszulComplex.d φ 0).range :=
  (((ChainComplex.isoHomologyι₀ (koszulComplex φ)).trans
    ((koszulComplex φ).opcyclesIsoSc' 1 0 0 (by simp) (by simp))).trans
      ((koszulComplex φ).sc' 1 0 0).moduleCatOpcyclesIso).toLinearEquiv
lemma d_zero_range_map : (koszulComplex.d φ 0).range.map (exteriorPower.zeroEquiv R _).toLinearMap = φ.range := by sorry
noncomputable def zeroHomologyOfListLinearEquiv (l : List R) : (ofList l).homology 0 ≃ₗ[R] R ⧸ Ideal.ofList l :=
  (zeroHomologyLinearEquivAux _).trans (Submodule.Quotient.equiv _ _ (exteriorPower.zeroEquiv R _)
    (by simp [koszulComplex.d_zero_range_map]))
end
open RingTheory.Sequence
lemma exactAt_of_isRegular (rs : List R) (reg : IsRegular R rs) (i : ℕ) (ne : i ≠ 0) : (ofList rs).ExactAt i := by sorry
end koszulComplex
namespace CommAlg.Koszul
section
open CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]
def resolutionOpcycles (K : HomologicalComplex (ModuleCat.{u} R) PalomarBarycentricTor.naturalDown) (hproj : ∀ n, Projective (K.X n)) (hexact : ∀ n, K.ExactAt (n + 1)) : ProjectiveResolution (K.opcycles 0) where
  complex := K
  projective := hproj
  π := (ChainComplex.toSingle₀Equiv K _).symm ⟨K.pOpcycles 0, K.d_pOpcycles 1 0⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        simp only [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
        refine ⟨?_, inferInstance⟩
        exact ShortComplex.exact_of_g_is_cokernel _ (K.opcyclesIsCokernel 1 0 (by simp))
      · exact K.shape 0 0 (by simp)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact hexact n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩
def transportResolution {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X) (e : X ≅ Y) : ProjectiveResolution Y where
  complex := P.complex
  projective := P.projective
  π := P.π ≫ (ChainComplex.single₀ _).map e.hom
def regularSequenceResolution (l : List R) (hl : RingTheory.Sequence.IsRegular R l) : ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.ofList l)) :=
  transportResolution
    (resolutionOpcycles (koszulComplex.ofList l)
      (fun n => by
        change Projective (ModuleCat.of R (⋀[R]^n (Fin l.length → R)))
        infer_instance)
      (fun n => koszulComplex.exactAt_of_isRegular l hl (n + 1) (by omega)))
    ((ChainComplex.isoHomologyι₀ (koszulComplex.ofList l)).symm ≪≫ (koszulComplex.zeroHomologyOfListLinearEquiv l).toModuleIso)
def coefficientComplex (l : List R) (M : ModuleCat.{u} R) : HomologicalComplex (ModuleCat.{u} R) PalomarBarycentricTor.naturalDown := (((CategoryTheory.MonoidalCategory.tensoringRight (ModuleCat R)).obj
  M).mapHomologicalComplex (ComplexShape.down ℕ)).obj (koszulComplex.ofList l)
end
section
variable {V : Type} {k : Type u} [CommRing k]
lemma ker_constantCoeff : RingHom.ker (constantCoeff : MvPolynomial V k →+* k) = idealOfVars V k := by sorry
def residueRingEquiv : (MvPolynomial V k ⧸ idealOfVars V k) ≃+* k := (Ideal.quotEquivOfEq ker_constantCoeff.symm).trans ((constantCoeff : MvPolynomial V k →+*
  k).quotientKerEquivOfRightInverse (fun a => constantCoeff_C V a))
@[simp] lemma residueRingEquiv_mk (f : MvPolynomial V k) : residueRingEquiv (Ideal.Quotient.mk (idealOfVars V k) f) = constantCoeff f := by sorry
end
section
open TensorProduct
variable {R : Type u} {V : Type} [CommRing R] [Fintype V] [LinearOrder V]
abbrev familyCoefficientComplex (x : V → R) (M : ModuleCat.{u} R) : HomologicalComplex (ModuleCat.{u} R) PalomarBarycentricTor.naturalDown := (((CategoryTheory.MonoidalCategory.tensoringRight (ModuleCat R)).obj
  M).mapHomologicalComplex (ComplexShape.down ℕ)).obj (koszulComplex (Fintype.linearCombination R x))
def coefficientCoordinates (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) : (familyCoefficientComplex x M).X i ≃ₗ[R] (Set.powersetCard V i →₀ M) :=
  TensorProduct.equivFinsuppOfBasisLeft ((Pi.basisFun R V).exteriorPower i)
def coordinateDifferential (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) : (Set.powersetCard V (i + 1) →₀ M) →ₗ[R] (Set.powersetCard V i →₀ M) :=
  let δ : (familyCoefficientComplex.{u} x M).X (i + 1) →ₗ[R]
      (familyCoefficientComplex.{u} x M).X i := ((familyCoefficientComplex.{u} x M).d (i + 1) i).hom
  (coefficientCoordinates.{u} x M i).toLinearMap.comp
    (δ.comp (coefficientCoordinates.{u} x M (i + 1)).symm.toLinearMap)
lemma coordinateDifferential_comp (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) : coordinateDifferential x M i ∘ₗ coordinateDifferential x M (i + 1) = 0 := by sorry
def coordinateComplex (x : V → R) (M : ModuleCat.{u} R) : HomologicalComplex (ModuleCat.{u} R) PalomarBarycentricTor.naturalDown := ChainComplex.of (fun i => ModuleCat.of R (Set.powersetCard V i →₀ M)) (fun i =>
  ModuleCat.ofHom (coordinateDifferential x M i)) (fun i => ModuleCat.hom_ext (coordinateDifferential_comp x M i))
@[simp] lemma coordinateComplex_d (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) : (coordinateComplex x M).d (i + 1) i = ModuleCat.ofHom (coordinateDifferential x M
  i) := by sorry
def coordinateComplexIso (x : V → R) (M : ModuleCat.{u} R) : familyCoefficientComplex x M ≅ coordinateComplex x M :=
  HomologicalComplex.Hom.isoOfComponents (fun i => (coefficientCoordinates x M i).toModuleIso)
    (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      rw [coordinateComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change coordinateDifferential x M j (coefficientCoordinates x M (j + 1) z) =
        coefficientCoordinates x M j (((familyCoefficientComplex x M).d (j + 1) j).hom z)
      simp only [coordinateDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply])
end
variable {V : Type} {k : Type u} [Fintype V] [LinearOrder V] [CommRing k]
def finiteVariableList : List (MvPolynomial V k) := List.ofFn (fun i : Fin (Fintype.card V) => X ((Fintype.equivFin V).symm i))
def finiteVariableIndex : Fin (finiteVariableList (V := V) (k := k)).length ≃ V :=
  (finCongr (by simp [finiteVariableList])).trans (Fintype.equivFin V).symm
theorem finite_variables_regular [Nontrivial k] : RingTheory.Sequence.IsRegular (MvPolynomial V k) (finiteVariableList (V := V) (k := k)) := by sorry
theorem ofList_finite_variables : Ideal.ofList (finiteVariableList (V := V) (k := k)) = idealOfVars V k := by sorry
abbrev FiniteResidue (V : Type) (k : Type u) [CommRing k] := MvPolynomial V k ⧸ idealOfVars V k
def finitePolynomialResolution [Nontrivial k] : ProjectiveResolution (ModuleCat.of (MvPolynomial V k) (FiniteResidue V k)) := transportResolution (regularSequenceResolution
  (finiteVariableList (V := V) (k := k)) finite_variables_regular) (Submodule.quotEquivOfEq _ _ (ofList_finite_variables (V := V) (k := k))).toModuleIso
def finiteVariableLinearEquiv : (Fin (finiteVariableList (V := V) (k := k)).length → MvPolynomial V k) ≃ₗ[MvPolynomial V k] (V → MvPolynomial V k) := LinearEquiv.funCongrLeft
  _ _ (finiteVariableIndex (V := V) (k := k)).symm
theorem finiteVariableLinearEquiv_comp : (Fintype.linearCombination (MvPolynomial V k) (X : V → MvPolynomial V k)) ∘ₗ (finiteVariableLinearEquiv (V := V) (k := k)).toLinearMap
  = Fintype.linearCombination (MvPolynomial V k) (finiteVariableList (V := V) (k := k)).get := by sorry
def finiteVariableKoszulIso : koszulComplex.ofList (finiteVariableList (V := V) (k := k)) ≅ koszulComplex (Fintype.linearCombination (MvPolynomial V k) (X : V → MvPolynomial V
  k)) := koszulComplex.isoOfEquiv _ finiteVariableLinearEquiv _ finiteVariableLinearEquiv_comp
def finiteCoefficientComplexIso (M : ModuleCat.{u} (MvPolynomial V k)) : coefficientComplex (finiteVariableList (V := V) (k := k)) M ≅ familyCoefficientComplex (X : V →
  MvPolynomial V k) M := (((CategoryTheory.MonoidalCategory.tensoringRight (ModuleCat (MvPolynomial V k))).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).mapIso
  finiteVariableKoszulIso
def finitePolynomialTor (i : ℕ) (M : ModuleCat.{u} (MvPolynomial V k)) : ModuleCat.{u} (MvPolynomial V k) := ((Tor' (ModuleCat (MvPolynomial V k)) i).obj (ModuleCat.of
  (MvPolynomial V k) (FiniteResidue V k))).obj M
def finitePolynomialTorIso [Nontrivial k] (i : ℕ) (M : ModuleCat.{u} (MvPolynomial V k)) : finitePolynomialTor i M ≅ (familyCoefficientComplex (X : V → MvPolynomial V k)
  M).homology i := (finitePolynomialResolution (V := V) (k := k)).isoLeftDerivedObj ((CategoryTheory.MonoidalCategory.tensoringRight _).obj M) i ≪≫
  (HomologicalComplex.homologyFunctor (ModuleCat (MvPolynomial V k)) (ComplexShape.down ℕ) i).mapIso (finiteCoefficientComplexIso M)
end CommAlg.Koszul
namespace CommAlg.Simplicial
open CliffordAlgebra
variable {V k : Type*} [Fintype V] [LinearOrder V] [CommRing k]
abbrev Ambient (V k : Type*) [Fintype V] [CommRing k] := ExteriorAlgebra k (V → k)
def basis : Module.Basis (Finset V) k (Ambient V k) := (Pi.basisFun k V).ExteriorAlgebra
def Chains (K : Finset V → Prop) (i : ℕ) : Submodule k (Ambient V k) := Submodule.span k (basis '' {s | K s ∧ s.card = i})
def Downward (K : Finset V → Prop) : Prop := ∀ ⦃s t⦄, t ⊆ s → K s → K t
abbrev boundary : Ambient V k →ₗ[k] Ambient V k := contractLeft (Q := (0 : QuadraticForm k (V → k))) (Fintype.linearCombination k (fun _ : V => (1 : k)))
lemma boundary_mem {K : Finset V → Prop} (hK : Downward K) {i : ℕ} {z : Ambient V k} (hz : z ∈ Chains K (i + 1)) : boundary z ∈ Chains K i := by sorry
end CommAlg.Simplicial
namespace CommAlg.Koszul
variable {V : Type} {k : Type u} [CommRing k]
def residueCoefficientModule : ModuleCat.{u} (MvPolynomial V k) := (ModuleCat.restrictScalars (constantCoeff : MvPolynomial V k →+* k)).obj (ModuleCat.of k k)
def residueCoefficientEquiv : FiniteResidue V k ≃ₗ[MvPolynomial V k] residueCoefficientModule (V := V) (k := k) where
  toFun := (residueRingEquiv (V := V) (k := k))
  invFun := (residueRingEquiv (V := V) (k := k)).symm
  left_inv := (residueRingEquiv (V := V) (k := k)).left_inv
  right_inv := (residueRingEquiv (V := V) (k := k)).right_inv
  map_add' := (residueRingEquiv (V := V) (k := k)).map_add
  map_smul' f q := by
    change (residueRingEquiv (V := V) (k := k)) (f • q) = constantCoeff f * (residueRingEquiv (V := V) (k := k)) q
    refine Quotient.inductionOn' q ?_
    intro p
    change (residueRingEquiv (V := V) (k := k))
      (Ideal.Quotient.mk (idealOfVars V k) (f * p)) = constantCoeff f * (residueRingEquiv (V := V) (k := k))
        (Ideal.Quotient.mk (idealOfVars V k) p)
    simp only [residueRingEquiv_mk, map_mul]
def residueCoefficientIso : ModuleCat.of (MvPolynomial V k) (FiniteResidue V k) ≅ residueCoefficientModule (V := V) (k := k) := residueCoefficientEquiv.toModuleIso
variable [Fintype V] [LinearOrder V]
def finitePolynomialTorCoefficientIso (i : ℕ) (M : ModuleCat.{u} (MvPolynomial V k)) : finitePolynomialTor i M ≅ ((Tor' (ModuleCat (MvPolynomial V k)) i).obj
  (residueCoefficientModule (V := V) (k := k))).obj M := ((Functor.flip (Tor' (ModuleCat (MvPolynomial V k)) i)).obj M).mapIso residueCoefficientIso
end CommAlg.Koszul
namespace FourPapers.Universal
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
def IsSimplicialPoset (P : Type*) [PartialOrder P] [OrderBot P] : Prop := ∀ p : P, ∃ n : ℕ, Nonempty (Set.Iic p ≃o Finset (Fin n))
def faceVertices (p : P) : Finset P := univ.filter fun a => IsAtom a ∧ a ≤ p
@[simp] theorem mem_faceVertices {p a : P} : a ∈ faceVertices p ↔ IsAtom a ∧ a ≤ p := by sorry
theorem faceVertices_mono : Monotone (faceVertices : P → Finset P) := by sorry
theorem existsUnique_subface (hs : IsSimplicialPoset P) (p : P) (s : Finset P) (hsu : s ⊆ faceVertices p) : ∃! x : Set.Iic p, faceVertices x.val = s := by sorry
def faceRank (p : P) : ℕ := (faceVertices p).card
@[simp] theorem faceRank_bot : faceRank (⊥ : P) = 0 := by sorry
theorem faceRank_strictMono (hs : IsSimplicialPoset P) : StrictMono (faceRank : P → ℕ) := by sorry
end
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
structure ModuleDiagram where
  obj : P → Type w
  [addCommGroup : ∀ p, AddCommGroup (obj p)]
  [module : ∀ p, Module K (obj p)]
  res : ∀ {p q}, q ≤ p → obj p →ₗ[K] obj q
  res_refl : ∀ p x, res (le_refl p) x = x
  res_comp : ∀ {p q r} (hqp : q ≤ p) (hrq : r ≤ q) x, res hrq (res hqp x) = res (hrq.trans hqp) x
attribute [instance] ModuleDiagram.addCommGroup ModuleDiagram.module
end FourPapers.Universal
namespace FourPapers.Universal.ModuleDiagram
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
variable {K P}
variable (D : ModuleDiagram K P)
def sections : Submodule K (∀ p, D.obj p) where
  carrier := {x | ∀ p q (h : q ≤ p), D.res h (x p) = x q}
  zero_mem' := by intros; simp
  add_mem' := by
    intro x y hx hy p q h
    simpa using congrArg₂ (· + ·) (hx p q h) (hy p q h)
  smul_mem' := by
    intro c x hx p q h
    simpa using congrArg (c • ·) (hx p q h)
end FourPapers.Universal.ModuleDiagram
namespace FourPapers.Universal
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
variable {K P}
structure CoherentEquiv (D E : ModuleDiagram K P) where
  component : ∀ p, D.obj p ≃ₗ[K] E.obj p
  naturality : ∀ p q (h : q ≤ p) x, E.res h (component p x) = component q (D.res h x)
end FourPapers.Universal
namespace FourPapers.Universal.CoherentEquiv
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
variable {K P}
variable {D E F : ModuleDiagram K P}
def symm (e : CoherentEquiv D E) : CoherentEquiv E D where
  component p := (e.component p).symm
  naturality p q h x := by
    apply (e.component q).injective
    simpa using (e.naturality p q h ((e.component p).symm x)).symm
def trans (e : CoherentEquiv D E) (f : CoherentEquiv E F) : CoherentEquiv D F where
  component p := (e.component p).trans (f.component p)
  naturality p q h x := by
    change F.res h (f.component p (e.component p x)) = f.component q (e.component q (D.res h x))
    rw [f.naturality, e.naturality]
def sectionEquiv (e : CoherentEquiv D E) : D.sections ≃ₗ[K] E.sections where
  toFun x := ⟨fun p => e.component p (x.val p), by
    intro p q h
    rw [e.naturality, x.property p q h]⟩
  invFun x := ⟨fun p => (e.component p).symm (x.val p), by
    intro p q h
    change D.res h (e.symm.component p (x.val p)) = e.symm.component q (x.val q)
    exact (e.symm.naturality p q h (x.val p)).trans
      (congrArg (e.symm.component q) (x.property p q h))⟩
  left_inv x := by
    refine Subtype.ext (funext fun p => ?_)
    exact (e.component p).symm_apply_apply (x.val p)
  right_inv x := by
    refine Subtype.ext (funext fun p => ?_)
    exact (e.component p).apply_symm_apply (x.val p)
  map_add' x y := by
    refine Subtype.ext (funext fun p => ?_)
    exact map_add (e.component p) (x.val p) (y.val p)
  map_smul' c x := by
    refine Subtype.ext (funext fun p => ?_)
    exact map_smul (e.component p) c (x.val p)
end FourPapers.Universal.CoherentEquiv
namespace FourPapers.Universal
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
section
variable (K : Type*) [CommRing K]
abbrev FaceVertex (p : P) := {a : P // IsAtom a ∧ a ≤ p}
abbrev PolynomialStalk (p : P) := MvPolynomial (FaceVertex p) K
def polynomialRestriction {p q : P} (hqp : q ≤ p) : PolynomialStalk K p →ₐ[K] PolynomialStalk K q := by
  classical
  exact aeval fun a => if h : a.val ≤ q then X ⟨a.val, a.property.1, h⟩ else 0
theorem polynomialRestriction_refl (p : P) : polynomialRestriction K (le_refl p) = AlgHom.id K (PolynomialStalk K p) := by sorry
theorem polynomialRestriction_comp {p q r : P} (hqp : q ≤ p) (hrq : r ≤ q) : (polynomialRestriction K hrq).comp (polynomialRestriction K hqp) = polynomialRestriction K
  (hrq.trans hqp) := by sorry
abbrev polynomialDiagram : ModuleDiagram K P where
  obj p := PolynomialStalk K p
  res h := (polynomialRestriction K h).toLinearMap
  res_refl p f := DFunLike.congr_fun (polynomialRestriction_refl K p) f
  res_comp hqp hrq f := DFunLike.congr_fun (polynomialRestriction_comp K hqp hrq) f
end
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
def palomarFaceRingModule (hs : IsSimplicialPoset P) : Module K (FaceRing K hs) := inferInstance
attribute [instance 2400] palomarFaceRingModule
def faceRingGenerator (hs : IsSimplicialPoset P) (p : P) : FaceRing K hs := Ideal.Quotient.mk (faceIdeal K hs) (faceSymbol K p)
def faceRankParameter (hs : IsSimplicialPoset P) (i : ℕ) : FaceRing K hs := ∑ p ∈ univ.filter (fun p : P => faceRank p = i), faceRingGenerator K hs p
def faceParameterAction (hs : IsSimplicialPoset P) (d : ℕ) : MvPolynomial (Fin d) K →ₐ[K] FaceRing K hs := MvPolynomial.aeval fun i => faceRankParameter K hs (i.val + 1)
end
section
variable {V : Type*} [Fintype V]
def rankWeight (d r : ℕ) : ℤ := (r : ℤ) * (2 * (d : ℤ) - r)
end
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P] (K : Type*) [CommRing K]
def stalkVertexSet (p q : P) : Finset (FaceVertex p) := univ.filter fun a => a.val ≤ q
@[simp] theorem stalkVertexSet_bot (p : P) : stalkVertexSet p (⊥ : P) = ∅ := by sorry
def faceProduct (p q : P) : PolynomialStalk K p := ∏ a ∈ stalkVertexSet p q, X a
def faceValue (p q : P) : PolynomialStalk K p :=
  if q ≤ p then faceProduct K p q else 0
def faceEvaluation (r : P) : FacePolynomial (P := P) K →ₐ[K] PolynomialStalk K r := MvPolynomial.aeval fun p => faceValue K r p.val
theorem faceEvaluation_relation (hs : IsSimplicialPoset P) (r : P) {f : FacePolynomial (P := P) K} (hf : f ∈ faceRelations K hs) : faceEvaluation K r f = 0 := by sorry
def faceRingEvaluation (hs : IsSimplicialPoset P) (r : P) : FaceRing K hs →ₐ[K] PolynomialStalk K r :=
  Ideal.Quotient.liftₐ (faceIdeal K hs) (faceEvaluation K r) (by
    change faceIdeal K hs ≤ RingHom.ker (faceEvaluation K r).toRingHom
    apply Ideal.span_le.mpr
    intro f hf
    exact faceEvaluation_relation K hs r hf)
end
section
variable {V K : Type*} [Fintype V] [DecidableEq V] [CommRing K]
abbrev BooleanFace (V : Type*) [DecidableEq V] := {F : Finset V // F.Nonempty}
def IsChainExponent (a : BooleanFace V →₀ ℕ) : Prop := ∀ F ∈ a.support, ∀ G ∈ a.support, F.val ⊆ G.val ∨ G.val ⊆ F.val
end
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
def subfaceOfVertexSet (hs : IsSimplicialPoset P) (p : P) (s : Finset (FaceVertex p)) : Set.Iic p :=
  (existsUnique_subface hs p (s.image Subtype.val) (by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := mem_image.mp ha
    exact mem_faceVertices.mpr v.property)).choose
theorem stalkVertexSet_subfaceOfVertexSet (hs : IsSimplicialPoset P) (p : P) (s : Finset (FaceVertex p)) : stalkVertexSet p (subfaceOfVertexSet hs p s).val = s := by sorry
def booleanFaceInclusion (hs : IsSimplicialPoset P) (p : P) : BooleanFace (FaceVertex p) ↪ NonzeroFace P where
  toFun F := ⟨(subfaceOfVertexSet hs p F.val).val, by
    intro hbot
    have he := stalkVertexSet_subfaceOfVertexSet hs p F.val
    rw [hbot, stalkVertexSet_bot] at he
    exact F.property.ne_empty he.symm⟩
  inj' F G h := by
    apply Subtype.ext
    have he : (subfaceOfVertexSet hs p F.val).val = (subfaceOfVertexSet hs p G.val).val := congrArg (fun z : NonzeroFace P => z.val) h
    have hv := congrArg (stalkVertexSet p) he
    simpa only [stalkVertexSet_subfaceOfVertexSet] using hv
theorem booleanFaceInclusion_le (hs : IsSimplicialPoset P) (p : P) (F : BooleanFace (FaceVertex p)) : (booleanFaceInclusion hs p F).val ≤ p := by sorry
section
variable (K : Type*) [CommRing K]
def BarycentricAllowed (a : NonzeroFace P →₀ ℕ) : Prop := ∀ p ∈ a.support, ∀ q ∈ a.support, p.val ≤ q.val ∨ q.val ≤ p.val
end
abbrev StandardFaceIndex (P : Type*) [PartialOrder P] [OrderBot P] := {a : NonzeroFace P →₀ ℕ // BarycentricAllowed a}
def standardCarrier (a : StandardFaceIndex P) : P :=
  if h : a.val.support.Nonempty then
    (Finset.exists_max_image a.val.support (fun p : NonzeroFace P => faceRank p.val) h).choose.val
  else ⊥
theorem standardCarrier_le_iff (hs : IsSimplicialPoset P) (a : StandardFaceIndex P) (p : P) : standardCarrier a ≤ p ↔ ∀ q ∈ a.val.support, q.val ≤ p := by sorry
theorem booleanFaceInclusion_range_iff (hs : IsSimplicialPoset P) (p : P) (q : NonzeroFace P) : q ∈ Set.range (booleanFaceInclusion hs p) ↔ q.val ≤ p := by sorry
theorem standardExponent_map_booleanFaceInclusion (hs : IsSimplicialPoset P) (p : P) {a : BooleanFace (FaceVertex p) →₀ ℕ} (ha : IsChainExponent a) : BarycentricAllowed
  (a.mapDomain (booleanFaceInclusion hs p)) := by sorry
theorem chainExponent_comap_booleanFaceInclusion (hs : IsSimplicialPoset P) (p : P) {a : NonzeroFace P →₀ ℕ} (ha : BarycentricAllowed a) : IsChainExponent (a.comapDomain
  (booleanFaceInclusion hs p) (booleanFaceInclusion hs p).injective.injOn) := by sorry
abbrev StandardInside (p : P) := {a : StandardFaceIndex P // standardCarrier a ≤ p}
def standardInsideEquiv (hs : IsSimplicialPoset P) (p : P) : {a : BooleanFace (FaceVertex p) →₀ ℕ // IsChainExponent a} ≃ StandardInside p where
  toFun a := ⟨⟨a.val.mapDomain (booleanFaceInclusion hs p), standardExponent_map_booleanFaceInclusion hs p a.property⟩, by
      apply (standardCarrier_le_iff hs _ p).mpr
      intro q hq
      rw [Finsupp.mapDomain_support_of_injective (booleanFaceInclusion hs p).injective] at hq
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hq
      exact booleanFaceInclusion_le hs p F⟩
  invFun a := ⟨a.val.val.comapDomain (booleanFaceInclusion hs p)
    (booleanFaceInclusion hs p).injective.injOn, chainExponent_comap_booleanFaceInclusion hs p a.val.property⟩
  left_inv a := Subtype.ext
    (Finsupp.comapDomain_mapDomain _ (booleanFaceInclusion hs p).injective a.val)
  right_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    apply Finsupp.mapDomain_comapDomain _ (booleanFaceInclusion hs p).injective
    intro q hq
    exact (booleanFaceInclusion_range_iff hs p q).mpr
      ((standardCarrier_le_iff hs a.val p).mp a.property q hq)
end
section
variable {P I : Type*} [Preorder P] (K : Type*) [CommRing K] (carrier : I → P)
def coefficientStalk (p : P) : Submodule K (I →₀ K) := Finsupp.supported K K {i | carrier i ≤ p}
def coefficientRestriction {p q : P} (_hqp : q ≤ p) : coefficientStalk K carrier p →ₗ[K] coefficientStalk K carrier q := (Finsupp.restrictDom K K {i | carrier i ≤ q}).comp
  (coefficientStalk K carrier p).subtype
@[simp] theorem coefficientRestriction_apply {p q : P} (hqp : q ≤ p) (x : coefficientStalk K carrier p) (i : I) : (coefficientRestriction K carrier hqp x).val i
  = if carrier i ≤ q then x.val i else 0 := by sorry
abbrev coefficientDiagram : ModuleDiagram K P where
  obj p := coefficientStalk K carrier p
  res h := coefficientRestriction K carrier h
  res_refl p x := by
    refine Subtype.ext (Finsupp.ext fun i => ?_)
    by_cases hi : carrier i ≤ p
    · simp [hi]
    · have hx := (Finsupp.mem_supported' K x.val).mp x.property i hi
      simp [hi, hx]
  res_comp := by
    intro p q r hqp hrq x
    refine Subtype.ext (Finsupp.ext fun i => ?_)
    by_cases hi : carrier i ≤ r
    · have hiq := hi.trans hrq
      simp [hi, hiq]
    · simp [hi]
def coefficientSection : (I →₀ K) →ₗ[K] (coefficientDiagram K carrier).sections where
  toFun x := ⟨fun p => Finsupp.restrictDom K K {i | carrier i ≤ p} x, by
    intro p q hqp
    refine Subtype.ext (Finsupp.ext fun i => ?_)
    change (if carrier i ≤ q then (if carrier i ≤ p then x i else 0) else 0) = (if carrier i ≤ q then x i else 0)
    by_cases hi : carrier i ≤ q
    · have hip := hi.trans hqp
      simp [hi, hip]
    · simp [hi]⟩
  map_add' x y := by
    refine Subtype.ext (funext fun p => ?_)
    exact map_add (Finsupp.restrictDom K K {i | carrier i ≤ p}) x y
  map_smul' c x := by
    refine Subtype.ext (funext fun p => ?_)
    exact map_smul (Finsupp.restrictDom K K {i | carrier i ≤ p}) c x
def coefficientAtCarrier (x : (coefficientDiagram K carrier).sections) (i : I) : K := (x.val (carrier i)).val i
variable [Fintype P]
def coefficientAssembly (x : (coefficientDiagram K carrier).sections) : I →₀ K :=
  Finsupp.onFinset (Finset.univ.biUnion fun p => (x.val p).val.support)
    (coefficientAtCarrier K carrier x) (by
      intro i hi
      apply Finset.mem_biUnion.mpr
      exact ⟨carrier i, Finset.mem_univ _, Finsupp.mem_support_iff.mpr hi⟩)
theorem coefficientAssembly_section (x : I →₀ K) : coefficientAssembly K carrier (coefficientSection K carrier x) = x := by sorry
theorem coefficientSection_assembly (x : (coefficientDiagram K carrier).sections) : coefficientSection K carrier (coefficientAssembly K carrier x) = x := by sorry
def coefficientSectionEquiv : (I →₀ K) ≃ₗ[K] (coefficientDiagram K carrier).sections where
  toFun := coefficientSection K carrier
  invFun := coefficientAssembly K carrier
  left_inv := coefficientAssembly_section K carrier
  right_inv := coefficientSection_assembly K carrier
  map_add' := (coefficientSection K carrier).map_add
  map_smul' := (coefficientSection K carrier).map_smul
def sectionsFromCoherentCoefficients (D : ModuleDiagram K P) (e : CoherentEquiv D (coefficientDiagram K carrier)) : D.sections ≃ₗ[K] (I →₀ K) := e.sectionEquiv.trans
  (coefficientSectionEquiv K carrier).symm
end
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P] (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
def faceRingMonomial (a : NonzeroFace P →₀ ℕ) : FaceRing K hs := Ideal.Quotient.mk (faceIdeal K hs) (monomial a 1)
end
section
variable {V T K : Type*} [Fintype V] [DecidableEq V] [Fintype T] [CommRing K]
def subsetExponent (F : Finset V) : V →₀ ℕ := ∑ v ∈ F, Finsupp.single v 1
end
section
variable {V : Type*} [Fintype V] [LinearOrder V]
def chainVertexMap : (BooleanFace V →₀ ℕ) →ₗ[ℕ] (V →₀ ℕ) := Finsupp.linearCombination ℕ (fun F => subsetExponent F.val)
def vertexHeight (a : V →₀ ℕ) : ℕ := Finset.univ.sup (fun v => a v)
def exponentLayer (a : V →₀ ℕ) (k : Fin (vertexHeight a)) : BooleanFace V := ⟨Finset.univ.filter (fun v => k.val < a v), by
    obtain ⟨v, hv, hkv⟩ := Finset.lt_sup_iff.mp k.isLt
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hkv⟩⟩⟩
def layerExponent (a : V →₀ ℕ) : BooleanFace V →₀ ℕ := ∑ k : Fin (vertexHeight a), Finsupp.single (exponentLayer a k) 1
theorem layerExponent_isChain (a : V →₀ ℕ) : IsChainExponent (layerExponent a) := by sorry
theorem chainVertexMap_layerExponent (a : V →₀ ℕ) : chainVertexMap (layerExponent a) = a := by sorry
theorem chainVertexMap_chain_injective : Function.Injective (fun a : {a : BooleanFace V →₀ ℕ // IsChainExponent a} => chainVertexMap a.val) := by sorry
def chainVertexEquiv : {a : BooleanFace V →₀ ℕ // IsChainExponent a} ≃ (V →₀ ℕ) where
  toFun a := chainVertexMap a.val
  invFun a := ⟨layerExponent a, layerExponent_isChain a⟩
  left_inv a := chainVertexMap_chain_injective (chainVertexMap_layerExponent (chainVertexMap a.val))
  right_inv := chainVertexMap_layerExponent
variable {W : Type*} [Fintype W] [DecidableEq W]
def chainVertexEquivUnordered : {a : BooleanFace W →₀ ℕ // IsChainExponent a} ≃ (W →₀ ℕ) := by
  letI : LinearOrder W := LinearOrder.lift' (Fintype.equivFin W) (Fintype.equivFin W).injective
  exact chainVertexEquiv
end
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
section
variable (K : Type*) [CommRing K]
variable {K}
def standardVertexEquiv (hs : IsSimplicialPoset P) (p : P) : StandardInside p ≃ (FaceVertex p →₀ ℕ) := (standardInsideEquiv hs p).symm.trans chainVertexEquivUnordered
def polynomialStandardBasis (hs : IsSimplicialPoset P) (p : P) : Module.Basis (StandardInside p) K (PolynomialStalk K p) := (MvPolynomial.basisMonomials (FaceVertex p)
  K).reindex (standardVertexEquiv hs p).symm
end
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
theorem faceRingEvaluation_naturality {p q : P} (hqp : q ≤ p) (f : FaceRing K hs) : polynomialRestriction K hqp (faceRingEvaluation K hs p f) = faceRingEvaluation K hs q f :=
  by sorry
def faceRingSection : FaceRing K hs →ₗ[K] (polynomialDiagram (P := P) K).sections where
  toFun f := ⟨fun p => faceRingEvaluation K hs p f, fun p q hqp => faceRingEvaluation_naturality K hs hqp f⟩
  map_add' f g := by
    refine Subtype.ext (funext fun p => ?_)
    exact map_add (faceRingEvaluation K hs p) f g
  map_smul' c f := by
    refine Subtype.ext (funext fun p => ?_)
    exact map_smul (faceRingEvaluation K hs p) c f
def polynomialStandardCoordinates (p : P) : PolynomialStalk K p ≃ₗ[K] coefficientStalk K (standardCarrier (P := P)) p := (polynomialStandardBasis (K := K) hs p).repr.trans
  (Finsupp.supportedEquivFinsupp {a : StandardFaceIndex P | standardCarrier a ≤ p}).symm
attribute [local instance 2450] AddMonoidAlgebra.instModule in
theorem polynomialStandardCoordinates_naturality {p q : P} (hqp : q ≤ p) (f : PolynomialStalk K p) : coefficientRestriction K standardCarrier hqp
  (polynomialStandardCoordinates K hs p f) = polynomialStandardCoordinates K hs q (polynomialRestriction K hqp f) := by sorry
def polynomialCoefficientEquiv : CoherentEquiv (polynomialDiagram (P := P) K) (coefficientDiagram K (standardCarrier (P := P))) where
  component := polynomialStandardCoordinates K hs
  naturality p q hqp f := polynomialStandardCoordinates_naturality K hs hqp f
def polynomialSectionCoordinates : (polynomialDiagram (P := P) K).sections ≃ₗ[K] (StandardFaceIndex P →₀ K) := sectionsFromCoherentCoefficients K standardCarrier
  (polynomialDiagram K) (polynomialCoefficientEquiv K hs)
def standardFaceCombination : (StandardFaceIndex P →₀ K) →ₗ[K] FaceRing K hs := Finsupp.linearCombination K (fun a => faceRingMonomial K hs a.val)
theorem standardFaceCombination_surjective : Function.Surjective (standardFaceCombination K hs) := by sorry
theorem standardFaceCombination_coefficients (x : StandardFaceIndex P →₀ K) : polynomialSectionCoordinates K hs (faceRingSection K hs (standardFaceCombination K hs x)) = x :=
  by sorry
def standardFaceBasis : Module.Basis (StandardFaceIndex P) K (FaceRing K hs) :=
  Module.Basis.ofRepr (LinearEquiv.ofBijective (standardFaceCombination K hs) ⟨by
      intro x y hxy
      have h := congrArg (fun f => polynomialSectionCoordinates K hs (faceRingSection K hs f)) hxy
      simpa only [standardFaceCombination_coefficients] using h, standardFaceCombination_surjective K hs⟩).symm
def standardRankWeight (d : ℕ) (a : StandardFaceIndex P) : ℤ := a.val.sum (fun F n => (n : ℤ) * rankWeight d (faceRank F.val))
def standardOrdinaryDegree (a : StandardFaceIndex P) : ℕ := a.val.sum (fun F n => n * faceRank F.val)
def faceRestrictionIdeal (Q : Set P) : Ideal (FaceRing K hs) := Ideal.span {x | ∃ p : P, p ∉ Q ∧ x = faceRingGenerator K hs p}
end
variable {V C : Type*} [Fintype V] [Fintype C]
structure ProperlyColoredComplex (V C : Type*) where
  face : Finset V → Prop
  downward : ∀ ⦃s t : Finset V⦄, s ⊆ t → face t → face s
  color : V → C
  proper : ∀ s, face s → Set.InjOn color (s : Set V)
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
def rankColoredOrderComplex (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) : ProperlyColoredComplex (NonzeroFace P) (Fin d) where
  face s := ∀ p ∈ s, ∀ q ∈ s, p.val ≤ q.val ∨ q.val ≤ p.val
  downward := by
    intro s t hst ht p hp q hq
    exact ht p (hst hp) q (hst hq)
  color p := ⟨faceRank p.val - 1, by
    have hpos : 0 < faceRank p.val := by
      simpa only [faceRank_bot] using
        (faceRank_strictMono hs) (bot_lt_iff_ne_bot.mpr p.property)
    have hbound := hrank p.val
    omega⟩
  proper s hs' p hp q hq he := by
    have hpos (v : NonzeroFace P) : 0 < faceRank v.val := by
      simpa only [faceRank_bot] using
        (faceRank_strictMono hs) (bot_lt_iff_ne_bot.mpr v.property)
    have hr : faceRank p.val = faceRank q.val := by
      have hh := congrArg Fin.val he
      have hp' := hpos p
      have hq' := hpos q
      dsimp at hh
      omega
    apply Subtype.ext
    rcases hs' p hp q hq with hpq | hqp
    · by_contra hn
      exact (Nat.ne_of_lt ((faceRank_strictMono hs) (lt_of_le_of_ne hpq hn))) hr
    · by_contra hn
      exact (Nat.ne_of_lt ((faceRank_strictMono hs) (lt_of_le_of_ne hqp (Ne.symm hn)))) hr.symm
end FourPapers.Universal
namespace FourPapers.FilteredHomology
variable {K : Type*} [CommRing K]
structure Filtration (M : Type*) [AddCommGroup M] [Module K M] where
  level : ℕ → Submodule K M
  zero : level 0 = ⊥
  mono : Monotone level
  exhaustive : ∀ x : M, ∃ n, x ∈ level n
variable {X Y Z : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z]
def lowerInLevel (F : Filtration (K := K) X) (n : ℕ) : Submodule K (F.level (n + 1)) := (F.level n).comap (F.level (n + 1)).subtype
abbrev Grade (F : Filtration (K := K) X) (n : ℕ) := F.level (n + 1) ⧸ lowerInLevel F n
def boundaryMap (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) : X →ₗ[K] LinearMap.ker g := f.codRestrict _ (fun x => LinearMap.congr_fun hfg x)
abbrev Homology (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) := LinearMap.ker g ⧸ LinearMap.range (boundaryMap f g hfg)
def homologyClass (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) : LinearMap.ker g →ₗ[K] Homology f g hfg := (LinearMap.range (boundaryMap f g hfg)).mkQ
def cycleLevel (F : Filtration (K := K) Y) (g : Y →ₗ[K] Z) (n : ℕ) : Submodule K (LinearMap.ker g) := (F.level n).comap (LinearMap.ker g).subtype
def homologyLevel (F : Filtration (K := K) Y) (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) (n : ℕ) : Submodule K (Homology f g hfg) := (cycleLevel F g n).map
  (homologyClass f g hfg)
def homologyFiltration (F : Filtration (K := K) Y) (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) : Filtration (K := K) (Homology f g hfg) where
  level := homologyLevel F f g hfg
  zero := by simp [homologyLevel, cycleLevel, F.zero]
  mono := fun _ _ h => Submodule.map_mono (Submodule.comap_mono (F.mono h))
  exhaustive x := by
    obtain ⟨z, rfl⟩ := (LinearMap.range (boundaryMap f g hfg)).mkQ_surjective x
    obtain ⟨n, hn⟩ := F.exhaustive z.val
    exact ⟨n, z, hn, rfl⟩
end FourPapers.FilteredHomology
namespace FourPapers.Universal
section
open CommAlg
variable {K : Type u} {V : Type v} [CommRing K] [Fintype V] [LinearOrder V]
def augmentedFaceBoundary (Λ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (i : ℕ) : Simplicial.Chains (k := K) Λ (i + 1) →ₗ[K] Simplicial.Chains (k := K) Λ i :=
  (Simplicial.boundary.domRestrict (Simplicial.Chains Λ (i + 1))).codRestrict _ (fun x => Simplicial.boundary_mem hΛ x.property)
def relativeFaceSubmodule (Λ Λ₀ : Finset V → Prop) (i : ℕ) : Submodule K (Simplicial.Chains (k := K) Λ i) := (Simplicial.Chains Λ₀ i).comap (Simplicial.Chains Λ i).subtype
abbrev RelativeAugmentedChains (Λ Λ₀ : Finset V → Prop) (i : ℕ) := Simplicial.Chains (k := K) Λ i ⧸ relativeFaceSubmodule (K := K) Λ Λ₀ i
def relativeAugmentedBoundary (Λ Λ₀ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (hΛ₀ : Simplicial.Downward Λ₀) (i : ℕ) : RelativeAugmentedChains (K := K) Λ Λ₀ (i + 1) →ₗ[K] RelativeAugmentedChains (K := K) Λ Λ₀ i :=
  Submodule.mapQ _ _ (augmentedFaceBoundary Λ hΛ i) (by
    intro x hx
    exact Simplicial.boundary_mem hΛ₀ hx)
def relativeAugmentedCoboundary (Λ Λ₀ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (hΛ₀ : Simplicial.Downward Λ₀) (i : ℕ) : Module.Dual K (RelativeAugmentedChains (K := K)
  Λ Λ₀ i) →ₗ[K] Module.Dual K (RelativeAugmentedChains (K := K) Λ Λ₀ (i + 1)) := (relativeAugmentedBoundary Λ Λ₀ hΛ hΛ₀ i).dualMap
theorem relativeAugmentedCoboundary_square (Λ Λ₀ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (hΛ₀ : Simplicial.Downward Λ₀) (i : ℕ) : (relativeAugmentedCoboundary (K := K)
  Λ Λ₀ hΛ hΛ₀ (i + 1)).comp (relativeAugmentedCoboundary (K := K) Λ Λ₀ hΛ hΛ₀ i) = 0 := by sorry
def relativeAugmentedCochainComplex (Λ Λ₀ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (hΛ₀ : Simplicial.Downward Λ₀) : HomologicalComplex (ModuleCat.{max u v} K) PalomarBarycentricTor.naturalUp :=
  CochainComplex.of (fun i => ModuleCat.of K (Module.Dual K (RelativeAugmentedChains (K := K) Λ Λ₀ i))) (fun i => ModuleCat.ofHom (relativeAugmentedCoboundary Λ Λ₀ hΛ hΛ₀ i))
  (fun i => ModuleCat.hom_ext (relativeAugmentedCoboundary_square Λ Λ₀ hΛ hΛ₀ i))
def reducedRelativeCohomology (Λ Λ₀ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (hΛ₀ : Simplicial.Downward Λ₀) (q : ℤ) : ModuleCat.{max u v} K :=
  if -1 ≤ q then (relativeAugmentedCochainComplex (K := K) Λ Λ₀ hΛ hΛ₀).homology (q + 1).toNat
  else ModuleCat.of K (ULift.{v} (Fin 0 → K))
def rankSelection {C : Type*} [DecidableEq C] (D : ProperlyColoredComplex V C) (S : Finset C) : Finset V → Prop := fun F => D.face F ∧ F.image D.color ⊆ S
theorem rankSelection_downward {C : Type*} [DecidableEq C] (D : ProperlyColoredComplex V C) (S : Finset C) : Simplicial.Downward (rankSelection D S) := by sorry
end
section
open CategoryTheory.MonoidalCategory
section
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] [HasProjectiveResolutions C] {F G : C ⥤ D} [F.Additive] [G.Additive]
def leftDerivedOfNaturalIso (e : F ≅ G) (i : ℕ) : F.leftDerived i ≅ G.leftDerived i where
  hom := NatTrans.leftDerived e.hom i
  inv := NatTrans.leftDerived e.inv i
  hom_inv_id := by
    rw [← NatTrans.leftDerived_comp, e.hom_inv_id, NatTrans.leftDerived_id]
  inv_hom_id := by
    rw [← NatTrans.leftDerived_comp, e.inv_hom_id, NatTrans.leftDerived_id]
end
variable {R : Type u} [CommRing R]
def tensorOrderIso (M : ModuleCat.{u} R) : (tensoringRight (ModuleCat.{u} R)).obj M ≅ (tensoringLeft (ModuleCat.{u} R)).obj M :=
  NatIso.ofComponents (fun N => (TensorProduct.comm R N M).toModuleIso) (by
    intro N N' f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro n m
    rfl)
def torArgumentOrderIso (i : ℕ) (N M : ModuleCat.{u} R) : ((Tor' (ModuleCat R) i).obj N).obj M ≅ ((Tor (ModuleCat R) i).obj M).obj N := (leftDerivedOfNaturalIso
  (tensorOrderIso M) i).app N
variable {V : Type} {k : Type u} [Fintype V] [LinearOrder V] [CommRing k]
def ordinaryFinitePolynomialTorIso [Nontrivial k] (i : ℕ) (M : ModuleCat.{u} (MvPolynomial V k)) : ((Tor (ModuleCat (MvPolynomial V k)) i).obj M).obj
  (CommAlg.Koszul.residueCoefficientModule (V := V) (k := k)) ≅ (CommAlg.Koszul.familyCoefficientComplex (MvPolynomial.X : V → MvPolynomial V k) M).homology i :=
  (torArgumentOrderIso i (CommAlg.Koszul.residueCoefficientModule (V := V) (k := k)) M).symm ≪≫ (CommAlg.Koszul.finitePolynomialTorCoefficientIso i M).symm ≪≫
  CommAlg.Koszul.finitePolynomialTorIso i M
end
open CategoryTheory.MonoidalCategory CommAlg
open scoped TensorProduct
variable {R : Type u} {V : Type} [CommRing R] [Fintype V] [LinearOrder V]
theorem coordinateDifferential_natural (x : V → R) {M N : ModuleCat.{u} R} (f : M ⟶ N) (i : ℕ) : (Finsupp.mapRange.linearMap f.hom).comp (Koszul.coordinateDifferential x M i)
  = (Koszul.coordinateDifferential x N i).comp (Finsupp.mapRange.linearMap f.hom) := by sorry
end FourPapers.Universal
namespace FourPapers.Universal.ProperlyColoredComplex
variable {C : Type*} [LinearOrder C] [DecidableEq C] {V : Type*} [Fintype V] (D : FourPapers.Universal.ProperlyColoredComplex V C)
def colorLinearOrder : LinearOrder V := LinearOrder.lift' (fun v => toLex (D.color v, (Fintype.equivFin V) v)) (by
    intro v w h
    apply (Fintype.equivFin V).injective
    exact congrArg (fun p => (ofLex p).2) h)
end FourPapers.Universal.ProperlyColoredComplex
namespace FourPapers.BasisGrading
variable {R M I A : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
def Piece (b : Module.Basis I R M) (deg : I → A) (a : A) : Submodule R M := Submodule.span R (b '' {i | deg i = a})
end FourPapers.BasisGrading
namespace FourPapers.FilteredHomology
section
variable {K X Y Z X' Y' Z' : Type*} [CommRing K] [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z] [AddCommGroup X'] [Module K X'] [AddCommGroup Y'] [Module K Y'] [AddCommGroup Z'] [Module K Z']
variable (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) (f' : X' →ₗ[K] Y') (g' : Y' →ₗ[K] Z') (hfg' : g'.comp f' = 0) (a : X →ₗ[K] X') (b : Y →ₗ[K] Y') (c : Z →ₗ[K] Z') (hab : b.comp f = f'.comp a) (hbc : c.comp g = g'.comp b)
def inducedCycleMap : LinearMap.ker g →ₗ[K] LinearMap.ker g' := (b.domRestrict _).codRestrict _ (by
    intro y
    change g' (b y.val) = 0
    have hy : g y.val = 0 := y.property
    have h := LinearMap.congr_fun hbc y.val
    simpa only [LinearMap.comp_apply, hy, map_zero] using h.symm)
section
include hab
theorem inducedCycleMap_boundary (x : X) : inducedCycleMap g g' b c hbc (boundaryMap f g hfg x) = boundaryMap f' g' hfg' (a x) := by sorry
end
def inducedHomologyMap : Homology f g hfg →ₗ[K] Homology f' g' hfg' := Submodule.mapQ _ _ (inducedCycleMap g g' b c hbc) (by
    rintro z ⟨x, rfl⟩
    exact ⟨a x, (inducedCycleMap_boundary f g hfg f' g' hfg' a b c hab hbc x).symm⟩)
end
variable {K X Y Z : Type*} [CommRing K] [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z]
def submoduleFiltration (F : Filtration (K := K) X) (N : Submodule K X) : Filtration (K := K) N where
  level n := (F.level n).comap N.subtype
  zero := by simp only [F.zero, Submodule.comap_bot, LinearMap.ker_eq_bot.mpr N.injective_subtype]
  mono := fun _ _ h => Submodule.comap_mono (F.mono h)
  exhaustive x := F.exhaustive x.val
def restrictedMap (f : X →ₗ[K] Y) (N : Submodule K X) (M : Submodule K Y) (hNM : ∀ x, x ∈ N → f x ∈ M) : N →ₗ[K] M := (f.domRestrict N).codRestrict M (fun x => hNM x.val
  x.property)
end FourPapers.FilteredHomology
namespace FourPapers.Universal
section
open FourPapers.FilteredHomology
variable {K I J X Y : Type*} [CommRing K] [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
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
def koszulExteriorDegree {d i : ℕ} (s : Set.powersetCard (Fin d) i) : ℕ := ∑ j ∈ s.val, (j.val + 1)
def koszulExteriorWeight (d : ℕ) {i : ℕ} (s : Set.powersetCard (Fin d) i) : ℤ := ∑ j ∈ s.val, rankWeight d (j.val + 1)
abbrev OriginalKoszulIndex (P : Type*) [PartialOrder P] [OrderBot P] (d i : ℕ) := Σ _ : Set.powersetCard (Fin d) i, StandardFaceIndex P
def originalKoszulDegree {d i : ℕ} (a : OriginalKoszulIndex P d i) : ℕ := standardOrdinaryDegree a.2 + koszulExteriorDegree a.1
def originalKoszulWeight (d : ℕ) {i : ℕ} (a : OriginalKoszulIndex P d i) : ℤ := standardRankWeight d a.2 + koszulExteriorWeight d a.1
end
section
open CommAlg
section
variable {K B B' : Type u} {C : Type} [CommRing K] [CommRing B] [CommRing B'] [Algebra K B] [Algebra K B'] [Fintype C] [LinearOrder C]
def parameterKoszulDifferential (γ : C → B) (i : ℕ) : (Set.powersetCard C (i + 1) →₀ B) →ₗ[K] (Set.powersetCard C i →₀ B) := (Koszul.coordinateDifferential γ (ModuleCat.of B
  B) i).restrictScalars K
theorem parameterKoszulDifferential_comp (γ : C → B) (i : ℕ) : (parameterKoszulDifferential (K := K) γ i).comp (parameterKoszulDifferential (K := K) γ (i + 1)) = 0 := by sorry
def parameterKoszulComplex (γ : C → B) : HomologicalComplex (ModuleCat.{u} K) PalomarBarycentricTor.naturalDown := ChainComplex.of (fun i => ModuleCat.of K (Set.powersetCard C i →₀ B)) (fun i => ModuleCat.ofHom
  (parameterKoszulDifferential (K := K) γ i)) (fun i => ModuleCat.hom_ext (parameterKoszulDifferential_comp (K := K) γ i))
@[simp] theorem parameterKoszulComplex_d (γ : C → B) (i : ℕ) : (parameterKoszulComplex (K := K) γ).d (i + 1) i = ModuleCat.ofHom (parameterKoszulDifferential (K
  := K) γ i) := by sorry
end
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
abbrev originalKoszulComplex : HomologicalComplex (ModuleCat.{u} K) PalomarBarycentricTor.naturalDown := parameterKoszulComplex (K := K) (fun i : Fin d => faceRankParameter K hs (i.val + 1))
end
section
open FourPapers.FilteredHomology
section
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ)
def originalKoszulBasis (i : ℕ) : Module.Basis (OriginalKoszulIndex P d i) K (Set.powersetCard (Fin d) i →₀ FaceRing K hs) := Finsupp.basis (fun _ => standardFaceBasis K hs)
def originalKoszulFiltration (i : ℕ) : Filtration (K := K) (Set.powersetCard (Fin d) i →₀ FaceRing K hs) := basisFiltration (originalKoszulBasis K hs d i) (fun a =>
  (originalKoszulWeight d a).toNat)
def originalKoszulDegreePiece (i j : ℕ) := FourPapers.BasisGrading.Piece (originalKoszulBasis K hs d i) originalKoszulDegree j
end
section
variable {K : Type u} [CommRing K]
abbrev complexIncoming (C : HomologicalComplex (ModuleCat.{u} K) PalomarBarycentricTor.naturalDown) (i : ℕ) := (C.d (i + 1) i).hom
abbrev complexOutgoing (C : HomologicalComplex (ModuleCat.{u} K) PalomarBarycentricTor.naturalDown) (i : ℕ) := (C.d i (i - 1)).hom
theorem complexIncomingOutgoing (C : HomologicalComplex (ModuleCat.{u} K) PalomarBarycentricTor.naturalDown) (i : ℕ) : (complexOutgoing C i).comp (complexIncoming C i) = 0 := by sorry
abbrev complexKernelHomology (C : HomologicalComplex (ModuleCat.{u} K) PalomarBarycentricTor.naturalDown) (i : ℕ) := Homology (complexIncoming C i) (complexOutgoing C i) (complexIncomingOutgoing C i)
def complexKernelHomologyIso (C : HomologicalComplex (ModuleCat.{u} K) PalomarBarycentricTor.naturalDown) (i : ℕ) : C.homology i ≅ ModuleCat.of K (complexKernelHomology C i) :=
  C.homologyIsoSc' (i + 1) i (i - 1) (ChainComplex.prev ℕ i)
    (by cases i <;> simp) ≪≫ (C.sc' (i + 1) i (i - 1)).moduleCatHomologyIso
def submoduleComplex (C : HomologicalComplex (ModuleCat.{u} K) PalomarBarycentricTor.naturalDown) (N : ∀ i, Submodule K (C.X i)) (hN : ∀ i x, x ∈ N (i + 1) → complexIncoming C i x ∈ N i) : HomologicalComplex (ModuleCat.{u} K) PalomarBarycentricTor.naturalDown :=
  ChainComplex.of (fun i => ModuleCat.of K (N i))
    (fun i => ModuleCat.ofHom (restrictedMap (complexIncoming C i) _ _ (hN i))) (by
      intro i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact congrArg (fun f => f x.val) (C.d_comp_d (i + 2) (i + 1) i))
@[simp] theorem submoduleComplex_d (C : HomologicalComplex (ModuleCat.{u} K) PalomarBarycentricTor.naturalDown) (N : ∀ i, Submodule K (C.X i)) (hN : ∀ i x, x ∈ N (i + 1) → complexIncoming C i x ∈ N
  i) (i : ℕ) : (submoduleComplex C N hN).d (i + 1) i = ModuleCat.ofHom (restrictedMap (complexIncoming C i) _ _ (hN i)) := by sorry
def complexHomologyFiltration (C : HomologicalComplex (ModuleCat.{u} K) PalomarBarycentricTor.naturalDown) (F : ∀ i, Filtration (K := K) (C.X i)) (i : ℕ) := homologyFiltration (F i) (complexIncoming C i)
  (complexOutgoing C i) (complexIncomingOutgoing C i)
end
section
variable {K B : Type u} {C : Type} [CommRing K] [CommRing B] [Algebra K B]
def idealCoefficientSubmodule (S : Type*) (I : Ideal B) : Submodule K (S →₀ B) where
  carrier := {x | ∀ s, x s ∈ I}
  zero_mem' := fun _ => I.zero_mem
  add_mem' := fun hx hy s => I.add_mem (hx s) (hy s)
  smul_mem' := fun k x hx s => I.smul_of_tower_mem k (hx s)
end
section
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ)
variable (Q : Set P) (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q)
def originalRelativeKoszulTerm (i : ℕ) : Submodule K ((originalKoszulComplex K hs d).X i) := idealCoefficientSubmodule _ (faceRestrictionIdeal K hs Q)
theorem originalRelativeKoszulTerm_preserved (i : ℕ) (x : (originalKoszulComplex K hs d).X (i + 1)) (hx : x ∈ originalRelativeKoszulTerm K hs d Q (i + 1)) : complexIncoming
  (originalKoszulComplex K hs d) i x ∈ originalRelativeKoszulTerm K hs d Q i := by sorry
def originalRelativeKoszulComplex : HomologicalComplex (ModuleCat.{u} K) PalomarBarycentricTor.naturalDown := submoduleComplex (originalKoszulComplex K hs d) (originalRelativeKoszulTerm K hs d Q)
  (originalRelativeKoszulTerm_preserved K hs d Q)
variable (hrank : ∀ p : P, faceRank p ≤ d)
def originalRelativeDegreeTerm (j i : ℕ) : Submodule K ((originalKoszulComplex K hs d).X i) := originalRelativeKoszulTerm K hs d Q i ⊓ originalKoszulDegreePiece K hs d i j
section
include hrank
theorem originalRelativeDegreeTerm_preserved (j i : ℕ) (x : (originalKoszulComplex K hs d).X (i + 1)) (hx : x ∈ originalRelativeDegreeTerm K hs d Q j (i + 1)) :
  complexIncoming (originalKoszulComplex K hs d) i x ∈ originalRelativeDegreeTerm K hs d Q j i := by sorry
end
def originalRelativeDegreeComplex (j : ℕ) : HomologicalComplex (ModuleCat.{u} K) PalomarBarycentricTor.naturalDown := submoduleComplex (originalKoszulComplex K hs d) (originalRelativeDegreeTerm K hs d Q j)
  (originalRelativeDegreeTerm_preserved K hs d Q hrank j)
def originalRelativeDegreeFiltration (j i : ℕ) := submoduleFiltration (originalKoszulFiltration K hs d i) (originalRelativeDegreeTerm K hs d Q j i)
abbrev originalRelativeInternalHomology (j i : ℕ) := complexKernelHomology (originalRelativeDegreeComplex K hs d Q hrank j) i
def originalRelativeInternalHomologyFiltration (j i : ℕ) := complexHomologyFiltration (originalRelativeDegreeComplex K hs d Q hrank j) (originalRelativeDegreeFiltration K hs d
  Q j) i
end
variable {K : Type u} [CommRing K]
variable {C D E : HomologicalComplex (ModuleCat.{u} K) PalomarBarycentricTor.naturalDown}
def complexKernelHomologyMap (f : C ⟶ D) (i : ℕ) : complexKernelHomology C i →ₗ[K] complexKernelHomology D i := inducedHomologyMap _ _ (complexIncomingOutgoing C i) _ _
  (complexIncomingOutgoing D i) (f.f (i + 1)).hom (f.f i).hom (f.f (i - 1)).hom (congrArg (fun q => q.hom) (f.comm (i + 1) i)).symm (congrArg (fun q => q.hom) (f.comm i (i -
  1))).symm
end
section
open CommAlg
section
variable {K B : Type u} {C : Type} [CommRing K] [CommRing B] [Algebra K B] [Fintype C] [LinearOrder C] (φ : MvPolynomial C K →ₐ[K] B)
theorem parameterRestriction_differential (i : ℕ) :
    letI : Algebra (MvPolynomial C K) B := φ.toRingHom.toAlgebra
    (Koszul.coordinateDifferential (MvPolynomial.X : C → MvPolynomial C K)
      (ModuleCat.of (MvPolynomial C K) B) i).restrictScalars K = parameterKoszulDifferential (K := K) (fun j => φ (MvPolynomial.X j)) i := by sorry
end
variable {K : Type u} {C : Type} [CommRing K] [Fintype C] [LinearOrder C]
def ordinaryModuleParameterTor (M : ModuleCat.{u} (MvPolynomial C K)) (i : ℕ) : ModuleCat.{u} K := (ModuleCat.restrictScalars (algebraMap K (MvPolynomial C K))).obj (((Tor
  (ModuleCat (MvPolynomial C K)) i).obj M).obj (Koszul.residueCoefficientModule (V := C) (k := K)))
def moduleTorCoordinateComplex (M : ModuleCat.{u} (MvPolynomial C K)) : HomologicalComplex (ModuleCat.{u} K) PalomarBarycentricTor.naturalDown := ((ModuleCat.restrictScalars (algebraMap K (MvPolynomial C
  K))).mapHomologicalComplex (ComplexShape.down ℕ)).obj (Koszul.coordinateComplex (MvPolynomial.X : C → MvPolynomial C K) M)
def ordinaryModuleTorCoordinateIsoNontrivial [Nontrivial K] (M : ModuleCat.{u} (MvPolynomial C K)) (i : ℕ) : ordinaryModuleParameterTor M i ≅ (moduleTorCoordinateComplex M).homology i :=
  let F := ModuleCat.restrictScalars (algebraMap K (MvPolynomial C K))
  F.mapIso (ordinaryFinitePolynomialTorIso i M ≪≫ (HomologicalComplex.homologyFunctor (ModuleCat (MvPolynomial C K)) (ComplexShape.down ℕ) i).mapIso
      (Koszul.coordinateComplexIso (MvPolynomial.X : C → MvPolynomial C K) M)) ≪≫
    (((Koszul.coordinateComplex (MvPolynomial.X : C → MvPolynomial C K) M).sc i).mapHomologyIso F).symm
def ordinaryModuleTorCoordinateIso (M : ModuleCat.{u} (MvPolynomial C K)) (i : ℕ) : ordinaryModuleParameterTor M i ≅ (moduleTorCoordinateComplex M).homology i := by
  by_cases h : Nontrivial K
  · letI := h
    exact ordinaryModuleTorCoordinateIsoNontrivial M i
  · letI : Subsingleton K := not_nontrivial_iff_subsingleton.mp h
    let T : ModuleCat.{u} K := ordinaryModuleParameterTor M i
    let H : ModuleCat.{u} K := (moduleTorCoordinateComplex M).homology i
    letI : Subsingleton T := Module.subsingleton K T
    letI : Subsingleton H := Module.subsingleton K H
    exact (LinearEquiv.ofSubsingleton T H).toModuleIso
end
section
open CommAlg FourPapers.FilteredHomology
section
variable {K T B : Type u} {C : Type} [CommRing K] [CommRing T] [Algebra K T] [CommRing B] [Algebra K B]
def moduleRestrictionEquiv (M : Type u) [AddCommGroup M] [Module T M] [Module K M] [IsScalarTower K T M] : ((ModuleCat.restrictScalars (algebraMap K T)).obj (ModuleCat.of T M)) ≃ₗ[K] M where
  toFun := id
  invFun := id
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' k x := by
    change (algebraMap K T k) • (show M from x) = k • (show M from x)
    exact algebraMap_smul T k (show M from x)
def idealCoefficientEquiv (S : Type*) [Finite S] (I : Ideal B) : (S →₀ I) ≃ₗ[K] idealCoefficientSubmodule (K := K) S I where
  toFun x := ⟨Finsupp.mapRange.linearMap (I.subtype.restrictScalars K) x, fun s => (x s).property⟩
  invFun x := Finsupp.equivFunOnFinite.symm (fun s => (⟨x.val s, x.property s⟩ : I))
  left_inv x := by ext s; rfl
  right_inv x := by apply Subtype.ext; ext s; rfl
  map_add' x y := by apply Subtype.ext; ext s; rfl
  map_smul' k x := by apply Subtype.ext; ext s; rfl
variable [Fintype C] [LinearOrder C] (φ : MvPolynomial C K →ₐ[K] B) (I : Ideal B)
def idealParameterCoefficientModule : ModuleCat.{u} (MvPolynomial C K) := by
  letI : Algebra (MvPolynomial C K) B := φ.toRingHom.toAlgebra
  exact ModuleCat.of (MvPolynomial C K) I
def ordinaryIdealParameterTor (i : ℕ) : ModuleCat.{u} K := ordinaryModuleParameterTor (idealParameterCoefficientModule φ I) i
theorem parameterIdealTerm_preserved (i : ℕ) (x : (parameterKoszulComplex (K := K) (fun c => φ (MvPolynomial.X c))).X (i + 1)) (hx : x ∈ idealCoefficientSubmodule (K := K) _
  I) : complexIncoming (parameterKoszulComplex (K := K) (fun c => φ (MvPolynomial.X c))) i x ∈ idealCoefficientSubmodule (K := K) _ I := by sorry
def idealParameterKoszulComplex : HomologicalComplex (ModuleCat.{u} K) PalomarBarycentricTor.naturalDown := submoduleComplex (parameterKoszulComplex (K := K) (fun c => φ (MvPolynomial.X c))) (fun i =>
  idealCoefficientSubmodule (K := K) (Set.powersetCard C i) I) (parameterIdealTerm_preserved φ I)
def idealParameterTermEquiv (i : ℕ) : (moduleTorCoordinateComplex (idealParameterCoefficientModule φ I)).X i ≃ₗ[K] (idealParameterKoszulComplex φ I).X i := by
  letI : Algebra (MvPolynomial C K) B := φ.toRingHom.toAlgebra
  exact (moduleRestrictionEquiv (T := MvPolynomial C K) (Set.powersetCard C i →₀ I)).trans
    (idealCoefficientEquiv (K := K) _ I)
def idealParameterKoszulIso : moduleTorCoordinateComplex (idealParameterCoefficientModule φ I) ≅ idealParameterKoszulComplex φ I := by
  letI : Algebra (MvPolynomial C K) B := φ.toRingHom.toAlgebra
  exact HomologicalComplex.Hom.isoOfComponents (fun i => (idealParameterTermEquiv φ I i).toModuleIso) (by
    intro i j hij
    obtain rfl : i = j + 1 := hij.symm
    simp only [moduleTorCoordinateComplex, idealParameterKoszulComplex,
      Functor.mapHomologicalComplex_obj_d, Koszul.coordinateComplex_d, submoduleComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    apply Subtype.ext
    simp only [complexIncoming, parameterKoszulComplex_d, ModuleCat.hom_ofHom]
    have h := LinearMap.congr_fun
      (coordinateDifferential_natural (MvPolynomial.X : C → MvPolynomial C K) (ModuleCat.ofHom (I.subtype.restrictScalars (MvPolynomial C K))) j) x
    change parameterKoszulDifferential (K := K) (fun c => φ (MvPolynomial.X c)) j
        (Finsupp.mapRange.linearMap (I.subtype.restrictScalars K) x) = _
    rw [← parameterRestriction_differential φ j]
    exact h.symm)
def ordinaryIdealParameterTorKoszulIso (i : ℕ) : ordinaryIdealParameterTor φ I i ≅ (idealParameterKoszulComplex φ I).homology i := ordinaryModuleTorCoordinateIso
  (idealParameterCoefficientModule φ I) i ≪≫ HomologicalComplex.homologyMapIso (idealParameterKoszulIso φ I) i
end
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (Q : Set P)
abbrev originalRelativeParameterTor (i : ℕ) := ordinaryIdealParameterTor (faceParameterAction K hs d) (faceRestrictionIdeal K hs Q) i
def originalRelativeParameterKoszulComplexIso : idealParameterKoszulComplex (faceParameterAction K hs d) (faceRestrictionIdeal K hs Q) ≅ originalRelativeKoszulComplex K hs d Q :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    obtain rfl : i = j + 1 := hij.symm
    simp only [idealParameterKoszulComplex, originalRelativeKoszulComplex, submoduleComplex_d, Iso.refl_hom, Category.id_comp, Category.comp_id]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [complexIncoming, parameterKoszulComplex_d, ModuleCat.hom_ofHom]
    change parameterKoszulDifferential (K := K)
        (fun c : Fin d => faceRankParameter K hs (c.val + 1)) j x.val = parameterKoszulDifferential (K := K)
        (fun c : Fin d => faceParameterAction K hs d (MvPolynomial.X c)) j x.val
    have hγ : (fun c : Fin d => faceParameterAction K hs d (MvPolynomial.X c)) = (fun c : Fin d => faceRankParameter K hs (c.val + 1)) := by
      funext c
      simp only [faceParameterAction, MvPolynomial.aeval_X]
    rw [hγ])
def originalRelativeParameterTorKoszulIso (i : ℕ) : originalRelativeParameterTor K hs d Q i ≅ (originalRelativeKoszulComplex K hs d Q).homology i :=
  ordinaryIdealParameterTorKoszulIso (faceParameterAction K hs d) (faceRestrictionIdeal K hs Q) i ≪≫ HomologicalComplex.homologyMapIso
  (originalRelativeParameterKoszulComplexIso K hs d Q) i
def originalRelativeParameterTorKernelIso (i : ℕ) : originalRelativeParameterTor K hs d Q i ≅ ModuleCat.of K (complexKernelHomology (originalRelativeKoszulComplex K hs d Q) i)
  := originalRelativeParameterTorKoszulIso K hs d Q i ≪≫ complexKernelHomologyIso (originalRelativeKoszulComplex K hs d Q) i
end
open FourPapers.FilteredHomology
section
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
variable (Q : Set P) (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q)
def originalRelativeDegreeInclusion (j : ℕ) : originalRelativeDegreeComplex K hs d Q hrank j ⟶ originalRelativeKoszulComplex K hs d Q where
  f i := ModuleCat.ofHom (Submodule.inclusion inf_le_left)
  comm' i k hik := by
    obtain rfl : i = k + 1 := hik.symm
    simp only [originalRelativeDegreeComplex, originalRelativeKoszulComplex, submoduleComplex_d]
    rfl
def originalRelativeTorDegreeMap (j i : ℕ) : originalRelativeInternalHomology K hs d Q hrank j i →ₗ[K] originalRelativeParameterTor K hs d Q i :=
  ((originalRelativeParameterTorKernelIso K hs d Q i).symm.toLinearEquiv).toLinearMap.comp (complexKernelHomologyMap (originalRelativeDegreeInclusion K hs d hrank Q j) i)
section
include hQ
theorem originalRelativeTorDegreeMap_injective (j i : ℕ) : Function.Injective (originalRelativeTorDegreeMap K hs d hrank Q j i) := by sorry
end
def originalRelativeTorDegreePiece (j i : ℕ) : Submodule K (originalRelativeParameterTor K hs d Q i) := LinearMap.range (originalRelativeTorDegreeMap K hs d hrank Q j i)
def originalRelativeTorDegreeEquiv (j i : ℕ) : originalRelativeInternalHomology K hs d Q hrank j i ≃ₗ[K] originalRelativeTorDegreePiece K hs d hrank Q j i :=
  LinearEquiv.ofInjective _ (originalRelativeTorDegreeMap_injective K hs d hrank Q hQ j i)
section
variable {X Y : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
def equivalenceFiltration (F : Filtration (K := K) X) (E : X ≃ₗ[K] Y) : Filtration (K := K) Y where
  level n := (F.level n).comap E.symm.toLinearMap
  zero := by rw [F.zero, Submodule.comap_bot]; exact LinearMap.ker_eq_bot.mpr E.symm.injective
  mono := fun _ _ h => Submodule.comap_mono (F.mono h)
  exhaustive y := F.exhaustive (E.symm y)
end
def originalRelativeTorFiltration (j i : ℕ) : Filtration (K := K) (originalRelativeTorDegreePiece K hs d hrank Q j i) := equivalenceFiltration K
  (originalRelativeInternalHomologyFiltration K hs d Q hrank j i) (originalRelativeTorDegreeEquiv K hs d hrank Q hQ j i)
end
variable {P K : Type u} {G : Type v} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K] [Group G]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
variable (Q : Set P) (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q)
abbrev originalRelativeTorAssociatedGraded (j i : ℕ) := ⨁ n, Grade (originalRelativeTorFiltration K hs d hrank Q hQ j i) n
def rankSubsetDegree {d : ℕ} (S : Finset (Fin d)) : ℕ := ∑ r ∈ S, (r.val + 1)
end FourPapers.Universal
namespace FourPapers.Universal.ProperlyColoredComplex
set_option backward.isDefEq.respectTransparency.types false
variable {V C K : Type*} [Fintype V] [Fintype C] [CommRing K] (D : FourPapers.Universal.ProperlyColoredComplex V C)
structure Subcomplex where
  face : Finset V → Prop
  downward : ∀ ⦃s t : Finset V⦄, s ⊆ t → face t → face s
  subface : ∀ s, face s → D.face s
end FourPapers.Universal.ProperlyColoredComplex
namespace FourPapers.Universal.ProperlyColoredComplex.Subcomplex
set_option backward.isDefEq.respectTransparency.types false
variable {V C K : Type*} [Fintype V] [Fintype C] [CommRing K] (D : FourPapers.Universal.ProperlyColoredComplex V C)
variable {D} (Q : D.Subcomplex)
def toColoredComplex : FourPapers.Universal.ProperlyColoredComplex V C where
  face := Q.face
  downward := Q.downward
  color := D.color
  proper s hs := D.proper s (Q.subface s hs)
end FourPapers.Universal.ProperlyColoredComplex.Subcomplex
namespace FourPapers.Universal
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P] (K : Type*) [CommRing K] (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
def rankColoredSubcomplex (Q : Set P) : (rankColoredOrderComplex hs d hrank).Subcomplex where
  face s := (⊥ : P) ∈ Q ∧ (rankColoredOrderComplex hs d hrank).face s ∧ ∀ p ∈ s, p.val ∈ Q
  downward := by
    intro s t hst ht
    exact ⟨ht.1, (rankColoredOrderComplex hs d hrank).downward hst ht.2.1, fun p hp => ht.2.2 p (hst hp)⟩
  subface s hs := hs.2.1
end
set_option backward.isDefEq.respectTransparency.types false
section
open CommAlg FourPapers.FilteredHomology
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
variable (Q : Set P) (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q)
abbrev rankSelectedRelativeCohomology (S : Finset (Fin d)) (i : ℕ) :=
  letI : LinearOrder (NonzeroFace P) := (rankColoredOrderComplex hs d hrank).colorLinearOrder
  letI : DecidableEq (Fin d) := Classical.decEq _
  letI : DecidableEq (NonzeroFace P) := Classical.decEq _
  reducedRelativeCohomology (K := K)
    (rankSelection (rankColoredOrderComplex hs d hrank) S)
    (rankSelection (rankColoredSubcomplex hs d hrank Q).toColoredComplex S)
    (rankSelection_downward (rankColoredOrderComplex hs d hrank) S)
    (rankSelection_downward (rankColoredSubcomplex hs d hrank Q).toColoredComplex S)
    ((S.card : ℤ) - i - 1)
end
open FourPapers.FilteredHomology
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
variable (Q : Set P) (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q)
theorem relativeTorRankSelectedComparison (j i : ℕ) : Nonempty (originalRelativeTorAssociatedGraded K hs d hrank Q hQ j i ≃ₗ[K] (⨁ S : {S : Finset (Fin d) // rankSubsetDegree S = j},
  rankSelectedRelativeCohomology K hs d hrank Q S.val i)) := by sorry
end FourPapers.Universal
