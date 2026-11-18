module
public import Mathlib
public meta import Lean.PrettyPrinter
/-! Theorem 1.2: the actual homogeneous parameter-Koszul homology filtration,
its finite upper endpoint, and its associated graded as the direct sum of
ordinary rank-selected reduced cohomologies. The Solution identifies the
ordinary parameter-Koszul complex with genuine derived Tor. The definitions
below are actual chain, kernel/image quotient and face-ring constructions. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
open scoped BigOperators DirectSum
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
/-- Literal FourPapers.Universal.IsSimplicialPoset; source theorem12.lean:5908. -/ def IsSimplicialPoset (P : Type*) [PartialOrder P] [OrderBot P] : Prop :=
  ∀ p : P, ∃ n : ℕ, Nonempty (Set.Iic p ≃o Finset (Fin n))
/-- Literal FourPapers.Universal.faceVertices; source theorem12.lean:5912. -/ def faceVertices (p : P) : Finset P :=
  univ.filter fun a => IsAtom a ∧ a ≤ p
/-- Literal FourPapers.Universal.mem_faceVertices; source theorem12.lean:5915. -/ @[simp] theorem mem_faceVertices {p a : P} : a ∈ faceVertices p ↔ IsAtom a ∧ a ≤ p := by sorry
/-- Literal FourPapers.Universal.faceVertices_mono; source theorem12.lean:5928. -/ theorem faceVertices_mono : Monotone (faceVertices : P → Finset P) := by sorry
/-- Literal FourPapers.Universal.existsUnique_subface; source theorem12.lean:5982. -/ theorem existsUnique_subface (hs : IsSimplicialPoset P) (p : P) (s : Finset P) (hsu : s ⊆ faceVertices p) : ∃! x : Set.Iic p, faceVertices x.val = s := by sorry
/-- Literal FourPapers.Universal.faceRank; source theorem12.lean:6024. -/ def faceRank (p : P) : ℕ := (faceVertices p).card
/-- Literal FourPapers.Universal.faceRank_bot; source theorem12.lean:6026. -/ @[simp] theorem faceRank_bot : faceRank (⊥ : P) = 0 := by sorry
/-- Literal FourPapers.Universal.faceRank_strictMono; source theorem12.lean:6028. -/ theorem faceRank_strictMono (hs : IsSimplicialPoset P) : StrictMono (faceRank : P → ℕ) := by sorry
/-- Literal FourPapers.Universal.koszulExteriorDegree; source theorem12.lean:19765. -/ def koszulExteriorDegree {d i : ℕ} (s : Set.powersetCard (Fin d) i) : ℕ :=
  ∑ j ∈ s.val, (j.val + 1)
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical MvPolynomial Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
/-- Literal FourPapers.Universal.NonzeroFace; source theorem12.lean:6405. -/ abbrev NonzeroFace (P : Type*) [Preorder P] [OrderBot P] := {p : P // p ≠ ⊥}
/-- Literal FourPapers.Universal.palomarNonzeroFaceFintype; source theorem12.lean:6407. -/
instance palomarNonzeroFaceFintype : Fintype (NonzeroFace P) := Fintype.ofFinite _
/-- Literal FourPapers.Universal.faceMeetBelow; source theorem12.lean:6410. -/ def faceMeetBelow (hs : IsSimplicialPoset P) (p q w : P) (hpw : p ≤ w) (hqw : q ≤ w) : P :=
  ((existsUnique_subface hs w (faceVertices p ∩ faceVertices q)
    (Finset.inter_subset_left.trans (faceVertices_mono hpw))).choose).val
/-- Literal FourPapers.Universal.IsMinimalCommonUpper; source theorem12.lean:6458. -/ def IsMinimalCommonUpper (p q w : P) : Prop :=
  p ≤ w ∧ q ≤ w ∧ ∀ v, p ≤ v → q ≤ v → v ≤ w → v = w
/-- Literal FourPapers.Universal.minimalCommonUppers; source theorem12.lean:6461. -/ def minimalCommonUppers (p q : P) : Finset P :=
  univ.filter (IsMinimalCommonUpper p q)
end FourPapers.Universal
namespace CommAlg.Simplicial
set_option backward.isDefEq.respectTransparency false
open CliffordAlgebra
variable {V k : Type*} [Fintype V] [LinearOrder V] [CommRing k]
/-- Literal CommAlg.Simplicial.Ambient; source theorem12.lean:5584. -/ abbrev Ambient (V k : Type*) [Fintype V] [CommRing k] := ExteriorAlgebra k (V → k)
/-- Literal CommAlg.Simplicial.basis; source theorem12.lean:5586. -/ def basis : Module.Basis (Finset V) k (Ambient V k) := (Pi.basisFun k V).ExteriorAlgebra
/-- Literal CommAlg.Simplicial.Chains; source theorem12.lean:5588. -/ def Chains (K : Finset V → Prop) (i : ℕ) : Submodule k (Ambient V k) :=
  Submodule.span k (basis '' {s | K s ∧ s.card = i})
/-- Literal CommAlg.Simplicial.Downward; source theorem12.lean:5591. -/ def Downward (K : Finset V → Prop) : Prop :=
  ∀ ⦃s t⦄, t ⊆ s → K s → K t
/-- Literal CommAlg.Simplicial.boundary; source theorem12.lean:5608. -/ abbrev boundary : Ambient V k →ₗ[k] Ambient V k :=
  contractLeft (Q := (0 : QuadraticForm k (V → k)))
    (Fintype.linearCombination k (fun _ : V => (1 : k)))
/-- Literal CommAlg.Simplicial.boundary_mem; source theorem12.lean:5696. -/ lemma boundary_mem {K : Finset V → Prop} (hK : Downward K) {i : ℕ} {z : Ambient V k} (hz : z ∈ Chains K (i + 1)) : boundary z ∈ Chains K i := by sorry
end CommAlg.Simplicial
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical MvPolynomial Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]
/-- Literal FourPapers.Universal.FacePolynomial; source theorem12.lean:6470. -/ abbrev FacePolynomial := MvPolynomial (NonzeroFace P) K
/-- Literal FourPapers.Universal.faceSymbol; source theorem12.lean:6473. -/ def faceSymbol (p : P) : FacePolynomial (P := P) K :=
  if hp : p = ⊥ then 1 else X ⟨p, hp⟩
/-- Literal FourPapers.Universal.faceRelations; source theorem12.lean:6485. -/ def faceRelations (hs : IsSimplicialPoset P) : Set (FacePolynomial (P := P) K) :=
  {f | (∃ (p q w : P) (hpw : p ≤ w) (hqw : q ≤ w),
      f = faceSymbol K p * faceSymbol K q -
        faceSymbol K (faceMeetBelow hs p q w hpw hqw) *
          ∑ u ∈ minimalCommonUppers p q, faceSymbol K u) ∨
    (∃ p q, (¬ ∃ w, p ≤ w ∧ q ≤ w) ∧
      f = faceSymbol K p * faceSymbol K q)}
/-- Literal FourPapers.Universal.faceIdeal; source theorem12.lean:6493. -/ def faceIdeal (hs : IsSimplicialPoset P) : Ideal (FacePolynomial (P := P) K) :=
  Ideal.span (faceRelations K hs)
/-- Literal FourPapers.Universal.FaceRing; source theorem12.lean:6497. -/ abbrev FaceRing (hs : IsSimplicialPoset P) :=
  FacePolynomial (P := P) K ⧸ faceIdeal K hs
/-- Literal FourPapers.Universal.barycentricIdeal; source theorem12.lean:6501. -/ def barycentricIdeal : Ideal (FacePolynomial (P := P) K) :=
  Ideal.span {f | ∃ p q : NonzeroFace P,
    ¬ p.val ≤ q.val ∧ ¬ q.val ≤ p.val ∧ f = X p * X q}
/-- Literal FourPapers.Universal.BarycentricRing; source theorem12.lean:6505. -/ abbrev BarycentricRing := FacePolynomial (P := P) K ⧸ barycentricIdeal (P := P) K
/-- Literal FourPapers.Universal.faceRingGenerator; source theorem12.lean:6507. -/ def faceRingGenerator (hs : IsSimplicialPoset P) (p : P) : FaceRing K hs :=
  Ideal.Quotient.mk (faceIdeal K hs) (faceSymbol K p)
/-- Literal FourPapers.Universal.barycentricGenerator; source theorem12.lean:6510. -/ def barycentricGenerator (p : P) : BarycentricRing (P := P) K :=
  Ideal.Quotient.mk (barycentricIdeal K) (faceSymbol K p)
/-- Literal FourPapers.Universal.faceRankParameter; source theorem12.lean:6514. -/ def faceRankParameter (hs : IsSimplicialPoset P) (i : ℕ) : FaceRing K hs :=
  ∑ p ∈ univ.filter (fun p : P => faceRank p = i), faceRingGenerator K hs p
/-- Literal FourPapers.Universal.barycentricRankParameter; source theorem12.lean:6517. -/ def barycentricRankParameter (i : ℕ) : BarycentricRing (P := P) K :=
  ∑ p ∈ univ.filter (fun p : P => faceRank p = i), barycentricGenerator K p
/-- Literal FourPapers.Universal.faceParameterAction; source theorem12.lean:6520. -/ def faceParameterAction (hs : IsSimplicialPoset P) (d : ℕ) : MvPolynomial (Fin d) K →ₐ[K] FaceRing K hs :=
  MvPolynomial.aeval fun i => faceRankParameter K hs (i.val + 1)
/-- Literal FourPapers.Universal.barycentricParameterAction; source theorem12.lean:6524. -/ def barycentricParameterAction (d : ℕ) : MvPolynomial (Fin d) K →ₐ[K] BarycentricRing (P := P) K :=
  MvPolynomial.aeval fun i => barycentricRankParameter K (i.val + 1)
/-- Literal FourPapers.Universal.BarycentricAllowed; source theorem12.lean:7826. -/ def BarycentricAllowed (a : NonzeroFace P →₀ ℕ) : Prop :=
  ∀ p ∈ a.support, ∀ q ∈ a.support, p.val ≤ q.val ∨ q.val ≤ p.val
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical CategoryTheory
universe u
variable {K : Type u} [CommRing K]
/-- Literal FourPapers.Universal.complexIncoming; source theorem12.lean:20422. -/ abbrev complexIncoming (C : ChainComplex (ModuleCat.{u} K) ℕ) (i : ℕ) :=
  (C.d (i + 1) i).hom
/-- Literal FourPapers.Universal.complexOutgoing; source theorem12.lean:20424. -/ abbrev complexOutgoing (C : ChainComplex (ModuleCat.{u} K) ℕ) (i : ℕ) :=
  (C.d i (i - 1)).hom
/-- Literal FourPapers.Universal.complexIncomingOutgoing; source theorem12.lean:20427. -/ theorem complexIncomingOutgoing (C : ChainComplex (ModuleCat.{u} K) ℕ) (i : ℕ) : (complexOutgoing C i).comp (complexIncoming C i) = 0 := by sorry
end FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Category Limits Module ExteriorAlgebra
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R)
/-- Literal koszulComplex.dAlternating; source theorem12.lean:720. -/ noncomputable def koszulComplex.dAlternating (n : ℕ) : M [⋀^Fin (n + 1)]→ₗ[R] ⋀[R]^n M :=
  AlternatingMap.alternatizeUncurryFin (φ.smulRight (exteriorPower.ιMulti R n))
/-- Literal koszulComplex.d; source theorem12.lean:734. -/ noncomputable def koszulComplex.d (n : ℕ) : ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M :=
  exteriorPower.alternatingMapLinearEquiv (koszulComplex.dAlternating φ n)
/-- Literal koszulComplex.d_comp_eq_zero; source theorem12.lean:737. -/ lemma koszulComplex.d_comp_eq_zero (n : ℕ) : koszulComplex.d φ n ∘ₗ koszulComplex.d φ (n + 1) = 0 := by sorry
/-- Literal koszulComplex; source theorem12.lean:753. -/ noncomputable def koszulComplex : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (⋀[R]^n M))
    (fun n ↦ ModuleCat.ofHom (koszulComplex.d φ n))
    (fun n ↦ by rw [← ModuleCat.ofHom_comp, koszulComplex.d_comp_eq_zero, ModuleCat.ofHom_zero])
end
namespace CommAlg.Koszul
set_option backward.isDefEq.respectTransparency false
open CategoryTheory TensorProduct
universe u v
variable {R : Type u} {V : Type} [CommRing R] [Fintype V] [LinearOrder V]
/-- Literal CommAlg.Koszul.familyCoefficientComplex; source theorem12.lean:5030. -/ abbrev familyCoefficientComplex (x : V → R) (M : ModuleCat.{u} R) : ChainComplex (ModuleCat.{u} R) ℕ :=
  (((CategoryTheory.MonoidalCategory.tensoringRight (ModuleCat R)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (koszulComplex (Fintype.linearCombination R x))
/-- Literal CommAlg.Koszul.coefficientCoordinates; source theorem12.lean:5036. -/ def coefficientCoordinates (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) : (familyCoefficientComplex x M).X i ≃ₗ[R] (Set.powersetCard V i →₀ M) :=
  TensorProduct.equivFinsuppOfBasisLeft ((Pi.basisFun R V).exteriorPower i)
/-- Literal CommAlg.Koszul.coordinateDifferential; source theorem12.lean:5042. -/ def coordinateDifferential (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) : (Set.powersetCard V (i + 1) →₀ M) →ₗ[R] (Set.powersetCard V i →₀ M) :=
  let δ : (familyCoefficientComplex.{u} x M).X (i + 1) →ₗ[R]
      (familyCoefficientComplex.{u} x M).X i :=
    ((familyCoefficientComplex.{u} x M).d (i + 1) i).hom
  (coefficientCoordinates.{u} x M i).toLinearMap.comp
    (δ.comp (coefficientCoordinates.{u} x M (i + 1)).symm.toLinearMap)
end CommAlg.Koszul
namespace CommAlg.Koszul
set_option backward.isDefEq.respectTransparency false
open CategoryTheory MvPolynomial
universe u v
variable {V : Type} {k : Type u} [CommRing k]
/-- Literal CommAlg.Koszul.residueCoefficientModule; source theorem12.lean:5819. -/ def residueCoefficientModule : ModuleCat.{u} (MvPolynomial V k) :=
  (ModuleCat.restrictScalars (constantCoeff : MvPolynomial V k →+* k)).obj (ModuleCat.of k k)
end CommAlg.Koszul
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
universe u v w
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
/-- Literal FourPapers.Universal.ModuleDiagram; source theorem12.lean:6077. -/ structure ModuleDiagram where
  obj : P → Type w
  [addCommGroup : ∀ p, AddCommGroup (obj p)]
  [module : ∀ p, Module K (obj p)]
  res : ∀ {p q}, q ≤ p → obj p →ₗ[K] obj q
  res_refl : ∀ p x, res (le_refl p) x = x
  res_comp : ∀ {p q r} (hqp : q ≤ p) (hrq : r ≤ q) x,
    res hrq (res hqp x) = res (hrq.trans hqp) x
attribute [instance] ModuleDiagram.addCommGroup ModuleDiagram.module
end FourPapers.Universal
namespace FourPapers.Universal.ModuleDiagram
set_option backward.isDefEq.respectTransparency false
universe u v w
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
variable {K P}
variable (D : ModuleDiagram K P)
/-- Literal FourPapers.Universal.ModuleDiagram.sections; source theorem12.lean:6095. -/ def sections : Submodule K (∀ p, D.obj p) where
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
set_option backward.isDefEq.respectTransparency false
universe u v w
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
variable {K P}
/-- Literal FourPapers.Universal.CoherentEquiv; source theorem12.lean:6141. -/ structure CoherentEquiv (D E : ModuleDiagram K P) where
  component : ∀ p, D.obj p ≃ₗ[K] E.obj p
  naturality : ∀ p q (h : q ≤ p) x,
    E.res h (component p x) = component q (D.res h x)
end FourPapers.Universal

namespace FourPapers.Universal.CoherentEquiv
section
set_option backward.isDefEq.respectTransparency false
universe u v w
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
variable {K P}
variable {D E F : ModuleDiagram K P}
/-- Literal original coherent inverse-limit construction. -/
def symm (e : CoherentEquiv D E) : CoherentEquiv E D where
  component p := (e.component p).symm
  naturality p q h x := by
    apply (e.component q).injective
    simpa using (e.naturality p q h ((e.component p).symm x)).symm
/-- Literal original coherent inverse-limit construction. -/
def sectionEquiv (e : CoherentEquiv D E) : D.sections ≃ₗ[K] E.sections where
  toFun x := ⟨fun p => e.component p (x.val p), by
    intro p q h
    rw [e.naturality, x.property p q h]⟩
  invFun x := ⟨fun p => (e.component p).symm (x.val p), by
    intro p q h
    change D.res h (e.symm.component p (x.val p)) =
      e.symm.component q (x.val q)
    exact (e.symm.naturality p q h (x.val p)).trans
      (congrArg (e.symm.component q) (x.property p q h))⟩
  left_inv x := by
    apply Subtype.ext
    funext p
    exact (e.component p).symm_apply_apply (x.val p)
  right_inv x := by
    apply Subtype.ext
    funext p
    exact (e.component p).apply_symm_apply (x.val p)
  map_add' x y := by
    apply Subtype.ext
    funext p
    exact map_add (e.component p) (x.val p) (y.val p)
  map_smul' c x := by
    apply Subtype.ext
    funext p
    exact map_smul (e.component p) c (x.val p)
end
end FourPapers.Universal.CoherentEquiv

namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]
/-- Literal FourPapers.Universal.FaceVertex; source theorem12.lean:6266. -/ abbrev FaceVertex (p : P) := {a : P // IsAtom a ∧ a ≤ p}
/-- Literal FourPapers.Universal.palomarFaceVertexFintype; source theorem12.lean:6268. -/
instance palomarFaceVertexFintype (p : P) : Fintype (FaceVertex p) := Fintype.ofFinite _
/-- Literal FourPapers.Universal.PolynomialStalk; source theorem12.lean:6274. -/ abbrev PolynomialStalk (p : P) := MvPolynomial (FaceVertex p) K
/-- Literal FourPapers.Universal.polynomialRestriction; source theorem12.lean:6277. -/ def polynomialRestriction {p q : P} (hqp : q ≤ p) : PolynomialStalk K p →ₐ[K] PolynomialStalk K q := by
  classical
  exact aeval fun a => if h : a.val ≤ q then X ⟨a.val, a.property.1, h⟩ else 0
/-- Literal FourPapers.Universal.polynomialRestriction_refl; source theorem12.lean:6293. -/ theorem polynomialRestriction_refl (p : P) : polynomialRestriction K (le_refl p) = AlgHom.id K (PolynomialStalk K p) := by sorry
/-- Literal FourPapers.Universal.polynomialRestriction_comp; source theorem12.lean:6300. -/ theorem polynomialRestriction_comp {p q r : P} (hqp : q ≤ p) (hrq : r ≤ q) : (polynomialRestriction K hrq).comp (polynomialRestriction K hqp) =
  polynomialRestriction K (hrq.trans hqp) := by sorry
/-- Literal FourPapers.Universal.polynomialDiagram; source theorem12.lean:6330. -/ abbrev polynomialDiagram : ModuleDiagram K P where
  obj p := PolynomialStalk K p
  res h := (polynomialRestriction K h).toLinearMap
  res_refl p f := DFunLike.congr_fun (polynomialRestriction_refl K p) f
  res_comp hqp hrq f := DFunLike.congr_fun (polynomialRestriction_comp K hqp hrq) f
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
/-- Literal FourPapers.Universal.subfaceOfVertexSet; source theorem12.lean:7737. -/ def subfaceOfVertexSet (hs : IsSimplicialPoset P) (p : P) (s : Finset (FaceVertex p)) : Set.Iic p :=
  (existsUnique_subface hs p (s.image Subtype.val) (by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := mem_image.mp ha
    exact mem_faceVertices.mpr v.property)).choose
/-- Literal FourPapers.Universal.StandardFaceIndex; source theorem12.lean:7914. -/ abbrev StandardFaceIndex (P : Type*) [PartialOrder P] [OrderBot P] :=
  {a : NonzeroFace P →₀ ℕ // BarycentricAllowed a}
/-- Literal FourPapers.Universal.standardCarrier; source theorem12.lean:7919. -/ def standardCarrier (a : StandardFaceIndex P) : P :=
  if h : a.val.support.Nonempty then
    (Finset.exists_max_image a.val.support (fun p : NonzeroFace P => faceRank p.val) h).choose.val
  else ⊥
/-- Literal FourPapers.Universal.standardCarrier_le_iff; source theorem12.lean:7924. -/ theorem standardCarrier_le_iff (hs : IsSimplicialPoset P) (a : StandardFaceIndex P) (p : P) : standardCarrier a ≤ p ↔ ∀ q ∈ a.val.support, q.val ≤ p := by sorry
/-- Literal FourPapers.Universal.StandardInside; source theorem12.lean:8005. -/ abbrev StandardInside (p : P) := {a : StandardFaceIndex P // standardCarrier a ≤ p}
/-- Literal FourPapers.Universal.OriginalKoszulIndex; source theorem12.lean:19771. -/ abbrev OriginalKoszulIndex (P : Type*) [PartialOrder P] [OrderBot P] (d i : ℕ) :=
  Σ _ : Set.powersetCard (Fin d) i, StandardFaceIndex P
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
/-- Literal FourPapers.Universal.faceRingMonomial; source theorem12.lean:8687. -/ def faceRingMonomial (a : NonzeroFace P →₀ ℕ) : FaceRing K hs :=
  Ideal.Quotient.mk (faceIdeal K hs) (monomial a 1)
/-- Literal FourPapers.Universal.standardOrdinaryDegree; source theorem12.lean:13414. -/ def standardOrdinaryDegree (a : StandardFaceIndex P) : ℕ :=
  a.val.sum (fun F n => n * faceRank F.val)
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V]
/-- Literal FourPapers.Universal.rankWeight; source theorem12.lean:6558. -/ def rankWeight (d r : ℕ) : ℤ := (r : ℤ) * (2 * (d : ℤ) - r)
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
/-- Literal FourPapers.Universal.koszulExteriorWeight; source theorem12.lean:19768. -/ def koszulExteriorWeight (d : ℕ) {i : ℕ} (s : Set.powersetCard (Fin d) i) : ℤ :=
  ∑ j ∈ s.val, rankWeight d (j.val + 1)
/-- Literal FourPapers.Universal.originalKoszulDegree; source theorem12.lean:19774. -/ def originalKoszulDegree {d i : ℕ} (a : OriginalKoszulIndex P d i) : ℕ :=
  standardOrdinaryDegree a.2 + koszulExteriorDegree a.1
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]
/-- Literal FourPapers.Universal.stalkVertexSet; source theorem12.lean:6835. -/ def stalkVertexSet (p q : P) : Finset (FaceVertex p) :=
  univ.filter fun a => a.val ≤ q
/-- Literal FourPapers.Universal.stalkVertexSet_bot; source theorem12.lean:6841. -/ @[simp] theorem stalkVertexSet_bot (p : P) : stalkVertexSet p (⊥ : P) = ∅ := by sorry
/-- Literal FourPapers.Universal.faceProduct; source theorem12.lean:6846. -/ def faceProduct (p q : P) : PolynomialStalk K p :=
  ∏ a ∈ stalkVertexSet p q, X a
/-- Literal FourPapers.Universal.faceValue; source theorem12.lean:6852. -/ def faceValue (p q : P) : PolynomialStalk K p :=
  if q ≤ p then faceProduct K p q else 0
/-- Literal FourPapers.Universal.faceEvaluation; source theorem12.lean:6932. -/ def faceEvaluation (r : P) : FacePolynomial (P := P) K →ₐ[K] PolynomialStalk K r :=
  MvPolynomial.aeval fun p => faceValue K r p.val
/-- Literal FourPapers.Universal.faceEvaluation_relation; source theorem12.lean:6942. -/ theorem faceEvaluation_relation (hs : IsSimplicialPoset P) (r : P) {f : FacePolynomial (P := P) K} (hf : f ∈ faceRelations K hs) : faceEvaluation K r f = 0 :=
  by sorry
/-- Literal FourPapers.Universal.faceRingEvaluation; source theorem12.lean:6955. -/ def faceRingEvaluation (hs : IsSimplicialPoset P) (r : P) : FaceRing K hs →ₐ[K] PolynomialStalk K r :=
  Ideal.Quotient.liftₐ (faceIdeal K hs) (faceEvaluation K r) (by
    change faceIdeal K hs ≤ RingHom.ker (faceEvaluation K r).toRingHom
    apply Ideal.span_le.mpr
    intro f hf
    exact faceEvaluation_relation K hs r hf)
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
/-- Literal FourPapers.Universal.faceRingEvaluation_naturality; source theorem12.lean:9764. -/ theorem faceRingEvaluation_naturality {p q : P} (hqp : q ≤ p) (f : FaceRing K hs) : polynomialRestriction K hqp (faceRingEvaluation K hs p f) =
  faceRingEvaluation K hs q f := by sorry
/-- Literal FourPapers.Universal.faceRingSection; source theorem12.lean:9772. -/ def faceRingSection : FaceRing K hs →ₗ[K] (polynomialDiagram (P := P) K).sections where
  toFun f := ⟨fun p => faceRingEvaluation K hs p f,
    fun p q hqp => faceRingEvaluation_naturality K hs hqp f⟩
  map_add' f g := by
    apply Subtype.ext
    funext p
    exact map_add (faceRingEvaluation K hs p) f g
  map_smul' c f := by
    apply Subtype.ext
    funext p
    exact map_smul (faceRingEvaluation K hs p) c f
/-- Literal FourPapers.Universal.standardRankWeight; source theorem12.lean:12534. -/ def standardRankWeight (d : ℕ) (a : StandardFaceIndex P) : ℤ :=
  a.val.sum (fun F n => (n : ℤ) * rankWeight d (faceRank F.val))
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
/-- Literal FourPapers.Universal.stalkVertexSet_subfaceOfVertexSet; source theorem12.lean:7752. -/ theorem stalkVertexSet_subfaceOfVertexSet (hs : IsSimplicialPoset P) (p : P) (s : Finset (FaceVertex p)) : stalkVertexSet p (subfaceOfVertexSet hs p s).val = s
  := by sorry
/-- Literal FourPapers.Universal.originalKoszulWeight; source theorem12.lean:19777. -/ def originalKoszulWeight (d : ℕ) {i : ℕ} (a : OriginalKoszulIndex P d i) : ℤ :=
  standardRankWeight d a.2 + koszulExteriorWeight d a.1
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {V K : Type*} [Fintype V] [DecidableEq V] [CommRing K]
/-- Literal FourPapers.Universal.BooleanFace; source theorem12.lean:7373. -/ abbrev BooleanFace (V : Type*) [DecidableEq V] := {F : Finset V // F.Nonempty}
/-- Literal FourPapers.Universal.IsChainExponent; source theorem12.lean:7396. -/ def IsChainExponent (a : BooleanFace V →₀ ℕ) : Prop :=
  ∀ F ∈ a.support, ∀ G ∈ a.support, F.val ⊆ G.val ∨ G.val ⊆ F.val
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
/-- Literal FourPapers.Universal.booleanFaceInclusion; source theorem12.lean:7774. -/ def booleanFaceInclusion (hs : IsSimplicialPoset P) (p : P) : BooleanFace (FaceVertex p) ↪ NonzeroFace P where
  toFun F := ⟨(subfaceOfVertexSet hs p F.val).val, by
    intro hbot
    have he := stalkVertexSet_subfaceOfVertexSet hs p F.val
    rw [hbot, stalkVertexSet_bot] at he
    exact F.property.ne_empty he.symm⟩
  inj' F G h := by
    apply Subtype.ext
    have he : (subfaceOfVertexSet hs p F.val).val =
        (subfaceOfVertexSet hs p G.val).val := congrArg (fun z : NonzeroFace P => z.val) h
    have hv := congrArg (stalkVertexSet p) he
    simpa only [stalkVertexSet_subfaceOfVertexSet] using hv
/-- Literal FourPapers.Universal.booleanFaceInclusion_le; source theorem12.lean:7788. -/ theorem booleanFaceInclusion_le (hs : IsSimplicialPoset P) (p : P) (F : BooleanFace (FaceVertex p)) : (booleanFaceInclusion hs p F).val ≤ p := by sorry
/-- Literal FourPapers.Universal.booleanFaceInclusion_range_iff; source theorem12.lean:7963. -/ theorem booleanFaceInclusion_range_iff (hs : IsSimplicialPoset P) (p : P) (q : NonzeroFace P) : q ∈ Set.range (booleanFaceInclusion hs p) ↔ q.val ≤ p := by
  sorry
/-- Literal FourPapers.Universal.standardExponent_map_booleanFaceInclusion; source theorem12.lean:7981. -/ theorem standardExponent_map_booleanFaceInclusion (hs : IsSimplicialPoset P) (p : P) {a : BooleanFace (FaceVertex p) →₀ ℕ} (ha : IsChainExponent a) :
  BarycentricAllowed (a.mapDomain (booleanFaceInclusion hs p)) := by sorry
/-- Literal FourPapers.Universal.chainExponent_comap_booleanFaceInclusion; source theorem12.lean:7992. -/ theorem chainExponent_comap_booleanFaceInclusion (hs : IsSimplicialPoset P) (p : P) {a : NonzeroFace P →₀ ℕ} (ha : BarycentricAllowed a) : IsChainExponent
  (a.comapDomain (booleanFaceInclusion hs p) (booleanFaceInclusion hs p).injective.injOn) := by sorry
/-- Literal FourPapers.Universal.standardInsideEquiv; source theorem12.lean:8009. -/ def standardInsideEquiv (hs : IsSimplicialPoset P) (p : P) : {a : BooleanFace (FaceVertex p) →₀ ℕ // IsChainExponent a} ≃ StandardInside p where
  toFun a := ⟨⟨a.val.mapDomain (booleanFaceInclusion hs p),
    standardExponent_map_booleanFaceInclusion hs p a.property⟩, by
      apply (standardCarrier_le_iff hs _ p).mpr
      intro q hq
      rw [Finsupp.mapDomain_support_of_injective (booleanFaceInclusion hs p).injective] at hq
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hq
      exact booleanFaceInclusion_le hs p F⟩
  invFun a := ⟨a.val.val.comapDomain (booleanFaceInclusion hs p)
    (booleanFaceInclusion hs p).injective.injOn,
    chainExponent_comap_booleanFaceInclusion hs p a.val.property⟩
  left_inv a := Subtype.ext
    (Finsupp.comapDomain_mapDomain _ (booleanFaceInclusion hs p).injective a.val)
  right_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    apply Finsupp.mapDomain_comapDomain _ (booleanFaceInclusion hs p).injective
    intro q hq
    exact (booleanFaceInclusion_range_iff hs p q).mpr
      ((standardCarrier_le_iff hs a.val p).mp a.property q hq)
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical
variable {P I : Type*} [Preorder P]
variable (K : Type*) [CommRing K] (carrier : I → P)
/-- Literal FourPapers.Universal.coefficientStalk; source theorem12.lean:8327. -/ def coefficientStalk (p : P) : Submodule K (I →₀ K) :=
  Finsupp.supported K K {i | carrier i ≤ p}
/-- Literal FourPapers.Universal.coefficientRestriction; source theorem12.lean:8330. -/ def coefficientRestriction {p q : P} (_hqp : q ≤ p) : coefficientStalk K carrier p →ₗ[K] coefficientStalk K carrier q :=
  (Finsupp.restrictDom K K {i | carrier i ≤ q}).comp
    (coefficientStalk K carrier p).subtype
/-- Literal FourPapers.Universal.coefficientRestriction_apply; source theorem12.lean:8335. -/ @[simp] theorem coefficientRestriction_apply {p q : P} (hqp : q ≤ p) (x : coefficientStalk K carrier p) (i : I) : (coefficientRestriction K carrier hqp x).val i
  = if carrier i ≤ q then x.val i else 0 := by sorry
/-- Literal FourPapers.Universal.coefficientDiagram; source theorem12.lean:8340. -/ abbrev coefficientDiagram : ModuleDiagram K P where
  obj p := coefficientStalk K carrier p
  res h := coefficientRestriction K carrier h
  res_refl p x := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    by_cases hi : carrier i ≤ p
    · simp [hi]
    · have hx := (Finsupp.mem_supported' K x.val).mp x.property i hi
      simp [hi, hx]
  res_comp := by
    intro p q r hqp hrq x
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    by_cases hi : carrier i ≤ r
    · have hiq := hi.trans hrq
      simp [hi, hiq]
    · simp [hi]
/-- Literal FourPapers.Universal.coefficientSection; source theorem12.lean:8361. -/ def coefficientSection : (I →₀ K) →ₗ[K] (coefficientDiagram K carrier).sections where
  toFun x := ⟨fun p => Finsupp.restrictDom K K {i | carrier i ≤ p} x, by
    intro p q hqp
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    change (if carrier i ≤ q then (if carrier i ≤ p then x i else 0) else 0) =
      (if carrier i ≤ q then x i else 0)
    by_cases hi : carrier i ≤ q
    · have hip := hi.trans hqp
      simp [hi, hip]
    · simp [hi]⟩
  map_add' x y := by
    apply Subtype.ext
    funext p
    exact map_add (Finsupp.restrictDom K K {i | carrier i ≤ p}) x y
  map_smul' c x := by
    apply Subtype.ext
    funext p
    exact map_smul (Finsupp.restrictDom K K {i | carrier i ≤ p}) c x
/-- Literal FourPapers.Universal.coefficientAtCarrier; source theorem12.lean:8386. -/ def coefficientAtCarrier (x : (coefficientDiagram K carrier).sections) (i : I) : K :=
  (x.val (carrier i)).val i
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical
variable {P I : Type*} [Preorder P]
variable (K : Type*) [CommRing K] (carrier : I → P)
variable [Fintype P]
/-- Literal FourPapers.Universal.coefficientAssembly; source theorem12.lean:8402. -/ def coefficientAssembly (x : (coefficientDiagram K carrier).sections) : I →₀ K :=
  Finsupp.onFinset (Finset.univ.biUnion fun p => (x.val p).val.support)
    (coefficientAtCarrier K carrier x) (by
      intro i hi
      apply Finset.mem_biUnion.mpr
      exact ⟨carrier i, Finset.mem_univ _, Finsupp.mem_support_iff.mpr hi⟩)
/-- Literal FourPapers.Universal.coefficientAssembly_section; source theorem12.lean:8412. -/ theorem coefficientAssembly_section (x : I →₀ K) : coefficientAssembly K carrier (coefficientSection K carrier x) = x := by sorry
/-- Literal FourPapers.Universal.coefficientSection_assembly; source theorem12.lean:8418. -/ theorem coefficientSection_assembly (x : (coefficientDiagram K carrier).sections) : coefficientSection K carrier (coefficientAssembly K carrier x) = x := by
  sorry
/-- Literal FourPapers.Universal.coefficientSectionEquiv; source theorem12.lean:8431. -/ def coefficientSectionEquiv : (I →₀ K) ≃ₗ[K] (coefficientDiagram K carrier).sections where
  toFun := coefficientSection K carrier
  invFun := coefficientAssembly K carrier
  left_inv := coefficientAssembly_section K carrier
  right_inv := coefficientSection_assembly K carrier
  map_add' := (coefficientSection K carrier).map_add
  map_smul' := (coefficientSection K carrier).map_smul
/-- Literal FourPapers.Universal.sectionsFromCoherentCoefficients; source theorem12.lean:8442. -/ def sectionsFromCoherentCoefficients (D : ModuleDiagram K P) (e : CoherentEquiv D (coefficientDiagram K carrier)) : D.sections ≃ₗ[K] (I →₀ K) :=
  e.sectionEquiv.trans (coefficientSectionEquiv K carrier).symm
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {V T K : Type*} [Fintype V] [DecidableEq V] [Fintype T] [CommRing K]
/-- Literal FourPapers.Universal.subsetExponent; source theorem12.lean:8826. -/ def subsetExponent (F : Finset V) : V →₀ ℕ :=
  ∑ v ∈ F, Finsupp.single v 1
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {V : Type*} [Fintype V] [LinearOrder V]
/-- Literal FourPapers.Universal.chainVertexMap; source theorem12.lean:9096. -/ def chainVertexMap : (BooleanFace V →₀ ℕ) →ₗ[ℕ] (V →₀ ℕ) :=
  Finsupp.linearCombination ℕ (fun F => subsetExponent F.val)
/-- Literal FourPapers.Universal.vertexHeight; source theorem12.lean:9199. -/ def vertexHeight (a : V →₀ ℕ) : ℕ := Finset.univ.sup (fun v => a v)
/-- Literal FourPapers.Universal.exponentLayer; source theorem12.lean:9204. -/ def exponentLayer (a : V →₀ ℕ) (k : Fin (vertexHeight a)) : BooleanFace V :=
  ⟨Finset.univ.filter (fun v => k.val < a v), by
    obtain ⟨v, hv, hkv⟩ := Finset.lt_sup_iff.mp k.isLt
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hkv⟩⟩⟩
/-- Literal FourPapers.Universal.layerExponent; source theorem12.lean:9213. -/ def layerExponent (a : V →₀ ℕ) : BooleanFace V →₀ ℕ :=
  ∑ k : Fin (vertexHeight a), Finsupp.single (exponentLayer a k) 1
/-- Literal FourPapers.Universal.layerExponent_isChain; source theorem12.lean:9231. -/ theorem layerExponent_isChain (a : V →₀ ℕ) : IsChainExponent (layerExponent a) := by sorry
/-- Literal FourPapers.Universal.chainVertexMap_layerExponent; source theorem12.lean:9245. -/ theorem chainVertexMap_layerExponent (a : V →₀ ℕ) : chainVertexMap (layerExponent a) = a := by sorry
/-- Literal FourPapers.Universal.chainVertexMap_chain_injective; source theorem12.lean:9347. -/ theorem chainVertexMap_chain_injective : Function.Injective (fun a : {a : BooleanFace V →₀ ℕ // IsChainExponent a} => chainVertexMap a.val) := by sorry
/-- Literal FourPapers.Universal.chainVertexEquiv; source theorem12.lean:9371. -/ def chainVertexEquiv : {a : BooleanFace V →₀ ℕ // IsChainExponent a} ≃ (V →₀ ℕ) where
  toFun a := chainVertexMap a.val
  invFun a := ⟨layerExponent a, layerExponent_isChain a⟩
  left_inv a := chainVertexMap_chain_injective (chainVertexMap_layerExponent (chainVertexMap a.val))
  right_inv := chainVertexMap_layerExponent
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {W : Type*} [Fintype W] [DecidableEq W]
/-- Literal FourPapers.Universal.chainVertexEquivUnordered; source theorem12.lean:9431. -/ def chainVertexEquivUnordered : {a : BooleanFace W →₀ ℕ // IsChainExponent a} ≃ (W →₀ ℕ) := by
  letI : LinearOrder W := LinearOrder.lift' (Fintype.equivFin W) (Fintype.equivFin W).injective
  exact chainVertexEquiv
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]
variable {K}
/-- Literal FourPapers.Universal.standardVertexEquiv; source theorem12.lean:9536. -/ def standardVertexEquiv (hs : IsSimplicialPoset P) (p : P) : StandardInside p ≃ (FaceVertex p →₀ ℕ) :=
  (standardInsideEquiv hs p).symm.trans chainVertexEquivUnordered
/-- Literal FourPapers.Universal.polynomialStandardBasis; source theorem12.lean:9553. -/ def polynomialStandardBasis (hs : IsSimplicialPoset P) (p : P) : Module.Basis (StandardInside p) K (PolynomialStalk K p) :=
  (MvPolynomial.basisMonomials (FaceVertex p) K).reindex (standardVertexEquiv hs p).symm
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
/-- Literal FourPapers.Universal.polynomialStandardCoordinates; source theorem12.lean:9813. -/ def polynomialStandardCoordinates (p : P) : PolynomialStalk K p ≃ₗ[K] coefficientStalk K (standardCarrier (P := P)) p :=
  (polynomialStandardBasis (K := K) hs p).repr.trans
    (Finsupp.supportedEquivFinsupp {a : StandardFaceIndex P | standardCarrier a ≤ p}).symm
/-- Literal FourPapers.Universal.polynomialStandardCoordinates_naturality; source theorem12.lean:9857. -/ theorem polynomialStandardCoordinates_naturality {p q : P} (hqp : q ≤ p) (f : PolynomialStalk K p) : coefficientRestriction K standardCarrier hqp
  (polynomialStandardCoordinates K hs p f) = polynomialStandardCoordinates K hs q (polynomialRestriction K hqp f) := by sorry
/-- Literal FourPapers.Universal.polynomialCoefficientEquiv; source theorem12.lean:9885. -/ def polynomialCoefficientEquiv : CoherentEquiv (polynomialDiagram (P := P) K) (coefficientDiagram K (standardCarrier (P := P))) where
  component := polynomialStandardCoordinates K hs
  naturality p q hqp f := polynomialStandardCoordinates_naturality K hs hqp f
/-- Literal FourPapers.Universal.polynomialSectionCoordinates; source theorem12.lean:9892. -/ def polynomialSectionCoordinates : (polynomialDiagram (P := P) K).sections ≃ₗ[K] (StandardFaceIndex P →₀ K) :=
  sectionsFromCoherentCoefficients K standardCarrier (polynomialDiagram K)
    (polynomialCoefficientEquiv K hs)
/-- Literal FourPapers.Universal.standardFaceCombination; source theorem12.lean:9897. -/ def standardFaceCombination : (StandardFaceIndex P →₀ K) →ₗ[K] FaceRing K hs :=
  Finsupp.linearCombination K (fun a => faceRingMonomial K hs a.val)
/-- Literal FourPapers.Universal.standardFaceCombination_surjective; source theorem12.lean:9900. -/ theorem standardFaceCombination_surjective : Function.Surjective (standardFaceCombination K hs) := by sorry
/-- Literal FourPapers.Universal.standardFaceCombination_coefficients; source theorem12.lean:9913. -/ theorem standardFaceCombination_coefficients (x : StandardFaceIndex P →₀ K) : polynomialSectionCoordinates K hs (faceRingSection K hs (standardFaceCombination K
  hs x)) = x := by sorry
/-- Literal FourPapers.Universal.standardFaceBasis; source theorem12.lean:9949. -/ def standardFaceBasis : Module.Basis (StandardFaceIndex P) K (FaceRing K hs) :=
  Module.Basis.ofRepr (LinearEquiv.ofBijective (standardFaceCombination K hs)
    ⟨by
      intro x y hxy
      have h := congrArg (fun f => polynomialSectionCoordinates K hs (faceRingSection K hs f)) hxy
      simpa only [standardFaceCombination_coefficients] using h,
      standardFaceCombination_surjective K hs⟩).symm
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {V C : Type*} [Fintype V] [Fintype C]
/-- Literal FourPapers.Universal.ProperlyColoredComplex; source theorem12.lean:16347. -/ structure ProperlyColoredComplex (V C : Type*) where
  face : Finset V → Prop
  downward : ∀ ⦃s t : Finset V⦄, s ⊆ t → face t → face s
  color : V → C
  proper : ∀ s, face s → Set.InjOn color (s : Set V)
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CommAlg
universe u v
variable {K : Type u} {V : Type v} [CommRing K] [Fintype V] [LinearOrder V]
/-- Literal FourPapers.Universal.augmentedFaceBoundary; source theorem12.lean:17362. -/ def augmentedFaceBoundary (Λ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (i : ℕ) : Simplicial.Chains (k := K) Λ (i + 1) →ₗ[K] Simplicial.Chains (k := K) Λ i :=
  (Simplicial.boundary.domRestrict (Simplicial.Chains Λ (i + 1))).codRestrict _
    (fun x => Simplicial.boundary_mem hΛ x.property)
/-- Literal FourPapers.Universal.rankSelection; source theorem12.lean:17435. -/ def rankSelection {C : Type*} [DecidableEq C] (D : ProperlyColoredComplex V C) (S : Finset C) : Finset V → Prop := fun F => D.face F ∧ F.image D.color ⊆ S
/-- Literal FourPapers.Universal.rankSelection_downward; source theorem12.lean:17438. -/ theorem rankSelection_downward {C : Type*} [DecidableEq C] (D : ProperlyColoredComplex V C) (S : Finset C) : Simplicial.Downward (rankSelection D S) := by sorry
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {V C : Type*} [Fintype V] [Fintype C]
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
/-- Literal FourPapers.Universal.rankColoredOrderComplex; source theorem12.lean:16492. -/ def rankColoredOrderComplex (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) : ProperlyColoredComplex (NonzeroFace P) (Fin d) where
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
set_option backward.isDefEq.respectTransparency false
open Classical
variable {K : Type*} [CommRing K]
/-- Literal FourPapers.FilteredHomology.Filtration; source theorem12.lean:16662. -/ structure Filtration (M : Type*) [AddCommGroup M] [Module K M] where
  level : ℕ → Submodule K M
  zero : level 0 = ⊥
  mono : Monotone level
  exhaustive : ∀ x : M, ∃ n, x ∈ level n
end FourPapers.FilteredHomology
namespace FourPapers.FilteredHomology
set_option backward.isDefEq.respectTransparency false
open Classical
variable {K : Type*} [CommRing K]
variable {X Y Z : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z]
/-- Literal FourPapers.FilteredHomology.lowerInLevel; source theorem12.lean:16698. -/ def lowerInLevel (F : Filtration (K := K) X) (n : ℕ) : Submodule K (F.level (n + 1)) :=
  (F.level n).comap (F.level (n + 1)).subtype
/-- Literal FourPapers.FilteredHomology.Grade; source theorem12.lean:16701. -/ abbrev Grade (F : Filtration (K := K) X) (n : ℕ) :=
  F.level (n + 1) ⧸ lowerInLevel F n
/-- Literal FourPapers.FilteredHomology.boundaryMap; source theorem12.lean:16731. -/ def boundaryMap (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) : X →ₗ[K] LinearMap.ker g :=
  f.codRestrict _ (fun x => LinearMap.congr_fun hfg x)
/-- Literal FourPapers.FilteredHomology.Homology; source theorem12.lean:16735. -/ abbrev Homology (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) :=
  LinearMap.ker g ⧸ LinearMap.range (boundaryMap f g hfg)
/-- Literal FourPapers.FilteredHomology.homologyClass; source theorem12.lean:16738. -/ def homologyClass (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) : LinearMap.ker g →ₗ[K] Homology f g hfg := (LinearMap.range (boundaryMap f g hfg)).mkQ
/-- Literal FourPapers.FilteredHomology.cycleLevel; source theorem12.lean:16751. -/ def cycleLevel (F : Filtration (K := K) Y) (g : Y →ₗ[K] Z) (n : ℕ) : Submodule K (LinearMap.ker g) := (F.level n).comap (LinearMap.ker g).subtype
/-- Literal FourPapers.FilteredHomology.homologyLevel; source theorem12.lean:16754. -/ def homologyLevel (F : Filtration (K := K) Y) (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) (n : ℕ) : Submodule K (Homology f g hfg) :=
  (cycleLevel F g n).map (homologyClass f g hfg)
/-- Literal FourPapers.FilteredHomology.homologyFiltration; source theorem12.lean:16758. -/ def homologyFiltration (F : Filtration (K := K) Y) (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) : Filtration (K := K) (Homology f g hfg) where
  level := homologyLevel F f g hfg
  zero := by simp [homologyLevel, cycleLevel, F.zero]
  mono := fun _ _ h => Submodule.map_mono (Submodule.comap_mono (F.mono h))
  exhaustive x := by
    obtain ⟨z, rfl⟩ := (LinearMap.range (boundaryMap f g hfg)).mkQ_surjective x
    obtain ⟨n, hn⟩ := F.exhaustive z.val
    exact ⟨n, z, hn, rfl⟩
end FourPapers.FilteredHomology
namespace FourPapers.FilteredHomology
set_option backward.isDefEq.respectTransparency false
open Classical
variable {K X Y Z : Type*} [CommRing K] [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z]
/-- Literal FourPapers.FilteredHomology.submoduleFiltration; source theorem12.lean:19027. -/ def submoduleFiltration (F : Filtration (K := K) X) (N : Submodule K X) : Filtration (K := K) N where
  level n := (F.level n).comap N.subtype
  zero := by simp only [F.zero, Submodule.comap_bot, LinearMap.ker_eq_bot.mpr N.injective_subtype]
  mono := fun _ _ h => Submodule.comap_mono (F.mono h)
  exhaustive x := F.exhaustive x.val
/-- Literal FourPapers.FilteredHomology.restrictedMap; source theorem12.lean:19034. -/ def restrictedMap (f : X →ₗ[K] Y) (N : Submodule K X) (M : Submodule K Y) (hNM : ∀ x, x ∈ N → f x ∈ M) : N →ₗ[K] M :=
  (f.domRestrict N).codRestrict M (fun x => hNM x.val x.property)
end FourPapers.FilteredHomology
namespace FourPapers.Universal.ProperlyColoredComplex
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {C : Type*} [LinearOrder C] [DecidableEq C]
variable {V : Type*} [Fintype V]
variable (D : FourPapers.Universal.ProperlyColoredComplex V C)
/-- Literal FourPapers.Universal.ProperlyColoredComplex.colorLinearOrder; source theorem12.lean:18025. -/ def colorLinearOrder : LinearOrder V :=
  LinearOrder.lift' (fun v => toLex (D.color v, (Fintype.equivFin V) v)) (by
    intro v w h
    apply (Fintype.equivFin V).injective
    exact congrArg (fun p => (ofLex p).2) h)
end FourPapers.Universal.ProperlyColoredComplex
namespace FourPapers.BasisGrading
set_option backward.isDefEq.respectTransparency false
open Classical
variable {R M I A : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
/-- Literal FourPapers.BasisGrading.Piece; source theorem12.lean:18578. -/ def Piece (b : Module.Basis I R M) (deg : I → A) (a : A) : Submodule R M :=
  Submodule.span R (b '' {i | deg i = a})
end FourPapers.BasisGrading
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical FourPapers.FilteredHomology
variable {K I J X Y : Type*} [CommRing K] [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
/-- Literal FourPapers.Universal.basisFiltration; source theorem12.lean:19426. -/ def basisFiltration (b : Module.Basis I K X) (w : I → ℕ) : Filtration (K := K) X where
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
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical CategoryTheory CommAlg
universe u v
variable {K B B' : Type u} {C : Type} [CommRing K] [CommRing B] [CommRing B'] [Algebra K B] [Algebra K B'] [Fintype C] [LinearOrder C]
/-- Literal FourPapers.Universal.parameterKoszulDifferential; source theorem12.lean:19834. -/ def parameterKoszulDifferential (γ : C → B) (i : ℕ) : (Set.powersetCard C (i + 1) →₀ B) →ₗ[K] (Set.powersetCard C i →₀ B) :=
  (Koszul.coordinateDifferential γ (ModuleCat.of B B) i).restrictScalars K
/-- Literal FourPapers.Universal.parameterKoszulDifferential_comp; source theorem12.lean:19838. -/ theorem parameterKoszulDifferential_comp (γ : C → B) (i : ℕ) : (parameterKoszulDifferential (K := K) γ i).comp (parameterKoszulDifferential (K := K) γ (i + 1))
  = 0 := by sorry
/-- Literal FourPapers.Universal.parameterKoszulComplex; source theorem12.lean:19852. -/ def parameterKoszulComplex (γ : C → B) : ChainComplex (ModuleCat.{u} K) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of K (Set.powersetCard C i →₀ B))
    (fun i => ModuleCat.ofHom (parameterKoszulDifferential (K := K) γ i))
    (fun i => ModuleCat.hom_ext (parameterKoszulDifferential_comp (K := K) γ i))
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical CategoryTheory CommAlg
universe u v
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
/-- Literal FourPapers.Universal.originalKoszulComplex; source theorem12.lean:19900. -/ abbrev originalKoszulComplex : ChainComplex (ModuleCat.{u} K) ℕ :=
  parameterKoszulComplex (K := K) (fun i : Fin d => faceRankParameter K hs (i.val + 1))
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical CategoryTheory FourPapers.FilteredHomology
universe u
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ)
/-- Literal FourPapers.Universal.originalKoszulBasis; source theorem12.lean:19946. -/ def originalKoszulBasis (i : ℕ) : Module.Basis (OriginalKoszulIndex P d i) K (Set.powersetCard (Fin d) i →₀ FaceRing K hs) :=
  Finsupp.basis (fun _ => standardFaceBasis K hs)
/-- Literal FourPapers.Universal.originalKoszulFiltration; source theorem12.lean:19954. -/ def originalKoszulFiltration (i : ℕ) : Filtration (K := K) (Set.powersetCard (Fin d) i →₀ FaceRing K hs) :=
  basisFiltration (originalKoszulBasis K hs d i) (fun a => (originalKoszulWeight d a).toNat)
/-- Literal FourPapers.Universal.originalKoszulDegreePiece; source theorem12.lean:19962. -/ def originalKoszulDegreePiece (i j : ℕ) :=
  FourPapers.BasisGrading.Piece (originalKoszulBasis K hs d i) originalKoszulDegree j
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical CategoryTheory FourPapers.FilteredHomology
universe u
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
/-- Literal FourPapers.Universal.originalKoszulDifferential; source theorem12.lean:20328. -/ abbrev originalKoszulDifferential (i : ℕ) := parameterKoszulDifferential (K := K)
  (fun j : Fin d => faceRankParameter K hs (j.val + 1)) i
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical CategoryTheory FourPapers.FilteredHomology
universe u
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
include hrank
/-- Literal FourPapers.Universal.originalKoszulDifferential_degree; source theorem12.lean:20382. -/ theorem originalKoszulDifferential_degree (i j : ℕ) (x : Set.powersetCard (Fin d) (i + 1) →₀ FaceRing K hs) (hx : x ∈ originalKoszulDegreePiece K hs d (i + 1)
  j) : originalKoszulDifferential K hs d i x ∈ originalKoszulDegreePiece K hs d i j := by sorry
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical CategoryTheory FourPapers.FilteredHomology
universe u
variable {K : Type u} [CommRing K]
variable {P : Type u} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
/-- Literal FourPapers.Universal.originalKoszulDegreeDifferential; source theorem12.lean:20590. -/ def originalKoszulDegreeDifferential (j i : ℕ) : originalKoszulDegreePiece K hs d (i + 1) j →ₗ[K] originalKoszulDegreePiece K hs d i j :=
  restrictedMap (originalKoszulDifferential K hs d i) _ _
    (originalKoszulDifferential_degree K hs d hrank i j)
/-- Literal FourPapers.Universal.originalKoszulDegreeComplex; source theorem12.lean:20595. -/ def originalKoszulDegreeComplex (j : ℕ) : ChainComplex (ModuleCat.{u} K) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of K (originalKoszulDegreePiece K hs d i j))
    (fun i => ModuleCat.ofHom (originalKoszulDegreeDifferential K hs d hrank j i)) (by
      intro i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact LinearMap.congr_fun (parameterKoszulDifferential_comp
        (K := K) (fun r : Fin d => faceRankParameter K hs (r.val + 1)) i) x.val)
/-- Literal FourPapers.Universal.originalDegreeTermFiltration; source theorem12.lean:20665. -/ def originalDegreeTermFiltration (j i : ℕ) : Filtration (K := K) (originalKoszulDegreePiece K hs d i j) :=
  submoduleFiltration (originalKoszulFiltration K hs d i) (originalKoszulDegreePiece K hs d i j)
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical CategoryTheory FourPapers.FilteredHomology
universe u
variable {K : Type u} [CommRing K]
/-- Literal FourPapers.Universal.complexKernelHomology; source theorem12.lean:20431. -/ abbrev complexKernelHomology (C : ChainComplex (ModuleCat.{u} K) ℕ) (i : ℕ) :=
  Homology (complexIncoming C i) (complexOutgoing C i) (complexIncomingOutgoing C i)
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical CategoryTheory FourPapers.FilteredHomology
universe u
variable {K : Type u} [CommRing K]
variable {P : Type u} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
/-- Literal FourPapers.Universal.originalInternalKoszulHomology; source theorem12.lean:20688. -/ abbrev originalInternalKoszulHomology (j i : ℕ) :=
  complexKernelHomology (originalKoszulDegreeComplex K hs d hrank j) i
/-- Literal FourPapers.Universal.originalInternalHomologyFiltration; source theorem12.lean:20691. -/ def originalInternalHomologyFiltration (j i : ℕ) : Filtration (K := K) (originalInternalKoszulHomology K hs d hrank j i) :=
  homologyFiltration (originalDegreeTermFiltration K hs d j i)
    (complexIncoming (originalKoszulDegreeComplex K hs d hrank j) i)
    (complexOutgoing (originalKoszulDegreeComplex K hs d hrank j) i)
    (complexIncomingOutgoing (originalKoszulDegreeComplex K hs d hrank j) i)
/-- Literal FourPapers.Universal.originalInternalHomologyFiltration_finite; source theorem12.lean:20699. -/ theorem originalInternalHomologyFiltration_finite (j i : ℕ) : (originalInternalHomologyFiltration K hs d hrank j i).level (2 * d * j + 1) = ⊤ := by sorry
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
universe u
variable {K P : Type u} [CommRing K] [PartialOrder P] [OrderBot P] [Fintype P]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
local instance originalParameterAlgebra : Algebra (MvPolynomial (Fin d) K) (FaceRing K hs) :=
  (faceParameterAction K hs d).toRingHom.toAlgebra
/-- The module action is explicitly the actual parameter algebra's scalar action. -/
local instance originalParameterModule : Module (MvPolynomial (Fin d) K) (FaceRing K hs) :=
  @Algebra.toModule _ _ _ _ (originalParameterAlgebra K hs d)
/-- Literal FourPapers.Universal.originalParameterTor; source theorem12.lean:23219. -/ def originalParameterTor (m : ℕ) : ModuleCat.{u} K :=
  (ModuleCat.restrictScalars (algebraMap K (MvPolynomial (Fin d) K))).obj
    (((Tor (ModuleCat (MvPolynomial (Fin d) K)) m).obj
      (ModuleCat.of (MvPolynomial (Fin d) K) (FaceRing K hs))).obj
        (CommAlg.Koszul.residueCoefficientModule (V := Fin d) (k := K)))
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open scoped DirectSum
open Classical FourPapers.FilteredHomology
universe u v
variable {P K : Type u} {G : Type v} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K] [Group G]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
/-- Literal FourPapers.Universal.rankSubsetDegree; source theorem12.lean:25192. -/ def rankSubsetDegree {d : ℕ} (S : Finset (Fin d)) : ℕ := ∑ r ∈ S, (r.val + 1)
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Classical CategoryTheory CommAlg
universe u v
variable {K : Type u} {V : Type v} [CommRing K] [Fintype V] [LinearOrder V]
/-- Literal FourPapers.Universal.augmentedCoboundary; source theorem12.lean:33851. -/ def augmentedCoboundary (Λ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (i : ℕ) : Module.Dual K (Simplicial.Chains (k := K) Λ i) →ₗ[K] Module.Dual K (Simplicial.Chains (k := K) Λ (i + 1)) :=
  (augmentedFaceBoundary Λ hΛ i).dualMap
/-- Literal FourPapers.Universal.augmentedCoboundary_square; source theorem12.lean:33856. -/ theorem augmentedCoboundary_square (Λ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (i : ℕ) : (augmentedCoboundary (K := K) Λ hΛ (i + 1)).comp
  (augmentedCoboundary (K := K) Λ hΛ i) = 0 := by sorry
/-- Literal FourPapers.Universal.augmentedCochainComplex; source theorem12.lean:33870. -/ def augmentedCochainComplex (Λ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) : CochainComplex (ModuleCat.{max u v} K) ℕ :=
  CochainComplex.of
    (fun i => ModuleCat.of K (Module.Dual K (Simplicial.Chains (k := K) Λ i)))
    (fun i => ModuleCat.ofHom (augmentedCoboundary Λ hΛ i))
    (fun i => ModuleCat.hom_ext (augmentedCoboundary_square Λ hΛ i))
/-- Literal FourPapers.Universal.reducedCohomology; source theorem12.lean:33884. -/ def reducedCohomology (Λ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (q : ℤ) : ModuleCat.{max u v} K :=
  if -1 ≤ q then (augmentedCochainComplex (K := K) Λ hΛ).homology (q + 1).toNat
  else ModuleCat.of K (ULift.{v} (Fin 0 → K))
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open scoped DirectSum
set_option backward.isDefEq.respectTransparency.types false
open Classical CategoryTheory FourPapers.FilteredHomology
universe u v
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
/-- Literal FourPapers.Universal.rankSelectedCohomology; source theorem12.lean:34159. -/ abbrev rankSelectedCohomology (S : Finset (Fin d)) (i : ℕ) :=
  letI : LinearOrder (NonzeroFace P) := (rankColoredOrderComplex hs d hrank).colorLinearOrder
  letI : DecidableEq (Fin d) := Classical.decEq _
  letI : DecidableEq (NonzeroFace P) := Classical.decEq _
  reducedCohomology (K := K) (rankSelection (rankColoredOrderComplex hs d hrank) S)
    (rankSelection_downward (rankColoredOrderComplex hs d hrank) S)
    ((S.card : ℤ) - i - 1)
end FourPapers.Universal
namespace PalomarBarycentricTor
open Classical CategoryTheory FourPapers.Universal FourPapers.FilteredHomology
universe u
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [Field K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
/-- Literal PalomarBarycentricTor.actualDerivedTorComparison; source theorem12.lean:999998. -/ theorem actualDerivedTorComparison (i : ℕ) : Nonempty (originalParameterTor K hs d i ≅ (originalKoszulComplex K hs d).homology i) := by sorry
/-- Literal PalomarBarycentricTor.associatedGraded; source theorem12.lean:999999. -/ theorem associatedGraded (j i : ℕ) : Nonempty ((⨁ n, Grade (originalInternalHomologyFiltration K hs d hrank j i) n) ≃ₗ[K] (⨁ (S : {S : Finset (Fin d) //
  rankSubsetDegree S = j}), rankSelectedCohomology K hs d hrank S.val i)) := by sorry
end PalomarBarycentricTor

-- Exact environment type lookups only; no values, traversal or source-project import.
run_cmd do
  let env ← Lean.getEnv
  for name in #[`FourPapers.Universal.complexIncoming._proof_1, `CommAlg.Simplicial.boundary._proof_1, `CommAlg.Simplicial.boundary._proof_2, `CommAlg.Simplicial.boundary._proof_3, `FourPapers.Universal.CoherentEquiv.trans._proof_2, `FourPapers.Universal.CoherentEquiv.trans._proof_3, `CommAlg.Koszul.familyCoefficientComplex._proof_1, `CommAlg.Koszul.familyCoefficientComplex._proof_2] do
    match env.find? name with
    | none => Lean.logInfo m!"{(Lean.Json.mkObj [("kind", Lean.toJson "BARYCENTRIC_INVARIANCE_TOR_AUXILIARY_TYPE"), ("name", Lean.toJson name.toString), ("found", Lean.toJson false)]).compress}"
    | some ci =>
      let raw := reprStr ci.type
      let pretty ← Lean.Elab.Command.liftTermElabM do
        return (← Lean.Meta.ppExpr ci.type).pretty
      let rec conclusion : Lean.Expr → Nat → Lean.Expr × Nat
        | .forallE _ _ b _, n => conclusion b (n+1)
        | e, n => (e,n)
      let (body, binders) := conclusion ci.type 0
      let head := match body.getAppFn with | .const n _ => n.toString | _ => "nonconstant"
      let row := Lean.Json.mkObj [("kind", Lean.toJson "BARYCENTRIC_INVARIANCE_TOR_AUXILIARY_TYPE"), ("name", Lean.toJson name.toString), ("found", Lean.toJson true), ("level_params", Lean.toJson (ci.levelParams.map Lean.Name.toString)), ("binders", Lean.toJson binders), ("conclusion_head", Lean.toJson head),
        ("type_characters", Lean.toJson raw.length), ("type_ast", Lean.toJson (String.ofList (raw.toList.take 2000))), ("type_ast_limit", Lean.toJson (2000 : Nat)), ("type_ast_truncated", Lean.toJson (decide (2000 < raw.length))),
        ("readable_type", Lean.toJson (String.ofList (pretty.toList.take 1600))), ("readable_characters", Lean.toJson pretty.length), ("readable_truncated", Lean.toJson (decide (1600 < pretty.length))), ("readable_is_full_explicit_ast", Lean.toJson false)]
      Lean.logInfo m!"{row.compress}"
