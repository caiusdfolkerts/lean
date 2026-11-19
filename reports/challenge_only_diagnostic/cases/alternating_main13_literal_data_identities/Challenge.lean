module
public import Mathlib
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace PalomarAlternatingDegeneration
namespace Model
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
def coefficient (j : ℕ) : Polynomial A →ₗ[K] A := (Polynomial.lcoeff A j).restrictScalars K
end Model
namespace TauCeti
section
open scoped DirectSum
universe u v w
variable (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]
structure InternalGrading (ι : Type := ℤ) [DecidableEq ι] where
  piece : ι → Submodule R M
  isInternal : DirectSum.IsInternal piece
end
end TauCeti
namespace TauCeti.InternalGrading
section
variable {R M N : Type*} {ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [DecidableEq ι]
theorem mapInternal (G : TauCeti.InternalGrading R M ι) (e : M ≃ₗ[R] N) : DirectSum.IsInternal (fun p => (G.piece p).map e.toLinearMap) := by sorry
def map (G : TauCeti.InternalGrading R M ι) (e : M ≃ₗ[R] N) : TauCeti.InternalGrading R N ι where
  piece p := (G.piece p).map e.toLinearMap
  isInternal := mapInternal G e
@[simp] theorem map_piece (G : TauCeti.InternalGrading R M ι) (e : M ≃ₗ[R] N) (p : ι) : (G.map e).piece p = (G.piece p).map e.toLinearMap := rfl
end
end TauCeti.InternalGrading
namespace TauCeti
section
end
end TauCeti
namespace PaperVerification.AlternatingForms
section
open scoped BigOperators
def pathVertexCost (e : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | j + 1 => e j - pathVertexCost e j
end
end PaperVerification.AlternatingForms
namespace PaperVerification.AlternatingForms
section
open scoped BigOperators
variable {ι : Type*} [Fintype ι]
def positiveWeightShift (u : ι → ℤ) : ℤ := 1 + ∑ i, |u i|
end
end PaperVerification.AlternatingForms
namespace PaperVerification.AlternatingForms
section
open MvPolynomial Matrix
open scoped BigOperators
variable {K : Type*} [Field K] {s n : ℕ}
def bandEntryCoefficient (α β : Fin s → Fin n) (i : Fin s) (j : Fin n) : K :=
  if α i ≤ j ∧ j ≤ β i then 1 else 0
def bandMatrix (α β : Fin s → Fin n) :
    Matrix (Fin s) (Fin n) (MvPolynomial (Fin s × Fin n) K) :=
  fun i j => monomial (Finsupp.single (i,j) 1) (bandEntryCoefficient α β i j)
def bandMinor (α β I : Fin s → Fin n) : MvPolynomial (Fin s × Fin n) K :=
  ((bandMatrix (K := K) α β).submatrix id I).det
def minorTermExponent (I : Fin s → Fin n) (σ : Equiv.Perm (Fin s)) :
    (Fin s × Fin n) →₀ ℕ := ∑ i, Finsupp.single (σ i,I i) 1
def PluckerIndex (s n : ℕ) := {I : Fin s → Fin n // StrictMono I}
instance pluckerFintype (s n : ℕ) : Fintype (PluckerIndex s n) := by classical unfold PluckerIndex; infer_instance
instance pluckerOrder (s n : ℕ) : PartialOrder (PluckerIndex s n) := by unfold PluckerIndex; infer_instance
def genericPluckerMinor (I : PluckerIndex s n) : MvPolynomial (Fin s × Fin n) K :=
  (Matrix.of fun i j : Fin s => (X (i,I.val j) : MvPolynomial (Fin s × Fin n) K)).det
def genericPluckerMap :
    MvPolynomial (PluckerIndex s n) K →ₐ[K] MvPolynomial (Fin s × Fin n) K :=
  aeval genericPluckerMinor
def matrixPluckerIdeal : Ideal (MvPolynomial (PluckerIndex s n) K) :=
  RingHom.ker (genericPluckerMap (K := K) (s := s) (n := n)).toRingHom
def intervalPluckerIdeal (α β : Fin s → Fin n) : Ideal (MvPolynomial (PluckerIndex s n) K) :=
  matrixPluckerIdeal ⊔ Ideal.span
    {p | ∃ I : PluckerIndex s n, (¬∀ i, α i ≤ I.val i ∧ I.val i ≤ β i) ∧ p = X I}
end
end PaperVerification.AlternatingForms
namespace PaperVerification.AlternatingForms
section
open scoped BigOperators
open MvPolynomial Matrix
variable {K : Type*} [Field K] {s n : ℕ}
def sortedPluckerIndex (I : Fin s → Fin n) (hI : Function.Injective I) :
    PluckerIndex s n :=
  ⟨I ∘ Tuple.sort I,(Tuple.monotone_sort I).strictMono_of_injective
    (hI.comp (Tuple.sort I).injective)⟩
def orderedPluckerCoordinate (I : Fin s → Fin n) : MvPolynomial (PluckerIndex s n) K :=
  if hI : Function.Injective I then
    (((Equiv.Perm.sign (Tuple.sort I).symm : ℤ) : K) • X (sortedPluckerIndex I hI))
  else 0
end
end PaperVerification.AlternatingForms
namespace PaperVerification.AlternatingForms
section
abbrev StrictPairs (m : ℕ) := {p : Fin m × Fin m // p.1 < p.2}
end
end PaperVerification.AlternatingForms
namespace PaperVerification.AlternatingForms
section
open scoped BigOperators
open MvPolynomial Matrix
variable {K : Type*} [Field K] {t n m : ℕ}
def pluckerIsotropyEquation (f : StrictPairs n → K) (J : Fin t → Fin n) :
    MvPolynomial (PluckerIndex (t+2) n) K :=
  ∑ a : StrictPairs n, f a •
    orderedPluckerCoordinate (Fin.cons a.val.1 (Fin.cons a.val.2 J))
def isotropicPluckerIdeal (forms : Fin m → StrictPairs n → K) :
    Ideal (MvPolynomial (PluckerIndex (t+2) n) K) :=
  matrixPluckerIdeal ⊔ Ideal.span (Set.range fun a : Fin m × (Fin t → Fin n) =>
    pluckerIsotropyEquation (forms a.1) a.2)
end
end PaperVerification.AlternatingForms
namespace PaperVerification.AlternatingForms
section
open scoped BigOperators
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
def oddPathEdgeCost (k j : ℕ) : ℤ :=
  if Even j then (2 : ℤ) ^ (j / 2 + 1) else (2 : ℤ) ^ (k - j / 2)
def oddPathVertexCost (k : ℕ) (i : Fin (2 * k + 1)) : ℤ :=
  pathVertexCost (oddPathEdgeCost k) i.val
def oddPathVertexWeight (k : ℕ) (i : Fin (2 * k + 1)) : ℤ :=
  positiveWeightShift (oddPathVertexCost k) - oddPathVertexCost k i
end
end PaperVerification.AlternatingForms
namespace PaperVerification.AlternatingForms
section
open MvPolynomial Matrix
open scoped BigOperators
variable {K : Type*} [Field K] {k t : ℕ}
def oddPluckerEdge (k : ℕ) (l : Fin 2) (i : Fin k) : StrictPairs (2*k+1) :=
  ⟨(⟨2*i.val+l.val,by have := i.isLt; have := l.isLt; omega⟩,
    ⟨2*i.val+l.val+1,by have := i.isLt; have := l.isLt; omega⟩),by
      change 2*i.val+l.val < 2*i.val+l.val+1
      omega⟩
def oddPluckerForms (k : ℕ) (l : Fin 2) (a : StrictPairs (2*k+1)) : K :=
  ∑ i : Fin k, if a=oddPluckerEdge k l i then 1 else 0
end
end PaperVerification.AlternatingForms
namespace PaperVerification.WeightedInitialFiber
section
open scoped BigOperators
open MvPolynomial
variable {K σ : Type*} [Field K]
local notation "P" => MvPolynomial σ K
def scaledPolynomial (w : σ → ℕ) : P →ₐ[K] Polynomial P :=
  MvPolynomial.aeval (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ w i)
def scaledQuotient (Q : Ideal P) (w : σ → ℕ) : P →ₐ[K] Polynomial (P ⧸ Q) :=
  (Polynomial.mapAlgHom (Ideal.Quotient.mkₐ K Q)).comp (scaledPolynomial w)
def reesMap (Q : Ideal P) (w : σ → ℕ) :
    Polynomial P →ₐ[K] Polynomial (P ⧸ Q) :=
  Polynomial.aevalTower (scaledQuotient Q w) (Polynomial.X : Polynomial (P ⧸ Q))
def reesAlgebra (Q : Ideal P) (w : σ → ℕ) : Subalgebra K (Polynomial (P ⧸ Q)) :=
  (reesMap Q w).range
theorem reesMultiplicationCommutes (Q : Ideal P) (w : σ → ℕ) (a b : reesAlgebra Q w) : a*b=b*a := by sorry
instance reesAlgebraCommRing (Q : Ideal P) (w : σ → ℕ) : CommRing (reesAlgebra Q w) := by
  let ringInst : Ring (reesAlgebra Q w) := inferInstance
  exact {ringInst with mul_comm := reesMultiplicationCommutes Q w}
def reesCover (Q : Ideal P) (w : σ → ℕ) : Polynomial P →ₐ[K] reesAlgebra Q w :=
  (reesMap Q w).rangeRestrict
def reesParameter (Q : Ideal P) (w : σ → ℕ) : reesAlgebra Q w :=
  reesCover Q w Polynomial.X
def reesParameterMap (Q : Ideal P) (w : σ → ℕ) : Polynomial K →ₐ[K] reesAlgebra Q w := Polynomial.aeval (reesParameter Q w)
instance reesPolynomialAlgebra (Q : Ideal P) (w : σ → ℕ) : Algebra (Polynomial K) (reesAlgebra Q w) := (reesParameterMap Q w).toRingHom.toAlgebra
abbrev ZeroFiber (Q : Ideal P) (w : σ → ℕ) :=
  reesAlgebra Q w ⧸ Ideal.span ({reesParameter Q w} : Set (reesAlgebra Q w))
end
end PaperVerification.WeightedInitialFiber
namespace PaperVerification.AlternatingForms
section
open scoped BigOperators
open MvPolynomial
variable {K : Type*} [Field K] {k s n : ℕ}
def oddNatVertexWeight (k : ℕ) (i : Fin (2*k+1)) : ℕ :=
  (oddPathVertexWeight k i).toNat
def pluckerVertexWeight (w : Fin n → ℕ) (I : PluckerIndex s n) : ℕ :=
  ∑ i,w (I.val i)
end
end PaperVerification.AlternatingForms
namespace PaperVerification.AlternatingForms
section
open scoped BigOperators
open PaperVerification.WeightedInitialFiber
open MvPolynomial
variable {K : Type*} [Field K] {k s t : ℕ}
def oddIntervalLower (k s : ℕ) (hs : s≤k+1) (i : Fin s) : Fin (2*k+1) :=
  ⟨2*i.val,by have := i.isLt; omega⟩
def oddIntervalUpper (k s : ℕ) (hs : s≤k+1) (i : Fin s) : Fin (2*k+1) :=
  ⟨2*(k+1-s+i.val),by have := i.isLt; omega⟩
end
end PaperVerification.AlternatingForms
namespace TauCeti.ExteriorAlgebra
section
open CliffordAlgebra
universe u v w
variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
theorem contractLeft_mem_exteriorPower (d : Module.Dual R M) {n : ℕ}
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^(n + 1) M) :
    contractLeft (Q := (0 : QuadraticForm R M)) d x ∈ ⋀[R]^n M := by sorry
end
end TauCeti.ExteriorAlgebra
namespace PaperVerification.WeightedInitialFiber
section
open scoped BigOperators
open MvPolynomial
variable {K σ : Type*} [Field K]
local notation "P" => MvPolynomial σ K
abbrev ParameterFiber (Q : Ideal P) (w : σ → ℕ) (c : K) :=
  reesAlgebra Q w ⧸ Ideal.span
    ({reesParameter Q w-algebraMap K (reesAlgebra Q w) c} : Set (reesAlgebra Q w))
end
end PaperVerification.WeightedInitialFiber
namespace PaperVerification.AlternatingForms.Hibi
section
variable {s n : ℕ} (α β : Fin s → Fin n)
def IntervalIndex := {I : PluckerIndex s n // ∀ i,α i≤I.val i ∧ I.val i≤β i}
instance intervalFintype : Fintype (IntervalIndex α β) := by classical unfold IntervalIndex PluckerIndex; infer_instance
instance intervalOrder : PartialOrder (IntervalIndex α β) := by unfold IntervalIndex PluckerIndex; infer_instance
def meet (I J : IntervalIndex α β) : IntervalIndex α β :=
  ⟨⟨fun i => min (I.val.val i) (J.val.val i),by
    intro i j hij
    exact lt_min ((min_le_left _ _).trans_lt (I.val.property hij))
      ((min_le_right _ _).trans_lt (J.val.property hij))⟩,by
    intro i
    exact ⟨le_min (I.property i).1 (J.property i).1,
      (min_le_left _ _).trans (I.property i).2⟩⟩
def join (I J : IntervalIndex α β) : IntervalIndex α β :=
  ⟨⟨fun i => max (I.val.val i) (J.val.val i),by
    intro i j hij
    exact max_lt ((I.val.property hij).trans_le (le_max_left _ _))
      ((J.val.property hij).trans_le (le_max_right _ _))⟩,by
    intro i
    exact ⟨(I.property i).1.trans (le_max_left _ _),
      max_le (I.property i).2 (J.property i).2⟩⟩
end
end PaperVerification.AlternatingForms.Hibi
namespace PaperVerification.AlternatingForms.Hibi
section
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K] {s n : ℕ} (α β : Fin s → Fin n)
def incomparable (I J : IntervalIndex α β) : Prop := ¬I≤J ∧ ¬J≤I
def relation (I J : IntervalIndex α β) : MvPolynomial (IntervalIndex α β) K :=
  X I*X J-X (meet α β I J)*X (join α β I J)
def relationIdeal : Ideal (MvPolynomial (IntervalIndex α β) K) :=
  Ideal.span {p | ∃ I J,incomparable α β I J ∧ p=relation α β I J}
end
end PaperVerification.AlternatingForms.Hibi
namespace PaperVerification.AlternatingForms.Hibi
section
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K] {s n : ℕ}
  (α β : Fin s → Fin n)
def goodBandMap : MvPolynomial (IntervalIndex α β) K →ₐ[K]
    MvPolynomial (Fin s × Fin n) K :=
  aeval (fun I => bandMinor α β I.val.val)
def goodBandIdeal : Ideal (MvPolynomial (IntervalIndex α β) K) :=
  RingHom.ker (goodBandMap α β).toRingHom
end
end PaperVerification.AlternatingForms.Hibi
namespace PaperVerification.WeightedSagbi
section
open MvPolynomial
open scoped BigOperators
open AlternatingForms WeightedInitialFiber
variable {K σ τ : Type*} [Field K]
def inducedWeight (u : τ → ℕ) (a : σ → τ →₀ ℕ) : σ → ℕ :=
  fun i => Finsupp.weight u (a i)
end
end PaperVerification.WeightedSagbi
namespace PaperVerification.AlternatingForms.Hibi
section
open MvPolynomial
open scoped BigOperators
open WeightedInitialFiber WeightedSagbi
variable {K : Type*} [Field K] [CharZero K] {s n : ℕ}
  (α β : Fin s → Fin n)
def diagonalEntryWeight (i : Fin s × Fin n) : ℕ := i.1.val*i.2.val
def diagonalExponent (I : IntervalIndex α β) : (Fin s × Fin n) →₀ ℕ :=
  minorTermExponent I.val.val 1
def diagonalWeight : IntervalIndex α β → ℕ :=
  inducedWeight (diagonalEntryWeight (s := s) (n := n)) (diagonalExponent α β)
end
end PaperVerification.AlternatingForms.Hibi
namespace PaperVerification.AlternatingForms
section
open MvPolynomial
open scoped BigOperators
open Hibi
variable {K : Type*} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)
local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "Q" => isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)
local notation "P" => MvPolynomial (IntervalIndex α β) K
def oddGoodMap : P →ₐ[K]
    (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸Q) :=
  (Ideal.Quotient.mkₐ K Q).comp (rename Subtype.val)
def oddGoodIdeal : Ideal P := RingHom.ker (oddGoodMap (K := K) k t hs).toRingHom
end
end PaperVerification.AlternatingForms
namespace PaperVerification.AlternatingForms
section
open scoped BigOperators
open MvPolynomial PaperVerification.WeightedInitialFiber
variable {K : Type*} [Field K] {n : ℕ}
def onePlaneIndex (i : Fin n) : PluckerIndex 1 n :=
  ⟨fun _ ↦ i, fun a b hab ↦ by
    have h : a = b := Subsingleton.elim _ _
    exact (not_lt_of_ge h.ge hab).elim⟩
theorem onePlaneIndex_eta (I : PluckerIndex 1 n) :
    onePlaneIndex (I.val 0) = I := by sorry
theorem onePlane_matrixPluckerIdeal :
    matrixPluckerIdeal (K := K) (s := 1) (n := n) = ⊥ := by sorry
end
end PaperVerification.AlternatingForms
namespace TauCeti
section
universe u v
open _root_.CategoryTheory CliffordAlgebra
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable (φ : Module.Dual R M)
def koszulDifferential (n : ℕ) : ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M :=
  (contractLeft (Q := (0 : QuadraticForm R M)) φ).restrict fun _ hx ↦
    ExteriorAlgebra.contractLeft_mem_exteriorPower φ hx
theorem koszulDifferential_comp_koszulDifferential (n : ℕ) :
    koszulDifferential φ n ∘ₗ koszulDifferential φ (n + 1) = 0 := by sorry
end
end TauCeti
namespace TauCeti
section
universe u v
open _root_.CategoryTheory CliffordAlgebra
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
@[expose] def koszulComplex (φ : Module.Dual R M) : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (⋀[R]^n M))
    (fun n ↦ ModuleCat.ofHom (koszulDifferential φ n))
    fun n ↦ ModuleCat.hom_ext (koszulDifferential_comp_koszulDifferential φ n)
end
end TauCeti
namespace PaperVerification.AlternatingForms.OnePlaneKoszul
section
open scoped Classical
open MvPolynomial RingTheory.Sequence CategoryTheory
universe u
variable (K : Type u) [Field K] (n : ℕ)
abbrev Ring := MvPolynomial (PluckerIndex 1 n) K ⧸ matrixPluckerIdeal
def indexEquiv : PluckerIndex 1 n ≃ Fin n where
  toFun I := I.val 0
  invFun := onePlaneIndex
  left_inv := onePlaneIndex_eta
  right_inv _ := rfl
def polynomialEquiv : Ring K n ≃ₐ[K] MvPolynomial (Fin n) K :=
  (Ideal.quotientEquivAlgOfEq K onePlane_matrixPluckerIdeal).trans
    ((AlgEquiv.quotientBot K _).trans (MvPolynomial.renameEquiv K (indexEquiv n)))
def generator (i : Fin n) : Ring K n :=
  Ideal.Quotient.mk _ (X (onePlaneIndex i))
def functional : Module.Dual (Ring K n) (Fin n → Ring K n) :=
  Fintype.linearCombination (Ring K n) (generator K n)
def complex : ChainComplex (ModuleCat (Ring K n)) ℕ :=
  TauCeti.koszulComplex (functional K n)
theorem complex_exactAt_succ (r : ℕ) : (complex K n).ExactAt (r+1) := by sorry
def augmentationIdeal : Ideal (Ring K n) := Ideal.span (Set.range (generator K n))
abbrev Residue := Ring K n ⧸ augmentationIdeal K n
def augmentation : (complex K n).X 0 ⟶ ModuleCat.of (Ring K n) (Residue K n) :=
  ModuleCat.ofHom ((augmentationIdeal K n).mkQ.comp
    (exteriorPower.zeroEquiv (Ring K n) (Fin n → Ring K n)).toLinearMap)
theorem d_augmentation : (complex K n).d 1 0 ≫ augmentation K n=0 := by sorry
theorem augmentation_exact : (ShortComplex.mk _ _ (d_augmentation K n)).Exact := by sorry
theorem augmentationEpi : CategoryTheory.Epi (augmentation K n) := by sorry
attribute [instance] augmentationEpi
def resolution : ProjectiveResolution (ModuleCat.of (Ring K n) (Residue K n)) where
  complex := complex K n
  projective r := by
    change Projective (ModuleCat.of (Ring K n) (⋀[Ring K n]^r (Fin n → Ring K n)))
    infer_instance
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨augmentation K n,d_augmentation K n⟩
  quasiIso := ⟨fun r ↦ by
    cases r with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,ShortComplex.quasiIso_iff_of_zeros']
      · change (ShortComplex.mk _ _ (d_augmentation K n)).Exact ∧ Epi (augmentation K n)
        exact ⟨augmentation_exact K n,inferInstance⟩
      all_goals rfl
    | succ r =>
      rw [quasiIsoAt_iff_exactAt']
      · exact complex_exactAt_succ K n r
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩
def torIso (E : ModuleCat (Ring K n)) (r : ℕ) :
    (((Tor (ModuleCat (Ring K n)) r).obj E).obj
      (ModuleCat.of (Ring K n) (Residue K n))) ≅
      ((((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat (Ring K n))).obj E).mapHomologicalComplex (ComplexShape.down ℕ)).obj (resolution K n).complex).homology r :=
  (resolution K n).isoLeftDerivedObj _ r
end
end PaperVerification.AlternatingForms.OnePlaneKoszul
namespace PaperVerification.AlternatingForms.OnePlaneKoszul
section
open scoped BigOperators _root_.TensorProduct
open MvPolynomial CategoryTheory CategoryTheory.Limits
universe u
variable (K : Type u) [Field K] (n : ℕ)
local notation "P" => Ring K n
local notation "Q" => Residue K n
local notation "J" => augmentationIdeal K n
def residueTensorComplex : ChainComplex (ModuleCat P) ℕ :=
  ((((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat P)).obj
    (ModuleCat.of P Q)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (resolution K n).complex)
theorem residueTensorComplex_d (i j : ℕ) :
    (residueTensorComplex K n).d i j=0 := by sorry
def residueTensorHomologyIso (r : ℕ) :
    (residueTensorComplex K n).homology r ≅ (residueTensorComplex K n).X r :=
  (ShortComplex.HomologyData.ofZeros ((residueTensorComplex K n).sc r)
    (residueTensorComplex_d K n _ _) (residueTensorComplex_d K n _ _)).left.homologyIso
def residueTorIso (r : ℕ) :
    (((Tor (ModuleCat P) r).obj (ModuleCat.of P Q)).obj (ModuleCat.of P Q)) ≅
      ModuleCat.of P (Q ⊗[P] (⋀[P]^r (Fin n → P))) :=
  torIso K n (ModuleCat.of P Q) r ≪≫ residueTensorHomologyIso K n r
end
end PaperVerification.AlternatingForms.OnePlaneKoszul
namespace PaperVerification.AlternatingForms.BasisDegree
section
open scoped Classical BigOperators
variable {R V I : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  (B : Module.Basis I R V) (δ : I → ℕ)
def piece (N : ℕ) : Submodule R V :=
  (Finsupp.supported R R {i | δ i=N}).comap B.repr.toLinearMap
theorem piece_iSupIndep : iSupIndep (piece B δ) := by sorry
theorem piece_iSup : (⨆ N,piece B δ N)=⊤ := by sorry
def grading : TauCeti.InternalGrading R V ℕ where
  piece := piece B δ
  isInternal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (piece_iSupIndep B δ) (piece_iSup B δ)
end
end PaperVerification.AlternatingForms.BasisDegree
namespace PaperVerification.AlternatingForms.OnePlaneKoszul
section
open scoped Classical BigOperators _root_.TensorProduct
open MvPolynomial CategoryTheory CategoryTheory.Limits
universe u
variable (K : Type u) [Field K] (n : ℕ)
local notation "P" => Ring K n
local notation "Q" => Residue K n
local notation "J" => augmentationIdeal K n
abbrev freeTermOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K P)).obj ((complex K n).X r)
instance freeTerm_isScalarTower (r : ℕ) : IsScalarTower K P (freeTermOverK K n r) := IsScalarTower.of_compHom K P ((complex K n).X r)
abbrev tensorTermOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K P)).obj ((residueTensorComplex K n).X r)
def freeBasis (r : ℕ) :
    Module.Basis (Set.powersetCard (Fin n) r) P (freeTermOverK K n r) :=
  (Pi.basisFun P (Fin n)).exteriorPower r
def coordinateBasis : Module.Basis (Fin n →₀ ℕ) K P :=
  (MvPolynomial.basisMonomials (Fin n) K).map (polynomialEquiv K n).symm.toLinearEquiv
def freeMonomialBasis (r : ℕ) :
    Module.Basis ((Fin n →₀ ℕ) × Set.powersetCard (Fin n) r) K (freeTermOverK K n r) :=
  (coordinateBasis K n).smulTower (freeBasis K n r)
def freeGrading (r : ℕ) : TauCeti.InternalGrading K (freeTermOverK K n r) ℕ :=
  BasisDegree.grading (freeMonomialBasis K n r) (fun a ↦ a.1.degree+r)
def specializeFree (r : ℕ) : freeTermOverK K n r →ₗ[K] tensorTermOverK K n r :=
  ((ModuleCat.restrictScalars (algebraMap K P)).map
    (ModuleCat.ofHom (TensorProduct.mk P Q (⋀[P]^r (Fin n → P)) 1))).hom
def tensorDegreePiece (r N : ℕ) : Submodule K (tensorTermOverK K n r) :=
  ((freeGrading K n r).piece N).map (specializeFree K n r)
theorem tensorDegreePiece_eq_bot (r N : ℕ) (hNr : N≠r) :
    tensorDegreePiece K n r N=⊥ := by sorry
theorem tensorDegreePieces_iSup (r : ℕ) : (⨆ N,tensorDegreePiece K n r N)=⊤ := by sorry
def tensorGrading (r : ℕ) : TauCeti.InternalGrading K (tensorTermOverK K n r) ℕ where
  piece := tensorDegreePiece K n r
  isInternal := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · intro N
      by_cases h : N=r
      · subst N
        have hz : (⨆ M≠r,tensorDegreePiece K n r M)=⊥ := by
          apply le_antisymm ?_ bot_le
          apply iSup_le
          intro M
          apply iSup_le
          intro hM
          rw [tensorDegreePiece_eq_bot K n r M hM]
        rw [hz]
        exact disjoint_bot_right
      · rw [tensorDegreePiece_eq_bot K n r N h]
        exact disjoint_bot_left
    · exact tensorDegreePieces_iSup K n r
def TorOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K P)).obj
    (((Tor (ModuleCat P) r).obj (ModuleCat.of P Q)).obj (ModuleCat.of P Q))
def torTermIsoOverK (r : ℕ) : TorOverK K n r ≅ tensorTermOverK K n r :=
  (ModuleCat.restrictScalars (algebraMap K P)).mapIso (residueTorIso K n r)
def torGrading (r : ℕ) : TauCeti.InternalGrading K (TorOverK K n r) ℕ :=
  (tensorGrading K n r).map (torTermIsoOverK K n r).toLinearEquiv.symm
theorem actual_onePlane_Tor_degree (r N : ℕ) :
    (torGrading K n r).piece N=if N=r then ⊤ else ⊥ := by sorry
end
end PaperVerification.AlternatingForms.OnePlaneKoszul
namespace PaperVerification.AlternatingForms
section
open scoped Classical
open MvPolynomial
open PaperVerification.WeightedInitialFiber
universe u v
variable {K : Type u} [Field K] [CharZero K]
def HasQuadraticGroebnerBasis {σ : Type v} (Q : Ideal (MvPolynomial σ K)) : Prop :=
  ∃ (m : MonomialOrder.{v,v} σ) (S : Set (MvPolynomial σ K)),
    S.Finite ∧ (∀ p∈S,p.IsHomogeneous 2) ∧ S ⊆ Q ∧
      Ideal.span (m.leadingTerm '' (Q : Set _)) = Ideal.span (m.leadingTerm '' S)
end
end PaperVerification.AlternatingForms
namespace Model
open PaperVerification.WeightedInitialFiber
variable {K : Type*} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
def quotientPiece {σ : Type*} (Q : Ideal (MvPolynomial σ K)) (d : ℕ) : Submodule K (MvPolynomial σ K ⧸ Q) := (MvPolynomial.homogeneousSubmodule σ K d).map (Ideal.Quotient.mkₐ K Q).toLinearMap
def reesPiece {σ : Type*} (Q : Ideal (MvPolynomial σ K)) (w : σ → ℕ) (d : ℕ) : Submodule K (reesAlgebra Q w) := ⨅ j, (quotientPiece Q d).comap ((coefficient j).comp (reesAlgebra Q w).val.toLinearMap)
def GradedWeightFamily {σ τ υ : Type*} (Q : Ideal (MvPolynomial σ K)) (w : σ → ℕ) (sourceIdeal : Ideal (MvPolynomial τ K)) (specialIdeal : Ideal (MvPolynomial υ K)) : Prop :=
  Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K) ∧
  Module.Flat (Polynomial K) (reesAlgebra Q w) ∧ DirectSum.IsInternal (reesPiece Q w) ∧
  (∀ (f : Polynomial K) (d : ℕ) (a : reesAlgebra Q w), a ∈ reesPiece Q w d → f • a ∈ reesPiece Q w d) ∧
  (∃ e : ZeroFiber Q w ≃ₐ[K] (MvPolynomial υ K ⧸ specialIdeal), ∀ d,
    ((reesPiece Q w d).map (Ideal.Quotient.mkₐ K (Ideal.span {reesParameter Q w})).toLinearMap).map e.toLinearMap = quotientPiece specialIdeal d) ∧
  ∀ (c : K), c ≠ 0 → ∃ e : ParameterFiber Q w c ≃ₐ[K] (MvPolynomial τ K ⧸ sourceIdeal), ∀ d,
    ((reesPiece Q w d).map (Ideal.Quotient.mkₐ K (Ideal.span {reesParameter Q w - algebraMap K (reesAlgebra Q w) c})).toLinearMap).map e.toLinearMap = quotientPiece sourceIdeal d
end Model
namespace Model
variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
def positiveCoordinates (B : Module.Basis (Option I) K A) : A →ₗ[K] (I →₀ K) := (Finsupp.lcomapDomain (R := K) (M := K) Option.some (Option.some_injective I)).comp B.repr.toLinearMap
def productCoordinates (B : Module.Basis (Option I) K A) (i j : I) : I →₀ K := positiveCoordinates B (B (some i) * B (some j))
def prepend (i : I) : (List I →₀ K) →ₗ[K] (List I →₀ K) := Finsupp.linearCombination K (fun L => Finsupp.single (i::L) 1)
def appendTail (L : List I) : (I →₀ K) →ₗ[K] (List I →₀ K) := Finsupp.linearCombination K (fun i => Finsupp.single (i::L) 1)
def mergeBasis (B : Module.Basis (Option I) K A) (i : I) (L : List I) : List I →₀ K := List.casesOn L 0 (fun j T => appendTail T (productCoordinates B i j))
def merge (B : Module.Basis (Option I) K A) (i : I) : (List I →₀ K) →ₗ[K] (List I →₀ K) := Finsupp.linearCombination K (mergeBasis B i)
def differentialBasis (B : Module.Basis (Option I) K A) (L : List I) : List I →₀ K := List.recOn L 0 (fun i T ih => merge B i (Finsupp.single T 1) - prepend i ih)
def differential (B : Module.Basis (Option I) K A) : (List I →₀ K) →ₗ[K] (List I →₀ K) := Finsupp.linearCombination K (differentialBasis B)
def barPiece (δ : I → ℕ) (r N : ℕ) : Submodule K (List I →₀ K) := Finsupp.supported K K {L | L.length=r ∧ (L.map δ).sum=N}
end Model
namespace PaperVerification.AlternatingForms
open MvPolynomial PaperVerification.WeightedInitialFiber
universe uMain
variable {K : Type uMain} [Field K] [CharZero K]
theorem paper13_weight_families (k : ℕ) :
  Model.GradedWeightFamily (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1)) (pluckerVertexWeight (oddNatVertexWeight k)) (matrixPluckerIdeal (s := 1) (n := 2*k+1)) (intervalPluckerIdeal (oddIntervalLower k 1 (by omega)) (oddIntervalUpper k 1 (by omega))) ∧
  (∀ (t : ℕ) (hs : t+2≤k+1), Model.GradedWeightFamily (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k)) (pluckerVertexWeight (oddNatVertexWeight k)) (isotropicPluckerIdeal (t := t) (oddPluckerForms k)) (intervalPluckerIdeal (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs))) ∧
  (∀ (s : ℕ) (hpos : 0<s) (hs : s≤k+1), Model.GradedWeightFamily (Hibi.goodBandIdeal (K := K) (oddIntervalLower k s hs) (oddIntervalUpper k s hs)) (Hibi.diagonalWeight (oddIntervalLower k s hs) (oddIntervalUpper k s hs)) (intervalPluckerIdeal (oddIntervalLower k s hs) (oddIntervalUpper k s hs)) (Hibi.relationIdeal (oddIntervalLower k s hs) (oddIntervalUpper k s hs))) := by sorry
theorem paper13_oneplane_quadratic (k : ℕ) : HasQuadraticGroebnerBasis (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1)) := by sorry
theorem paper13_quadratic (k t : ℕ) (hs : t+2≤k+1) :
  Nonempty ((MvPolynomial (Hibi.IntervalIndex (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs)) K ⧸ oddGoodIdeal k t hs) ≃ₐ[K] (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K ⧸ isotropicPluckerIdeal (t := t) (oddPluckerForms k))) ∧ HasQuadraticGroebnerBasis (oddGoodIdeal (K := K) k t hs) := by sorry
theorem paper13_higher_koszul (k t : ℕ) (hs : t+2≤k+1) :
  ∃ (I : Type uMain) (B : Module.Basis (Option I) K (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K ⧸ isotropicPluckerIdeal (t := t) (oddPluckerForms k)))
    (ε : (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K ⧸ isotropicPluckerIdeal (t := t) (oddPluckerForms k)) →ₐ[K] K) (δ : I → ℕ),
    B none=1 ∧ (∀ i, ε (B (some i))=0) ∧
    (∀ i, 0<δ i ∧ B (some i) ∈ Model.quotientPiece (isotropicPluckerIdeal (t := t) (oddPluckerForms k)) (δ i)) ∧
    (∀ j, ε (Ideal.Quotient.mk _ (X j))=0) ∧
    (∀ r N, r≠N → ∀ z ∈ Model.barPiece (K := K) δ r N, Model.differential B z=0 → ∃ y ∈ Model.barPiece (K := K) δ (r+1) N, -Model.differential B y=z) := by sorry
end PaperVerification.AlternatingForms
end PalomarAlternatingDegeneration
namespace PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open MvPolynomial Matrix
variable {K : Type*} [Field K] {s n : ℕ}
abbrev PluckerChartVariable (p : PluckerIndex s n) :=
  Fin s × {j : Fin n // j ∉ Set.range p.val}
end
end PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
namespace PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open MvPolynomial Matrix
variable {K : Type*} [Field K] {s n : ℕ}
def pluckerChartMatrix (p : PluckerIndex s n) :
    Matrix (Fin s) (Fin n) (MvPolynomial (PluckerChartVariable p) K) :=
  Matrix.of fun i j => if j=p.val i then 1 else if h : j ∈ Set.range p.val then 0
    else X (i,⟨j,h⟩)
end
end PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
namespace PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open MvPolynomial Matrix
variable {K : Type*} [Field K] {t n m : ℕ}
def alternatingRowPair {R : Type*} [CommRing R] [Algebra K R]
    (f : StrictPairs n → K) (A : Matrix (Fin (t+2)) (Fin n) R)
    (i j : Fin (t+2)) : R :=
  ∑ a : StrictPairs n, f a •
    (A i a.val.1*A j a.val.2 - A i a.val.2*A j a.val.1)
end
end PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
namespace PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open MvPolynomial Matrix
variable {K : Type*} [Field K] {t n m : ℕ}
def isotropicChartIdeal (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    Ideal (MvPolynomial (PluckerChartVariable p) K) :=
  Ideal.span (Set.range fun a : Fin m × StrictPairs (t+2) =>
    alternatingRowPair (forms a.1) (pluckerChartMatrix p) a.2.val.1 a.2.val.2)
end
end PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
namespace PalomarAlternatingDegeneration.PaperVerification.WeightedInitialFiber
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open MvPolynomial
variable {K σ : Type*} [Field K]
local notation "P" => MvPolynomial σ K
variable {R : Type*} [CommRing R]
def IsSaturatedWithRespectTo (Q J : Ideal R) : Prop :=
  ∀ f : R, (∃ m : ℕ, ∀ g∈J^m,g*f∈Q) ↔ f∈Q
end
end PalomarAlternatingDegeneration.PaperVerification.WeightedInitialFiber
namespace PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open MvPolynomial
open PaperVerification.WeightedInitialFiber
variable {K : Type*} [Field K] [CharZero K]
def pluckerIrrelevantIdeal (s n : ℕ) : Ideal (MvPolynomial (PluckerIndex s n) K) :=
  Ideal.span (Set.range (X : PluckerIndex s n → MvPolynomial (PluckerIndex s n) K))
end
end PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
namespace PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open MvPolynomial
open PaperVerification.WeightedInitialFiber
variable {K : Type*} [Field K] [CharZero K]
theorem odd_isotropicPluckerIdeal_isPrime (k t : ℕ) (hs : t+2≤k+1) :
    (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k)).IsPrime := by sorry
end
end PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
namespace PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open MvPolynomial
open PaperVerification.WeightedInitialFiber
variable {K : Type*} [Field K] [CharZero K]
theorem onePlane_ideal_isPrime (n : ℕ) :
    (matrixPluckerIdeal (K := K) (s := 1) (n := n)).IsPrime := by sorry
end
end PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
namespace PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open MvPolynomial
open PaperVerification.WeightedInitialFiber
variable {K : Type*} [Field K] [CharZero K]
theorem odd_isotropicPluckerIdeal_saturated (k t : ℕ) (hs : t+2≤k+1) :
    IsSaturatedWithRespectTo
      (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
      (pluckerIrrelevantIdeal (t+2) (2*k+1)) := by sorry
end
end PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
namespace PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open MvPolynomial
open PaperVerification.WeightedInitialFiber
variable {K : Type*} [Field K] [CharZero K]
theorem onePlane_PluckerIdeal_saturated (k : ℕ) :
    IsSaturatedWithRespectTo
      (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
      (pluckerIrrelevantIdeal 1 (2*k+1)) := by sorry
end
end PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
namespace PalomarAlternatingDegeneration.PalomarAlternatingGeometry
section
set_option autoImplicit false
open scoped BigOperators
open scoped BigOperators
open PaperVerification.AlternatingForms MvPolynomial
universe uChart
theorem oddAffineCharts {K : Type uChart} [Field K] [CharZero K]
    (k t : ℕ) (hs : t+2 ≤ k+1) (p : PluckerIndex (t+2) (2*k+1)) :
    Nonempty ((MvPolynomial (PluckerIndex (t+2) (2*k+1)) K ⧸
      (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k) ⊔ Ideal.span {X p-1})) ≃ₐ[K]
      (MvPolynomial (PluckerChartVariable p) K ⧸
        isotropicChartIdeal p (oddPluckerForms (K := K) k))) := by sorry
end
end PalomarAlternatingDegeneration.PalomarAlternatingGeometry
namespace CanonicalSourceWeight
open PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
section
open scoped BigOperators
def pathVertexCost (e : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | j + 1 => e j - CanonicalSourceWeight.pathVertexCost e j
end
section
open scoped BigOperators
variable {ι : Type*} [Fintype ι]
def positiveWeightShift (u : ι → ℤ) : ℤ := 1 + ∑ i, |u i|
end
section
open scoped BigOperators
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
def oddPathEdgeCost (k j : ℕ) : ℤ :=
  if Even j then (2 : ℤ) ^ (j / 2 + 1) else (2 : ℤ) ^ (k - j / 2)
end
section
open scoped BigOperators
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
def oddPathVertexCost (k : ℕ) (i : Fin (2 * k + 1)) : ℤ :=
  CanonicalSourceWeight.pathVertexCost (CanonicalSourceWeight.oddPathEdgeCost k) i.val
end
section
open scoped BigOperators
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
def oddPathVertexWeight (k : ℕ) (i : Fin (2 * k + 1)) : ℤ :=
  CanonicalSourceWeight.positiveWeightShift (CanonicalSourceWeight.oddPathVertexCost k) - CanonicalSourceWeight.oddPathVertexCost k i
end
section
open scoped BigOperators
open MvPolynomial
variable {K : Type*} [Field K] {k s n : ℕ}
def oddNatVertexWeight (k : ℕ) (i : Fin (2*k+1)) : ℕ :=
  (CanonicalSourceWeight.oddPathVertexWeight k i).toNat
end
section
open scoped BigOperators
open MvPolynomial
variable {K : Type*} [Field K] {k s n : ℕ}
def pluckerVertexWeight (w : Fin n → ℕ) (I : PluckerIndex s n) : ℕ :=
  ∑ i,w (I.val i)
end
end CanonicalSourceWeight
namespace CanonicalSourceBar
open PalomarAlternatingDegeneration.PaperVerification.AlternatingForms
section
open scoped BigOperators
variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
def positiveVector (i : I) : A := B (some i)
end
section
open scoped BigOperators
variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
def positiveCoordinates : A →ₗ[K] (I →₀ K) :=
  (Finsupp.lcomapDomain (R := K) (M := K) Option.some (Option.some_injective I)).comp
    B.repr.toLinearMap
end
section
open scoped BigOperators
variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
def productCoefficients (i j : I) : I →₀ K :=
  CanonicalSourceBar.positiveCoordinates B (CanonicalSourceBar.positiveVector B i*CanonicalSourceBar.positiveVector B j)
end
section
open scoped BigOperators
variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
local notation "W" => List I →₀ K
def prepend (i : I) : W →ₗ[K] W :=
  Finsupp.linearCombination K (fun L => Finsupp.single (i::L) 1)
end
section
open scoped BigOperators
variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
local notation "W" => List I →₀ K
def appendTail (L : List I) : (I →₀ K) →ₗ[K] W :=
  Finsupp.linearCombination K (fun i => Finsupp.single (i::L) 1)
end
section
open scoped BigOperators
variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
local notation "W" => List I →₀ K
def mergeBasis (i : I) : List I → W
  | [] => 0
  | j::L => CanonicalSourceBar.appendTail L (CanonicalSourceBar.productCoefficients B i j)
end
section
open scoped BigOperators
variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
local notation "W" => List I →₀ K
def merge (i : I) : W →ₗ[K] W := Finsupp.linearCombination K (CanonicalSourceBar.mergeBasis B i)
end
end CanonicalSourceBar
namespace PalomarAlternatingDegeneration
namespace PaperVerification.AlternatingForms
private theorem literalEdgeCost_eq (k : ℕ) : oddPathEdgeCost k = _root_.CanonicalSourceWeight.oddPathEdgeCost k := by
  funext j
  by_cases h : Even j
  · simp only [oddPathEdgeCost, _root_.CanonicalSourceWeight.oddPathEdgeCost, if_pos h]
  · simp only [oddPathEdgeCost, _root_.CanonicalSourceWeight.oddPathEdgeCost, if_neg h]
private theorem literalPathCost_eq (e : ℕ → ℤ) (j : ℕ) : pathVertexCost e j = _root_.CanonicalSourceWeight.pathVertexCost e j := by
  induction j with
  | zero => rfl
  | succ j ih => simpa only [pathVertexCost, _root_.CanonicalSourceWeight.pathVertexCost, ih]
private theorem literalVertexCost_eq (k : ℕ) : oddPathVertexCost k = _root_.CanonicalSourceWeight.oddPathVertexCost k := by
  funext i
  change pathVertexCost (oddPathEdgeCost k) i.val = _root_.CanonicalSourceWeight.pathVertexCost (_root_.CanonicalSourceWeight.oddPathEdgeCost k) i.val
  rw [literalEdgeCost_eq, literalPathCost_eq]
private theorem literalShift_eq {ι : Type*} [Fintype ι] (u : ι → ℤ) : positiveWeightShift u = _root_.CanonicalSourceWeight.positiveWeightShift u := rfl
private theorem literalVertexWeight_eq (k : ℕ) : oddPathVertexWeight k = _root_.CanonicalSourceWeight.oddPathVertexWeight k := by
  funext i
  change positiveWeightShift (oddPathVertexCost k) - oddPathVertexCost k i = _root_.CanonicalSourceWeight.positiveWeightShift (_root_.CanonicalSourceWeight.oddPathVertexCost k) - _root_.CanonicalSourceWeight.oddPathVertexCost k i
  rw [literalVertexCost_eq, literalShift_eq]
private theorem literalNatWeight_eq (k : ℕ) : oddNatVertexWeight k = _root_.CanonicalSourceWeight.oddNatVertexWeight k := by
  funext i
  change (oddPathVertexWeight k i).toNat = (_root_.CanonicalSourceWeight.oddPathVertexWeight k i).toNat
  rw [literalVertexWeight_eq]
private theorem literalPluckerWeight_eq (k s : ℕ) : pluckerVertexWeight (s := s) (oddNatVertexWeight k) = _root_.CanonicalSourceWeight.pluckerVertexWeight (s := s) (_root_.CanonicalSourceWeight.oddNatVertexWeight k) := by
  funext I
  change (∑ j, oddNatVertexWeight k (I.val j)) = ∑ j, _root_.CanonicalSourceWeight.oddNatVertexWeight k (I.val j)
  rw [literalNatWeight_eq]
end PaperVerification.AlternatingForms
section
variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
private theorem literalPositiveCoordinates_eq (B : Module.Basis (Option I) K A) : Model.positiveCoordinates B = _root_.CanonicalSourceBar.positiveCoordinates B := by
  ext x i
  rfl
private theorem literalProductCoordinates_eq (B : Module.Basis (Option I) K A) (i j : I) : Model.productCoordinates B i j = _root_.CanonicalSourceBar.productCoefficients B i j := by
  change Model.positiveCoordinates B (B (some i) * B (some j)) = _root_.CanonicalSourceBar.positiveCoordinates B (B (some i) * B (some j))
  rw [literalPositiveCoordinates_eq]
private theorem literalPrepend_eq (i : I) : Model.prepend (K := K) i = _root_.CanonicalSourceBar.prepend (K := K) i := rfl
private theorem literalAppendTail_eq (L : List I) : Model.appendTail (K := K) L = _root_.CanonicalSourceBar.appendTail (K := K) L := rfl
private theorem literalMergeBasis_eq (B : Module.Basis (Option I) K A) (i : I) (L : List I) : Model.mergeBasis B i L = _root_.CanonicalSourceBar.mergeBasis B i L := by
  cases L with
  | nil => rfl
  | cons j T =>
    change Model.appendTail T (Model.productCoordinates B i j) = _root_.CanonicalSourceBar.appendTail T (_root_.CanonicalSourceBar.productCoefficients B i j)
    rw [literalAppendTail_eq, literalProductCoordinates_eq]
private theorem literalMerge_eq (B : Module.Basis (Option I) K A) (i : I) : Model.merge B i = _root_.CanonicalSourceBar.merge B i := by
  change Finsupp.linearCombination K (Model.mergeBasis B i) = Finsupp.linearCombination K (_root_.CanonicalSourceBar.mergeBasis B i)
  congr 1
  funext L
  exact literalMergeBasis_eq B i L
end
end PalomarAlternatingDegeneration
