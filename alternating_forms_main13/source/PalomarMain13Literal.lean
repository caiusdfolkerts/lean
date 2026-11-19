module
public import Mathlib
public import PalomarOriginalSolution
import all PalomarOriginalSolution
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Classical
namespace PalomarAlternatingDegeneration
namespace Model
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
/-- Actual polynomial coefficient, restricted along the given coefficient algebra. -/
def coefficient (j : ℕ) : Polynomial A →ₗ[K] A := (Polynomial.lcoeff A j).restrictScalars K
end Model
namespace TauCeti
section
open scoped DirectSum
universe u v w
variable (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]
open _root_.TauCeti
/-- Literal TauCeti.InternalGrading; exact original coordinate/Tor semantics. -/
structure InternalGrading (ι : Type := ℤ) [DecidableEq ι] where
  /-- The submodule of elements of degree `p`. -/
  piece : ι → Submodule R M
  /-- The homogeneous pieces form an internal direct sum. -/
  isInternal : DirectSum.IsInternal piece
end
end TauCeti
namespace TauCeti.InternalGrading
section
variable {R M N : Type*} {ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [DecidableEq ι]
/-- Exact original model obligation; compared with its genuine source proof. -/
theorem mapInternal (G : TauCeti.InternalGrading R M ι) (e : M ≃ₗ[R] N) : DirectSum.IsInternal (fun p => (G.piece p).map e.toLinearMap) := by
  let G0 : _root_.TauCeti.InternalGrading R M ι := ⟨G.piece,G.isInternal⟩
  exact (_root_.TauCeti.InternalGrading.map G0 e).isInternal
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
open _root_.PaperVerification.AlternatingForms
/-- Literal PaperVerification.AlternatingForms.pathVertexCost; exact original coordinate/Tor semantics. -/
def pathVertexCost (e : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | j + 1 => e j - pathVertexCost e j
end
end PaperVerification.AlternatingForms
namespace PaperVerification.AlternatingForms
section
open scoped BigOperators
variable {ι : Type*} [Fintype ι]
open _root_.PaperVerification.AlternatingForms
/-- Literal PaperVerification.AlternatingForms.positiveWeightShift; exact original coordinate/Tor semantics. -/
def positiveWeightShift (u : ι → ℤ) : ℤ := 1 + ∑ i, |u i|
end
end PaperVerification.AlternatingForms
namespace PaperVerification.AlternatingForms
section
open MvPolynomial Matrix
open scoped BigOperators
variable {K : Type*} [Field K] {s n : ℕ}
open _root_.PaperVerification.AlternatingForms
/-- Literal PaperVerification.AlternatingForms.bandEntryCoefficient; exact original coordinate/Tor semantics. -/
def bandEntryCoefficient (α β : Fin s → Fin n) (i : Fin s) (j : Fin n) : K :=
  if α i ≤ j ∧ j ≤ β i then 1 else 0
/-- Literal PaperVerification.AlternatingForms.bandMatrix; exact original coordinate/Tor semantics. -/
def bandMatrix (α β : Fin s → Fin n) :
    Matrix (Fin s) (Fin n) (MvPolynomial (Fin s × Fin n) K) :=
  fun i j => monomial (Finsupp.single (i,j) 1) (bandEntryCoefficient α β i j)
/-- Literal PaperVerification.AlternatingForms.bandMinor; exact original coordinate/Tor semantics. -/
def bandMinor (α β I : Fin s → Fin n) : MvPolynomial (Fin s × Fin n) K :=
  ((bandMatrix (K := K) α β).submatrix id I).det
/-- Literal PaperVerification.AlternatingForms.minorTermExponent; exact original coordinate/Tor semantics. -/
def minorTermExponent (I : Fin s → Fin n) (σ : Equiv.Perm (Fin s)) :
    (Fin s × Fin n) →₀ ℕ := ∑ i, Finsupp.single (σ i,I i) 1
/-- Literal PaperVerification.AlternatingForms.PluckerIndex; exact original coordinate/Tor semantics. -/
def PluckerIndex (s n : ℕ) := {I : Fin s → Fin n // StrictMono I}
instance pluckerFintype (s n : ℕ) : Fintype (PluckerIndex s n) := by classical unfold PluckerIndex; infer_instance
instance pluckerOrder (s n : ℕ) : PartialOrder (PluckerIndex s n) := by unfold PluckerIndex; infer_instance
/-- Literal PaperVerification.AlternatingForms.genericPluckerMinor; exact original coordinate/Tor semantics. -/
def genericPluckerMinor (I : PluckerIndex s n) : MvPolynomial (Fin s × Fin n) K :=
  (Matrix.of fun i j : Fin s => (X (i,I.val j) : MvPolynomial (Fin s × Fin n) K)).det
/-- Literal PaperVerification.AlternatingForms.genericPluckerMap; exact original coordinate/Tor semantics. -/
def genericPluckerMap :
    MvPolynomial (PluckerIndex s n) K →ₐ[K] MvPolynomial (Fin s × Fin n) K :=
  aeval genericPluckerMinor
/-- Literal PaperVerification.AlternatingForms.matrixPluckerIdeal; exact original coordinate/Tor semantics. -/
def matrixPluckerIdeal : Ideal (MvPolynomial (PluckerIndex s n) K) :=
  RingHom.ker (genericPluckerMap (K := K) (s := s) (n := n)).toRingHom
/-- Literal PaperVerification.AlternatingForms.intervalPluckerIdeal; exact original coordinate/Tor semantics. -/
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
open _root_.PaperVerification.AlternatingForms
/-- Literal PaperVerification.AlternatingForms.sortedPluckerIndex; exact original coordinate/Tor semantics. -/
def sortedPluckerIndex (I : Fin s → Fin n) (hI : Function.Injective I) :
    PluckerIndex s n :=
  ⟨I ∘ Tuple.sort I,(Tuple.monotone_sort I).strictMono_of_injective
    (hI.comp (Tuple.sort I).injective)⟩
/-- Literal PaperVerification.AlternatingForms.orderedPluckerCoordinate; exact original coordinate/Tor semantics. -/
def orderedPluckerCoordinate (I : Fin s → Fin n) : MvPolynomial (PluckerIndex s n) K :=
  if hI : Function.Injective I then
    (((Equiv.Perm.sign (Tuple.sort I).symm : ℤ) : K) • X (sortedPluckerIndex I hI))
  else 0
end
end PaperVerification.AlternatingForms
namespace PaperVerification.AlternatingForms
section

open _root_.PaperVerification.AlternatingForms
/-- Literal PaperVerification.AlternatingForms.StrictPairs; exact original coordinate/Tor semantics. -/
abbrev StrictPairs (m : ℕ) := {p : Fin m × Fin m // p.1 < p.2}
end
end PaperVerification.AlternatingForms
namespace PaperVerification.AlternatingForms
section
open scoped BigOperators
open MvPolynomial Matrix
variable {K : Type*} [Field K] {t n m : ℕ}
open _root_.PaperVerification.AlternatingForms
/-- Literal PaperVerification.AlternatingForms.pluckerIsotropyEquation; exact original coordinate/Tor semantics. -/
def pluckerIsotropyEquation (f : StrictPairs n → K) (J : Fin t → Fin n) :
    MvPolynomial (PluckerIndex (t+2) n) K :=
  ∑ a : StrictPairs n, f a •
    orderedPluckerCoordinate (Fin.cons a.val.1 (Fin.cons a.val.2 J))
/-- Literal PaperVerification.AlternatingForms.isotropicPluckerIdeal; exact original coordinate/Tor semantics. -/
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
open _root_.PaperVerification.AlternatingForms
/-- Literal PaperVerification.AlternatingForms.oddPathEdgeCost; exact original coordinate/Tor semantics. -/
def oddPathEdgeCost (k j : ℕ) : ℤ :=
  if Even j then (2 : ℤ) ^ (j / 2 + 1) else (2 : ℤ) ^ (k - j / 2)
/-- Literal PaperVerification.AlternatingForms.oddPathVertexCost; exact original coordinate/Tor semantics. -/
def oddPathVertexCost (k : ℕ) (i : Fin (2 * k + 1)) : ℤ :=
  pathVertexCost (oddPathEdgeCost k) i.val
/-- Literal PaperVerification.AlternatingForms.oddPathVertexWeight; exact original coordinate/Tor semantics. -/
def oddPathVertexWeight (k : ℕ) (i : Fin (2 * k + 1)) : ℤ :=
  positiveWeightShift (oddPathVertexCost k) - oddPathVertexCost k i
end
end PaperVerification.AlternatingForms
namespace PaperVerification.AlternatingForms
section
open MvPolynomial Matrix
open scoped BigOperators
variable {K : Type*} [Field K] {k t : ℕ}
open _root_.PaperVerification.AlternatingForms
/-- Literal PaperVerification.AlternatingForms.oddPluckerEdge; exact original coordinate/Tor semantics. -/
def oddPluckerEdge (k : ℕ) (l : Fin 2) (i : Fin k) : StrictPairs (2*k+1) :=
  ⟨(⟨2*i.val+l.val,by have := i.isLt; have := l.isLt; omega⟩,
    ⟨2*i.val+l.val+1,by have := i.isLt; have := l.isLt; omega⟩),by
      change 2*i.val+l.val < 2*i.val+l.val+1
      omega⟩
/-- Literal PaperVerification.AlternatingForms.oddPluckerForms; exact original coordinate/Tor semantics. -/
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
open _root_.PaperVerification.WeightedInitialFiber
/-- Literal PaperVerification.WeightedInitialFiber.scaledPolynomial; exact original coordinate/Tor semantics. -/
def scaledPolynomial (w : σ → ℕ) : P →ₐ[K] Polynomial P :=
  MvPolynomial.aeval (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ w i)
/-- Literal PaperVerification.WeightedInitialFiber.scaledQuotient; exact original coordinate/Tor semantics. -/
def scaledQuotient (Q : Ideal P) (w : σ → ℕ) : P →ₐ[K] Polynomial (P ⧸ Q) :=
  (Polynomial.mapAlgHom (Ideal.Quotient.mkₐ K Q)).comp (scaledPolynomial w)
/-- Literal PaperVerification.WeightedInitialFiber.reesMap; exact original coordinate/Tor semantics. -/
def reesMap (Q : Ideal P) (w : σ → ℕ) :
    Polynomial P →ₐ[K] Polynomial (P ⧸ Q) :=
  Polynomial.aevalTower (scaledQuotient Q w) (Polynomial.X : Polynomial (P ⧸ Q))
/-- Literal PaperVerification.WeightedInitialFiber.reesAlgebra; exact original coordinate/Tor semantics. -/
def reesAlgebra (Q : Ideal P) (w : σ → ℕ) : Subalgebra K (Polynomial (P ⧸ Q)) :=
  (reesMap Q w).range
/-- Exact original model obligation; compared with its genuine source proof. -/
theorem reesMultiplicationCommutes (Q : Ideal P) (w : σ → ℕ) (a b : reesAlgebra Q w) : a*b=b*a := by
  apply Subtype.ext
  change (a : Polynomial (P ⧸ Q)) * (b : Polynomial (P ⧸ Q)) = (b : Polynomial (P ⧸ Q)) * (a : Polynomial (P ⧸ Q))
  exact _root_.mul_comm (a : Polynomial (P ⧸ Q)) (b : Polynomial (P ⧸ Q))
instance reesAlgebraCommRing (Q : Ideal P) (w : σ → ℕ) : CommRing (reesAlgebra Q w) := by
  let ringInst : Ring (reesAlgebra Q w) := inferInstance
  exact {ringInst with mul_comm := reesMultiplicationCommutes Q w}
/-- Literal PaperVerification.WeightedInitialFiber.reesCover; exact original coordinate/Tor semantics. -/
def reesCover (Q : Ideal P) (w : σ → ℕ) : Polynomial P →ₐ[K] reesAlgebra Q w :=
  (reesMap Q w).rangeRestrict
/-- Literal PaperVerification.WeightedInitialFiber.reesParameter; exact original coordinate/Tor semantics. -/
def reesParameter (Q : Ideal P) (w : σ → ℕ) : reesAlgebra Q w :=
  reesCover Q w Polynomial.X
def reesParameterMap (Q : Ideal P) (w : σ → ℕ) : Polynomial K →ₐ[K] reesAlgebra Q w := Polynomial.aeval (reesParameter Q w)
instance reesPolynomialAlgebra (Q : Ideal P) (w : σ → ℕ) : Algebra (Polynomial K) (reesAlgebra Q w) := (reesParameterMap Q w).toRingHom.toAlgebra
/-- Literal PaperVerification.WeightedInitialFiber.ZeroFiber; exact original coordinate/Tor semantics. -/
abbrev ZeroFiber (Q : Ideal P) (w : σ → ℕ) :=
  reesAlgebra Q w ⧸ Ideal.span ({reesParameter Q w} : Set (reesAlgebra Q w))
end
end PaperVerification.WeightedInitialFiber
namespace PaperVerification.AlternatingForms
section
open scoped BigOperators
open MvPolynomial
variable {K : Type*} [Field K] {k s n : ℕ}
open _root_.PaperVerification.AlternatingForms
/-- Literal PaperVerification.AlternatingForms.oddNatVertexWeight; exact original coordinate/Tor semantics. -/
def oddNatVertexWeight (k : ℕ) (i : Fin (2*k+1)) : ℕ :=
  (oddPathVertexWeight k i).toNat
/-- Literal PaperVerification.AlternatingForms.pluckerVertexWeight; exact original coordinate/Tor semantics. -/
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
open _root_.PaperVerification.AlternatingForms
/-- Literal PaperVerification.AlternatingForms.oddIntervalLower; exact original coordinate/Tor semantics. -/
def oddIntervalLower (k s : ℕ) (hs : s≤k+1) (i : Fin s) : Fin (2*k+1) :=
  ⟨2*i.val,by have := i.isLt; omega⟩
/-- Literal PaperVerification.AlternatingForms.oddIntervalUpper; exact original coordinate/Tor semantics. -/
def oddIntervalUpper (k s : ℕ) (hs : s≤k+1) (i : Fin s) : Fin (2*k+1) :=
  ⟨2*(k+1-s+i.val),by have := i.isLt; omega⟩
end
end PaperVerification.AlternatingForms
namespace TauCeti.ExteriorAlgebra
section
open CliffordAlgebra
universe u v w
variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
open _root_.TauCeti.ExteriorAlgebra
/-- Literal TauCeti.ExteriorAlgebra.contractLeft_mem_exteriorPower; exact original coordinate/Tor semantics. -/
theorem contractLeft_mem_exteriorPower (d : Module.Dual R M) {n : ℕ}
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^(n + 1) M) :
    contractLeft (Q := (0 : QuadraticForm R M)) d x ∈ ⋀[R]^n M := by
  suffices h : ∀ i (x : ExteriorAlgebra R M) (_ : x ∈ ⋀[R]^i M),
      contractLeft (Q := (0 : QuadraticForm R M)) d x ∈ ⋀[R]^(i - 1) M from h _ x hx
  intro i x hx
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [contractLeft_ι_mul, Nat.succ_sub_one]
    refine sub_mem (Submodule.smul_mem _ _ hx) ?_
    rcases i with _ | i
    · rw [contractLeft_eq_zero_of_mem_exteriorPower_zero d hx, mul_zero]
      exact zero_mem _
    · rw [Nat.add_sub_cancel] at ih
      exact ι_mul_mem_exteriorPower v ih
end
end TauCeti.ExteriorAlgebra
namespace PaperVerification.WeightedInitialFiber
section
open scoped BigOperators
open MvPolynomial
variable {K σ : Type*} [Field K]
local notation "P" => MvPolynomial σ K
open _root_.PaperVerification.WeightedInitialFiber
/-- Literal PaperVerification.WeightedInitialFiber.ParameterFiber; exact original coordinate/Tor semantics. -/
abbrev ParameterFiber (Q : Ideal P) (w : σ → ℕ) (c : K) :=
  reesAlgebra Q w ⧸ Ideal.span
    ({reesParameter Q w-algebraMap K (reesAlgebra Q w) c} : Set (reesAlgebra Q w))
end
end PaperVerification.WeightedInitialFiber
namespace PaperVerification.AlternatingForms.Hibi
section
variable {s n : ℕ} (α β : Fin s → Fin n)
open _root_.PaperVerification.AlternatingForms.Hibi
/-- Literal PaperVerification.AlternatingForms.Hibi.IntervalIndex; exact original coordinate/Tor semantics. -/
def IntervalIndex := {I : PluckerIndex s n // ∀ i,α i≤I.val i ∧ I.val i≤β i}
instance intervalFintype : Fintype (IntervalIndex α β) := by classical unfold IntervalIndex PluckerIndex; infer_instance
instance intervalOrder : PartialOrder (IntervalIndex α β) := by unfold IntervalIndex PluckerIndex; infer_instance
/-- Literal PaperVerification.AlternatingForms.Hibi.meet; exact original coordinate/Tor semantics. -/
def meet (I J : IntervalIndex α β) : IntervalIndex α β :=
  ⟨⟨fun i => min (I.val.val i) (J.val.val i),by
    intro i j hij
    exact lt_min ((min_le_left _ _).trans_lt (I.val.property hij))
      ((min_le_right _ _).trans_lt (J.val.property hij))⟩,by
    intro i
    exact ⟨le_min (I.property i).1 (J.property i).1,
      (min_le_left _ _).trans (I.property i).2⟩⟩
/-- Literal PaperVerification.AlternatingForms.Hibi.join; exact original coordinate/Tor semantics. -/
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
open _root_.PaperVerification.AlternatingForms.Hibi
/-- Literal PaperVerification.AlternatingForms.Hibi.incomparable; exact original coordinate/Tor semantics. -/
def incomparable (I J : IntervalIndex α β) : Prop := ¬I≤J ∧ ¬J≤I
/-- Literal PaperVerification.AlternatingForms.Hibi.relation; exact original coordinate/Tor semantics. -/
def relation (I J : IntervalIndex α β) : MvPolynomial (IntervalIndex α β) K :=
  X I*X J-X (meet α β I J)*X (join α β I J)
/-- Literal PaperVerification.AlternatingForms.Hibi.relationIdeal; exact original coordinate/Tor semantics. -/
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
open _root_.PaperVerification.AlternatingForms.Hibi
/-- Literal PaperVerification.AlternatingForms.Hibi.goodBandMap; exact original coordinate/Tor semantics. -/
def goodBandMap : MvPolynomial (IntervalIndex α β) K →ₐ[K]
    MvPolynomial (Fin s × Fin n) K :=
  aeval (fun I => bandMinor α β I.val.val)
/-- Literal PaperVerification.AlternatingForms.Hibi.goodBandIdeal; exact original coordinate/Tor semantics. -/
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
open _root_.PaperVerification.WeightedSagbi
/-- Literal PaperVerification.WeightedSagbi.inducedWeight; exact original coordinate/Tor semantics. -/
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
open _root_.PaperVerification.AlternatingForms.Hibi
/-- Literal PaperVerification.AlternatingForms.Hibi.diagonalEntryWeight; exact original coordinate/Tor semantics. -/
def diagonalEntryWeight (i : Fin s × Fin n) : ℕ := i.1.val*i.2.val
/-- Literal PaperVerification.AlternatingForms.Hibi.diagonalExponent; exact original coordinate/Tor semantics. -/
def diagonalExponent (I : IntervalIndex α β) : (Fin s × Fin n) →₀ ℕ :=
  minorTermExponent I.val.val 1
/-- Literal PaperVerification.AlternatingForms.Hibi.diagonalWeight; exact original coordinate/Tor semantics. -/
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
open _root_.PaperVerification.AlternatingForms
/-- Literal PaperVerification.AlternatingForms.oddGoodMap; exact original coordinate/Tor semantics. -/
def oddGoodMap : P →ₐ[K]
    (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸Q) :=
  (Ideal.Quotient.mkₐ K Q).comp (rename Subtype.val)
/-- Literal PaperVerification.AlternatingForms.oddGoodIdeal; exact original coordinate/Tor semantics. -/
def oddGoodIdeal : Ideal P := RingHom.ker (oddGoodMap (K := K) k t hs).toRingHom
end
end PaperVerification.AlternatingForms
namespace PaperVerification.AlternatingForms
section
open scoped BigOperators
open MvPolynomial PaperVerification.WeightedInitialFiber
variable {K : Type*} [Field K] {n : ℕ}
open _root_.PaperVerification.AlternatingForms
/-- Literal PaperVerification.AlternatingForms.onePlaneIndex; exact original coordinate/Tor semantics. -/
def onePlaneIndex (i : Fin n) : PluckerIndex 1 n :=
  ⟨fun _ ↦ i, fun a b hab ↦ by
    have h : a = b := Subsingleton.elim _ _
    exact (not_lt_of_ge h.ge hab).elim⟩
/-- Literal PaperVerification.AlternatingForms.onePlaneIndex_eta; exact original coordinate/Tor semantics. -/
theorem onePlaneIndex_eta (I : PluckerIndex 1 n) :
    onePlaneIndex (I.val 0) = I := by
  apply Subtype.ext
  funext a
  have h : a = 0 := Subsingleton.elim _ _
  rw [h]
  rfl
/-- Literal PaperVerification.AlternatingForms.onePlane_matrixPluckerIdeal; exact original coordinate/Tor semantics. -/
theorem onePlane_matrixPluckerIdeal :
    matrixPluckerIdeal (K := K) (s := 1) (n := n) = ⊥ := by
  change RingHom.ker
    (genericPluckerMap (K := K) (s := 1) (n := n)).toRingHom = ⊥
  apply (RingHom.injective_iff_ker_eq_bot _).mp
  exact (onePlaneGenericMapEquiv (K := K) (n := n)).injective
end
end PaperVerification.AlternatingForms
namespace TauCeti
section
universe u v
open _root_.CategoryTheory CliffordAlgebra
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable (φ : Module.Dual R M)
open _root_.TauCeti
/-- Literal TauCeti.koszulDifferential; exact original coordinate/Tor semantics. -/
def koszulDifferential (n : ℕ) : ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M :=
  (contractLeft (Q := (0 : QuadraticForm R M)) φ).restrict fun _ hx ↦
    ExteriorAlgebra.contractLeft_mem_exteriorPower φ hx
/-- Literal TauCeti.koszulDifferential_comp_koszulDifferential; exact original coordinate/Tor semantics. -/
theorem koszulDifferential_comp_koszulDifferential (n : ℕ) :
    koszulDifferential φ n ∘ₗ koszulDifferential φ (n + 1) = 0 :=
  LinearMap.ext fun x ↦ Subtype.ext (contractLeft_contractLeft φ x.1)
end
end TauCeti
namespace TauCeti
section
universe u v
open _root_.CategoryTheory CliffordAlgebra
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
open _root_.TauCeti
/-- Literal TauCeti.koszulComplex; exact original coordinate/Tor semantics. -/
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
open _root_.PaperVerification.AlternatingForms.OnePlaneKoszul
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.Ring; exact original coordinate/Tor semantics. -/
abbrev Ring := MvPolynomial (PluckerIndex 1 n) K ⧸ matrixPluckerIdeal
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.indexEquiv; exact original coordinate/Tor semantics. -/
def indexEquiv : PluckerIndex 1 n ≃ Fin n where
  toFun I := I.val 0
  invFun := onePlaneIndex
  left_inv := onePlaneIndex_eta
  right_inv _ := rfl
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.polynomialEquiv; exact original coordinate/Tor semantics. -/
def polynomialEquiv : Ring K n ≃ₐ[K] MvPolynomial (Fin n) K :=
  (Ideal.quotientEquivAlgOfEq K onePlane_matrixPluckerIdeal).trans
    ((AlgEquiv.quotientBot K _).trans (MvPolynomial.renameEquiv K (indexEquiv n)))
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.generator; exact original coordinate/Tor semantics. -/
def generator (i : Fin n) : Ring K n :=
  Ideal.Quotient.mk _ (X (onePlaneIndex i))
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.functional; exact original coordinate/Tor semantics. -/
def functional : Module.Dual (Ring K n) (Fin n → Ring K n) :=
  Fintype.linearCombination (Ring K n) (generator K n)
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.complex; exact original coordinate/Tor semantics. -/
def complex : ChainComplex (ModuleCat (Ring K n)) ℕ :=
  TauCeti.koszulComplex (functional K n)
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.complex_exactAt_succ; exact original coordinate/Tor semantics. -/
theorem complex_exactAt_succ (r : ℕ) : (complex K n).ExactAt (r+1) :=
  TauCeti.koszulComplex.exactAt_of_isWeaklyRegular (generator K n)
    (variables_weaklyRegular K n) r
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.augmentationIdeal; exact original coordinate/Tor semantics. -/
def augmentationIdeal : Ideal (Ring K n) := Ideal.span (Set.range (generator K n))
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.Residue; exact original coordinate/Tor semantics. -/
abbrev Residue := Ring K n ⧸ augmentationIdeal K n
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.augmentation; exact original coordinate/Tor semantics. -/
def augmentation : (complex K n).X 0 ⟶ ModuleCat.of (Ring K n) (Residue K n) :=
  ModuleCat.ofHom ((augmentationIdeal K n).mkQ.comp
    (exteriorPower.zeroEquiv (Ring K n) (Fin n → Ring K n)).toLinearMap)
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.d_augmentation; exact original coordinate/Tor semantics. -/
theorem d_augmentation : (complex K n).d 1 0 ≫ augmentation K n=0 := by
  apply ModuleCat.hom_ext
  exact LinearMap.range_le_ker_iff.mp (le_of_eq (range_d_zero_eq_ker_augmentation K n))
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.augmentation_exact; exact original coordinate/Tor semantics. -/
theorem augmentation_exact : (ShortComplex.mk _ _ (d_augmentation K n)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact range_d_zero_eq_ker_augmentation K n
/-- Exact original model obligation; compared with its genuine source proof. -/
theorem augmentationEpi : CategoryTheory.Epi (augmentation K n) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  exact (Submodule.mkQ_surjective _).comp (exteriorPower.zeroEquiv (Ring K n) (Fin n → Ring K n)).surjective
attribute [instance] augmentationEpi
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.resolution; exact original coordinate/Tor semantics. -/
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
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.torIso; exact original coordinate/Tor semantics. -/
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
open _root_.PaperVerification.AlternatingForms.OnePlaneKoszul
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.residueTensorComplex; exact original coordinate/Tor semantics. -/
def residueTensorComplex : ChainComplex (ModuleCat P) ℕ :=
  ((((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat P)).obj
    (ModuleCat.of P Q)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (resolution K n).complex)
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.residueTensorComplex_d; exact original coordinate/Tor semantics. -/
theorem residueTensorComplex_d (i j : ℕ) :
    (residueTensorComplex K n).d i j=0 := by
  by_cases h : j+1=i
  · subst i
    exact residueTensorComplex_d_succ K n j
  · exact (residueTensorComplex K n).shape i j h
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.residueTensorHomologyIso; exact original coordinate/Tor semantics. -/
def residueTensorHomologyIso (r : ℕ) :
    (residueTensorComplex K n).homology r ≅ (residueTensorComplex K n).X r :=
  (ShortComplex.HomologyData.ofZeros ((residueTensorComplex K n).sc r)
    (residueTensorComplex_d K n _ _) (residueTensorComplex_d K n _ _)).left.homologyIso
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.residueTorIso; exact original coordinate/Tor semantics. -/
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
open _root_.PaperVerification.AlternatingForms.BasisDegree
/-- Literal PaperVerification.AlternatingForms.BasisDegree.piece; exact original coordinate/Tor semantics. -/
def piece (N : ℕ) : Submodule R V :=
  (Finsupp.supported R R {i | δ i=N}).comap B.repr.toLinearMap
/-- Literal PaperVerification.AlternatingForms.BasisDegree.piece_iSupIndep; exact original coordinate/Tor semantics. -/
theorem piece_iSupIndep : iSupIndep (piece B δ) := by
  intro N
  rw [Submodule.disjoint_def]
  intro x hx hother
  apply B.repr.injective
  rw [map_zero]
  apply Finsupp.ext
  intro i
  change B.repr x i=0
  by_cases hi : δ i=N
  · have hle : (⨆ M≠N,piece B δ M)≤(B.coord i).ker := by
      apply iSup_le
      intro M
      apply iSup_le
      intro hMN
      intro y hy
      exact LinearMap.mem_ker.mpr ((mem_piece B δ M y).mp hy i
        (by rw [hi]; exact Ne.symm hMN))
    exact LinearMap.mem_ker.mp (hle hother)
  · exact (mem_piece B δ N x).mp hx i hi
/-- Literal PaperVerification.AlternatingForms.BasisDegree.piece_iSup; exact original coordinate/Tor semantics. -/
theorem piece_iSup : (⨆ N,piece B δ N)=⊤ := by
  apply top_unique
  rw [←B.span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨i,rfl⟩
  exact (le_iSup (piece B δ) (δ i)) (basis_mem_piece B δ i)
/-- Literal PaperVerification.AlternatingForms.BasisDegree.grading; exact original coordinate/Tor semantics. -/
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
open _root_.PaperVerification.AlternatingForms.OnePlaneKoszul
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.freeTermOverK; exact original coordinate/Tor semantics. -/
abbrev freeTermOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K P)).obj ((complex K n).X r)
instance freeTerm_isScalarTower (r : ℕ) : IsScalarTower K P (freeTermOverK K n r) := IsScalarTower.of_compHom K P ((complex K n).X r)
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.tensorTermOverK; exact original coordinate/Tor semantics. -/
abbrev tensorTermOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K P)).obj ((residueTensorComplex K n).X r)
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.freeBasis; exact original coordinate/Tor semantics. -/
def freeBasis (r : ℕ) :
    Module.Basis (Set.powersetCard (Fin n) r) P (freeTermOverK K n r) :=
  (Pi.basisFun P (Fin n)).exteriorPower r
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.coordinateBasis; exact original coordinate/Tor semantics. -/
def coordinateBasis : Module.Basis (Fin n →₀ ℕ) K P :=
  (MvPolynomial.basisMonomials (Fin n) K).map (polynomialEquiv K n).symm.toLinearEquiv
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.freeMonomialBasis; exact original coordinate/Tor semantics. -/
def freeMonomialBasis (r : ℕ) :
    Module.Basis ((Fin n →₀ ℕ) × Set.powersetCard (Fin n) r) K (freeTermOverK K n r) :=
  (coordinateBasis K n).smulTower (freeBasis K n r)
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.freeGrading; exact original coordinate/Tor semantics. -/
def freeGrading (r : ℕ) : TauCeti.InternalGrading K (freeTermOverK K n r) ℕ :=
  BasisDegree.grading (freeMonomialBasis K n r) (fun a ↦ a.1.degree+r)
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.specializeFree; exact original coordinate/Tor semantics. -/
def specializeFree (r : ℕ) : freeTermOverK K n r →ₗ[K] tensorTermOverK K n r :=
  ((ModuleCat.restrictScalars (algebraMap K P)).map
    (ModuleCat.ofHom (TensorProduct.mk P Q (⋀[P]^r (Fin n → P)) 1))).hom
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.tensorDegreePiece; exact original coordinate/Tor semantics. -/
def tensorDegreePiece (r N : ℕ) : Submodule K (tensorTermOverK K n r) :=
  ((freeGrading K n r).piece N).map (specializeFree K n r)
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.tensorDegreePiece_eq_bot; exact original coordinate/Tor semantics. -/
theorem tensorDegreePiece_eq_bot (r N : ℕ) (hNr : N≠r) :
    tensorDegreePiece K n r N=⊥ := by
  change _root_.PaperVerification.AlternatingForms.OnePlaneKoszul.tensorDegreePiece K n r N=⊥
  exact _root_.PaperVerification.AlternatingForms.OnePlaneKoszul.tensorDegreePiece_eq_bot K n r N hNr
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.tensorDegreePieces_iSup; exact original coordinate/Tor semantics. -/
theorem tensorDegreePieces_iSup (r : ℕ) : (⨆ N,tensorDegreePiece K n r N)=⊤ := by
  simp only [tensorDegreePiece]
  rw [←Submodule.map_iSup,(freeGrading K n r).isInternal.submodule_iSup_eq_top,
    Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (specializeFree_surjective K n r)
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.tensorGrading; exact original coordinate/Tor semantics. -/
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
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.TorOverK; exact original coordinate/Tor semantics. -/
def TorOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K P)).obj
    (((Tor (ModuleCat P) r).obj (ModuleCat.of P Q)).obj (ModuleCat.of P Q))
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.torTermIsoOverK; exact original coordinate/Tor semantics. -/
def torTermIsoOverK (r : ℕ) : TorOverK K n r ≅ tensorTermOverK K n r :=
  (ModuleCat.restrictScalars (algebraMap K P)).mapIso (residueTorIso K n r)
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.torGrading; exact original coordinate/Tor semantics. -/
def torGrading (r : ℕ) : TauCeti.InternalGrading K (TorOverK K n r) ℕ :=
  (tensorGrading K n r).map (torTermIsoOverK K n r).toLinearEquiv.symm
/-- Literal PaperVerification.AlternatingForms.OnePlaneKoszul.actual_onePlane_Tor_degree; exact original coordinate/Tor semantics. -/
theorem actual_onePlane_Tor_degree (r N : ℕ) :
    (torGrading K n r).piece N=if N=r then ⊤ else ⊥ := by
  change (_root_.PaperVerification.AlternatingForms.OnePlaneKoszul.torGrading K n r).piece N=if N=r then ⊤ else ⊥
  exact _root_.PaperVerification.AlternatingForms.OnePlaneKoszul.actual_onePlane_Tor_degree K n r N
end
end PaperVerification.AlternatingForms.OnePlaneKoszul
namespace PaperVerification.AlternatingForms
section
open scoped Classical
open MvPolynomial
open PaperVerification.WeightedInitialFiber
universe u v
variable {K : Type u} [Field K] [CharZero K]
open _root_.PaperVerification.AlternatingForms
/-- Literal PaperVerification.AlternatingForms.HasQuadraticGroebnerBasis; exact original coordinate/Tor semantics. -/
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
/-- The genuine ordinary coordinate-degree piece of the actual quotient ring. -/
def quotientPiece {σ : Type*} (Q : Ideal (MvPolynomial σ K)) (d : ℕ) : Submodule K (MvPolynomial σ K ⧸ Q) := (MvPolynomial.homogeneousSubmodule σ K d).map (Ideal.Quotient.mkₐ K Q).toLinearMap
/-- The actual Rees element has degree d exactly when every original quotient coefficient does. -/
def reesPiece {σ : Type*} (Q : Ideal (MvPolynomial σ K)) (w : σ → ℕ) (d : ℕ) : Submodule K (reesAlgebra Q w) := ⨅ j, (quotientPiece Q d).comap ((coefficient j).comp (reesAlgebra Q w).val.toLinearMap)
/-- Actual flat weight family, with parameter degree zero and every ordinary-graded endpoint piece. -/
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
/-- Actual positive-basis coordinates of an algebra element. -/
def positiveCoordinates (B : Module.Basis (Option I) K A) : A →ₗ[K] (I →₀ K) := (Finsupp.lcomapDomain (R := K) (M := K) Option.some (Option.some_injective I)).comp B.repr.toLinearMap
/-- Actual multiplication table of positive augmentation-basis vectors. -/
def productCoordinates (B : Module.Basis (Option I) K A) (i j : I) : I →₀ K := positiveCoordinates B (B (some i) * B (some j))
def prepend (i : I) : (List I →₀ K) →ₗ[K] (List I →₀ K) := Finsupp.linearCombination K (fun L => Finsupp.single (i::L) 1)
def appendTail (L : List I) : (I →₀ K) →ₗ[K] (List I →₀ K) := Finsupp.linearCombination K (fun i => Finsupp.single (i::L) 1)
def mergeBasis (B : Module.Basis (Option I) K A) (i : I) (L : List I) : List I →₀ K := List.casesOn L 0 (fun j T => appendTail T (productCoordinates B i j))
def merge (B : Module.Basis (Option I) K A) (i : I) : (List I →₀ K) →ₗ[K] (List I →₀ K) := Finsupp.linearCombination K (mergeBasis B i)
/-- Alternating adjacent products in the genuine normalized bar tensors. -/
def differentialBasis (B : Module.Basis (Option I) K A) (L : List I) : List I →₀ K := List.recOn L 0 (fun i T ih => merge B i (Finsupp.single T 1) - prepend i ih)
def differential (B : Module.Basis (Option I) K A) : (List I →₀ K) →ₗ[K] (List I →₀ K) := Finsupp.linearCombination K (differentialBasis B)
/-- Actual tensor length and original homogeneous coordinate degree. -/
def barPiece (δ : I → ℕ) (r N : ℕ) : Submodule K (List I →₀ K) := Finsupp.supported K K {L | L.length=r ∧ (L.map δ).sum=N}
end Model
namespace PaperVerification.AlternatingForms
open MvPolynomial PaperVerification.WeightedInitialFiber
universe uMain
variable {K : Type uMain} [Field K] [CharZero K]
-- Principal proofs and the original-complex/fiber-piece bridges are in PalomarMain13Proofs.
end PaperVerification.AlternatingForms
end PalomarAlternatingDegeneration
