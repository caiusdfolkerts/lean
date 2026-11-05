module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Elab.Tactic.Omega
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.MonoidAlgebra.Ideal
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Logic.Relation
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Bornology.BoundedOperation
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.LeftRight

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricExchange
section Source_ToricExchange

-- original header: module
-- original header: public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
-- original header: public import Mathlib.Data.Multiset.AddSub
-- original header: public import Mathlib.Logic.Relation
-- original header: public import Mathlib.Tactic.Abel
-- original header: public import Mathlib.Tactic.IntervalCases
-- original header: @[expose] public section
/-!
# Quadratic exchange on decomposition fibers

The vertices are actual multisets of points of a set in an additive commutative group.
An edge replaces precisely two entries by two entries with the same sum.
No connectivity assumption is hidden in the definition of an edge or a fiber.
-/

namespace PaperVerification.ToricExchange

variable {M : Type*} [AddCommGroup M] (A : Set M)

/-- Sum of the ambient lattice vectors in a multiset of points of `A`. -/
def total (s : Multiset A) : M := (s.map Subtype.val).sum

@[simp] theorem total_zero : total A 0 = 0 := by simp [total]
@[simp] theorem total_cons (a : A) (s : Multiset A) :
    total A (a ::ₘ s) = (a : M) + total A s := by simp [total]
@[simp] theorem total_singleton (a : A) : total A {a} = (a : M) := by
  simp [total]
@[simp] theorem total_add (s t : Multiset A) :
    total A (s + t) = total A s + total A t := by simp [total]

/-- A single quadratic exchange, preserving all entries outside the selected pair. -/
def QuadraticMove (s t : Multiset A) : Prop :=
  ∃ (r : Multiset A) (a b c d : A),
    s = a ::ₘ b ::ₘ r ∧ t = c ::ₘ d ::ₘ r ∧
    (a : M) + b = (c : M) + d

/-- Connectivity by finitely many genuine quadratic exchanges. -/
def Connected (s t : Multiset A) : Prop :=
  Relation.ReflTransGen (QuadraticMove A) s t

namespace QuadraticMove

variable {A}

theorem symm {s t : Multiset A} (h : QuadraticMove A s t) : QuadraticMove A t s := by
  rcases h with ⟨r, a, b, c, d, hs, ht, he⟩
  exact ⟨r, c, d, a, b, ht, hs, he.symm⟩

theorem card_eq {s t : Multiset A} (h : QuadraticMove A s t) : s.card = t.card := by
  rcases h with ⟨r, a, b, c, d, rfl, rfl, he⟩
  simp

theorem total_eq {s t : Multiset A} (h : QuadraticMove A s t) : total A s = total A t := by
  rcases h with ⟨r, a, b, c, d, rfl, rfl, he⟩
  simpa only [total_cons, ← add_assoc] using congrArg (· + total A r) he

theorem add_right {s t : Multiset A} (h : QuadraticMove A s t) (u : Multiset A) :
    QuadraticMove A (s + u) (t + u) := by
  rcases h with ⟨r, a, b, c, d, rfl, rfl, he⟩
  exact ⟨r + u, a, b, c, d, by simp, by simp, he⟩

end QuadraticMove

namespace Connected

variable {A}

@[refl] theorem refl (s : Multiset A) : Connected A s s := Relation.ReflTransGen.refl

theorem single {s t : Multiset A} (h : QuadraticMove A s t) : Connected A s t :=
  Relation.ReflTransGen.single h

@[trans] theorem trans {r s t : Multiset A} (h : Connected A r s) (k : Connected A s t) :
    Connected A r t := Relation.ReflTransGen.trans h k

@[symm] theorem symm {s t : Multiset A} (h : Connected A s t) : Connected A t s := by
  induction h with
  | refl => exact refl _
  | @tail b c hbc hcd ih =>
    exact trans (single hcd.symm) ih

theorem card_eq {s t : Multiset A} (h : Connected A s t) : s.card = t.card := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans h.card_eq

theorem total_eq {s t : Multiset A} (h : Connected A s t) : total A s = total A t := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans h.total_eq

theorem add_right {s t : Multiset A} (h : Connected A s t) (u : Multiset A) :
    Connected A (s + u) (t + u) := by
  induction h with
  | refl => exact refl _
  | tail _ h ih => exact trans ih (single (h.add_right u))

theorem cons {s t : Multiset A} (h : Connected A s t) (a : A) :
    Connected A (a ::ₘ s) (a ::ₘ t) := by
  have h' := h.add_right {a}
  rw [add_comm s {a}, add_comm t {a}, Multiset.singleton_add, Multiset.singleton_add] at h'
  exact h' 

end Connected

/-- The midpoint decomposition property needed in the all-degree exchange induction.
For lattice points of a convex polytope this follows from convexity and IDP. -/
def MidpointDecomposition : Prop :=
  ∀ (u v : Multiset A), 0 < u.card → u.card = v.card → ∀ z : M,
    z + z = total A u + total A v →
    ∃ w : Multiset A, w.card = u.card ∧ total A w = z

/-- The local triple-reduction conclusion supplied by the parity and adjoint arguments. -/
def TripleReduction : Prop :=
  ∀ a b c : A, ∃ p q : A,
    Connected A (a ::ₘ b ::ₘ c ::ₘ 0) (p ::ₘ q ::ₘ q ::ₘ 0)

/-- A prescribed parity for the first summand creates a repeated entry in two exchanges. -/
theorem triple_reduction_of_parity {a b c p q e : A}
    (hab : (a : M) + b = (p : M) + q)
    (hpc : (p : M) + c = (e : M) + e) :
    Connected A (a ::ₘ b ::ₘ c ::ₘ 0) (q ::ₘ e ::ₘ e ::ₘ 0) := by
  have h₁ : Connected A (a ::ₘ b ::ₘ c ::ₘ 0) (p ::ₘ q ::ₘ c ::ₘ 0) :=
    Connected.single ⟨c ::ₘ 0, a, b, p, q, rfl, rfl, hab⟩
  have h₂ : Connected A (p ::ₘ q ::ₘ c ::ₘ 0) (q ::ₘ e ::ₘ e ::ₘ 0) :=
    Connected.single ⟨q ::ₘ 0, p, c, e, e,
      by simp only [Multiset.cons_swap q c],
      by simp only [Multiset.cons_swap q e], hpc⟩
  exact h₁.trans h₂

/-- The geometric portion of Proposition 2.1, expressed by the minimal-face map.
`parity` is prescribed parity plus midpoint convexity on each face; `adjoint` moves
one entry into the relative interior of a proper face. Both hypotheses are equations
and face relations, not assumptions of exchange connectivity. -/
theorem tripleReduction_of_face_data {F : Type*} [SemilatticeSup F] [OrderTop F]
    (face : A → F)
    (parity : ∀ a b c : A, face c ≤ face a ⊔ face b →
      ∃ p q e : A, (a : M) + b = (p : M) + q ∧ (p : M) + c = (e : M) + e)
    (adjoint : ∀ a b : A, face a ⊔ face b ≠ ⊤ →
      ∃ u v : A, (a : M) + b = (u : M) + v ∧
        face u = face a ⊔ face b ∧ face v ≤ face a ⊔ face b) :
    TripleReduction A := by
  intro a b c
  by_cases hc : face c ≤ face a ⊔ face b
  · obtain ⟨p, q, e, hab, hpc⟩ := parity a b c hc
    exact ⟨q, e, triple_reduction_of_parity A hab hpc⟩
  · have hproper : face a ⊔ face b ≠ ⊤ := by
      intro htop
      apply hc
      rw [htop]
      exact le_top
    obtain ⟨u, v, huv, huf, hvf⟩ := adjoint a b hproper
    have hvc : face v ≤ face u ⊔ face c := le_sup_of_le_left (by simpa only [huf] using hvf)
    obtain ⟨p, q, e, hup, hpv⟩ := parity u c v hvc
    have h₁ : Connected A (a ::ₘ b ::ₘ c ::ₘ 0) (u ::ₘ v ::ₘ c ::ₘ 0) :=
      Connected.single ⟨c ::ₘ 0, a, b, u, v, rfl, rfl, huv⟩
    have h₂ : Connected A (u ::ₘ v ::ₘ c ::ₘ 0) (q ::ₘ e ::ₘ e ::ₘ 0) := by
      simpa only [Multiset.cons_swap c v] using triple_reduction_of_parity A hup hpv
    exact ⟨q, e, h₁.trans h₂⟩

theorem exists_repeated (htriple : TripleReduction A) (s : Multiset A)
    (hs : 3 ≤ s.card) :
    ∃ (b : A) (u : Multiset A), Connected A s (b ::ₘ b ::ₘ u) := by
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (show 0 < s.card by omega)
  obtain ⟨r, rfl⟩ := Multiset.exists_cons_of_mem ha
  obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.mp (show 0 < r.card by simp at hs; omega)
  obtain ⟨r', rfl⟩ := Multiset.exists_cons_of_mem hb
  obtain ⟨c, hc⟩ := Multiset.card_pos_iff_exists_mem.mp (show 0 < r'.card by simp at hs; omega)
  obtain ⟨r'', rfl⟩ := Multiset.exists_cons_of_mem hc
  obtain ⟨p, q, h⟩ := htriple a b c
  refine ⟨q, p ::ₘ r'', ?_⟩
  have h' := h.add_right r''
  simpa only [Multiset.cons_add, Multiset.zero_add, Multiset.cons_swap p q] using h'

theorem connected_of_card_le_two (s t : Multiset A) (hn : s.card ≤ 2)
    (hc : s.card = t.card) (hz : total A s = total A t) : Connected A s t := by
  interval_cases hs : s.card
  · have hs0 : s = 0 := Multiset.card_eq_zero.mp hs
    have ht0 : t = 0 := Multiset.card_eq_zero.mp (show t.card = 0 by omega)
    subst s; subst t
    exact Connected.refl _
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hs
    obtain ⟨b, rfl⟩ := Multiset.card_eq_one.mp (by simpa using hc.symm)
    have hab : a = b := Subtype.ext (by simpa [total] using hz)
    subst b
    exact Connected.refl _
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hs
    obtain ⟨c, d, rfl⟩ := Multiset.card_eq_two.mp (by simpa using hc.symm)
    exact Connected.single ⟨0, a, b, c, d, rfl, rfl, by simpa [total] using hz⟩

/-- Every decomposition fiber is connected once midpoint decomposition and the
local triple-reduction property are available. The induction is over all natural degrees. -/
theorem all_fibers_connected (hmid : MidpointDecomposition A) (htriple : TripleReduction A)
    (s t : Multiset A) (hc : s.card = t.card) (hz : total A s = total A t) :
    Connected A s t := by
  have main : ∀ n (s t : Multiset A), s.card = n → t.card = n →
      total A s = total A t → Connected A s t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s t hs ht hz
      by_cases hn : n ≤ 2
      · exact connected_of_card_le_two A s t (by simpa only [hs] using hn) (hs.trans ht.symm) hz
      have hn3 : 3 ≤ n := by omega
      obtain ⟨b, u, hsu⟩ := exists_repeated A htriple s (by simpa only [hs] using hn3)
      obtain ⟨d, v, htv⟩ := exists_repeated A htriple t (by simpa only [ht] using hn3)
      have hu : u.card + 2 = n := by simpa [hs, Nat.add_assoc] using hsu.card_eq.symm
      have hv : v.card + 2 = n := by simpa [ht, Nat.add_assoc] using htv.card_eq.symm
      have hsu' : total A s = (b : M) + b + total A u := by
        simpa only [total_cons, ← add_assoc] using hsu.total_eq
      have htv' : total A t = (d : M) + d + total A v := by
        simpa only [total_cons, ← add_assoc] using htv.total_eq
      let q : M := total A s - b - d
      have hq : q + q = total A u + total A v := by
        dsimp [q]
        calc
          total A s - b - d + (total A s - b - d) =
              (total A s - b - b) + (total A t - d - d) := by rw [← hz]; abel
          _ = total A u + total A v := by rw [hsu', htv']; abel
      obtain ⟨g, hg, hgz⟩ := hmid u v (by omega) (by omega) q hq
      have hl : Connected A (b ::ₘ u) (d ::ₘ g) := by
        apply ih (n - 1) (by omega)
        · simp; omega
        · simp; omega
        · simp only [total_cons, hgz]
          dsimp [q]
          rw [hsu']
          abel
      have hr : Connected A (b ::ₘ g) (d ::ₘ v) := by
        apply ih (n - 1) (by omega)
        · simp; omega
        · simp; omega
        · simp only [total_cons, hgz]
          dsimp [q]
          rw [hz, htv']
          abel
      have hmiddle : Connected A (b ::ₘ b ::ₘ u) (d ::ₘ d ::ₘ v) :=
        (hl.cons b).trans (by simpa only [Multiset.cons_swap b d] using hr.cons d)
      exact hsu.trans (hmiddle.trans htv.symm)
  exact main s.card s t rfl hc.symm hz

end PaperVerification.ToricExchange
end Source_ToricExchange
-- END ORIGINAL PaperVerification.ToricExchange


-- BEGIN ORIGINAL PaperVerification.ToricConvexity
section Source_ToricConvexity

-- original header: module
-- original header: public import PaperVerification.ToricExchange
-- original header: public import Mathlib.Analysis.Convex.Combination
-- original header: public import Mathlib.Algebra.BigOperators.Fin
-- original header: public import Mathlib.Tactic.Module
-- original header: public import Mathlib.Tactic.Positivity
-- original header: public import Mathlib.Tactic.NormNum
-- original header: @[expose] public section
/-!
# The convexity and integer-decomposition bridge

This file makes the geometric hypothesis in the exchange induction explicit.
The degree-`k` polytope is the ordinary scalar dilate `k • P`, represented by
an existential witness in `P`. The integer-decomposition property is required at
all positive natural degrees, with no bounded-degree restriction.
-/

noncomputable section

namespace PaperVerification.ToricExchange

variable {M V : Type*} [AddCommGroup M] [AddCommGroup V] [Module ℝ V]
variable (embedding : M →+ V) (P : Set V)

/-- The actual set of lattice points in a real convex set. -/
def latticePoints : Set M := embedding ⁻¹' P

/-- Integer decomposition in every positive degree, for the specified lattice embedding. -/
def IntegerDecompositionProperty : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ z : M,
    (∃ x ∈ P, embedding z = (k : ℝ) • x) →
    ∃ s : Multiset (latticePoints embedding P), s.card = k ∧
      total (latticePoints embedding P) s = z

/-- The arithmetic mean of a nonempty multiset of lattice points lies in the
convex set containing those points. -/
theorem average_total_mem (hP : Convex ℝ P)
    (s : Multiset (latticePoints embedding P)) (hs : 0 < s.card) :
    (s.card : ℝ)⁻¹ • embedding (total (latticePoints embedding P) s) ∈ P := by
  classical
  let l := s.toList
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  have hweights : (∑ _i : Fin l.length, (s.card : ℝ)⁻¹) = 1 := by
    simp [l, Multiset.length_toList, nsmul_eq_mul, mul_inv_cancel₀ hn]
  have hsum : (∑ i : Fin l.length, embedding ((l[i.1] : latticePoints embedding P) : M)) =
      embedding (total (latticePoints embedding P) s) := by
    rw [Fin.sum_univ_fun_getElem l
      (fun a : latticePoints embedding P => embedding (a : M))]
    change (s.toList.map (fun a : latticePoints embedding P => embedding (a : M))).sum = _
    rw [Multiset.sum_map_toList s
      (fun a : latticePoints embedding P => embedding (a : M))]
    simp only [total, map_multiset_sum, Multiset.map_map]
    rfl
  have hmean := hP.sum_mem (t := Finset.univ)
    (w := fun _i : Fin l.length => (s.card : ℝ)⁻¹)
    (z := fun i : Fin l.length => embedding ((l[i.1] : latticePoints embedding P) : M))
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)) hweights
    (fun i _ => (l[i.1]).property)
  simpa only [← Finset.smul_sum, hsum] using hmean

/-- Convexity and the actual integer-decomposition property imply precisely the
midpoint decomposition used by the all-degree exchange proof. -/
theorem midpointDecomposition_of_convex_idp (hP : Convex ℝ P)
    (hidp : IntegerDecompositionProperty embedding P) :
    MidpointDecomposition (latticePoints embedding P) := by
  intro u v hu huv z hz
  have hv : 0 < v.card := by omega
  have huP := average_total_mem embedding P hP u hu
  have hvP := average_total_mem embedding P hP v hv
  rw [← huv] at hvP
  have hz' : embedding z + embedding z =
      embedding (total (latticePoints embedding P) u) +
      embedding (total (latticePoints embedding P) v) := by
    simpa using congrArg embedding hz
  have hhalf : (1 / 2 : ℝ) •
      (embedding (total (latticePoints embedding P) u) +
        embedding (total (latticePoints embedding P) v)) = embedding z := by
    rw [← hz',← two_smul ℝ (embedding z),smul_smul]
    norm_num
  have hw := hP huP hvP (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hw' : (u.card : ℝ)⁻¹ • embedding z ∈ P := by
    convert hw using 1
    rw [← hhalf]
    simp only [smul_add,smul_comm (u.card : ℝ)⁻¹ (1 / 2 : ℝ)]
  apply hidp u.card (by omega) z
  refine ⟨(u.card : ℝ)⁻¹ • embedding z, hw', ?_⟩
  have hn : (u.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
  simp [smul_smul, mul_inv_cancel₀ hn]

/-- Congruence modulo twice the ambient lattice, stated without quotient notation. -/
def SameParity (a b : M) : Prop := ∃ w : M, a - b = w + w

/-- For points in an affine face, ambient parity is exactly parity in the saturated
face lattice: the halving witness automatically lies in the real face direction. -/
theorem sameParity_iff_saturated_direction (W : Submodule ℝ V) (p c : M)
    (hdirection : embedding (p - c) ∈ W) :
    SameParity p c ↔ ∃ w : M, embedding w ∈ W ∧ p - c = w + w := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_, hw⟩
    have htwice : embedding w + embedding w ∈ W := by
      simpa only [hw, map_add] using hdirection
    have hhalf := W.smul_mem (1 / 2 : ℝ) htwice
    convert hhalf using 1
    rw [← two_smul ℝ (embedding w),smul_smul]
    norm_num
  · rintro ⟨w, _, hw⟩
    exact ⟨w, hw⟩

/-- Convexity turns an integral parity midpoint into an actual lattice point of the polytope. -/
theorem midpoint_of_sameParity (hP : Convex ℝ P)
    (p c : latticePoints embedding P) (hpc : SameParity (p : M) c) :
    ∃ e : latticePoints embedding P, (p : M) + c = (e : M) + e := by
  obtain ⟨w, hw⟩ := hpc
  have he : (p : M) + c = (c + w) + (c + w) := by
    calc
      (p : M) + c = (p - c) + (c + c) := by abel
      _ = (w + w) + (c + c) := by rw [hw]
      _ = (c + w) + (c + w) := by abel
  have hmid := hP p.property c.property (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have he' : embedding p + embedding c = embedding (c + w) + embedding (c + w) := by
    simpa using congrArg embedding he
  have hm : embedding (c + w) ∈ P := by
    convert hmid using 1
    rw [← smul_add, he',← two_smul ℝ (embedding (c + w)),smul_smul]
    norm_num
  exact ⟨⟨c + w, hm⟩, he⟩

/-- The parity and proper-face adjoint data imply triple reduction using actual convexity,
so no midpoint-closure axiom is needed. -/
theorem tripleReduction_of_convex_face_data (hP : Convex ℝ P)
    {F : Type*} [SemilatticeSup F] [OrderTop F]
    (face : latticePoints embedding P → F)
    (parity : ∀ a b c : latticePoints embedding P, face c ≤ face a ⊔ face b →
      ∃ p q : latticePoints embedding P,
        (a : M) + b = (p : M) + q ∧ SameParity (p : M) c)
    (adjoint : ∀ a b : latticePoints embedding P, face a ⊔ face b ≠ ⊤ →
      ∃ u v : latticePoints embedding P, (a : M) + b = (u : M) + v ∧
        face u = face a ⊔ face b ∧ face v ≤ face a ⊔ face b) :
    TripleReduction (latticePoints embedding P) := by
  apply tripleReduction_of_face_data (latticePoints embedding P) face ?_ adjoint
  intro a b c hc
  obtain ⟨p, q, he, hp⟩ := parity a b c hc
  obtain ⟨e, hmid⟩ := midpoint_of_sameParity embedding P hP p c hp
  exact ⟨p, q, e, he, hmid⟩

end PaperVerification.ToricExchange
end
end Source_ToricConvexity
-- END ORIGINAL PaperVerification.ToricConvexity


-- BEGIN ORIGINAL PaperVerification.ToricIdeal
section Source_ToricIdeal

-- original header: module
-- original header: public import PaperVerification.ToricExchange
-- original header: public import Mathlib.Algebra.MonoidAlgebra.MapDomain
-- original header: public import Mathlib.Algebra.MonoidAlgebra.Ideal
-- original header: public import Mathlib.Algebra.MvPolynomial.Basic
-- original header: public import Mathlib.Algebra.Polynomial.Basic
-- original header: public import Mathlib.RingTheory.Ideal.Maps
-- original header: public import Mathlib.Data.Finsupp.Multiset
-- original header: public import Mathlib.RingTheory.Ideal.Quotient.Defs
-- original header: @[expose] public section
/-!
# Toric ideals and quadratic exchange

This file uses genuine semigroup algebras and ideal kernels. The monomials of the
polynomial algebra are first indexed by multisets, then identified with Mathlib's
`MvPolynomial` by the multiplicity equivalence.
-/

noncomputable section

namespace PaperVerification.ToricExchange

open AddMonoidAlgebra

section GeneralKernel

variable {R S T : Type*} [CommRing R] [AddCommMonoid S] [AddCommMonoid T]

/-- The ideal of all binomials whose exponents have the same image. -/
def fiberIdeal (f : S →+ T) : Ideal (AddMonoidAlgebra R S) :=
  Ideal.span {p | ∃ s t : S, f s = f t ∧ p = single s 1 - single t 1}

/-- The kernel of a semigroup-algebra map is generated by its fiber binomials.
This holds over every commutative coefficient ring. -/
theorem kernel_mapDomain_eq_fiberIdeal (f : S →+ T) :
    RingHom.ker (AddMonoidAlgebra.mapDomainRingHom R f) = fiberIdeal (R := R) f := by
  classical
  apply le_antisymm
  · intro p hp
    let I : Ideal (AddMonoidAlgebra R S) := fiberIdeal f
    let q := Ideal.Quotient.mk I
    let rep : T → S := Function.invFun f
    have hrep (s : S) : f (rep (f s)) = f s := Function.apply_invFun_apply (f := f) (a := s)
    have hsingle (s : S) (r : R) : q (single s r) = q (single (rep (f s)) r) := by
      apply Ideal.Quotient.eq.mpr
      have hgen : single s (1 : R) - single (rep (f s)) 1 ∈ I :=
        Ideal.subset_span ⟨s, rep (f s), (hrep s).symm, rfl⟩
      have hmul := I.mul_mem_left (single (0 : S) r) hgen
      simpa only [mul_sub, single_mul_single, zero_add, mul_one] using hmul
    let g : T → R → AddMonoidAlgebra R S ⧸ I := fun t r => q (single (rep t) r)
    have hg0 (t : T) : g t 0 = 0 := by simp [g]
    have hgadd (t : T) (r₁ r₂ : R) : g t (r₁ + r₂) = g t r₁ + g t r₂ := by
      simp [g, single_add]
    have hfactor : q p = (Finsupp.mapDomain f p.coeff).sum g := by
      calc
        q p = q (p.coeff.sum single) := congrArg q p.sum_coeff_single.symm
        _ = p.coeff.sum (fun s r => q (single s r)) := map_finsuppSum q _ _
        _ = p.coeff.sum (fun s r => g (f s) r) := by
          apply Finsupp.sum_congr
          intro s hs
          exact hsingle s _
        _ = (Finsupp.mapDomain f p.coeff).sum g :=
          (Finsupp.sum_mapDomain_index hg0 hgadd).symm
    have hcoeff : Finsupp.mapDomain f p.coeff = 0 := by
      have hp' : AddMonoidAlgebra.mapDomain f p = 0 := hp
      simpa [AddMonoidAlgebra.mapDomain] using congrArg AddMonoidAlgebra.coeff hp'
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q p = 0
    rw [hfactor, hcoeff]
    simp
  · apply Ideal.span_le.mpr
    rintro p ⟨s, t, hst, rfl⟩
    change (AddMonoidAlgebra.mapDomainRingHom R f) (single s 1 - single t 1) = 0
    rw [map_sub]
    simp [AddMonoidAlgebra.mapDomainRingHom, hst]

end GeneralKernel

section QuadraticKernel

variable {M : Type*} [AddCommGroup M] (A : Set M)
variable (R : Type*) [CommRing R]

/-- The degree and lattice sum of a multiset monomial. -/
def grade : Multiset A →+ M × ℕ where
  toFun s := (total A s, s.card)
  map_zero' := by simp
  map_add' s t := by simp

/-- The homogeneous toric map before the multiset/multiplicity identification. -/
noncomputable def multisetToricMap : AddMonoidAlgebra R (Multiset A) →+* AddMonoidAlgebra R (M × ℕ) :=
  AddMonoidAlgebra.mapDomainRingHom R (grade A)

/-- The actual ideal generated by equal-sum quadratic binomials. -/
def quadraticIdeal : Ideal (AddMonoidAlgebra R (Multiset A)) :=
  Ideal.span {p | ∃ a b c d : A, (a : M) + b = (c : M) + d ∧
    p = single (a ::ₘ b ::ₘ 0) 1 - single (c ::ₘ d ::ₘ 0) 1}

theorem move_binomial_mem {s t : Multiset A} (h : QuadraticMove A s t) :
    single s (1 : R) - single t 1 ∈ quadraticIdeal A R := by
  rcases h with ⟨r, a, b, c, d, rfl, rfl, he⟩
  have hgen : single (a ::ₘ b ::ₘ 0) (1 : R) - single (c ::ₘ d ::ₘ 0) 1 ∈
      quadraticIdeal A R := Ideal.subset_span ⟨a, b, c, d, he, rfl⟩
  have hmul := (quadraticIdeal A R).mul_mem_right (single r 1) hgen
  simpa only [sub_mul, single_mul_single, one_mul, Multiset.cons_add,
    Multiset.zero_add] using hmul

theorem connected_binomial_mem {s t : Multiset A} (h : Connected A s t) :
    single s (1 : R) - single t 1 ∈ quadraticIdeal A R := by
  induction h with
  | refl => simp
  | @tail b c hbc hcd ih =>
    have hsum := (quadraticIdeal A R).add_mem ih (move_binomial_mem A R hcd)
    simpa only [sub_add_sub_cancel] using hsum

/-- Connectivity of all fibers gives quadratic generation of the genuine toric kernel. -/
theorem kernel_eq_quadraticIdeal
    (hconn : ∀ s t : Multiset A, s.card = t.card → total A s = total A t → Connected A s t) :
    RingHom.ker (multisetToricMap A R) = quadraticIdeal A R := by
  rw [multisetToricMap, kernel_mapDomain_eq_fiberIdeal]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨s, t, he, rfl⟩
    exact connected_binomial_mem A R (hconn s t (congrArg Prod.snd he) (congrArg Prod.fst he))
  · apply Ideal.span_le.mpr
    rintro p ⟨a, b, c, d, he, rfl⟩
    apply Ideal.subset_span
    refine ⟨a ::ₘ b ::ₘ 0, c ::ₘ d ::ₘ 0, ?_, rfl⟩
    apply Prod.ext
    · simpa [grade] using he
    · simp [grade]

/-- The complete algebraic exchange criterion, in every degree and over every
commutative coefficient ring. -/
theorem quadratic_generation_of_midpoint_and_triples
    (hmid : MidpointDecomposition A) (htriple : TripleReduction A) :
    RingHom.ker (multisetToricMap A R) = quadraticIdeal A R :=
  kernel_eq_quadraticIdeal A R (all_fibers_connected A hmid htriple)

/-- The multiplicity equivalence identifies multiset monomials with Mathlib polynomials. -/
noncomputable def polynomialEquiv : AddMonoidAlgebra R (Multiset A) ≃+* MvPolynomial A R := by
  classical
  exact AddMonoidAlgebra.mapDomainRingEquiv R Multiset.toFinsupp

/-- The faithful homogeneous toric map, `X a ↦ χ^a t`, with target exponent `(a,1)`. -/
noncomputable def toricMap : MvPolynomial A R →+* AddMonoidAlgebra R (M × ℕ) :=
  (multisetToricMap A R).comp (polynomialEquiv A R).symm.toRingHom

@[simp] theorem polynomialEquiv_singleton (a : A) :
    polynomialEquiv A R (single ({a} : Multiset A) 1) = MvPolynomial.X a := by
  classical
  simp [polynomialEquiv, MvPolynomial.X, MvPolynomial.monomial,
    AddMonoidAlgebra.lsingle]

@[simp] theorem polynomialEquiv_constant (r : R) :
    polynomialEquiv A R (single (0 : Multiset A) r) = MvPolynomial.C r := by
  classical
  simp [polynomialEquiv, MvPolynomial.C, MvPolynomial.monomial,
    AddMonoidAlgebra.lsingle]

@[simp] theorem polynomialEquiv_symm_C (r : R) :
    (polynomialEquiv A R).symm (MvPolynomial.C r) = single (0 : Multiset A) r := by
  apply (polynomialEquiv A R).injective
  simp

@[simp] theorem polynomialEquiv_pair (a b : A) :
    polynomialEquiv A R (single (a ::ₘ b ::ₘ 0) 1) =
      MvPolynomial.X a * MvPolynomial.X b := by
  have he : (single (a ::ₘ b ::ₘ 0) 1 : AddMonoidAlgebra R (Multiset A)) =
      single ({a} : Multiset A) 1 * single ({b} : Multiset A) 1 := by
    simp [single_mul_single]
  rw [he, map_mul, polynomialEquiv_singleton, polynomialEquiv_singleton]

@[simp] theorem polynomialEquiv_symm_X (a : A) :
    (polynomialEquiv A R).symm (MvPolynomial.X a) = single ({a} : Multiset A) 1 := by
  apply (polynomialEquiv A R).injective
  simp

@[simp] theorem toricMap_X (a : A) :
    toricMap A R (MvPolynomial.X a) = single ((a : M), 1) 1 := by
  simp [toricMap, multisetToricMap, AddMonoidAlgebra.mapDomainRingHom, grade]

@[simp] theorem toricMap_C (r : R) :
    toricMap A R (MvPolynomial.C r) = single ((0 : M), (0 : ℕ)) r := by
  simp [toricMap, multisetToricMap, AddMonoidAlgebra.mapDomainRingHom, grade]

/-- The conventional quadratic ideal in Mathlib's polynomial ring. -/
def polynomialQuadraticIdeal : Ideal (MvPolynomial A R) :=
  Ideal.span {p | ∃ a b c d : A, (a : M) + b = (c : M) + d ∧
    p = MvPolynomial.X a * MvPolynomial.X b - MvPolynomial.X c * MvPolynomial.X d}

theorem quadraticIdeal_map_polynomialEquiv :
    (quadraticIdeal A R).map (polynomialEquiv A R).toRingHom = polynomialQuadraticIdeal A R := by
  have hmap (a b c d : A) :
      (polynomialEquiv A R).toRingHom
        (single (a ::ₘ b ::ₘ 0) 1 - single (c ::ₘ d ::ₘ 0) 1) =
        MvPolynomial.X a * MvPolynomial.X b - MvPolynomial.X c * MvPolynomial.X d := by
    change polynomialEquiv A R (_ - _) = _
    rw [map_sub, polynomialEquiv_pair, polynomialEquiv_pair]
  rw [quadraticIdeal, Ideal.map_span, polynomialQuadraticIdeal]
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨a, b, c, d, he, rfl⟩, rfl⟩
    exact ⟨a, b, c, d, he, hmap a b c d⟩
  · rintro ⟨a, b, c, d, he, rfl⟩
    exact ⟨single (a ::ₘ b ::ₘ 0) 1 - single (c ::ₘ d ::ₘ 0) 1,
      ⟨a, b, c, d, he, rfl⟩, hmap a b c d⟩

/-- Quadratic generation stated in Mathlib's `MvPolynomial`, with no loss of degree
or coefficient-field generality. -/
theorem polynomial_kernel_eq_quadrics (hmid : MidpointDecomposition A)
    (htriple : TripleReduction A) :
    RingHom.ker (toricMap A R) = polynomialQuadraticIdeal A R := by
  rw [← quadraticIdeal_map_polynomialEquiv]
  have hk := quadratic_generation_of_midpoint_and_triples A R hmid htriple
  ext p
  constructor
  · intro hp
    have hp' : (polynomialEquiv A R).symm p ∈ quadraticIdeal A R := by
      rw [← hk]
      exact hp
    have hm := Ideal.mem_map_of_mem (polynomialEquiv A R).toRingHom hp'
    simpa using hm
  · intro hp
    obtain ⟨q, hq, rfl⟩ := (Ideal.mem_map_iff_of_surjective
      (polynomialEquiv A R).toRingHom (polynomialEquiv A R).surjective).mp hp
    change multisetToricMap A R ((polynomialEquiv A R).symm ((polynomialEquiv A R) q)) = 0
    simp only [RingEquiv.symm_apply_apply]
    change q ∈ RingHom.ker (multisetToricMap A R)
    rw [hk]
    exact hq

/-- The canonical equivalence between exponent pairs `(a,k)` and `χ^a t^k`. -/
noncomputable def characterPolynomialEquiv :
    AddMonoidAlgebra R (M × ℕ) ≃+* Polynomial (AddMonoidAlgebra R M) :=
  (AddMonoidAlgebra.mapDomainRingEquiv R (AddEquiv.prodComm : M × ℕ ≃+ ℕ × M)).trans
    (AddMonoidAlgebra.curryRingEquiv.trans (Polynomial.toFinsuppIso _).symm)

@[simp] theorem characterPolynomialEquiv_single (m : M) (k : ℕ) (r : R) :
    characterPolynomialEquiv (M := M) R (single (m, k) r) =
      Polynomial.monomial k (single m r) := by
  apply Polynomial.toFinsupp_injective
  simp [characterPolynomialEquiv, Polynomial.toFinsuppIso]

/-- The toric homomorphism with exactly the paper's target `R[M][t]`. -/
noncomputable def paperToricMap :
    MvPolynomial A R →+* Polynomial (AddMonoidAlgebra R M) :=
  (characterPolynomialEquiv (M := M) R).toRingHom.comp (toricMap A R)

/-- Each generator is sent to the character times the homogenizing variable. -/
@[simp] theorem paperToricMap_X (a : A) :
    paperToricMap A R (MvPolynomial.X a) =
      Polynomial.C (single (a : M) 1) * Polynomial.X := by
  simp [paperToricMap, Polynomial.C_mul_X_eq_monomial]

/-- The coefficient ring is included as constant characters and constant polynomials. -/
@[simp] theorem paperToricMap_C (r : R) :
    paperToricMap A R (MvPolynomial.C r) = Polynomial.C (single (0 : M) r) := by
  simp [paperToricMap, Polynomial.monomial_zero_left]

/-- The exchange criterion yields the paper's ideal equality in the conventional target. -/
theorem paper_kernel_eq_quadrics (hmid : MidpointDecomposition A)
    (htriple : TripleReduction A) :
    RingHom.ker (paperToricMap A R) = polynomialQuadraticIdeal A R := by
  rw [paperToricMap, RingHom.ker_comp_of_injective _
    (characterPolynomialEquiv (M := M) R).injective]
  exact polynomial_kernel_eq_quadrics A R hmid htriple

end QuadraticKernel

end PaperVerification.ToricExchange
end
end Source_ToricIdeal
-- END ORIGINAL PaperVerification.ToricIdeal


-- BEGIN ORIGINAL PaperVerification.ToricCriterion
section Source_ToricCriterion

-- original header: module
-- original header: public import PaperVerification.ToricIdeal
-- original header: public import PaperVerification.ToricConvexity
-- original header: @[expose] public section
/-!
# The complete exchange criterion with explicit geometric inputs

This is the algebraic reduction underlying Proposition 2.1. The face map
and its parity/adjoint properties are explicit inputs: they are not constructed from
smoothness or an edge-length bound in this file.
-/

namespace PaperVerification.ToricExchange

variable {M V : Type*} [AddCommGroup M] [AddCommGroup V] [Module ℝ V]
variable (embedding : M →+ V) (P : Set V)
variable (R : Type*) [CommRing R]

/-- Convexity, full IDP, face parity, and proper-face adjoint decomposition yield
quadratic generation in the conventional ring `R[X_a] → R[M][t]`.
All natural degrees and every commutative coefficient ring are included. -/
theorem quadratic_generation_of_convex_face_data (hP : Convex ℝ P)
    (hidp : IntegerDecompositionProperty embedding P)
    {F : Type*} [SemilatticeSup F] [OrderTop F]
    (face : latticePoints embedding P → F)
    (parity : ∀ a b c : latticePoints embedding P, face c ≤ face a ⊔ face b →
      ∃ p q : latticePoints embedding P,
        (a : M) + b = (p : M) + q ∧ SameParity (p : M) c)
    (adjoint : ∀ a b : latticePoints embedding P, face a ⊔ face b ≠ ⊤ →
      ∃ u v : latticePoints embedding P, (a : M) + b = (u : M) + v ∧
        face u = face a ⊔ face b ∧ face v ≤ face a ⊔ face b) :
    RingHom.ker (paperToricMap (latticePoints embedding P) R) =
      polynomialQuadraticIdeal (latticePoints embedding P) R :=
  paper_kernel_eq_quadrics (latticePoints embedding P) R
    (midpointDecomposition_of_convex_idp embedding P hP hidp)
    (tripleReduction_of_convex_face_data embedding P hP face parity adjoint)

end PaperVerification.ToricExchange
end Source_ToricCriterion
-- END ORIGINAL PaperVerification.ToricCriterion


-- BEGIN ORIGINAL PaperVerification.FiniteExponentialBalance
section Source_FiniteExponentialBalance

-- original header: module
-- original header: public import Mathlib.Analysis.InnerProductSpace.Calculus
-- original header: public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
-- original header: public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
-- original header: public import Mathlib.Analysis.Calculus.LocalExtr.Basic
-- original header: public import Mathlib.Analysis.Normed.Group.Bounded
-- original header: public import Mathlib.Topology.Order.Compact
-- original header: public import Mathlib.Data.Fintype.Lattice
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.Positivity
-- original header: public import Mathlib.Tactic.FieldSimp
-- original header: public import Mathlib.Tactic.Ring
-- original header: @[expose] public section
/-!
# Finite exponential balancing

An analytic ingredient of the determinant-minimization argument in the toric
lattice-covering lemma. A finite spanning configuration with a strictly positive
zero relation admits an exponential reweighting with zero barycenter.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped BigOperators InnerProductSpace
open Filter Topology

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Sum of positive parts of the configuration's directional inner products. -/
def positivePartSum (v : ι → E) (x : E) : ℝ := ∑ i, max ⟪v i, x⟫_ℝ 0

lemma positivePartSum_nonneg (v : ι → E) (x : E) : 0 ≤ positivePartSum v x :=
  Finset.sum_nonneg (fun i _ => le_max_right _ _)

lemma positivePartSum_continuous (v : ι → E) : Continuous (positivePartSum v) := by
  unfold positivePartSum
  exact continuous_finset_sum _ (fun i _ =>
    (continuous_const.inner continuous_id).max continuous_const)

lemma positivePartSum_smul (v : ι → E) (x : E) {a : ℝ} (ha : 0 ≤ a) :
    positivePartSum v (a • x) = a * positivePartSum v x := by
  simp only [positivePartSum, real_inner_smul_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [mul_zero] using (mul_max_of_nonneg ⟪v i, x⟫_ℝ 0 ha).symm

/-- A positive zero relation rules out a nonzero direction having all inner products nonpositive. -/
lemma positivePartSum_pos (v : ι → E)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hzero : ∑ i, p i • v i = 0)
    {x : E} (hx : x ≠ 0) : 0 < positivePartSum v x := by
  have hnonneg := positivePartSum_nonneg v x
  by_contra hnot
  have hsum : positivePartSum v x = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
  have hmaxzero : (fun i => max ⟪v i, x⟫_ℝ 0) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg (fun i => le_max_right ⟪v i, x⟫_ℝ 0)).mp hsum
  have hmax : ∀ i, max ⟪v i, x⟫_ℝ 0 = 0 := fun i => congrFun hmaxzero i
  have hnonpos : ∀ i, ⟪v i, x⟫_ℝ ≤ 0 := fun i =>
    (le_max_left _ _).trans (hmax i).le
  have hweighted : ∑ i, p i * ⟪v i, x⟫_ℝ = 0 := by
    have h := congrArg (fun y : E => ⟪y, x⟫_ℝ) hzero
    simpa only [sum_inner, real_inner_smul_left, inner_zero_left] using h
  have htermzero : (fun i => p i * ⟪v i, x⟫_ℝ) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonpos
      (fun i => mul_nonpos_of_nonneg_of_nonpos (hp i).le (hnonpos i))).mp hweighted
  have hterm : ∀ i, p i * ⟪v i, x⟫_ℝ = 0 := fun i => congrFun htermzero i
  have hinner : ∀ i, ⟪v i, x⟫_ℝ = 0 := fun i =>
    (mul_eq_zero.mp (hterm i)).resolve_left (hp i).ne'
  have hspaninner : ∀ y ∈ Submodule.span ℝ (Set.range v), ⟪y, x⟫_ℝ = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact hinner i
    | zero => simp
    | add y z hy hz hy' hz' => simp [inner_add_left, hy', hz']
    | smul a y hy hy' => simp [real_inner_smul_left, hy']
  have hxspan : x ∈ Submodule.span ℝ (Set.range v) := by
    rw [hspan]
    exact Submodule.mem_top
  have hself := hspaninner x hxspan
  exact hx ((inner_self_eq_zero (𝕜 := ℝ)).mp hself)

/-- Uniform linear growth of the positive-part support function. -/
lemma positivePartSum_lower_bound [FiniteDimensional ℝ E] [Nontrivial E]
    (v : ι → E) (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hzero : ∑ i, p i • v i = 0) :
    ∃ ε > 0, ∀ x : E, ε * ‖x‖ ≤ positivePartSum v x := by
  have hsne : (Metric.sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num)
  obtain ⟨u, hu, hmin⟩ :=
    (isCompact_sphere (0 : E) 1).exists_isMinOn hsne
      (positivePartSum_continuous v).continuousOn
  have hunorm : ‖u‖ = 1 := by simpa using hu
  have hu0 : u ≠ 0 := by intro h; simp [h] at hunorm
  refine ⟨positivePartSum v u, positivePartSum_pos v hspan p hp hzero hu0, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx, positivePartSum]
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxunit : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E) 1 := by
    simp [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnorm.le), hnorm.ne']
  have h : positivePartSum v u ≤ positivePartSum v (‖x‖⁻¹ • x) := hmin hxunit
  rw [positivePartSum_smul v x (inv_nonneg.mpr hnorm.le)] at h
  have hmul := mul_le_mul_of_nonneg_right h hnorm.le
  simpa [mul_assoc, mul_comm, mul_left_comm, hnorm.ne'] using hmul

/-- A finite positive exponential sum. -/
def exponentialSum (v : ι → E) (d : ι → ℝ) (x : E) : ℝ :=
  ∑ i, d i * Real.exp ⟪v i, x⟫_ℝ

lemma exponentialSum_continuous (v : ι → E) (d : ι → ℝ) :
    Continuous (exponentialSum v d) := by
  unfold exponentialSum
  exact continuous_finset_sum _ (fun i _ =>
    continuous_const.mul (continuous_const.inner continuous_id).rexp)

/-- The balancing theorem for a configuration spanning its ambient real inner-product space. -/
theorem finite_exponential_balance [FiniteDimensional ℝ E] [Nonempty ι]
    (v : ι → E) (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hzero : ∑ i, p i • v i = 0)
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ x : E, ∑ i, (d i * Real.exp ⟪v i, x⟫_ℝ) • v i = 0 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · letI := hE
    exact ⟨0, Subsingleton.elim _ _⟩
  letI := hE
  obtain ⟨ε, hε, hbound⟩ := positivePartSum_lower_bound v hspan p hp hzero
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min d
  have hcoeff : 0 < d i₀ * ε := mul_pos (hd i₀) hε
  have hlower : ∀ x, d i₀ * ε * ‖x‖ ≤ exponentialSum v d x := by
    intro x
    calc
      d i₀ * ε * ‖x‖ ≤ d i₀ * positivePartSum v x := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hbound x) (hd i₀).le
      _ = ∑ i, d i₀ * max ⟪v i, x⟫_ℝ 0 := by rw [positivePartSum, Finset.mul_sum]
      _ ≤ exponentialSum v d x := by
        apply Finset.sum_le_sum
        intro i _
        have he : max ⟪v i, x⟫_ℝ 0 ≤ Real.exp ⟪v i, x⟫_ℝ := by
          refine max_le ?_ (Real.exp_pos _).le
          linarith [Real.add_one_le_exp ⟪v i, x⟫_ℝ]
        exact mul_le_mul (hi₀ i) he (le_max_right _ _) (hd i).le
  have hlim : Tendsto (exponentialSum v d) (cocompact E) atTop :=
    tendsto_atTop_mono hlower
      (Tendsto.const_mul_atTop hcoeff tendsto_norm_cocompact_atTop)
  obtain ⟨x, hxmin⟩ := (exponentialSum_continuous v d).exists_forall_le hlim
  let g : E := ∑ i, (d i * Real.exp ⟪v i, x⟫_ℝ) • v i
  have hlocal : IsLocalMin (fun t : ℝ => exponentialSum v d (x + t • g)) 0 := by
    exact Filter.Eventually.of_forall (fun t => by simpa using hxmin (x + t • g))
  have hpath : HasDerivAt (fun t : ℝ => x + t • g) g 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const g).const_add x
  have hderiv : HasDerivAt (fun t : ℝ => exponentialSum v d (x + t • g))
      ⟪g, g⟫_ℝ 0 := by
    have hi (i : ι) : HasDerivAt
        (fun t : ℝ => d i * Real.exp ⟪v i, x + t • g⟫_ℝ)
        ((d i * Real.exp ⟪v i, x⟫_ℝ) * ⟪v i, g⟫_ℝ) 0 := by
      have hi' : HasDerivAt (fun t : ℝ => ⟪v i, x + t • g⟫_ℝ) ⟪v i, g⟫_ℝ 0 := by
        simpa using (hasDerivAt_const (0 : ℝ) (v i)).inner ℝ hpath
      simpa [mul_assoc] using hi'.exp.const_mul (d i)
    have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
    simpa only [exponentialSum, g, sum_inner, real_inner_smul_left] using hs
  refine ⟨x, ?_⟩
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp (hlocal.hasDerivAt_eq_zero hderiv)

/-- The same balancing theorem in the span of the configuration. This removes
any unnecessary full-dimensionality assumption on the ambient space. -/
theorem finite_exponential_balance_in_span [FiniteDimensional ℝ E] [Nonempty ι]
    (v : ι → E)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hzero : ∑ i, p i • v i = 0)
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ x : E, ∑ i, (d i * Real.exp ⟪v i, x⟫_ℝ) • v i = 0 := by
  let W : Submodule ℝ E := Submodule.span ℝ (Set.range v)
  have hv : ∀ i, v i ∈ W := fun i => Submodule.subset_span ⟨i, rfl⟩
  let vW : ι → W := fun i => ⟨v i, hv i⟩
  have hspan : Submodule.span ℝ (Set.range vW) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff W hv).mpr rfl
  have hzeroW : ∑ i, p i • vW i = 0 := by
    apply Subtype.ext
    simpa [vW] using hzero
  obtain ⟨x, hx⟩ := finite_exponential_balance vW hspan p hp hzeroW d hd
  refine ⟨x, ?_⟩
  have h := congrArg (fun z : W => (z : E)) hx
  simpa [vW] using h

/-- A strictly positive convex combination is the barycenter of a suitable
exponential reweighting with any prescribed positive base coefficients.

This is the finite-dimensional analytic step behind the log-determinant
argument: the points will be the incidence vectors of all vector-space bases. -/
theorem finite_exponential_barycenter [FiniteDimensional ℝ E] [Nonempty ι]
    (v : ι → E) (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1)
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ x : E, ∑ i, (d i * Real.exp ⟪v i, x⟫_ℝ) •
      (v i - ∑ j, p j • v j) = 0 := by
  let c : E := ∑ j, p j • v j
  have hzero : ∑ i, p i • (v i - c) = 0 := by
    simp [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hpsum, c]
  obtain ⟨x, hx⟩ := finite_exponential_balance_in_span
    (fun i => v i - c) p hp hzero d hd
  refine ⟨x, ?_⟩
  have h := congrArg (fun z : E => Real.exp ⟪c, x⟫_ℝ • z) hx
  rw [smul_zero, Finset.smul_sum] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, inner_sub_left]
  congr 1
  calc
    d i * Real.exp ⟪v i, x⟫_ℝ =
        d i * (Real.exp ⟪c, x⟫_ℝ *
          Real.exp (⟪v i, x⟫_ℝ - ⟪c, x⟫_ℝ)) := by
            rw [← Real.exp_add]
            congr 2
            ring
    _ = _ := by ring

end PaperVerification.Toric
end
end Source_FiniteExponentialBalance
-- END ORIGINAL PaperVerification.FiniteExponentialBalance


-- BEGIN ORIGINAL PaperVerification.CauchyBinet
section Source_CauchyBinet

-- original header: module

/-
  PaperVerification/CauchyBinet.lean

  Cauchy–Binet formula over a commutative ring (Sun arXiv:2609.04176v1 §4).
  Mathlib v4.32.2 has no Cauchy–Binet; proved from `det_apply'` / `det_mul`-style
  Leibniz expansion, vanishing on non-injective column maps, and partitioning
  injectives by image via `Finset.orderEmbOfFin`.
-/
-- original header: public import Mathlib.Data.Fintype.BigOperators
-- original header: public import Mathlib.Data.Finset.Powerset
-- original header: public import Mathlib.Data.Finset.Sort
-- original header: public import Mathlib.Data.Matrix.Basic
-- original header: public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
-- original header: public import Mathlib.Logic.Equiv.Set
-- original header: @[expose] public section
set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

noncomputable section

namespace PaperVerification.CauchyBinet

open Matrix Finset Equiv
open scoped Matrix BigOperators

variable {R : Type*} [CommRing R]

local notation "ε " σ:arg => ((Equiv.Perm.sign σ : ℤ) : R)

/-! ## Column / row minors via `orderEmbOfFin` -/

/-- Square column minor of an `m × n` matrix on an `m`-element column set. -/
def colsSubmatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (s : Finset (Fin n)) (hs : s.card = m) : Matrix (Fin m) (Fin m) R :=
  A.submatrix id (s.orderEmbOfFin hs)

/-- Square row minor of an `n × m` matrix on an `m`-element row set. -/
def rowsSubmatrix {m n : ℕ} (B : Matrix (Fin n) (Fin m) R)
    (s : Finset (Fin n)) (hs : s.card = m) : Matrix (Fin m) (Fin m) R :=
  B.submatrix (s.orderEmbOfFin hs) id

@[simp] theorem colsSubmatrix_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (s : Finset (Fin n)) (hs : s.card = m) (i j : Fin m) :
    colsSubmatrix A s hs i j = A i (s.orderEmbOfFin hs j) :=
  rfl

@[simp] theorem rowsSubmatrix_apply {m n : ℕ} (B : Matrix (Fin n) (Fin m) R)
    (s : Finset (Fin n)) (hs : s.card = m) (i j : Fin m) :
    rowsSubmatrix B s hs i j = B (s.orderEmbOfFin hs i) j :=
  rfl

/-! ## CB0: `m = 0` and `m = 1` -/

theorem det_mul_fin_zero {n : ℕ}
    (A : Matrix (Fin 0) (Fin n) R) (B : Matrix (Fin n) (Fin 0) R) :
    (A * B).det = 1 :=
  det_fin_zero

theorem det_mul_eq_sum_minors_fin_zero {n : ℕ}
    (A : Matrix (Fin 0) (Fin n) R) (B : Matrix (Fin n) (Fin 0) R) :
    (A * B).det =
      ∑ s ∈ (univ : Finset (Fin n)).powersetCard 0,
        if hs : s.card = 0 then
          (colsSubmatrix A s hs).det * (rowsSubmatrix B s hs).det
        else 0 := by
  simp [det_fin_zero, colsSubmatrix, rowsSubmatrix, powersetCard_zero]

theorem det_mul_fin_one {n : ℕ}
    (A : Matrix (Fin 1) (Fin n) R) (B : Matrix (Fin n) (Fin 1) R) :
    (A * B).det = ∑ k : Fin n, A 0 k * B k 0 := by
  rw [det_fin_one, Matrix.mul_apply]

theorem det_mul_eq_sum_minors_fin_one {n : ℕ}
    (A : Matrix (Fin 1) (Fin n) R) (B : Matrix (Fin n) (Fin 1) R) :
    (A * B).det =
      ∑ s ∈ (univ : Finset (Fin n)).powersetCard 1,
        if hs : s.card = 1 then
          (colsSubmatrix A s hs).det * (rowsSubmatrix B s hs).det
        else 0 := by
  rw [det_mul_fin_one]
  have hmap :
      (univ : Finset (Fin n)).powersetCard 1 =
        (univ : Finset (Fin n)).map ⟨fun k => {k}, singleton_injective⟩ :=
    powersetCard_one _
  rw [hmap, sum_map]
  refine Fintype.sum_congr _ _ fun k => ?_
  have hs : ({k} : Finset (Fin n)).card = 1 := card_singleton k
  simp only [Function.Embedding.coeFn_mk, dif_pos hs, det_fin_one,
    colsSubmatrix_apply, rowsSubmatrix_apply, orderEmbOfFin_singleton]

/-! ## Helpers: expansion, vanishing, permutations of a column image -/

/-- Leibniz expansion of `det(A * B)` as a sum over column-selection maps. -/
theorem det_mul_eq_sum_colMap {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det =
      ∑ p : Fin m → Fin n, (A.submatrix id p).det * ∏ i : Fin m, B (p i) i := by
  calc
    (A * B).det
        = ∑ p : Fin m → Fin n,
            ∑ σ : Perm (Fin m), ε σ * ∏ i, A (σ i) (p i) * B (p i) i := by
          simp only [det_apply', Matrix.mul_apply, prod_univ_sum, mul_sum,
            Fintype.piFinset_univ]
          rw [sum_comm]
    _ = ∑ p : Fin m → Fin n,
            ∑ σ : Perm (Fin m),
              (ε σ * ∏ i, A (σ i) (p i)) * ∏ i, B (p i) i := by
          refine sum_congr rfl fun p _ => sum_congr rfl fun σ _ => ?_
          rw [prod_mul_distrib, mul_assoc]
    _ = ∑ p : Fin m → Fin n,
            (∑ σ : Perm (Fin m), ε σ * ∏ i, A (σ i) (p i)) *
              ∏ i, B (p i) i := by
          refine sum_congr rfl fun p _ => ?_
          exact (Finset.sum_mul _ _ _).symm
    _ = ∑ p : Fin m → Fin n, (A.submatrix id p).det * ∏ i, B (p i) i := by
          refine sum_congr rfl fun p _ => ?_
          congr 1
          simpa [submatrix_apply] using (det_apply' (A.submatrix id p)).symm

/-- Non-injective column selection forces a repeated column, hence determinant zero. -/
theorem det_submatrix_eq_zero_of_not_injective {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) {p : Fin m → Fin n}
    (hp : ¬ Function.Injective p) :
    (A.submatrix id p).det = 0 := by
  simp only [Function.Injective] at hp
  push Not at hp
  obtain ⟨i, j, hpij, hij⟩ := hp
  exact det_zero_of_column_eq hij fun k => by simp [hpij]

/-- Only injective column maps contribute to the expansion. -/
theorem det_mul_eq_sum_injective_colMap {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det =
      ∑ p : Fin m → Fin n,
        if Function.Injective p then
          (A.submatrix id p).det * ∏ i : Fin m, B (p i) i
        else 0 := by
  rw [det_mul_eq_sum_colMap]
  refine sum_congr rfl fun p _ => ?_
  split_ifs with hp
  · rfl
  · rw [det_submatrix_eq_zero_of_not_injective A hp, zero_mul]

/-- The unique permutation realizing an injective map as `orderEmbOfFin ∘ τ`. -/
def permOfImage {m n : ℕ} (p : Fin m → Fin n) (hp : Function.Injective p)
    (s : Finset (Fin n)) (hs : s.card = m)
    (him : image p univ = s) : Perm (Fin m) :=
  let emb : Fin m → Fin n := s.orderEmbOfFin hs
  have hrangep : Set.range p = (s : Set (Fin n)) := by
    rw [← him, coe_image, coe_univ, Set.image_univ]
  have hrangee : Set.range emb = (s : Set (Fin n)) := range_orderEmbOfFin s hs
  (Equiv.ofInjective p hp).trans <|
    (Set.equivOfEq (hrangep.trans hrangee.symm)).trans
      (Equiv.ofInjective emb (s.orderEmbOfFin hs).injective).symm

theorem apply_orderEmb_permOfImage {m n : ℕ} (p : Fin m → Fin n)
    (hp : Function.Injective p) (s : Finset (Fin n)) (hs : s.card = m)
    (him : image p univ = s) (i : Fin m) :
    s.orderEmbOfFin hs (permOfImage p hp s hs him i) = p i := by
  dsimp [permOfImage]
  exact Equiv.apply_ofInjective_symm (s.orderEmbOfFin hs).injective _

theorem permOfImage_comp {m n : ℕ} (p : Fin m → Fin n)
    (hp : Function.Injective p) (s : Finset (Fin n)) (hs : s.card = m)
    (him : image p univ = s) :
    (s.orderEmbOfFin hs : Fin m → Fin n) ∘ permOfImage p hp s hs him = p :=
  funext fun i => apply_orderEmb_permOfImage p hp s hs him i

/-- Image of an injective `Fin m → Fin n` is an `m`-element subset of `univ`. -/
theorem image_mem_powersetCard {m n : ℕ} {p : Fin m → Fin n}
    (hp : Function.Injective p) :
    image p univ ∈ (univ : Finset (Fin n)).powersetCard m := by
  refine mem_powersetCard.mpr ⟨subset_univ _, ?_⟩
  rw [card_image_of_injective _ hp, card_univ, Fintype.card_fin]

/-- `orderEmbOfFin` of the full universe is the identity map. -/
theorem orderEmbOfFin_univ_eq_id (m : ℕ) :
    ((univ : Finset (Fin m)).orderEmbOfFin (by simp [card_univ, Fintype.card_fin]) :
      Fin m → Fin m) =
      id := by
  have h :
      (id : Fin m → Fin m) =
        (univ : Finset (Fin m)).orderEmbOfFin
          (by simp [card_univ, Fintype.card_fin]) :=
    orderEmbOfFin_unique (s := (univ : Finset (Fin m)))
      (by simp [card_univ, Fintype.card_fin]) (fun _ => mem_univ _)
      (strictMono_id : StrictMono (id : Fin m → Fin m))
  exact h.symm

/-! ## CB1: square case `m = n` -/

theorem powersetCard_univ_self (m : ℕ) :
    (univ : Finset (Fin m)).powersetCard m = {univ} := by
  ext s
  simp only [mem_powersetCard, mem_singleton, subset_univ, true_and]
  exact ⟨fun hs => eq_univ_of_card _ (hs.trans (by simp [card_univ, Fintype.card_fin])),
    fun hs => hs ▸ by simp [card_univ, Fintype.card_fin]⟩

theorem colsSubmatrix_univ {m : ℕ} (A : Matrix (Fin m) (Fin m) R) :
    colsSubmatrix A univ (by simp [card_univ, Fintype.card_fin]) = A := by
  ext i j
  simp [colsSubmatrix, orderEmbOfFin_univ_eq_id]

theorem rowsSubmatrix_univ {m : ℕ} (B : Matrix (Fin m) (Fin m) R) :
    rowsSubmatrix B univ (by simp [card_univ, Fintype.card_fin]) = B := by
  ext i j
  simp [rowsSubmatrix, orderEmbOfFin_univ_eq_id]

/-- Square Cauchy–Binet collapses to `Matrix.det_mul`. -/
theorem det_mul_eq_sum_minors_square {m : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin m) (Fin m) R) :
    (A * B).det =
      ∑ s ∈ (univ : Finset (Fin m)).powersetCard m,
        if hs : s.card = m then
          (colsSubmatrix A s hs).det * (rowsSubmatrix B s hs).det
        else 0 := by
  rw [powersetCard_univ_self, sum_singleton]
  have hs : (univ : Finset (Fin m)).card = m := by simp [card_univ, Fintype.card_fin]
  simp only [dif_pos hs, colsSubmatrix_univ, rowsSubmatrix_univ, Matrix.det_mul]

/-! ## Fiber of a fixed image: sum over permutations -/

theorem det_submatrix_comp_perm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (emb : Fin m → Fin n) (τ : Perm (Fin m)) :
    (A.submatrix id (emb ∘ τ)).det = ε τ * (A.submatrix id emb).det := by
  have h : A.submatrix id (emb ∘ τ) = (A.submatrix id emb).submatrix id τ := by
    ext; simp [Function.comp_apply]
  rw [h, det_permute']

theorem sum_fiber_eq_det_mul_det {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R)
    (s : Finset (Fin n)) (hs : s.card = m) :
    (∑ τ : Perm (Fin m),
        (A.submatrix id ((s.orderEmbOfFin hs : Fin m → Fin n) ∘ τ)).det *
          (∏ i : Fin m, B (((s.orderEmbOfFin hs : Fin m → Fin n) ∘ τ) i) i)) =
      (colsSubmatrix A s hs).det * (rowsSubmatrix B s hs).det := by
  let emb : Fin m → Fin n := fun i => s.orderEmbOfFin hs i
  change ∑ τ : Perm (Fin m),
      (A.submatrix id (emb ∘ τ)).det * (∏ i : Fin m, B (emb (τ i)) i) =
    (A.submatrix id emb).det * (B.submatrix emb id).det
  have hsum :
      ∑ τ : Perm (Fin m),
          (A.submatrix id (emb ∘ τ)).det * (∏ i : Fin m, B (emb (τ i)) i) =
        ∑ τ : Perm (Fin m),
          (A.submatrix id emb).det * (ε τ * (∏ i : Fin m, B (emb (τ i)) i)) := by
    refine sum_congr rfl fun τ _ => ?_
    rw [det_submatrix_comp_perm A emb τ]
    ring
  rw [hsum, ← Finset.mul_sum]
  congr 1
  exact (det_apply' (B.submatrix emb id)).symm

/-- Enumerate injective maps with a fixed image by permutations of `orderEmbOfFin`. -/
theorem sum_injective_with_image {m n : ℕ}
    (f : (Fin m → Fin n) → R) (s : Finset (Fin n)) (hs : s.card = m) :
    (∑ p : Fin m → Fin n,
        if Function.Injective p ∧ image p univ = s then f p else 0) =
      ∑ τ : Perm (Fin m), f ((s.orderEmbOfFin hs : Fin m → Fin n) ∘ τ) := by
  classical
  let emb : Fin m → Fin n := (s.orderEmbOfFin hs : Fin m → Fin n)
  have hembinj : Function.Injective emb := (s.orderEmbOfFin hs).injective
  have himemb : image emb univ = s := image_orderEmbOfFin_univ s hs
  have hfilter :
      ∑ τ : Perm (Fin m), f (emb ∘ τ) =
        (filter (fun p : Fin m → Fin n => Function.Injective p ∧ image p univ = s)
          univ).sum f := by
    refine sum_bij (fun τ _ => emb ∘ (τ : Fin m → Fin m)) ?mem ?inj ?surj ?eq
    · intro τ _
      refine mem_filter.mpr ⟨mem_univ _, hembinj.comp τ.injective, ?_⟩
      have himτ : image (τ : Fin m → Fin m) univ = univ := by
        rw [← coe_inj, coe_image, coe_univ, Set.image_univ, τ.surjective.range_eq]
      rw [image_comp, himτ, himemb]
    · intro τ₁ _ τ₂ _ h
      exact Equiv.Perm.ext fun i => hembinj (congrFun h i)
    · intro p hp
      obtain ⟨_, hpinj, him⟩ := mem_filter.mp hp
      refine ⟨permOfImage p hpinj s hs him, mem_univ _, ?_⟩
      -- `emb ∘ permOfImage = p`
      simpa [emb] using permOfImage_comp p hpinj s hs him
    · intro τ _; rfl
  have hsplit :
      (∑ p : Fin m → Fin n,
          if Function.Injective p ∧ image p univ = s then f p else 0) =
        (filter (fun p : Fin m → Fin n => Function.Injective p ∧ image p univ = s)
          univ).sum f :=
    (sum_filter (fun p : Fin m → Fin n => Function.Injective p ∧ image p univ = s)
      (f := f)).symm
  exact hsplit.trans hfilter.symm

/-! ## CB2: general Cauchy–Binet -/

/-- Group injective column maps by their image in `powersetCard m`. -/
theorem sum_injective_eq_sum_powerset {m n : ℕ} (f : (Fin m → Fin n) → R) :
    (∑ p : Fin m → Fin n, if Function.Injective p then f p else 0) =
      ∑ s ∈ (univ : Finset (Fin n)).powersetCard m,
        ∑ p : Fin m → Fin n,
          if Function.Injective p ∧ image p univ = s then f p else 0 := by
  classical
  have hswap :
      (∑ s ∈ (univ : Finset (Fin n)).powersetCard m,
          ∑ p : Fin m → Fin n,
            if Function.Injective p ∧ image p univ = s then f p else 0) =
        ∑ p : Fin m → Fin n,
          ∑ s ∈ (univ : Finset (Fin n)).powersetCard m,
            if Function.Injective p ∧ image p univ = s then f p else 0 :=
    sum_comm
  rw [hswap]
  refine sum_congr rfl fun p _ => ?_
  by_cases hp : Function.Injective p
  · have him : image p univ ∈ (univ : Finset (Fin n)).powersetCard m :=
      image_mem_powersetCard hp
    rw [sum_eq_single (image p univ)]
    · simp [hp]
    · intro s hs hne
      simp only [hp, true_and]
      split_ifs with h
      · exact (hne h.symm).elim
      · rfl
    · intro hnot
      exact (hnot him).elim
  · simp only [hp, false_and, ite_false, sum_const_zero]

/-- **Cauchy–Binet.** For `A : m × n` and `B : n × m` over a commutative ring,
`det(A * B)` equals the sum of products of complementary minors over all
`m`-element subsets of `Fin n`. -/
theorem det_mul_eq_sum_minors {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det =
      ∑ s ∈ (univ : Finset (Fin n)).powersetCard m,
        if hs : s.card = m then
          (colsSubmatrix A s hs).det * (rowsSubmatrix B s hs).det
        else 0 := by
  classical
  rw [det_mul_eq_sum_injective_colMap]
  have hgroup :=
    sum_injective_eq_sum_powerset
      (fun p : Fin m → Fin n => (A.submatrix id p).det * ∏ i : Fin m, B (p i) i)
  rw [hgroup]
  refine sum_congr rfl fun s hs => ?_
  have hcard : s.card = m := (mem_powersetCard.mp hs).2
  simp only [dif_pos hcard]
  have hfiber :=
    sum_injective_with_image
      (fun p : Fin m → Fin n => (A.submatrix id p).det * ∏ i : Fin m, B (p i) i)
      s hcard
  rw [hfiber, sum_fiber_eq_det_mul_det A B s hcard]

/-! ## CB3: corollaries -/

/-- If `m > n`, there are no `m`-column subsets, so `det(A * B) = 0`. -/
theorem det_mul_eq_zero_of_card_lt {m n : ℕ} (hmn : n < m)
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det = 0 := by
  rw [det_mul_eq_sum_minors]
  have hempty : (univ : Finset (Fin n)).powersetCard m = ∅ := by
    rw [powersetCard_eq_empty]
    simpa [card_univ, Fintype.card_fin] using hmn
  simp [hempty]

/-- Square re-export of `Matrix.det_mul` through the Cauchy–Binet packaging. -/
theorem det_mul_square {m : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin m) (Fin m) R) :
    (A * B).det = A.det * B.det :=
  Matrix.det_mul A B

end PaperVerification.CauchyBinet
end
end Source_CauchyBinet
-- END ORIGINAL PaperVerification.CauchyBinet


-- BEGIN ORIGINAL PaperVerification.ToricGramDeterminant
section Source_ToricGramDeterminant

-- original header: module
-- original header: public import PaperVerification.CauchyBinet
-- original header: public import Mathlib.LinearAlgebra.Matrix.SchurComplement
-- original header: public import Mathlib.LinearAlgebra.Matrix.PosDef
-- original header: public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
-- original header: public import Mathlib.Tactic.Ring
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.Positivity
-- original header: @[expose] public section
/-!
# Gram determinants and basis marginals

These identities provide the algebraic part of the lattice-covering lemma.
The leverage identity is obtained by doubling one column weight and applying
the rank-one determinant formula; no differentiation of a matrix inverse or
an unproved log-determinant identity is required.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped Matrix BigOperators
open PaperVerification.CauchyBinet

variable {d n : ℕ}

/-- The positive weighted Gram matrix of a column configuration. -/
def weightedGram (V : Matrix (Fin d) (Fin n) ℝ) (a : Fin n → ℝ) :
    Matrix (Fin d) (Fin d) ℝ := V * Matrix.diagonal a * V.transpose

/-- The squared maximal minor, extended by zero to subsets of other sizes. -/
def squaredMinor (V : Matrix (Fin d) (Fin n) ℝ) (s : Finset (Fin n)) : ℝ :=
  if hs : s.card = d then (colsSubmatrix V s hs).det ^ 2 else 0

lemma squaredMinor_nonneg (V : Matrix (Fin d) (Fin n) ℝ) (s : Finset (Fin n)) :
    0 ≤ squaredMinor V s := by
  unfold squaredMinor
  split_ifs <;> positivity

lemma prod_orderEmbOfFin (s : Finset (Fin n)) (hs : s.card = d) (a : Fin n → ℝ) :
    (∏ i : Fin d, a (s.orderEmbOfFin hs i)) = ∏ j ∈ s, a j := by
  calc
    (∏ i : Fin d, a (s.orderEmbOfFin hs i)) =
        ∏ j ∈ Finset.univ.map (s.orderEmbOfFin hs).toEmbedding, a j := by
          rw [Finset.prod_map]
          rfl
    _ = _ := by rw [Finset.map_orderEmbOfFin_univ]

lemma weightedGram_apply (V : Matrix (Fin d) (Fin n) ℝ) (a : Fin n → ℝ)
    (i j : Fin d) : weightedGram V a i j = ∑ k, a k * V i k * V j k := by
  rw [weightedGram, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The weighted Cauchy–Binet expansion, with all zero minors retained. -/
theorem weightedGram_det (V : Matrix (Fin d) (Fin n) ℝ) (a : Fin n → ℝ) :
    (weightedGram V a).det =
      ∑ s : Finset (Fin n), squaredMinor V s * ∏ j ∈ s, a j := by
  classical
  rw [weightedGram, det_mul_eq_sum_minors]
  have hminor (s : Finset (Fin n)) (hs : s.card = d) :
      (colsSubmatrix (V * Matrix.diagonal a) s hs).det *
        (rowsSubmatrix V.transpose s hs).det =
          squaredMinor V s * ∏ j ∈ s, a j := by
    have hc : colsSubmatrix (V * Matrix.diagonal a) s hs =
        colsSubmatrix V s hs *
          Matrix.diagonal (fun i => a (s.orderEmbOfFin hs i)) := by
      ext i j
      simp [colsSubmatrix, Matrix.mul_diagonal]
    have hr : rowsSubmatrix V.transpose s hs = (colsSubmatrix V s hs).transpose := by
      ext i j
      rfl
    rw [hc, hr, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose,
      prod_orderEmbOfFin, squaredMinor, dif_pos hs]
    ring
  calc
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
        if hs : s.card = d then
          (colsSubmatrix (V * Matrix.diagonal a) s hs).det *
            (rowsSubmatrix V.transpose s hs).det else 0) =
        ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
          squaredMinor V s * ∏ j ∈ s, a j := by
      apply Finset.sum_congr rfl
      intro s hs
      have hcard := (Finset.mem_powersetCard.mp hs).2
      rw [dif_pos hcard]
      exact hminor s hcard
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro s _ hs
      have hcard : s.card ≠ d := by
        intro heq
        exact hs (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, heq⟩)
      simp [squaredMinor, hcard]

lemma prod_update_double (a : Fin n → ℝ) (j : Fin n) (s : Finset (Fin n)) :
    (∏ k ∈ s, Function.update a j (2 * a j) k) =
      (∏ k ∈ s, a k) + if j ∈ s then ∏ k ∈ s, a k else 0 := by
  by_cases hj : j ∈ s
  · rw [Finset.prod_update_of_mem hj, if_pos hj,
      Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hj a]
    ring
  · rw [Finset.prod_update_of_notMem hj, if_neg hj, add_zero]

/-- Doubling a column weight adds exactly the basis mass of subsets containing it. -/
theorem weightedGram_det_update_double (V : Matrix (Fin d) (Fin n) ℝ)
    (a : Fin n → ℝ) (j : Fin n) :
    (weightedGram V (Function.update a j (2 * a j))).det =
      (weightedGram V a).det +
        ∑ s : Finset (Fin n),
          if j ∈ s then squaredMinor V s * ∏ k ∈ s, a k else 0 := by
  rw [weightedGram_det, weightedGram_det, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [prod_update_double]
  by_cases hj : j ∈ s <;> simp [hj, mul_add]

lemma weightedGram_update_double (V : Matrix (Fin d) (Fin n) ℝ)
    (a : Fin n → ℝ) (j : Fin n) :
    weightedGram V (Function.update a j (2 * a j)) = weightedGram V a +
      Matrix.replicateCol Unit (a j • fun i => V i j) *
        Matrix.replicateRow Unit (fun i => V i j) := by
  ext i k
  have hterm (r : Fin n) :
      Function.update a j (2 * a j) r * V i r * V k r =
        a r * V i r * V k r + if r = j then a j * V i j * V k j else 0 := by
    by_cases hr : r = j
    · subst r
      simp only [Function.update_self, if_true]
      ring
    · simp [Function.update_of_ne hr, hr]
  simp only [weightedGram_apply, hterm, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.add_apply,
    Matrix.mul_apply, Fintype.sum_unique, Matrix.replicateCol_apply,
    Matrix.replicateRow_apply, Pi.smul_apply, smul_eq_mul]

/-- The basis-marginal identity used to match zonotope widths to an inverse
weighted Gram matrix. The only nondegeneracy hypothesis is invertibility. -/
theorem weightedGram_basis_marginal (V : Matrix (Fin d) (Fin n) ℝ)
    (a : Fin n → ℝ) (hunit : IsUnit (weightedGram V a).det) (j : Fin n) :
    (weightedGram V a).det *
        (a j * ((fun i => V i j) ⬝ᵥ
          ((weightedGram V a)⁻¹ *ᵥ (fun i => V i j)))) =
      ∑ s : Finset (Fin n),
        if j ∈ s then squaredMinor V s * ∏ k ∈ s, a k else 0 := by
  have hdet := weightedGram_det_update_double V a j
  rw [weightedGram_update_double,
    Matrix.det_add_replicateCol_mul_replicateRow hunit] at hdet
  rw [Matrix.mul_assoc, ← Matrix.replicateCol_mulVec,
    Matrix.det_unique (n := Unit)] at hdet
  simp only [Matrix.add_apply, Matrix.one_apply_eq,
    Matrix.replicateRow_mul_replicateCol_apply,
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] at hdet
  nlinarith

end PaperVerification.Toric
end
end Source_ToricGramDeterminant
-- END ORIGINAL PaperVerification.ToricGramDeterminant


-- BEGIN ORIGINAL PaperVerification.ToricGramBalance
section Source_ToricGramBalance

-- original header: module
-- original header: public import PaperVerification.FiniteExponentialBalance
-- original header: public import PaperVerification.ToricGramDeterminant
-- original header: public import Mathlib.Analysis.InnerProductSpace.PiL2
-- original header: public import Mathlib.Analysis.Matrix.Hermitian
-- original header: public import Mathlib.Algebra.Order.Star.Real
-- original header: public import Mathlib.Tactic.Positivity
-- original header: @[expose] public section
/-!
# Realizing matroid-base weights by a weighted Gram matrix

The basis set below consists precisely of nonsingular maximal column minors.
Every strictly positive probability distribution on these bases determines
widths realized by the inverse Gram matrix leverage formula.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped Matrix BigOperators InnerProductSpace
open PaperVerification.CauchyBinet

variable {d n : ℕ}

/-- Unordered vector-space bases among the columns of a matrix. -/
def ColumnBasis (V : Matrix (Fin d) (Fin n) ℝ) :=
  {s : Finset (Fin n) // 0 < squaredMinor V s}

instance (V : Matrix (Fin d) (Fin n) ℝ) : Fintype (ColumnBasis V) := by
  classical
  unfold ColumnBasis
  infer_instance

lemma squaredMinor_pos_iff (V : Matrix (Fin d) (Fin n) ℝ) (s : Finset (Fin n)) :
    0 < squaredMinor V s ↔
      ∃ hs : s.card = d, (colsSubmatrix V s hs).det ≠ 0 := by
  by_cases hs : s.card = d
  · simp [squaredMinor, hs, sq_pos_iff]
  · simp [squaredMinor, hs]

/-- Incidence vector of a column basis in the real Euclidean coordinate space. -/
def basisIncidence (V : Matrix (Fin d) (Fin n) ℝ) (B : ColumnBasis V) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun j => if j ∈ B.val then 1 else 0)

@[simp] lemma basisIncidence_apply (V : Matrix (Fin d) (Fin n) ℝ)
    (B : ColumnBasis V) (j : Fin n) :
    basisIncidence V B j = if j ∈ B.val then 1 else 0 := rfl

/-- The width vector associated with a probability distribution on bases. -/
def basisBarycenter (V : Matrix (Fin d) (Fin n) ℝ) (p : ColumnBasis V → ℝ) :
    EuclideanSpace ℝ (Fin n) := ∑ B, p B • basisIncidence V B

lemma euclidean_sum_apply {ι : Type*} [Fintype ι]
    (f : ι → EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    (∑ i, f i) j = ∑ i, f i j := by
  change ((∑ i, f i).ofLp) j = _
  rw [WithLp.ofLp_sum, Finset.sum_apply]

lemma basisBarycenter_apply (V : Matrix (Fin d) (Fin n) ℝ)
    (p : ColumnBasis V → ℝ) (j : Fin n) :
    basisBarycenter V p j = ∑ B, if j ∈ B.val then p B else 0 := by
  rw [basisBarycenter, euclidean_sum_apply]
  apply Finset.sum_congr rfl
  intro B _
  simp [basisIncidence]

lemma basisIncidence_exp_inner (V : Matrix (Fin d) (Fin n) ℝ)
    (B : ColumnBasis V) (x : EuclideanSpace ℝ (Fin n)) :
    Real.exp ⟪basisIncidence V B, x⟫_ℝ = ∏ j ∈ B.val, Real.exp (x j) := by
  have hi : ⟪basisIncidence V B, x⟫_ℝ = ∑ j ∈ B.val, x j := by
    simp [basisIncidence, PiLp.inner_apply, Finset.sum_ite_mem, mul_comm]
  rw [hi, Real.exp_sum]

/-- Remove zero terms from a sum indexed by all column subsets. -/
lemma sum_columnBasis_eq (V : Matrix (Fin d) (Fin n) ℝ)
    (f : Finset (Fin n) → ℝ)
    (hf : ∀ s, squaredMinor V s = 0 → f s = 0) :
    (∑ B : ColumnBasis V, f B.val) = ∑ s, f s := by
  classical
  calc
    (∑ B : ColumnBasis V, f B.val) =
        ∑ s ∈ Finset.univ.filter (fun s => 0 < squaredMinor V s), f s := by
      exact (Finset.sum_subtype _ (by simp) f).symm
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro s _ hs
      have hnot : ¬ 0 < squaredMinor V s := by simpa using hs
      exact hf s (le_antisymm (le_of_not_gt hnot) (squaredMinor_nonneg V s))

lemma weightedGram_det_eq_basis_sum (V : Matrix (Fin d) (Fin n) ℝ) (a : Fin n → ℝ) :
    (weightedGram V a).det =
      ∑ B : ColumnBasis V, squaredMinor V B.val * ∏ j ∈ B.val, a j := by
  rw [weightedGram_det]
  exact (sum_columnBasis_eq V _ (by intro s hs; simp [hs])).symm

lemma weightedGram_det_pos (V : Matrix (Fin d) (Fin n) ℝ)
    [Nonempty (ColumnBasis V)] (a : Fin n → ℝ) (ha : ∀ j, 0 < a j) :
    0 < (weightedGram V a).det := by
  rw [weightedGram_det_eq_basis_sum]
  exact Finset.sum_pos
    (fun B _ => mul_pos B.property (Finset.prod_pos (fun j _ => ha j)))
    Finset.univ_nonempty

lemma weightedGram_posDef (V : Matrix (Fin d) (Fin n) ℝ)
    [Nonempty (ColumnBasis V)] (a : Fin n → ℝ) (ha : ∀ j, 0 < a j) :
    (weightedGram V a).PosDef := by
  have hpsd : (weightedGram V a).PosSemidef := by
    have hdiag : (Matrix.diagonal a).PosSemidef :=
      Matrix.PosSemidef.diagonal (fun j => (ha j).le)
    simpa [weightedGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hdiag.mul_mul_conjTranspose_same V
  exact (hpsd.posDef_iff_det_ne_zero).mpr (weightedGram_det_pos V a ha).ne'

/-- Every positive convex combination of basis indicators is realized by a
positive column weighting and its inverse Gram matrix. -/
theorem basisBarycenter_realized (V : Matrix (Fin d) (Fin n) ℝ)
    [Nonempty (ColumnBasis V)]
    (p : ColumnBasis V → ℝ) (hp : ∀ B, 0 < p B) (hpsum : ∑ B, p B = 1) :
    ∃ a : Fin n → ℝ, (∀ j, 0 < a j) ∧
      ∀ j, basisBarycenter V p j =
        a j * ((fun i => V i j) ⬝ᵥ ((weightedGram V a)⁻¹ *ᵥ (fun i => V i j))) := by
  obtain ⟨x, hx⟩ := finite_exponential_barycenter
    (basisIncidence V) p hp hpsum (fun B => squaredMinor V B.val)
    (fun B => B.property)
  change (∑ B : ColumnBasis V,
    (squaredMinor V B.val * Real.exp ⟪basisIncidence V B, x⟫_ℝ) •
      (basisIncidence V B - basisBarycenter V p)) = 0 at hx
  let a : Fin n → ℝ := fun j => Real.exp (x j)
  have ha : ∀ j, 0 < a j := fun j => Real.exp_pos _
  have hdet : 0 < (weightedGram V a).det := weightedGram_det_pos V a ha
  refine ⟨a, ha, ?_⟩
  intro j
  have hj := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z j) hx
  simp only [euclidean_sum_apply, PiLp.smul_apply, PiLp.sub_apply, PiLp.zero_apply,
    basisIncidence_exp_inner, basisIncidence_apply, smul_eq_mul] at hj
  change (∑ B : ColumnBasis V,
    (squaredMinor V B.val * ∏ k ∈ B.val, a k) *
      ((if j ∈ B.val then 1 else 0) - basisBarycenter V p j)) = 0 at hj
  have hmass :
      (∑ B : ColumnBasis V,
        if j ∈ B.val then squaredMinor V B.val * ∏ k ∈ B.val, a k else 0) =
        (weightedGram V a).det * basisBarycenter V p j := by
    have hsplit :
        (∑ B : ColumnBasis V,
          (squaredMinor V B.val * ∏ k ∈ B.val, a k) *
            ((if j ∈ B.val then 1 else 0) - basisBarycenter V p j)) =
          (∑ B : ColumnBasis V,
            if j ∈ B.val then squaredMinor V B.val * ∏ k ∈ B.val, a k else 0) -
            (weightedGram V a).det * basisBarycenter V p j := by
      rw [weightedGram_det_eq_basis_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro B _
      split_ifs <;> ring
    rw [hsplit] at hj
    exact sub_eq_zero.mp hj
  have hsum :
      (∑ s : Finset (Fin n),
        if j ∈ s then squaredMinor V s * ∏ k ∈ s, a k else 0) =
        (weightedGram V a).det * basisBarycenter V p j := by
    rw [← sum_columnBasis_eq V _ (by intro s hs; simp [hs])]
    exact hmass
  have hmarg := weightedGram_basis_marginal V a (isUnit_iff_ne_zero.mpr hdet.ne') j
  rw [hsum] at hmarg
  exact (mul_left_cancel₀ hdet.ne' hmarg).symm

end PaperVerification.Toric
end
end Source_ToricGramBalance
-- END ORIGINAL PaperVerification.ToricGramBalance


-- BEGIN ORIGINAL PaperVerification.ToricLatticeCovering
section Source_ToricLatticeCovering

-- original header: module
-- original header: public import Mathlib.Analysis.InnerProductSpace.Basic
-- original header: public import Mathlib.Topology.MetricSpace.HausdorffDistance
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.Abel
-- original header: public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
-- original header: public import Mathlib.Analysis.Normed.Group.Bounded
-- original header: public import Mathlib.Topology.Order.Compact
-- original header: public import Mathlib.Tactic.Ring
-- original header: @[expose] public section
/-!
# The nearest-point step in the lattice-covering argument

This module proves the geometric part of Lemma 4.1. The existence of a
balancing inner product for every point of the matroid base polytope is a
separate analytic theorem, not an assumption silently discharged here.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped BigOperators InnerProductSpace

/-- A centered zonotope with half-widths `c i / 2` in directions `v i`. -/
def CenteredZonotope {ι E : Type*} [Fintype ι] [AddCommMonoid E] [Module ℝ E]
    (v : ι → E) (c : ι → ℝ) : Set E :=
  {y | ∃ t : ι → ℝ, (∀ i, |t i| ≤ c i / 2) ∧ ∑ i, t i • v i = y}

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every Euclidean nearest-point error satisfies all neighboring-point inequalities. -/
theorem nearest_error_inner_bound (Γ : AddSubgroup E) (x z : E)
    (hz : z ∈ Γ) (hnearest : ∀ y ∈ Γ, ‖x - z‖ ≤ ‖x - y‖)
    (v : E) (hv : v ∈ Γ) :
    |⟪v, x - z⟫_ℝ| ≤ ‖v‖ ^ 2 / 2 := by
  have hminus : ‖x - z‖ ≤ ‖(x - z) - v‖ := by
    have h := hnearest (z + v) (Γ.add_mem hz hv)
    convert h using 1 <;> congr 1 <;> abel
  have hplus : ‖x - z‖ ≤ ‖(x - z) + v‖ := by
    have h := hnearest (z - v) (Γ.sub_mem hz hv)
    convert h using 1 <;> congr 1 <;> abel
  have hminus2 : ‖x - z‖ ^ 2 ≤ ‖(x - z) - v‖ ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hminus
  have hplus2 : ‖x - z‖ ^ 2 ≤ ‖(x - z) + v‖ ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hplus
  rw [norm_sub_sq_real (x - z) v] at hminus2
  rw [norm_add_sq_real (x - z) v] at hplus2
  rw [real_inner_comm (x - z) v]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A weighted tight frame gives a covering zonotope for every closed additive
subgroup containing its vectors, in a proper real inner-product space.

Applied after the log-determinant balancing step, this is exactly the
nearest-lattice-point argument in Lemma 4.1. No lattice-covering conclusion
is included among the hypotheses.
-/
theorem balanced_frame_covering [ProperSpace E]
    (Γ : AddSubgroup E) (hclosed : IsClosed (Γ : Set E))
    (v : ι → E) (hv : ∀ i, v i ∈ Γ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hframe : ∀ y : E, ∑ i, (w i * ⟪v i, y⟫_ℝ) • v i = y)
    (x : E) :
    ∃ z ∈ Γ, x - z ∈ CenteredZonotope v (fun i => w i * ‖v i‖ ^ 2) := by
  obtain ⟨z, hz, hdist⟩ := hclosed.exists_infDist_eq_dist ⟨0, Γ.zero_mem⟩ x
  have hnearest : ∀ y ∈ Γ, ‖x - z‖ ≤ ‖x - y‖ := by
    intro y hy
    rw [← dist_eq_norm, ← dist_eq_norm, ← hdist]
    exact Metric.infDist_le_dist_of_mem hy
  refine ⟨z, hz, fun i => w i * ⟪v i, x - z⟫_ℝ, ?_, hframe (x - z)⟩
  intro i
  have h := nearest_error_inner_bound Γ x z hz hnearest (v i) (hv i)
  rw [abs_mul, abs_of_nonneg (hw i)]
  have hmul := mul_le_mul_of_nonneg_left h (hw i)
  nlinarith

/-- The quadratic norm-square determined by a real continuous linear operator. -/
def quadraticValue (T : E →L[ℝ] E) (x : E) : ℝ := ⟪x, T x⟫_ℝ

lemma quadraticValue_continuous (T : E →L[ℝ] E) : Continuous (quadraticValue T) :=
  continuous_id.inner T.continuous

lemma quadraticValue_smul (T : E →L[ℝ] E) (x : E) (a : ℝ) :
    quadraticValue T (a • x) = a ^ 2 * quadraticValue T x := by
  simp only [quadraticValue, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- Positive definite quadratic forms have a uniform norm-square lower bound. -/
theorem quadraticValue_lower_bound [FiniteDimensional ℝ E] [Nontrivial E]
    (T : E →L[ℝ] E) (hpos : ∀ x ≠ 0, 0 < quadraticValue T x) :
    ∃ ε > 0, ∀ x, ε * ‖x‖ ^ 2 ≤ quadraticValue T x := by
  have hsne : (Metric.sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num)
  obtain ⟨u, hu, hmin⟩ :=
    (isCompact_sphere (0 : E) 1).exists_isMinOn hsne
      (quadraticValue_continuous T).continuousOn
  have hunorm : ‖u‖ = 1 := by simpa using hu
  have hu0 : u ≠ 0 := by intro h; simp [h] at hunorm
  refine ⟨quadraticValue T u, hpos u hu0, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx, quadraticValue]
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxunit : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E) 1 := by
    simp [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnorm.le), hnorm.ne']
  have h : quadraticValue T u ≤ quadraticValue T (‖x‖⁻¹ • x) := hmin hxunit
  rw [quadraticValue_smul] at h
  have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg ‖x‖)
  simpa [mul_assoc, mul_comm, mul_left_comm, ← mul_pow, hnorm.ne'] using hmul

/-- A positive definite quadratic distance attains its minimum on every closed
additive subgroup. Discreteness and full rank are not needed for this step. -/
theorem exists_quadratic_nearest [FiniteDimensional ℝ E]
    (Γ : AddSubgroup E) (hclosed : IsClosed (Γ : Set E))
    (T : E →L[ℝ] E) (hpos : ∀ x ≠ 0, 0 < quadraticValue T x) (x : E) :
    ∃ z ∈ Γ, ∀ y ∈ Γ, quadraticValue T (x - z) ≤ quadraticValue T (x - y) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · letI := hE
    refine ⟨0, Γ.zero_mem, ?_⟩
    intro y _
    exact le_of_eq (congrArg (fun z => quadraticValue T (x - z)) (Subsingleton.elim 0 y))
  letI := hE
  obtain ⟨ε, hε, hbound⟩ := quadraticValue_lower_bound T hpos
  have hnorm : Filter.Tendsto (fun y : E => ‖x - y‖) (Filter.cocompact E)
      Filter.atTop := by
    simpa only [Function.comp_def, ← Metric.cobounded_eq_cocompact] using
      tendsto_norm_cobounded_atTop.comp (tendsto_const_sub_cobounded x)
  have hpow : Filter.Tendsto (fun y : E => ‖x - y‖ ^ 2) (Filter.cocompact E)
      Filter.atTop := (Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hnorm
  have hlim : Filter.Tendsto (fun y : E => quadraticValue T (x - y))
      (Filter.cocompact E) Filter.atTop :=
    Filter.tendsto_atTop_mono (fun y => hbound (x - y))
      (Filter.Tendsto.const_mul_atTop hε hpow)
  have hcont : Continuous (fun y : E => quadraticValue T (x - y)) :=
    (quadraticValue_continuous T).comp (continuous_const.sub continuous_id)
  have hev : ∀ᶠ y in Filter.cocompact E,
      quadraticValue T (x - 0) ≤ quadraticValue T (x - y) :=
    hlim.eventually (Filter.eventually_ge_atTop _)
  obtain ⟨z, hz, hmin⟩ := hcont.continuousOn.exists_isMinOn' hclosed Γ.zero_mem
    (hev.filter_mono inf_le_left)
  exact ⟨z, hz, fun y hy => hmin hy⟩

/-- Symmetric quadratic expansion. -/
lemma quadraticValue_add (T : E →L[ℝ] E)
    (hsym : ∀ a b, ⟪a, T b⟫_ℝ = ⟪b, T a⟫_ℝ) (a b : E) :
    quadraticValue T (a + b) =
      quadraticValue T a + 2 * ⟪b, T a⟫_ℝ + quadraticValue T b := by
  simp only [quadraticValue, map_add, inner_add_left, inner_add_right]
  rw [hsym a b]
  ring

lemma quadraticValue_sub (T : E →L[ℝ] E)
    (hsym : ∀ a b, ⟪a, T b⟫_ℝ = ⟪b, T a⟫_ℝ) (a b : E) :
    quadraticValue T (a - b) =
      quadraticValue T a - 2 * ⟪b, T a⟫_ℝ + quadraticValue T b := by
  simp only [quadraticValue, map_sub, inner_sub_left, inner_sub_right]
  rw [hsym a b]
  ring

/-- The full ellipsoidal nearest-point step used in Lemma 4.1. -/
theorem ellipsoidal_frame_covering [FiniteDimensional ℝ E]
    (Γ : AddSubgroup E) (hclosed : IsClosed (Γ : Set E))
    (T : E →L[ℝ] E)
    (hsym : ∀ a b, ⟪a, T b⟫_ℝ = ⟪b, T a⟫_ℝ)
    (hpos : ∀ x ≠ 0, 0 < quadraticValue T x)
    (v : ι → E) (hv : ∀ i, v i ∈ Γ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hframe : ∀ y : E, ∑ i, (w i * ⟪v i, T y⟫_ℝ) • v i = y)
    (x : E) :
    ∃ z ∈ Γ, x - z ∈ CenteredZonotope v (fun i => w i * quadraticValue T (v i)) := by
  obtain ⟨z, hz, hnearest⟩ := exists_quadratic_nearest Γ hclosed T hpos x
  refine ⟨z, hz, fun i => w i * ⟪v i, T (x - z)⟫_ℝ, ?_, hframe (x - z)⟩
  intro i
  have hminus : quadraticValue T (x - z) ≤ quadraticValue T ((x - z) - v i) := by
    have h := hnearest (z + v i) (Γ.add_mem hz (hv i))
    convert h using 1 <;> congr 1 <;> abel
  have hplus : quadraticValue T (x - z) ≤ quadraticValue T ((x - z) + v i) := by
    have h := hnearest (z - v i) (Γ.sub_mem hz (hv i))
    convert h using 1 <;> congr 1 <;> abel
  rw [quadraticValue_sub T hsym (x - z) (v i)] at hminus
  rw [quadraticValue_add T hsym (x - z) (v i)] at hplus
  have habs : |⟪v i, T (x - z)⟫_ℝ| ≤ quadraticValue T (v i) / 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  rw [abs_mul, abs_of_nonneg (hw i)]
  have hmul := mul_le_mul_of_nonneg_left habs (hw i)
  nlinarith

end PaperVerification.Toric
end
end Source_ToricLatticeCovering
-- END ORIGINAL PaperVerification.ToricLatticeCovering


-- BEGIN ORIGINAL PaperVerification.ToricBasisCovering
section Source_ToricBasisCovering

-- original header: module
-- original header: public import PaperVerification.ToricGramBalance
-- original header: public import PaperVerification.ToricLatticeCovering
-- original header: public import Mathlib.Topology.MetricSpace.Sequences
-- original header: public import Mathlib.Topology.Order.Compact
-- original header: public import Mathlib.Tactic.Ring
-- original header: public import Mathlib.Analysis.SpecificLimits.Basic
-- original header: public import Mathlib.Analysis.Convex.Combination
-- original header: public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
-- original header: public import Mathlib.Algebra.Module.ZLattice.Basic
-- original header: @[expose] public section
/-!
# Covering by averaged basis boxes

This file connects the Gram balancing construction to the actual Euclidean
covering statement. Closed additive subgroups suffice for the geometric proof;
full lattices are a special case.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped Matrix BigOperators InnerProductSpace
open Filter Topology

variable {d n : ℕ}

def matrixColumn (V : Matrix (Fin d) (Fin n) ℝ) (j : Fin n) :
    EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun i => V i j)

/-- Nonvanishing of a maximal minor is exactly linear independence of the
selected vectors in the actual Euclidean ambient space. -/
lemma column_minor_ne_zero_iff_linearIndependent
    (V : Matrix (Fin d) (Fin n) ℝ) (s : Finset (Fin n)) (hs : s.card = d) :
    (PaperVerification.CauchyBinet.colsSubmatrix V s hs).det ≠ 0 ↔
      LinearIndependent ℝ (fun i => matrixColumn V (s.orderEmbOfFin hs i)) := by
  let e : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] (Fin d → ℝ) :=
    WithLp.linearEquiv 2 ℝ (Fin d → ℝ)
  have he : LinearMap.ker e.toLinearMap = ⊥ := LinearMap.ker_eq_bot.mpr e.injective
  have hmap := e.toLinearMap.linearIndependent_iff
    (v := fun i => matrixColumn V (s.orderEmbOfFin hs i)) he
  change LinearIndependent ℝ (PaperVerification.CauchyBinet.colsSubmatrix V s hs).col ↔
    LinearIndependent ℝ (fun i => matrixColumn V (s.orderEmbOfFin hs i)) at hmap
  rw [Matrix.linearIndependent_col_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero] at hmap
  exact hmap

/-- The maximal-minor predicate used in `ColumnBasis` is equivalent to the
existence of a genuine real vector-space basis with those selected columns. -/
lemma column_minor_ne_zero_iff_basis
    (V : Matrix (Fin d) (Fin n) ℝ) (s : Finset (Fin n)) (hs : s.card = d) :
    (PaperVerification.CauchyBinet.colsSubmatrix V s hs).det ≠ 0 ↔
      ∃ b : Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)),
        ∀ i, b i = matrixColumn V (s.orderEmbOfFin hs i) := by
  rw [column_minor_ne_zero_iff_linearIndependent]
  constructor
  · intro hli
    let b := basisOfLinearIndependentOfCardEqFinrank'
      (fun i => matrixColumn V (s.orderEmbOfFin hs i)) hli (by simp)
    refine ⟨b, ?_⟩
    intro i
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp)) i
  · rintro ⟨b, hb⟩
    have heq : (fun i => matrixColumn V (s.orderEmbOfFin hs i)) = fun i => b i :=
      funext (fun i => (hb i).symm)
    rw [heq]
    exact b.linearIndependent

def matrixOperator (A : Matrix (Fin d) (Fin d) ℝ) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  A.toEuclideanLin.toContinuousLinearMap

lemma matrixOperator_apply (A : Matrix (Fin d) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    matrixOperator A x = WithLp.toLp 2 (A *ᵥ x.ofLp) := rfl

lemma euclidean_inner_eq_dot (x y : EuclideanSpace ℝ (Fin d)) :
    ⟪x, y⟫_ℝ = x.ofLp ⬝ᵥ y.ofLp := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

lemma matrixOperator_positive (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) :
    ∀ x ≠ 0, 0 < quadraticValue (matrixOperator A) x := by
  intro x hx
  have hx' : x.ofLp ≠ 0 := by
    intro h
    apply hx
    exact WithLp.ofLp_injective 2 h
  simpa [quadraticValue, matrixOperator_apply, euclidean_inner_eq_dot] using
    hA.dotProduct_mulVec_pos hx'

lemma matrixOperator_symmetric (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) :
    ∀ x y : EuclideanSpace ℝ (Fin d),
      ⟪x, matrixOperator A y⟫_ℝ = ⟪y, matrixOperator A x⟫_ℝ := by
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  intro x y
  change ⟪x, A.toEuclideanLin y⟫_ℝ = ⟪y, A.toEuclideanLin x⟫_ℝ
  rw [← hs x y]
  exact real_inner_comm y (A.toEuclideanLin x)

lemma gram_inverse_frame (V : Matrix (Fin d) (Fin n) ℝ)
    (a : Fin n → ℝ) (hunit : IsUnit (weightedGram V a).det)
    (y : EuclideanSpace ℝ (Fin d)) :
    ∑ j, (a j * ⟪matrixColumn V j, matrixOperator (weightedGram V a)⁻¹ y⟫_ℝ) •
      matrixColumn V j = y := by
  let z : Fin d → ℝ := (weightedGram V a)⁻¹ *ᵥ y.ofLp
  have hfactor : weightedGram V a *ᵥ z =
      V *ᵥ (Matrix.diagonal a *ᵥ (V.transpose *ᵥ z)) := by
    simp only [Matrix.mulVec_mulVec, weightedGram, Matrix.mul_assoc]
  have hcancel : weightedGram V a *ᵥ z = y.ofLp := by
    dsimp [z]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  apply PiLp.ext
  intro i
  rw [euclidean_sum_apply]
  calc
    (∑ j, ((a j * ⟪matrixColumn V j,
        matrixOperator (weightedGram V a)⁻¹ y⟫_ℝ) • matrixColumn V j) i) =
        (V *ᵥ (Matrix.diagonal a *ᵥ (V.transpose *ᵥ z))) i := by
      simp only [PiLp.smul_apply, smul_eq_mul, matrixColumn, PiLp.toLp_apply,
        euclidean_inner_eq_dot, matrixOperator_apply, WithLp.ofLp_toLp]
      change (∑ j, (a j * ((fun k => V k j) ⬝ᵥ z)) * V i j) =
        ∑ j, V i j * (Matrix.diagonal a *ᵥ (V.transpose *ᵥ z)) j
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.mulVec_diagonal]
      change a j * (∑ k, V k j * z k) * V i j =
        V i j * (a j * (∑ k, V k j * z k))
      ring
    _ = y i := by simpa only [← hfactor, hcancel]

/-- Covering for strictly positive combinations of all basis indicators. -/
theorem positive_basis_average_covering (V : Matrix (Fin d) (Fin n) ℝ)
    [Nonempty (ColumnBasis V)]
    (Γ : AddSubgroup (EuclideanSpace ℝ (Fin d)))
    (hclosed : IsClosed (Γ : Set (EuclideanSpace ℝ (Fin d))))
    (hv : ∀ j, matrixColumn V j ∈ Γ)
    (p : ColumnBasis V → ℝ) (hp : ∀ B, 0 < p B) (hpsum : ∑ B, p B = 1)
    (x : EuclideanSpace ℝ (Fin d)) :
    ∃ z ∈ Γ, x - z ∈ CenteredZonotope (matrixColumn V) (basisBarycenter V p) := by
  obtain ⟨a, ha, hwidth⟩ := basisBarycenter_realized V p hp hpsum
  have hG := weightedGram_posDef V a ha
  have hQ := hG.inv
  have hunit : IsUnit (weightedGram V a).det :=
    isUnit_iff_ne_zero.mpr (weightedGram_det_pos V a ha).ne'
  obtain ⟨z, hz, herror⟩ := ellipsoidal_frame_covering Γ hclosed
    (matrixOperator (weightedGram V a)⁻¹)
    (matrixOperator_symmetric _ hQ.isHermitian)
    (matrixOperator_positive _ hQ) (matrixColumn V) hv a (fun j => (ha j).le)
    (gram_inverse_frame V a hunit) x
  refine ⟨z, hz, ?_⟩
  convert herror using 1
  congr 1
  funext j
  rw [hwidth]
  simp [quadraticValue, matrixColumn, matrixOperator_apply, euclidean_inner_eq_dot]

/-- The covering property passes to limits of uniformly bounded width vectors.
Only closedness of the additive subgroup is used in the limiting step. -/
theorem centeredZonotope_covering_limit {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Γ : AddSubgroup E) (hclosed : IsClosed (Γ : Set E))
    (v : ι → E) (c : ι → ℝ) (cseq : ℕ → ι → ℝ)
    (hlim : ∀ j, Tendsto (fun k => cseq k j) atTop (𝓝 (c j)))
    (hbound : ∀ k j, cseq k j ≤ 1) (x : E)
    (hcover : ∀ k, ∃ z ∈ Γ, x - z ∈ CenteredZonotope v (cseq k)) :
    ∃ z ∈ Γ, x - z ∈ CenteredZonotope v c := by
  classical
  have hdata : ∀ k, ∃ t : ι → ℝ,
      (∀ j, |t j| ≤ cseq k j / 2) ∧ x - ∑ j, t j • v j ∈ Γ := by
    intro k
    obtain ⟨z, hz, t, ht, hsum⟩ := hcover k
    refine ⟨t, ht, ?_⟩
    rw [hsum]
    convert hz using 1 <;> congr 1 <;> abel
  choose t ht hΓ using hdata
  have htmem : ∀ k, t k ∈ Set.Icc (fun _ : ι => (-1 : ℝ)) (fun _ => (1 : ℝ)) := by
    intro k
    constructor <;> intro j
    · have h := (abs_le.mp (ht k j)).1
      have h' := hbound k j
      linarith
    · have h := (abs_le.mp (ht k j)).2
      have h' := hbound k j
      linarith
  obtain ⟨t₀, _, φ, hφ, htlim⟩ := isCompact_Icc.tendsto_subseq htmem
  have hcoord (j : ι) : Tendsto (fun k => t (φ k) j) atTop (𝓝 (t₀ j)) :=
    (continuous_apply j).continuousAt.tendsto.comp htlim
  have htbound : ∀ j, |t₀ j| ≤ c j / 2 := by
    intro j
    exact le_of_tendsto_of_tendsto' (hcoord j).abs
      ((hlim j).comp hφ.tendsto_atTop |>.div_const 2) (fun k => ht (φ k) j)
  have hcont : Continuous (fun u : ι → ℝ => x - ∑ j, u j • v j) :=
    continuous_const.sub <| continuous_finset_sum _
      (fun j _ => (continuous_apply j).smul continuous_const)
  have hΓ₀ : x - ∑ j, t₀ j • v j ∈ Γ :=
    hclosed.mem_of_tendsto (hcont.continuousAt.tendsto.comp htlim)
      (Eventually.of_forall (fun k => hΓ (φ k)))
  refine ⟨x - ∑ j, t₀ j • v j, hΓ₀, t₀, htbound, ?_⟩
  abel

lemma basisBarycenter_le_one (V : Matrix (Fin d) (Fin n) ℝ)
    (p : ColumnBasis V → ℝ) (hp : ∀ B, 0 ≤ p B) (hpsum : ∑ B, p B = 1)
    (j : Fin n) : basisBarycenter V p j ≤ 1 := by
  rw [basisBarycenter_apply, ← hpsum]
  apply Finset.sum_le_sum
  intro B _
  split_ifs <;> simp [hp B]

/-- Covering for every convex combination of the basis indicators, including
all boundary points of the representable matroid base polytope. -/
theorem basis_average_covering (V : Matrix (Fin d) (Fin n) ℝ)
    [Nonempty (ColumnBasis V)]
    (Γ : AddSubgroup (EuclideanSpace ℝ (Fin d)))
    (hclosed : IsClosed (Γ : Set (EuclideanSpace ℝ (Fin d))))
    (hv : ∀ j, matrixColumn V j ∈ Γ)
    (p : ColumnBasis V → ℝ) (hp : ∀ B, 0 ≤ p B) (hpsum : ∑ B, p B = 1)
    (x : EuclideanSpace ℝ (Fin d)) :
    ∃ z ∈ Γ, x - z ∈ CenteredZonotope (matrixColumn V) (basisBarycenter V p) := by
  let N : ℝ := Fintype.card (ColumnBasis V)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hεpos (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hεle (k : ℕ) : ε k ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity)).mpr
    exact le_add_of_nonneg_left (Nat.cast_nonneg k)
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let pseq : ℕ → ColumnBasis V → ℝ :=
    fun k B => ε k * N⁻¹ + (1 - ε k) * p B
  have hpseq (k : ℕ) (B : ColumnBasis V) : 0 < pseq k B := by
    dsimp [pseq]
    exact add_pos_of_pos_of_nonneg (mul_pos (hεpos k) (inv_pos.mpr hN))
      (mul_nonneg (sub_nonneg.mpr (hεle k)) (hp B))
  have hsumseq (k : ℕ) : ∑ B, pseq k B = 1 := by
    simp only [pseq, Finset.sum_add_distrib, ← Finset.mul_sum, hpsum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change ε k * (N * N⁻¹) + (1 - ε k) * 1 = 1
    rw [mul_inv_cancel₀ hN.ne']
    ring
  have hplim (B : ColumnBasis V) : Tendsto (fun k => pseq k B) atTop (𝓝 (p B)) := by
    simpa [pseq] using
      (hεlim.mul_const N⁻¹).add
        (((tendsto_const_nhds (x := (1 : ℝ))).sub hεlim).mul_const (p B))
  refine centeredZonotope_covering_limit Γ hclosed (matrixColumn V) (basisBarycenter V p)
    (fun k => basisBarycenter V (pseq k)) ?_ ?_ x ?_
  · intro j
    simp only [basisBarycenter_apply]
    apply tendsto_finsetSum
    intro B _
    by_cases hj : j ∈ B.val
    · simpa [hj] using hplim B
    · simp only [hj, if_false]
      exact tendsto_const_nhds
  · intro k j
    exact basisBarycenter_le_one V (pseq k) (fun B => (hpseq k B).le) (hsumseq k) j
  · intro k
    exact positive_basis_average_covering V Γ hclosed hv (pseq k) (hpseq k) (hsumseq k) x

/-- Lemma 4.1, in standard Euclidean coordinates. The hypothesis on the widths
is membership in the actual convex hull of the incidence vectors of all
nonsingular maximal column subsets. The result includes boundary widths.

The subgroup assumption is weaker than the manuscript's full-lattice
assumption, while every direction must still belong to that subgroup. -/
theorem matroid_basis_polytope_covering (V : Matrix (Fin d) (Fin n) ℝ)
    (Γ : AddSubgroup (EuclideanSpace ℝ (Fin d)))
    (hclosed : IsClosed (Γ : Set (EuclideanSpace ℝ (Fin d))))
    (hv : ∀ j, matrixColumn V j ∈ Γ)
    (c : EuclideanSpace ℝ (Fin n))
    (hc : c ∈ convexHull ℝ (Set.range (basisIncidence V)))
    (x : EuclideanSpace ℝ (Fin d)) :
    ∃ z ∈ Γ, x - z ∈ CenteredZonotope (matrixColumn V) c := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hc
  obtain ⟨s, w, hw, hsum, hcomb⟩ := hc
  have hsne : s.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hs
    simp [hs] at hsum
  obtain ⟨B, _⟩ := hsne
  letI : Nonempty (ColumnBasis V) := ⟨B⟩
  let p : ColumnBasis V → ℝ := fun B => if B ∈ s then w B else 0
  have hp : ∀ B, 0 ≤ p B := by
    intro B
    by_cases hB : B ∈ s
    · simpa [p, hB] using hw B hB
    · simp [p, hB]
  have hpsum : ∑ B, p B = 1 := by simpa [p, Finset.sum_ite_mem] using hsum
  have hpc : basisBarycenter V p = c := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum] at hcomb
    simpa [basisBarycenter, p, ite_smul, Finset.sum_ite_mem] using hcomb
  simpa [hpc] using basis_average_covering V Γ hclosed hv p hp hpsum x

/-- The full-lattice formulation of Lemma 4.1. The final conclusion explicitly
states that the zonotope meets the coset represented by every ambient point. -/
theorem lattice_basis_polytope_covering (V : Matrix (Fin d) (Fin n) ℝ)
    (Γ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (hv : ∀ j, matrixColumn V j ∈ Γ)
    (c : EuclideanSpace ℝ (Fin n))
    (hc : c ∈ convexHull ℝ (Set.range (basisIncidence V)))
    (x : EuclideanSpace ℝ (Fin d)) :
    ∃ y ∈ CenteredZonotope (matrixColumn V) c, y - x ∈ Γ := by
  letI : DiscreteTopology Γ.toAddSubgroup := inferInstanceAs (DiscreteTopology Γ)
  have hclosed : IsClosed (Γ.toAddSubgroup : Set (EuclideanSpace ℝ (Fin d))) :=
    AddSubgroup.isClosed_of_discreteTopology
  obtain ⟨z, hz, herror⟩ :=
    matroid_basis_polytope_covering V Γ.toAddSubgroup hclosed hv c hc x
  refine ⟨x - z, herror, ?_⟩
  convert Γ.neg_mem hz using 1 <;> congr 1 <;> abel

end PaperVerification.Toric
end
end Source_ToricBasisCovering
-- END ORIGINAL PaperVerification.ToricBasisCovering


-- BEGIN ORIGINAL PaperVerification.ToricBoxAverages
section Source_ToricBoxAverages

-- original header: module
-- original header: public import PaperVerification.ToricBasisCovering
-- original header: public import Mathlib.Analysis.Convex.Combination
-- original header: public import Mathlib.Tactic.FieldSimp
-- original header: public import Mathlib.Tactic.Abel
-- original header: @[expose] public section
/-!
# Matched box averages and lattice decompositions

This is equation (7) of the toric manuscript, with the centered zonotope and
all convex-combination hypotheses made explicit. Different boxes may use
unrelated bases of the common ambient real vector space.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped BigOperators

variable {J ι E : Type*} [Fintype J] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The centered unit box in a selected subset of the vector configuration. -/
def SubsetBox (v : ι → E) (s : Finset ι) : Set E :=
  CenteredZonotope v (fun j => if j ∈ s then 1 else 0)

/-- Total occurrence weight of each vector in a family of selected subsets. -/
def averagedWidths (s : J → Finset ι) (p : J → ℝ) (j : ι) : ℝ :=
  ∑ B, if j ∈ s B then p B else 0

lemma averagedWidths_nonneg (s : J → Finset ι) (p : J → ℝ) (hp : ∀ B, 0 ≤ p B)
    (j : ι) : 0 ≤ averagedWidths s p j := by
  apply Finset.sum_nonneg
  intro B _
  split_ifs <;> simp [hp B]

lemma neg_mem_centeredZonotope (v : ι → E) (c : ι → ℝ) {z : E}
    (hz : z ∈ CenteredZonotope v c) : -z ∈ CenteredZonotope v c := by
  obtain ⟨t, ht, hsum⟩ := hz
  refine ⟨fun j => -t j, ?_, ?_⟩
  · intro j
    simpa using ht j
  · simpa only [neg_smul, Finset.sum_neg_distrib, hsum]

/-- A point of the averaged-width zonotope is an actual convex Minkowski
average of points of the individual unit boxes. Zero width coordinates and
zero probability weights are included. -/
theorem zonotope_exists_box_average (v : ι → E) (s : J → Finset ι)
    (p : J → ℝ) (hp : ∀ B, 0 ≤ p B) {z : E}
    (hz : z ∈ CenteredZonotope v (averagedWidths s p)) :
    ∃ q : J → E, (∀ B, q B ∈ SubsetBox v (s B)) ∧ ∑ B, p B • q B = z := by
  classical
  obtain ⟨t, ht, hsum⟩ := hz
  let c : ι → ℝ := averagedWidths s p
  let u : J → ι → ℝ := fun B j => if j ∈ s B then t j / c j else 0
  have hc (j : ι) : 0 ≤ c j := averagedWidths_nonneg s p hp j
  have htzero (j : ι) (hj : c j = 0) : t j = 0 := by
    have h := ht j
    change |t j| ≤ c j / 2 at h
    rw [hj, zero_div] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have hu (B : J) (j : ι) : |u B j| ≤ (if j ∈ s B then 1 else 0) / 2 := by
    by_cases hmem : j ∈ s B
    · simp only [u, hmem, if_true]
      by_cases hj : c j = 0
      · simp [hj]
      · have hcpos : 0 < c j := lt_of_le_of_ne (hc j) (Ne.symm hj)
        rw [abs_div, abs_of_pos hcpos]
        apply (div_le_iff₀ hcpos).mpr
        have h := ht j
        change |t j| ≤ c j / 2 at h
        linarith
    · simp [u, hmem]
  have hcoeff (j : ι) : ∑ B, p B * u B j = t j := by
    calc
      (∑ B, p B * u B j) =
          (∑ B, if j ∈ s B then p B else 0) * (t j / c j) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro B _
        by_cases hj : j ∈ s B <;> simp [u, hj]
      _ = t j := by
        change c j * (t j / c j) = t j
        by_cases hj : c j = 0
        · simp [hj, htzero j hj]
        · field_simp [hj]
  refine ⟨fun B => ∑ j, u B j • v j, ?_, ?_⟩
  · intro B
    exact ⟨u B, hu B, rfl⟩
  · calc
      (∑ B, p B • ∑ j, u B j • v j) = ∑ j, ∑ B, (p B * u B j) • v j := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
      _ = ∑ j, t j • v j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_smul, hcoeff]
      _ = z := hsum

/-- Equation (7): matched box centers and the common average zonotope give
points simultaneously in the first polytope and in the reflected second one. -/
theorem matched_boxes_average (A B : Set E) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (v : ι → E) (s : J → Finset ι) (p : J → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (a b : J → E)
    (hboxA : ∀ i z, z ∈ SubsetBox v (s i) → a i + z ∈ A)
    (hboxB : ∀ i z, z ∈ SubsetBox v (s i) → b i + z ∈ B)
    (m : E) (hm : m = ∑ i, p i • (a i + b i))
    {z : E} (hz : z ∈ CenteredZonotope v (averagedWidths s p)) :
    (∑ i, p i • a i) + z ∈ A ∧ m - ((∑ i, p i • a i) + z) ∈ B := by
  obtain ⟨q, hq, hqsum⟩ := zonotope_exists_box_average v s p hp hz
  have hfirst := hA.sum_mem (t := Finset.univ) (fun i _ => hp i) hpsum
    (fun i _ => hboxA i (q i) (hq i))
  have hsecond := hB.sum_mem (t := Finset.univ) (fun i _ => hp i) hpsum
    (fun i _ => hboxB i (-q i) (neg_mem_centeredZonotope v _ (hq i)))
  constructor
  · simpa only [smul_add, Finset.sum_add_distrib, hqsum] using hfirst
  · have hsum : (∑ i, p i • (b i + -q i)) =
        m - ((∑ i, p i • a i) + z) := by
      rw [hm]
      simp only [smul_add, smul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, hqsum]
      abel
    rw [← hsum]
    exact hsecond

/-- Lattice decomposition supplied by matched integral basis boxes. This is
the common geometric consequence of Lemma 4.1 and equation (7). -/
theorem matched_boxes_lattice_decomposition {d n : ℕ}
    (V : Matrix (Fin d) (Fin n) ℝ)
    (Γ : AddSubgroup (EuclideanSpace ℝ (Fin d)))
    (hclosed : IsClosed (Γ : Set (EuclideanSpace ℝ (Fin d))))
    (hv : ∀ j, matrixColumn V j ∈ Γ)
    (A B : Set (EuclideanSpace ℝ (Fin d))) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (s : J → Finset (Fin n)) (hs : ∀ i, 0 < squaredMinor V (s i))
    (p : J → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (a b : J → EuclideanSpace ℝ (Fin d))
    (hboxA : ∀ i z, z ∈ SubsetBox (matrixColumn V) (s i) → a i + z ∈ A)
    (hboxB : ∀ i z, z ∈ SubsetBox (matrixColumn V) (s i) → b i + z ∈ B)
    (m : EuclideanSpace ℝ (Fin d)) (hmΓ : m ∈ Γ)
    (hm : m = ∑ i, p i • (a i + b i)) :
    ∃ x ∈ A, ∃ y ∈ B, x ∈ Γ ∧ y ∈ Γ ∧ x + y = m := by
  let C : EuclideanSpace ℝ (Fin n) :=
    ∑ i, p i • basisIncidence V ⟨s i, hs i⟩
  have hC : C ∈ convexHull ℝ (Set.range (basisIncidence V)) :=
    mem_convexHull_of_exists_fintype p (fun i => basisIncidence V ⟨s i, hs i⟩)
      hp hpsum (fun i => Set.mem_range_self _) rfl
  have hwidth : (C : Fin n → ℝ) = averagedWidths s p := by
    funext j
    dsimp only [C]
    rw [euclidean_sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp [basisIncidence]
  let ac : EuclideanSpace ℝ (Fin d) := ∑ i, p i • a i
  obtain ⟨x, hxΓ, hxerror⟩ := matroid_basis_polytope_covering V Γ hclosed hv C hC ac
  have hxbox : x - ac ∈ CenteredZonotope (matrixColumn V) (averagedWidths s p) := by
    have hn := neg_mem_centeredZonotope (matrixColumn V) C hxerror
    simpa only [neg_sub, hwidth] using hn
  have hboth := matched_boxes_average A B hA hB (matrixColumn V) s p hp hpsum
    a b hboxA hboxB m hm hxbox
  have hAx : x ∈ A := by
    simpa [ac, add_sub_cancel_left] using hboth.1
  have hBy : m - x ∈ B := by
    simpa [ac, add_sub_cancel_left] using hboth.2
  exact ⟨x, hAx, m - x, hBy, hxΓ, Γ.sub_mem hmΓ hxΓ, by abel⟩

end PaperVerification.Toric
end
end Source_ToricBoxAverages
-- END ORIGINAL PaperVerification.ToricBoxAverages


-- BEGIN ORIGINAL PaperVerification.ToricSimplexParity
section Source_ToricSimplexParity

-- original header: module
-- original header: public import Mathlib.Data.Fin.Tuple.Basic
-- original header: public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
-- original header: public import Mathlib.Algebra.Order.BigOperators.Group.Finset
-- original header: public import Mathlib.Algebra.BigOperators.Ring.Finset
-- original header: public import Mathlib.Algebra.BigOperators.Fin
-- original header: public import Lean.Elab.Tactic.Omega
-- original header: @[expose] public section
/-!
# Integral simplex allocation with prescribed parity

The allocation theorem below is the homogeneous-coordinate form of Lemma 4.4
of *Quadratic generation for smooth polytopes with long edges*.
No geometric statements about arbitrary smooth polytopes are assumed here.
-/

namespace PaperVerification.Toric

open scoped BigOperators

/-- Allocate a prescribed number of tokens among finitely many integral capacities. -/
theorem allocate_le_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℕ) (k : ℕ) (hk : k ≤ ∑ i ∈ s, c i) :
    ∃ u : ι → ℕ, (∀ i ∈ s, u i ≤ c i) ∧ (∑ i ∈ s, u i) = k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
      have : k = 0 := by simpa using hk
      subst k
      exact ⟨fun _ => 0, by simp⟩
  | @insert a s ha ih =>
      have hk' : k ≤ c a + ∑ i ∈ s, c i := by simpa [Finset.sum_insert ha] using hk
      obtain ⟨u, hu, hsum⟩ := ih (k - min k (c a)) (by omega)
      refine ⟨Function.update u a (min k (c a)), ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simp
        · simp only [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]
          exact hu i hi
      · rw [Finset.sum_insert ha]
        have hupdate : ∑ i ∈ s, Function.update u a (min k (c a)) i = ∑ i ∈ s, u i := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Function.update_of_ne (ne_of_mem_of_not_mem hi ha) _ _
        rw [hupdate]
        simp only [Function.update_self]
        omega

/-- A zero-one sum on `d + 1` coordinates cannot exceed `k ≥ d` if its parity is `k`'s. -/
theorem bit_sum_le {d k : ℕ} (e : Fin (d + 1) → ℕ)
    (he : ∀ i, e i ≤ 1) (hdk : d ≤ k) (hpar : (∑ i, e i) % 2 = k % 2) :
    ∑ i, e i ≤ k := by
  have hbound : (∑ i, e i) ≤ d + 1 := by
    calc
      (∑ i, e i) ≤ ∑ _ : Fin (d + 1), 1 := Finset.sum_le_sum (fun i _ => he i)
      _ = d + 1 := by simp
  omega

/-- Full homogeneous-coordinate simplex parity allocation.

`m` is an interior integral point of the sum of simplices of degrees `k` and `l`.
The requested parity `e` includes the zeroth homogeneous coordinate; its sum must
therefore have the parity of `k`. The dimension is arbitrary.
-/
theorem simplex_parity_homogeneous {d k l : ℕ}
    (hdk : d ≤ k) (hdl : d ≤ l)
    (m e : Fin (d + 1) → ℕ)
    (hm : ∀ i, 0 < m i) (he : ∀ i, e i ≤ 1)
    (hsum : ∑ i, m i = k + l)
    (hpar : (∑ i, e i) % 2 = k % 2) :
    ∃ a b : Fin (d + 1) → ℕ,
      (∀ i, a i + b i = m i) ∧
      (∑ i, a i) = k ∧ (∑ i, b i) = l ∧
      (∀ i, a i % 2 = e i) := by
  let c : Fin (d + 1) → ℕ := fun i => (m i - e i) / 2
  let f : Fin (d + 1) → ℕ := fun i => (m i - e i) % 2
  have hef : ∀ i, e i + 2 * c i + f i = m i := by
    intro i
    dsimp [c, f]
    have := Nat.mod_add_div (m i - e i) 2
    have := hm i
    have := he i
    omega
  have hf : ∀ i, f i ≤ 1 := by
    intro i
    dsimp [f]
    omega
  have htotal : (∑ i, e i) + 2 * (∑ i, c i) + (∑ i, f i) = k + l := by
    calc
      _ = ∑ i, (e i + 2 * c i + f i) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ i, m i := Finset.sum_congr rfl (fun i _ => hef i)
      _ = k + l := hsum
  have hE : (∑ i, e i) ≤ k := bit_sum_le e he hdk hpar
  have hFpar : (∑ i, f i) % 2 = l % 2 := by omega
  have hF : (∑ i, f i) ≤ l := bit_sum_le f hf hdl hFpar
  have hK : k = (∑ i, e i) + 2 * ((k - ∑ i, e i) / 2) := by omega
  have hcap : (k - ∑ i, e i) / 2 ≤ ∑ i, c i := by omega
  obtain ⟨u, hu, husum⟩ := allocate_le_sum Finset.univ c ((k - ∑ i, e i) / 2) hcap
  let a : Fin (d + 1) → ℕ := fun i => e i + 2 * u i
  have ha : ∀ i, a i ≤ m i := by
    intro i
    have := hu i (Finset.mem_univ i)
    have := hef i
    dsimp [a]
    omega
  refine ⟨a, fun i => m i - a i, ?_, ?_, ?_, ?_⟩
  · intro i
    change a i + (m i - a i) = m i
    have := ha i
    omega
  · dsimp [a]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, husum]
    omega
  · have hasum : ∑ i, a i = k := by
      dsimp [a]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, husum]
      omega
    rw [Finset.sum_tsub_distrib Finset.univ (fun i _ => ha i), hsum, hasum]
    omega
  · intro i
    have := he i
    dsimp [a]
    omega

/-- Integral points of the standard affine simplex of degree `k`. -/
def NatSimplex {d : ℕ} (k : ℕ) (a : Fin d → ℕ) : Prop := ∑ i, a i ≤ k

/-- Affine-coordinate version of Lemma 4.4, including all dimensions.
The strict inequalities on `m` are exactly the interior inequalities of
`(k + l) Δ_d`. The requested residue vector is unrestricted.
-/
theorem simplex_parity_affine {d k l : ℕ}
    (hdk : d ≤ k) (hdl : d ≤ l)
    (m r : Fin d → ℕ)
    (hm : ∀ i, 0 < m i) (hmsum : (∑ i, m i) < k + l) :
    ∃ a b : Fin d → ℕ,
      NatSimplex k a ∧ NatSimplex l b ∧
      (∀ i, a i + b i = m i) ∧
      (∀ i, a i % 2 = r i % 2) := by
  let e : Fin d → ℕ := fun i => r i % 2
  have he : ∀ i, e i ≤ 1 := by
    intro i
    dsimp [e]
    omega
  have hEsum : (∑ i, e i) ≤ k := by
    calc
      (∑ i, e i) ≤ ∑ _ : Fin d, 1 := Finset.sum_le_sum (fun i _ => he i)
      _ = d := by simp
      _ ≤ k := hdk
  let m' : Fin (d + 1) → ℕ := Fin.cons (k + l - ∑ i, m i) m
  let e' : Fin (d + 1) → ℕ := Fin.cons ((k - ∑ i, e i) % 2) e
  have hm' : ∀ i, 0 < m' i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [m', Fin.cons_zero]
      omega
    · simpa [m'] using hm j
  have he' : ∀ i, e' i ≤ 1 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [e', Fin.cons_zero]
      omega
    · simpa [e'] using he j
  have hmsum' : ∑ i, m' i = k + l := by
    simp only [Fin.sum_univ_succ, m', Fin.cons_zero, Fin.cons_succ]
    omega
  have hepar' : (∑ i, e' i) % 2 = k % 2 := by
    simp only [Fin.sum_univ_succ, e', Fin.cons_zero, Fin.cons_succ]
    omega
  obtain ⟨a', b', hab', ha', hb', hpar'⟩ :=
    simplex_parity_homogeneous hdk hdl m' e' hm' he' hmsum' hepar'
  refine ⟨fun i => a' i.succ, fun i => b' i.succ, ?_, ?_, ?_, ?_⟩
  · change (∑ i : Fin d, a' i.succ) ≤ k
    rw [Fin.sum_univ_succ] at ha'
    omega
  · change (∑ i : Fin d, b' i.succ) ≤ l
    rw [Fin.sum_univ_succ] at hb'
    omega
  · intro i
    simpa [m'] using hab' i.succ
  · intro i
    simpa [e', e] using hpar' i.succ

/-- The actual integer-coordinate inequalities for the degree-`k` standard simplex. -/
def IntegerSimplex {d : ℕ} (k : ℕ) (a : Fin d → ℤ) : Prop :=
  (∀ i, 0 ≤ a i) ∧ (∑ i, a i) ≤ k

/-- Coordinate congruence is exactly membership of the difference in the
doubled integer lattice; this identifies the residue condition with `M / 2M`. -/
theorem integer_parity_iff_double {ι : Type*} (a α : ι → ℤ) :
    (∀ i, (a i - α i) % 2 = 0) ↔ ∃ w : ι → ℤ, a - α = w + w := by
  constructor
  · intro h
    refine ⟨fun i => (a i - α i) / 2, ?_⟩
    funext i
    have hi := h i
    simp only [Pi.sub_apply, Pi.add_apply]
    omega
  · rintro ⟨w, hw⟩ i
    have hi := congrFun hw i
    simp only [Pi.sub_apply, Pi.add_apply] at hi
    omega

/-- Natural-coordinate simplex points and their integer embeddings agree exactly. -/
theorem natSimplex_iff_integerSimplex {d k : ℕ} (a : Fin d → ℕ) :
    NatSimplex k a ↔ IntegerSimplex k (fun i => (a i : ℤ)) := by
  simp [NatSimplex, IntegerSimplex, ← Nat.cast_sum]

/-- Lemma 4.4 in the ambient integer lattice, with unrestricted integer parity classes. -/
theorem simplex_parity_integer {d k l : ℕ}
    (hdk : d ≤ k) (hdl : d ≤ l)
    (m α : Fin d → ℤ)
    (hm : ∀ i, 0 < m i) (hmsum : (∑ i, m i) < (k + l : ℕ)) :
    ∃ a b : Fin d → ℤ,
      IntegerSimplex k a ∧ IntegerSimplex l b ∧
      (∀ i, a i + b i = m i) ∧
      (∀ i, (a i - α i) % 2 = 0) := by
  let mN : Fin d → ℕ := fun i => (m i).toNat
  let rN : Fin d → ℕ := fun i => (α i % 2).toNat
  have hmN : ∀ i, 0 < mN i := by
    intro i
    dsimp [mN]
    have h := hm i
    omega
  have hmcast : ∀ i, (mN i : ℤ) = m i := by
    intro i
    dsimp [mN]
    exact Int.toNat_of_nonneg (le_of_lt (hm i))
  have hmNsum : (∑ i, mN i) < k + l := by
    have hsumcast : ((∑ i, mN i : ℕ) : ℤ) = ∑ i, m i := by
      simp only [Nat.cast_sum, hmcast]
    omega
  obtain ⟨aN, bN, haN, hbN, habN, hparN⟩ :=
    simplex_parity_affine hdk hdl mN rN hmN hmNsum
  refine ⟨fun i => (aN i : ℤ), fun i => (bN i : ℤ),
    (natSimplex_iff_integerSimplex aN).mp haN,
    (natSimplex_iff_integerSimplex bN).mp hbN, ?_, ?_⟩
  · intro i
    change (aN i : ℤ) + (bN i : ℤ) = m i
    have h := habN i
    have hc := hmcast i
    omega
  · intro i
    change ((aN i : ℤ) - α i) % 2 = 0
    have h := hparN i
    have hr : (rN i : ℤ) = α i % 2 := by
      dsimp [rN]
      exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
    omega

end PaperVerification.Toric
end Source_ToricSimplexParity
-- END ORIGINAL PaperVerification.ToricSimplexParity


-- BEGIN ORIGINAL PaperVerification.ToricSimplexGeometry
section Source_ToricSimplexGeometry

-- original header: module
-- original header: public import PaperVerification.ToricSimplexParity
-- original header: public import Mathlib.Analysis.Normed.Operator.Banach
-- original header: public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
-- original header: public import Mathlib.Topology.Instances.Real.Lemmas
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Analysis.Convex.Combination
-- original header: public import Mathlib.Tactic.FieldSimp
-- original header: public import Mathlib.Tactic.Positivity
-- original header: public import Mathlib.Tactic.Ring
-- original header: @[expose] public section
/-!
# Geometric correspondence for the simplex allocation theorem

Standard simplices are defined by their usual real coordinate inequalities.
Their actual topological interiors and integer points are related here to
`simplex_parity_integer`; in particular, no interior hypothesis is replaced
by an unexplained arithmetic proxy.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped BigOperators Pointwise

/-- The standard degree-`k` simplex in real affine coordinates. -/
def RealSimplex (d : ℕ) (k : ℝ) : Set (Fin d → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ k}

/-- The coordinate simplex is precisely the convex hull of the origin and scaled
standard basis vectors. This identifies `RealSimplex d k` with the paper's `k Δ_d`. -/
theorem realSimplex_eq_convexHull {d : ℕ} {k : ℝ} (hk : 0 < k) :
    RealSimplex d k =
      convexHull ℝ (insert (0 : Fin d → ℝ) (Set.range fun i => Pi.single i k)) := by
  have hconv : Convex ℝ (RealSimplex d k) := by
    intro x hx y hy a b ha hb hab
    refine ⟨fun i => add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i)), ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    have hx' := mul_le_mul_of_nonneg_left hx.2 ha
    have hy' := mul_le_mul_of_nonneg_left hy.2 hb
    nlinarith
  have hverts : insert (0 : Fin d → ℝ) (Set.range fun i => Pi.single i k) ⊆
      RealSimplex d k := by
    rintro x (rfl | ⟨i, rfl⟩)
    · exact ⟨fun _ => le_rfl, by simpa using hk.le⟩
    · refine ⟨?_, ?_⟩
      · intro j
        simp only [Pi.single_apply]
        split_ifs <;> positivity
      · simp
  refine Set.Subset.antisymm ?_ (convexHull_min hverts hconv)
  intro x hx
  let w : Fin (d + 1) → ℝ := Fin.cons (1 - (∑ i, x i) / k) (fun i => x i / k)
  let v : Fin (d + 1) → (Fin d → ℝ) := Fin.cons 0 (fun i => Pi.single i k)
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change 0 ≤ 1 - (∑ i, x i) / k
      exact sub_nonneg.mpr ((div_le_one hk).mpr hx.2)
    · change 0 ≤ x j / k
      exact div_nonneg (hx.1 j) hk.le
  have hwsum : ∑ i, w i = 1 := by
    simp only [Fin.sum_univ_succ, w, Fin.cons_zero, Fin.cons_succ,
      ← Finset.sum_div]
    ring
  have hv : ∀ i, v i ∈ insert (0 : Fin d → ℝ) (Set.range fun i => Pi.single i k) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Set.mem_insert 0 _
    · exact Set.mem_insert_of_mem _ (Set.mem_range_self j)
  have hwv : ∑ i, w i • v i = x := by
    ext j
    simp [Fin.sum_univ_succ, w, v, Pi.single_apply, Finset.sum_apply, hk.ne']
  exact mem_convexHull_of_exists_fintype w v hw hwsum hv hwv

private def coordinateSum (d : ℕ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ i, ContinuousLinearMap.proj i

@[simp] private theorem coordinateSum_apply {d : ℕ} (x : Fin d → ℝ) :
    coordinateSum d x = ∑ i, x i := by
  simp [coordinateSum]

/-- Topological interior of the positive-dimensional standard simplex. -/
theorem interior_realSimplex (d : ℕ) (k : ℝ) :
    interior (RealSimplex (d + 1) k) =
      {x | (∀ i, 0 < x i) ∧ ∑ i, x i < k} := by
  have hcoord (i : Fin (d + 1)) :
      interior {x : Fin (d + 1) → ℝ | 0 ≤ x i} = {x | 0 < x i} := by
    have h :=
      ((isOpenMap_eval (X := fun _ : Fin (d + 1) => ℝ) i).preimage_interior_eq_interior_preimage
        (continuous_apply i) (Set.Ici (0 : ℝ))).symm
    rw [interior_Ici] at h
    simpa only [Set.preimage, Set.Ici, Set.Ioi, Function.eval, Set.mem_setOf_eq] using h
  have hsurj : Function.Surjective (coordinateSum (d + 1)) := by
    intro y
    exact ⟨Pi.single 0 y, by simp⟩
  have hsum :
      interior {x : Fin (d + 1) → ℝ | ∑ i, x i ≤ k} = {x | ∑ i, x i < k} := by
    have h :=
      ((coordinateSum (d + 1)).isOpenMap hsurj).preimage_interior_eq_interior_preimage
        (coordinateSum (d + 1)).continuous (Set.Iic k) |>.symm
    rw [interior_Iic] at h
    simpa only [Set.preimage, Set.Iic, Set.Iio, coordinateSum_apply, Set.mem_setOf_eq] using h
  have hset : RealSimplex (d + 1) k =
      (⋂ i, {x : Fin (d + 1) → ℝ | 0 ≤ x i}) ∩ {x | ∑ i, x i ≤ k} := by
    ext x
    simp [RealSimplex]
  rw [hset, interior_inter, interior_iInter_of_finite]
  simp_rw [hcoord, hsum]
  ext x
  simp

/-- Every point of the Minkowski sum satisfies the combined simplex inequalities. -/
theorem add_realSimplex_subset (d : ℕ) (k l : ℝ) :
    RealSimplex d k + RealSimplex d l ⊆ RealSimplex d (k + l) := by
  rintro x ⟨a, ha, b, hb, rfl⟩
  refine ⟨fun i => add_nonneg (ha.1 i) (hb.1 i), ?_⟩
  simpa only [Pi.add_apply, Finset.sum_add_distrib] using add_le_add ha.2 hb.2

/-- The integer and real coordinate definitions agree under the canonical embedding. -/
theorem integerSimplex_iff_realSimplex {d k : ℕ} (a : Fin d → ℤ) :
    IntegerSimplex k a ↔ (fun i => (a i : ℝ)) ∈ RealSimplex d k := by
  constructor
  · rintro ⟨ha, hs⟩
    refine ⟨fun i => Int.cast_nonneg_iff.mpr (ha i), ?_⟩
    have h : ((∑ i, a i : ℤ) : ℝ) ≤ ((k : ℤ) : ℝ) := Int.cast_le.mpr hs
    simpa only [Int.cast_sum, Int.cast_natCast] using h
  · rintro ⟨ha, hs⟩
    refine ⟨fun i => Int.cast_nonneg_iff.mp (ha i), ?_⟩
    have h : ((∑ i, a i : ℤ) : ℝ) ≤ ((k : ℤ) : ℝ) := by
      simpa only [Int.cast_sum, Int.cast_natCast] using hs
    exact Int.cast_le.mp h

/-- Lemma 4.4 stated with actual real simplices, topological interior of their
Minkowski sum, and the full integer lattice in every positive dimension. -/
theorem simplex_parity_topological {d k l : ℕ}
    (hd : 0 < d) (hdk : d ≤ k) (hdl : d ≤ l)
    (m α : Fin d → ℤ)
    (hm : (fun i => (m i : ℝ)) ∈
      interior (RealSimplex d k + RealSimplex d l)) :
    ∃ a b : Fin d → ℤ,
      (fun i => (a i : ℝ)) ∈ RealSimplex d k ∧
      (fun i => (b i : ℝ)) ∈ RealSimplex d l ∧
      (∀ i, a i + b i = m i) ∧
      (∀ i, (a i - α i) % 2 = 0) := by
  cases d with
  | zero => omega
  | succ d =>
      have hm' := interior_mono (add_realSimplex_subset (d + 1) k l) hm
      rw [interior_realSimplex] at hm'
      have hmpos : ∀ i, 0 < m i := by
        intro i
        have h : (0 : ℝ) < (m i : ℝ) := hm'.1 i
        exact Int.cast_pos.mp h
      have hmsum : (∑ i, m i) < (k + l : ℕ) := by
        have h := hm'.2
        push_cast at h ⊢
        exact_mod_cast h
      obtain ⟨a, b, ha, hb, hab, hpar⟩ :=
        simplex_parity_integer hdk hdl m α hmpos hmsum
      exact ⟨a, b, (integerSimplex_iff_realSimplex a).mp ha,
        (integerSimplex_iff_realSimplex b).mp hb, hab, hpar⟩

end PaperVerification.Toric
end
end Source_ToricSimplexGeometry
-- END ORIGINAL PaperVerification.ToricSimplexGeometry


-- BEGIN ORIGINAL PaperVerification.ToricCornerBoxes
section Source_ToricCornerBoxes

-- original header: module
-- original header: public import PaperVerification.ToricSimplexGeometry
-- original header: public import PaperVerification.ToricBoxAverages
-- original header: public import Mathlib.Algebra.Module.LinearMap.End
-- original header: public import Mathlib.LinearAlgebra.Basis.Defs
-- original header: public import Mathlib.Tactic.Positivity
-- original header: @[expose] public section
/-!
# Unit corner boxes and their facet-center slack

The unit-box assertion needed for integer decomposition follows directly from
convexity and long edge segments. It does not require contraction theory.
The second part proves the half-integral facet slack of every contained unit
basis box, which is the Cartier-center estimate in Lemma 4.2.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A simplex of edge extent `r` contains every nonnegative coordinate
combination with total coordinate sum at most `r`. -/
theorem corner_simplex_mem {d : ℕ} (A : Set E) (hA : Convex ℝ A) (p : E) (hp : p ∈ A)
    (v : Fin d → E) (r : ℝ) (hr : 0 < r) (hv : ∀ i, p + r • v i ∈ A)
    (t : Fin d → ℝ) (ht : ∀ i, 0 ≤ t i) (hsum : ∑ i, t i ≤ r) :
    p + ∑ i, t i • v i ∈ A := by
  let L : (Fin d → ℝ) →ₗ[ℝ] E := ∑ i, (LinearMap.proj i).smulRight (v i)
  have hL (x : Fin d → ℝ) : L x = ∑ i, x i • v i := by simp [L]
  let S : Set (Fin d → ℝ) := {x | p + L x ∈ A}
  have hS : Convex ℝ S := (hA.translate_preimage_right p).linear_preimage L
  have hverts : insert (0 : Fin d → ℝ) (Set.range fun i => Pi.single i r) ⊆ S := by
    rintro x (rfl | ⟨i, rfl⟩)
    · simpa [S] using hp
    · simpa [S, L, Pi.single_apply] using hv i
  have htSimplex : t ∈ RealSimplex d r := ⟨ht, hsum⟩
  rw [realSimplex_eq_convexHull hr] at htSimplex
  have hmem := convexHull_min hverts hS htSimplex
  simpa [S, hL] using hmem

/-- Any convex body containing `d` long outgoing edge segments contains their
entire unit corner box. The directions need not be linearly independent for
this convexity statement. -/
theorem unit_corner_box_of_long_segments {d : ℕ} (hd : 0 < d)
    (A : Set E) (hA : Convex ℝ A) (p : E) (hp : p ∈ A)
    (v : Fin d → E) (lengths : Fin d → ℝ)
    (hlength : ∀ i, (d : ℝ) ≤ lengths i)
    (hv : ∀ i, p + lengths i • v i ∈ A)
    (t : Fin d → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    p + ∑ i, t i • v i ∈ A := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hv' (i : Fin d) : p + (d : ℝ) • v i ∈ A := by
    have hlen : 0 < lengths i := hdR.trans_le (hlength i)
    have hratio : (d : ℝ) / lengths i ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hdR.le hlen.le, (div_le_one hlen).mpr (hlength i)⟩
    have h := hA.lineMap_mem hp (hv i) hratio
    simpa [AffineMap.lineMap_apply_module', smul_smul, hlen.ne', add_comm] using h
  apply corner_simplex_mem A hA p hp v (d : ℝ) hdR hv' t (fun i => (ht i).1)
  calc
    (∑ i, t i) ≤ ∑ _ : Fin d, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => (ht i).2)
    _ = d := by simp

/-- A contained centered unit box forces the stated slack for any supporting
affine functional. -/
theorem unit_box_center_slack {ι : Type*} [Fintype ι]
    (f : E →ᵃ[ℝ] ℝ) (c : E) (v : ι → E)
    (hbox : ∀ t : ι → ℝ, (∀ i, |t i| ≤ 1 / 2) →
      0 ≤ f (c + ∑ i, t i • v i)) :
    (∑ i, |f.linear (v i)|) / 2 ≤ f c := by
  let t : ι → ℝ := fun i => if 0 ≤ f.linear (v i) then -(1 / 2) else 1 / 2
  have ht : ∀ i, |t i| ≤ 1 / 2 := by
    intro i
    dsimp [t]
    split_ifs <;> norm_num
  have hterm (i : ι) : t i * f.linear (v i) = -(|f.linear (v i)| / 2) := by
    by_cases hi : 0 ≤ f.linear (v i)
    · simp [t, hi, abs_of_nonneg hi] <;> ring
    · simp [t, hi, abs_of_neg (lt_of_not_ge hi)] <;> ring
  have hf : f (c + ∑ i, t i • v i) = f c + ∑ i, t i * f.linear (v i) := by
    rw [add_comm]
    change f ((∑ i, t i • v i) +ᵥ c) = _
    rw [AffineMap.map_vadd]
    simp [map_sum, map_smul, vadd_eq_add, smul_eq_mul, add_comm]
  have h := hbox t ht
  rw [hf] at h
  simp only [hterm, Finset.sum_neg_distrib, ← Finset.sum_div] at h
  linarith

/-- An integral, nonzero normal has total absolute coefficient at least one
on every genuine real basis on which it takes integer values. -/
theorem integral_basis_normal_abs_sum {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (f : E →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (z : ι → ℤ) (hz : ∀ i, (z i : ℝ) = f (b i)) :
    1 ≤ ∑ i, |f (b i)| := by
  have hne : ∃ i, f (b i) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hf
    exact b.ext (fun i => by simpa using h i)
  obtain ⟨i, hi⟩ := hne
  have hzi : z i ≠ 0 := by
    intro hzero
    apply hi
    rw [← hz i, hzero, Int.cast_zero]
  have hziabs : (1 : ℤ) ≤ |z i| := Int.one_le_abs hzi
  have hiabs : (1 : ℝ) ≤ |f (b i)| := by
    rw [← hz i]
    exact_mod_cast hziabs
  have hsum : |f (b i)| ≤ ∑ j, |f (b j)| :=
    Finset.single_le_sum (f := fun j => |f (b j)|)
      (fun j _ => abs_nonneg (f (b j))) (Finset.mem_univ i)
  exact hiabs.trans hsum

/-- The center slack estimate of Lemma 4.2 for every nonzero integral facet
normal: a contained unit basis box has center slack at least one half. -/
theorem integral_unit_box_center_slack {ι : Type*} [Fintype ι]
    (f : E →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (c : E) (b : Module.Basis ι ℝ E)
    (z : ι → ℤ) (hz : ∀ i, (z i : ℝ) = f.linear (b i))
    (hbox : ∀ t : ι → ℝ, (∀ i, |t i| ≤ 1 / 2) →
      0 ≤ f (c + ∑ i, t i • b i)) :
    1 / 2 ≤ f c := by
  have h₁ := unit_box_center_slack f c b hbox
  have h₂ := integral_basis_normal_abs_sum b f.linear hf z hz
  linarith

end PaperVerification.Toric
end
end Source_ToricCornerBoxes
-- END ORIGINAL PaperVerification.ToricCornerBoxes


-- BEGIN ORIGINAL PaperVerification.ToricFaces
section Source_ToricFaces

-- original header: module
-- original header: public import PaperVerification.ToricCriterion
-- original header: public import Mathlib.Analysis.Convex.Extreme
-- original header: public import Mathlib.Analysis.Convex.Intrinsic
-- original header: public import Mathlib.Topology.Order.LeftRight
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.FieldSimp
-- original header: @[expose] public section
/-!
# Actual faces and the hypotheses of Proposition 2.1

This file derives the exchange criterion from statements about genuine convex faces,
relative interiors, and affine half-space descriptions. The face index used by the
exchange proof is computed from the active inequalities. Globally vanishing
inequalities are removed, so the construction also works for lower-dimensional sets.
-/

noncomputable section

namespace PaperVerification.ToricExchange

open Set Filter
open scoped Pointwise Topology

variable {M V ι : Type*} [AddCommGroup M]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Relative interior commutes with any nonzero real dilation. -/
theorem intrinsicInterior_smul (c : ℝ) (hc : c ≠ 0) (F : Set V) :
    intrinsicInterior ℝ (c • F) = c • intrinsicInterior ℝ F := by
  let e : V ≃ᵃ[ℝ] V := (LinearEquiv.smulOfNeZero ℝ V c hc).toAffineEquiv
  exact e.intrinsicInterior_image F

/-- A nonnegative affine functional vanishing at a relative-interior point
vanishes on the whole set. No continuity of the functional is required. -/
theorem affine_zero_on_of_intrinsicInterior (F : Set V) (f : V →ᵃ[ℝ] ℝ)
    (hnonneg : ∀ y ∈ F, 0 ≤ f y) {x : V}
    (hx : x ∈ intrinsicInterior ℝ F) (hfx : f x = 0) :
    ∀ y ∈ F, f y = 0 := by
  rcases mem_intrinsicInterior.mp hx with ⟨xA, hxA, rfl⟩
  letI : Nonempty (affineSpan ℝ F) := ⟨xA⟩
  intro y hy
  let yA : affineSpan ℝ F := ⟨y, subset_affineSpan ℝ F hy⟩
  have hline : Tendsto (AffineMap.lineMap xA yA : ℝ → affineSpan ℝ F)
      (𝓝 0) (𝓝 xA) := by
    simpa only [ContinuousAt, AffineMap.lineMap_apply_zero] using
      (AffineMap.lineMap_continuous (p := xA) (q := yA)).continuousAt (x := (0 : ℝ))
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, (AffineMap.lineMap xA yA t : V) ∈ F :=
    hline.eventually (mem_interior_iff_mem_nhds.mp hxA)
  obtain ⟨t, ht, htF⟩ := hevent.exists_lt
  have hvalue : f (AffineMap.lineMap xA yA t : V) = t * f y := by
    change (f.comp (affineSpan ℝ F).subtype) (AffineMap.lineMap xA yA t) = _
    rw [AffineMap.apply_lineMap]
    simp [AffineMap.lineMap_apply_module, hfx, yA, smul_eq_mul]
  have hn := hnonneg _ htF
  rw [hvalue] at hn
  have hy0 := hnonneg y hy
  nlinarith

/-- An actual face containing a relative-interior point contains the entire
set whose relative interior is being taken. This proves the minimal-face property
without assuming a combinatorial face poset. -/
theorem subset_extreme_of_intrinsicInterior_mem {P F G : Set V}
    (hFP : F ⊆ P) (hG : IsExtreme ℝ P G) {x : V}
    (hxF : x ∈ intrinsicInterior ℝ F) (hxG : x ∈ G) : F ⊆ G := by
  rcases mem_intrinsicInterior.mp hxF with ⟨xA, hxA, rfl⟩
  letI : Nonempty (affineSpan ℝ F) := ⟨xA⟩
  intro y hy
  let yA : affineSpan ℝ F := ⟨y, subset_affineSpan ℝ F hy⟩
  have hline : Tendsto (AffineMap.lineMap xA yA : ℝ → affineSpan ℝ F)
      (𝓝 0) (𝓝 xA) := by
    simpa only [ContinuousAt, AffineMap.lineMap_apply_zero] using
      (AffineMap.lineMap_continuous (p := xA) (q := yA)).continuousAt (x := (0 : ℝ))
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, (AffineMap.lineMap xA yA t : V) ∈ F :=
    hline.eventually (mem_interior_iff_mem_nhds.mp hxA)
  obtain ⟨t, ht, htF⟩ := hevent.exists_lt
  let z : V := (AffineMap.lineMap xA yA t : V)
  have hz : z = (1 - t) • (xA : V) + t • y := by
    change (affineSpan ℝ F).subtype (AffineMap.lineMap xA yA t) = _
    rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
    rfl
  have hden : 0 < 1 - t := by linarith
  have hab : (-t / (1 - t)) + 1 / (1 - t) = 1 := by
    field_simp [ne_of_gt hden] <;> ring
  have hbx : (1 / (1 - t)) * (1 - t) = 1 := by field_simp [ne_of_gt hden]
  have hay : (-t / (1 - t)) + (1 / (1 - t)) * t = 0 := by ring
  have hxseg : (xA : V) ∈ openSegment ℝ y z := by
    refine ⟨-t / (1 - t), 1 / (1 - t), div_pos (neg_pos.mpr ht) hden,
      div_pos zero_lt_one hden, hab, ?_⟩
    calc
      (-t / (1 - t)) • y + (1 / (1 - t)) • z =
          ((1 / (1 - t)) * (1 - t)) • (xA : V) +
            ((-t / (1 - t)) + (1 / (1 - t)) * t) • y := by rw [hz]; module
      _ = (xA : V) := by rw [hbx, hay]; simp
  exact hG.left_mem_of_mem_openSegment (hFP hy) (hFP htF) hxG hxseg

/-- A finite affine half-space system. This is ordinary geometric input, not a
connectivity or decomposition assumption. -/
structure AffineInequalities (ι V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  slack : ι → V →ᵃ[ℝ] ℝ
  continuous_slack : ∀ i, Continuous (slack i)

namespace AffineInequalities

variable (H : AffineInequalities ι V)

/-- The actual intersection of the closed affine half-spaces. -/
def region : Set V := {x | ∀ i, 0 ≤ H.slack i x}

/-- The face obtained by making the listed inequalities equalities. -/
def face (J : Set ι) : Set V :=
  {x | x ∈ H.region ∧ ∀ i ∈ J, H.slack i x = 0}

/-- Inequalities that are not identically zero on the region. -/
def informative (i : ι) : Prop := ∃ y ∈ H.region, H.slack i y ≠ 0

/-- Active, informative inequalities. Constant zero constraints are discarded. -/
def active (x : V) : Set ι := {i | H.slack i x = 0 ∧ H.informative i}

/-- All constraints vanishing at both points, including constant constraints. -/
def jointZeros (a b : V) : Set ι := {i | H.slack i a = 0 ∧ H.slack i b = 0}

theorem convex_region : Convex ℝ H.region := by
  intro x hx y hy a b ha hb hab i
  rw [Convex.combo_affine_apply hab]
  exact add_nonneg (smul_nonneg ha (hx i)) (smul_nonneg hb (hy i))

theorem convex_face (J : Set ι) : Convex ℝ (H.face J) := by
  intro x hx y hy a b ha hb hab
  refine ⟨H.convex_region hx.1 hy.1 ha hb hab, ?_⟩
  intro i hi
  rw [Convex.combo_affine_apply hab, hx.2 i hi, hy.2 i hi]
  simp

theorem isExtreme_face (J : Set ι) : IsExtreme ℝ H.region (H.face J) := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  rintro x hx y hy z hz ⟨a, b, ha, hb, hab, he⟩
  refine ⟨hx, ?_⟩
  intro i hi
  have hzero := hz.2 i hi
  rw [← he, Convex.combo_affine_apply hab] at hzero
  have hx0 := hx i
  have hy0 := hy i
  simp only [smul_eq_mul] at hzero
  nlinarith

theorem slack_eq_zero_on_affineSpan {J : Set ι} {i : ι} (hi : i ∈ J)
    {x : V} (hx : x ∈ affineSpan ℝ (H.face J)) : H.slack i x = 0 := by
  refine affineSpan_induction (p := fun y => H.slack i y = 0) hx ?_ ?_
  · intro y hy
    exact hy.2 i hi
  · intro c u v w hu hv hw
    rw [AffineMap.map_vadd, map_smul, AffineMap.linear_apply_vsub]
    simp [hu, hv, hw]

/-- Strictness of all unselected constraints is an explicit open neighborhood
inside the affine span of the face. -/
theorem mem_intrinsicInterior_face_of_strict [Finite ι] {J : Set ι} {x : V}
    (hx : x ∈ H.face J) (hstrict : ∀ i ∉ J, 0 < H.slack i x) :
    x ∈ intrinsicInterior ℝ (H.face J) := by
  let xA : affineSpan ℝ (H.face J) := ⟨x, subset_affineSpan ℝ (H.face J) hx⟩
  let U : Set (affineSpan ℝ (H.face J)) :=
    ⋂ i : {i : ι // i ∉ J}, {y | 0 < H.slack i.1 (y : V)}
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const ((H.continuous_slack i.1).comp continuous_subtype_val)
  have hxU : xA ∈ U := by
    exact mem_iInter.mpr fun i => hstrict i.1 i.2
  have hUF : U ⊆ ((↑) ⁻¹' H.face J : Set (affineSpan ℝ (H.face J))) := by
    intro y hy
    refine ⟨?_, ?_⟩
    · intro i
      by_cases hi : i ∈ J
      · exact le_of_eq (H.slack_eq_zero_on_affineSpan hi y.property).symm
      · exact le_of_lt (mem_iInter.mp hy ⟨i, hi⟩)
    · intro i hi
      exact H.slack_eq_zero_on_affineSpan hi y.property
  refine mem_intrinsicInterior.mpr ⟨xA, ?_, rfl⟩
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hU.mem_nhds hxU) hUF)

theorem midpoint_mem_face {a b : V} (ha : a ∈ H.region) (hb : b ∈ H.region) :
    (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b ∈ H.face (H.jointZeros a b) := by
  apply H.convex_face (H.jointZeros a b)
    ⟨ha, fun _ hi => hi.1⟩ ⟨hb, fun _ hi => hi.2⟩ <;> norm_num

/-- The midpoint of a pair lies in the relative interior of its genuine active face. -/
theorem midpoint_mem_intrinsicInterior_face [Finite ι] {a b : V}
    (ha : a ∈ H.region) (hb : b ∈ H.region) :
    (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b ∈
      intrinsicInterior ℝ (H.face (H.jointZeros a b)) := by
  apply H.mem_intrinsicInterior_face_of_strict (H.midpoint_mem_face ha hb)
  intro i hi
  rw [Convex.combo_affine_apply (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)]
  have ha0 := ha i
  have hb0 := hb i
  have hne : H.slack i a ≠ 0 ∨ H.slack i b ≠ 0 := by
    by_cases hia : H.slack i a = 0
    · exact Or.inr (fun hib => hi ⟨hia, hib⟩)
    · exact Or.inl hia
  simp only [smul_eq_mul]
  rcases hne with hne | hne
  · have hpos : 0 < H.slack i a := lt_of_le_of_ne ha0 hne.symm
    linarith
  · have hpos : 0 < H.slack i b := lt_of_le_of_ne hb0 hne.symm
    linarith

/-- Relative-interior points of the pair's face have precisely the common active
constraints. This is the exact minimal-face fact used in the exchange argument. -/
theorem active_eq_of_intrinsicInterior_jointFace {a b u : V}
    (ha : a ∈ H.region) (hb : b ∈ H.region)
    (hu : u ∈ intrinsicInterior ℝ (H.face (H.jointZeros a b))) :
    H.active u = H.active a ∩ H.active b := by
  have huF := intrinsicInterior_subset hu
  have hzero (i : ι) : H.slack i u = 0 ↔ H.slack i a = 0 ∧ H.slack i b = 0 := by
    constructor
    · intro hi
      have hz := affine_zero_on_of_intrinsicInterior (H.face (H.jointZeros a b))
        (H.slack i) (fun y hy => hy.1 i) hu hi
      exact ⟨hz a ⟨ha, fun _ h => h.1⟩, hz b ⟨hb, fun _ h => h.2⟩⟩
    · exact fun hi => huF.2 i hi
  ext i
  constructor
  · rintro ⟨hi, hinf⟩
    have hp := (hzero i).mp hi
    exact ⟨⟨hp.1, hinf⟩, ⟨hp.2, hinf⟩⟩
  · rintro ⟨⟨ha0, hinf⟩, ⟨hb0, _⟩⟩
    exact ⟨(hzero i).mpr ⟨ha0, hb0⟩, hinf⟩

theorem mem_jointFace_of_active_subset {a b c : V}
    (hc : c ∈ H.region) (h : H.active a ∩ H.active b ⊆ H.active c) :
    c ∈ H.face (H.jointZeros a b) := by
  refine ⟨hc, ?_⟩
  intro i hi
  by_cases hinf : H.informative i
  · exact (h ⟨⟨hi.1, hinf⟩, ⟨hi.2, hinf⟩⟩).1
  · by_contra hn
    exact hinf ⟨c, hc, hn⟩

theorem jointFace_ne_region_of_active_ne_empty {a b : V}
    (h : H.active a ∩ H.active b ≠ ∅) : H.face (H.jointZeros a b) ≠ H.region := by
  obtain ⟨i, hi⟩ := Set.nonempty_iff_ne_empty.mpr h
  obtain ⟨y, hy, hne⟩ := hi.1.2
  intro he
  have hyF : y ∈ H.face (H.jointZeros a b) := by simpa only [he] using hy
  exact hne (hyF.2 i ⟨hi.1.1, hi.2.1⟩)


/-- The common-active face is the smallest actual convex face containing the pair. -/
theorem jointFace_minimal [Finite ι] {a b : V}
    (ha : a ∈ H.region) (hb : b ∈ H.region) {G : Set V}
    (hGconvex : Convex ℝ G) (hG : IsExtreme ℝ H.region G)
    (haG : a ∈ G) (hbG : b ∈ G) : H.face (H.jointZeros a b) ⊆ G := by
  apply subset_extreme_of_intrinsicInterior_mem
    (H.isExtreme_face _).subset hG (H.midpoint_mem_intrinsicInterior_face ha hb)
  exact hGconvex haG hbG (by norm_num) (by norm_num) (by norm_num)

/-- Every nonempty convex face is exactly an active-inequality face. This ensures
that the affine-inequality description captures all geometric faces. -/
theorem exists_activeFace_eq [Finite ι] {G : Set V}
    (hGconvex : Convex ℝ G) (hG : IsExtreme ℝ H.region G) (hGne : G.Nonempty) :
    ∃ x ∈ G, G = H.face (H.jointZeros x x) := by
  obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior hGconvex hGne
  have hxG := intrinsicInterior_subset hx
  have hxP := hG.subset hxG
  have hxF : x ∈ intrinsicInterior ℝ (H.face (H.jointZeros x x)) := by
    have h := H.midpoint_mem_intrinsicInterior_face hxP hxP
    have he : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x = x := by module
    simpa only [he] using h
  refine ⟨x, hxG, Set.Subset.antisymm ?_ ?_⟩
  · exact subset_extreme_of_intrinsicInterior_mem hG.subset (H.isExtreme_face _) hx
      (intrinsicInterior_subset hxF)
  · exact subset_extreme_of_intrinsicInterior_mem (H.isExtreme_face _).subset hG hxF hxG

end AffineInequalities

/-- Prescribed parity on every actual face, including every lattice point of its
saturated affine span as a parity representative. This is Proposition 2.1(i). -/
def FaceParity (embedding : M →+ V) (P : Set V) : Prop :=
  ∀ F : Set V, Convex ℝ F → IsExtreme ℝ P F →
    ∀ z : M, embedding z ∈ intrinsicInterior ℝ ((2 : ℝ) • F) →
    ∀ c : M, embedding c ∈ affineSpan ℝ F →
      ∃ p q : M, embedding p ∈ F ∧ embedding q ∈ F ∧ p + q = z ∧ SameParity p c

/-- Adjoint decomposition on every actual proper face. This is Proposition 2.1(ii). -/
def FaceAdjoint (embedding : M →+ V) (P : Set V) : Prop :=
  ∀ F : Set V, Convex ℝ F → IsExtreme ℝ P F → F ≠ P →
    ∀ z : M, embedding z ∈ intrinsicInterior ℝ ((2 : ℝ) • F) →
      ∃ p q : M, embedding p ∈ F ∧ embedding q ∈ intrinsicInterior ℝ F ∧ p + q = z

/-- The sum of two lattice points belongs to the relative interior of twice their
active face. This proves the passage from a pair to the literal hypothesis of (i)/(ii). -/
theorem pair_sum_mem_intrinsicInterior_twice_face [Finite ι]
    (H : AffineInequalities ι V) (embedding : M →+ V)
    (a b : latticePoints embedding H.region) :
    embedding ((a : M) + b) ∈ intrinsicInterior ℝ
      ((2 : ℝ) • H.face (H.jointZeros (embedding a) (embedding b))) := by
  rw [intrinsicInterior_smul 2 (by norm_num)]
  refine ⟨(1 / 2 : ℝ) • embedding a + (1 / 2 : ℝ) • embedding b,
    H.midpoint_mem_intrinsicInterior_face a.property b.property, ?_⟩
  rw [map_add]
  dsimp only
  rw [two_smul, add_add_add_comm, ← add_smul, ← add_smul]
  norm_num

/-- Proposition 2.1's triple reduction for an actual finitely described polyhedron.
The hypotheses are the literal relative-interior, face-parity, and adjoint statements;
all intermediate face relations are derived from its affine inequalities. -/
theorem tripleReduction_of_face_parity_adjoint [Finite ι]
    (H : AffineInequalities ι V) (embedding : M →+ V)
    (hparity : FaceParity embedding H.region) (hadjoint : FaceAdjoint embedding H.region) :
    TripleReduction (latticePoints embedding H.region) := by
  let faceIndex : latticePoints embedding H.region → (Set ι)ᵒᵈ :=
    fun a => H.active (embedding a)
  apply tripleReduction_of_convex_face_data embedding H.region H.convex_region faceIndex
  · intro a b c hc
    change H.active (embedding a) ∩ H.active (embedding b) ⊆ H.active (embedding c) at hc
    let F := H.face (H.jointZeros (embedding a) (embedding b))
    have hcF : embedding c ∈ F := H.mem_jointFace_of_active_subset c.property hc
    obtain ⟨p, q, hp, hq, he, hpc⟩ := hparity F (H.convex_face _) (H.isExtreme_face _)
      ((a : M) + b) (pair_sum_mem_intrinsicInterior_twice_face H embedding a b)
      c (subset_affineSpan ℝ F hcF)
    exact ⟨⟨p, hp.1⟩, ⟨q, hq.1⟩, he.symm, hpc⟩
  · intro a b hab
    change H.active (embedding a) ∩ H.active (embedding b) ≠ ∅ at hab
    let F := H.face (H.jointZeros (embedding a) (embedding b))
    obtain ⟨p, q, hp, hq, he⟩ := hadjoint F (H.convex_face _) (H.isExtreme_face _)
      (H.jointFace_ne_region_of_active_ne_empty hab) ((a : M) + b)
      (pair_sum_mem_intrinsicInterior_twice_face H embedding a b)
    have hqF : embedding q ∈ F := intrinsicInterior_subset hq
    refine ⟨⟨q, hqF.1⟩, ⟨p, hp.1⟩, ?_, ?_, ?_⟩
    · simpa only [add_comm] using he.symm
    · exact H.active_eq_of_intrinsicInterior_jointFace a.property b.property hq
    · change H.active (embedding a) ∩ H.active (embedding b) ⊆ H.active (embedding p)
      rintro i ⟨ha, hb⟩
      exact ⟨hp.2 i ⟨ha.1, hb.1⟩, ha.2⟩

/-- The full quadratic-generation conclusion of Proposition 2.1 for every finite
half-space presentation, with genuine faces and no assumed exchange connectivity. -/
theorem quadratic_generation_of_face_parity_adjoint [Finite ι]
    (H : AffineInequalities ι V) (embedding : M →+ V)
    (hidp : IntegerDecompositionProperty embedding H.region)
    (hparity : FaceParity embedding H.region) (hadjoint : FaceAdjoint embedding H.region)
    (R : Type*) [CommRing R] :
    RingHom.ker (paperToricMap (latticePoints embedding H.region) R) =
      polynomialQuadraticIdeal (latticePoints embedding H.region) R :=
  paper_kernel_eq_quadrics (latticePoints embedding H.region) R
    (midpointDecomposition_of_convex_idp embedding H.region H.convex_region hidp)
    (tripleReduction_of_face_parity_adjoint H embedding hparity hadjoint)

end PaperVerification.ToricExchange
end
end Source_ToricFaces
-- END ORIGINAL PaperVerification.ToricFaces


