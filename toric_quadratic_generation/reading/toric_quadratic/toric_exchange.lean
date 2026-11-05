module
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Logic.Relation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.IntervalCases
@[expose] public section
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
