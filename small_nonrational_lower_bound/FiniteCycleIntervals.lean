module

public import FiniteCycleCandidates
public import Init.Data.List.Nat.Range

@[expose] public section

/-!
# Boolean interval replay for finite function certificates

An explicit base-n coding is proved to enumerate every function. The
certificate checks Boolean predicates on bounded natural codes, avoiding
the large intermediate proof objects produced by deciding a universally
quantified function type. The resulting statement still quantifies every
function and every injection, without a sampling or bounded-code assumption.
-/

namespace Papers.RationalityTen.FiniteCycleCandidates

/-- Least significant digit is the first coordinate. -/
def encodeFunction {n : ℕ} : {k : ℕ} → (Fin k → Fin n) → ℕ
  | 0, _ => 0
  | k + 1, f => (f 0).val + n * encodeFunction (Fin.tail f)

def decodeFunction (n : ℕ) (hn : 0 < n) : (k : ℕ) → ℕ → Fin k → Fin n
  | 0, _ => fun i => i.elim0
  | k + 1, code => Fin.cons ⟨code % n, Nat.mod_lt _ hn⟩ (decodeFunction n hn k (code / n))

theorem encodeFunction_lt {n k : ℕ} (f : Fin k → Fin n) : encodeFunction f < n ^ k := by
  induction k with
  | zero => simp only [encodeFunction, pow_zero]; decide
  | succ k ih =>
    change (f 0).val + n * encodeFunction (Fin.tail f) < n ^ (k + 1)
    calc
      _ < n + n * encodeFunction (Fin.tail f) := Nat.add_lt_add_right (f 0).isLt _
      _ = n * (encodeFunction (Fin.tail f) + 1) := by
        simp only [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ n * n ^ k := Nat.mul_le_mul_left n (Nat.succ_le_of_lt (ih (Fin.tail f)))
      _ = n ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]

theorem decodeFunction_encode {n k : ℕ} (hn : 0 < n) (f : Fin k → Fin n) :
    decodeFunction n hn k (encodeFunction f) = f := by
  induction k with
  | zero => funext i; exact i.elim0
  | succ k ih =>
    have hmod : ((f 0).val + n * encodeFunction (Fin.tail f)) % n = (f 0).val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (f 0).isLt]
    have hdiv : ((f 0).val + n * encodeFunction (Fin.tail f)) / n =
        encodeFunction (Fin.tail f) := by
      rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt (f 0).isLt, Nat.zero_add]
    change Fin.cons ⟨((f 0).val + n * encodeFunction (Fin.tail f)) % n, _⟩
      (decodeFunction n hn k (((f 0).val + n * encodeFunction (Fin.tail f)) / n)) = f
    have hhead : (⟨((f 0).val + n * encodeFunction (Fin.tail f)) % n,
        Nat.mod_lt _ hn⟩ : Fin n) = f 0 := Fin.ext hmod
    rw [hhead, hdiv, ih]
    exact Fin.cons_self_tail f

def checkCodes (test : ℕ → Bool) (start count : ℕ) : Bool :=
  (List.range' start count).all test

def CodeInterval (test : ℕ → Bool) (lo hi : ℕ) : Prop :=
  ∀ i, lo ≤ i → i < hi → test i = true

theorem codeInterval_of_check (test : ℕ → Bool) (lo count : ℕ)
    (h : checkCodes test lo count = true) : CodeInterval test lo (lo + count) := by
  intro i hlo hi
  exact List.all_eq_true.mp h i (List.mem_range'_1.mpr ⟨hlo, hi⟩)

theorem codeInterval_append (test : ℕ → Bool) (lo middle hi : ℕ)
    (hleft : CodeInterval test lo middle) (hright : CodeInterval test middle hi) :
    CodeInterval test lo hi := by
  intro i hlo hi
  by_cases hm : i < middle
  · exact hleft i hlo hm
  · exact hright i (Nat.le_of_not_gt hm) hi

/-- The natural-code check is a proof for every function, because each
function has its own proved-bounded code and decoding is exact. -/
theorem all_functions_of_code_interval {n k : ℕ} (hn : 0 < n)
    (P : (Fin k → Fin n) → Prop) [DecidablePred P]
    (h : CodeInterval (fun code => decide (P (decodeFunction n hn k code))) 0 (n ^ k)) :
    ∀ f : Fin k → Fin n, P f := by
  intro f
  have hc := of_decide_eq_true (h (encodeFunction f) (Nat.zero_le _) (encodeFunction_lt f))
  simpa only [decodeFunction_encode] using hc

end Papers.RationalityTen.FiniteCycleCandidates
