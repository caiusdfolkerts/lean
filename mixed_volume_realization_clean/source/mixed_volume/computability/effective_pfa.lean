/- Primitive-recursive exact output for the checked seven-state compiler. -/
module

public import mixed_volume.computability.prefix_pfa
public import mixed_volume.computability.rational_primrec

set_option autoImplicit false

@[expose] public section
open Matrix
open scoped BigOperators

namespace MixedVolume.EffectivePFA
open RationalPrimrec QuadraticEncoding SevenState UniformMix PrefixPFA

variable {α : Type*} [Primcodable α]

/-- Every coefficient of the six-dimensional representation is an exact
primitive-recursive rational function of its four scalar inputs. -/
theorem raw_effective {x r y s : α → ℚ}
    (hx : RationalPrimrec x) (hr : RationalPrimrec r)
    (hy : RationalPrimrec y) (hs : RationalPrimrec s) (i j : Fin 6) :
    RationalPrimrec (fun a => raw (x a) (r a) (y a) (s a) i j) := by
  fin_cases i <;> fin_cases j <;> dsimp only [raw, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons]
  all_goals repeat first
    | exact hx
    | exact hr
    | exact hy
    | exact hs
    | exact RationalPrimrec.const _
    | apply RationalPrimrec.mul
    | apply RationalPrimrec.pow

theorem B_effective {u v : α → List Bool} (hu : Primrec u) (hv : Primrec v)
    (i j : Fin 6) : RationalPrimrec (fun a => B (u a) (v a) i j) := by
  exact RationalPrimrec.matrix_mul
    (RationalPrimrec.matrix_mul (fun i j => RationalPrimrec.const (α := α) (inverseS i j))
      (raw_effective (word_value.comp hu) (word_scale.comp hu)
        (word_value.comp hv) (word_scale.comp hv)))
    (fun i j => RationalPrimrec.const (α := α) (S i j)) i j

theorem C_effective {u v : α → List Bool} (hu : Primrec u) (hv : Primrec v)
    (i j : State) : RationalPrimrec (fun a => C (u a) (v a) i j) := by
  cases i with
  | none => cases j <;> exact RationalPrimrec.const _
  | some i =>
    cases j with
    | none =>
      exact (RationalPrimrec.const (α := α) 1).sub
        (finite_sum (fun j => B_effective hu hv i j))
    | some j => exact B_effective hu hv i j

variable {ι : Type*} [Fintype ι]

theorem cap_effective {C : α → ι → M7}
    (hC : ∀ a i j, RationalPrimrec (fun x => C x a i j)) :
    RationalPrimrec (fun x => cap (C x)) :=
  finite_sum (fun a => finite_sum (fun i => finite_sum (fun j => (hC a i j).abs)))

theorem mixing_effective {C : α → ι → M7}
    (hC : ∀ a i j, RationalPrimrec (fun x => C x a i j)) :
    RationalPrimrec (fun x => mixing (C x)) :=
  (RationalPrimrec.const 1).div
    (((RationalPrimrec.const 7).mul (cap_effective hC)).add (RationalPrimrec.const 8))

theorem transition_effective {C : α → ι → M7}
    (hC : ∀ a i j, RationalPrimrec (fun x => C x a i j))
    (a : ι) (i j : State) :
    RationalPrimrec (fun x => transition (C x) a i j) := by
  exact ((mixing_effective hC).mul (hC a i j)).add
    (((RationalPrimrec.const 1).sub (mixing_effective hC)).mul (RationalPrimrec.const _))

theorem family_effective {upper lower : α → ι → List Bool} {u v : α → List Bool}
    (hu : Primrec u) (hv : Primrec v)
    (hU : ∀ a, Primrec (fun x => upper x a))
    (hL : ∀ a, Primrec (fun x => lower x a)) (a : Option ι) (i j : State) :
    RationalPrimrec (fun x => family (upper x) (lower x) (u x) (v x) a i j) := by
  cases a with
  | none => exact C_effective hu hv i j
  | some a => exact C_effective (hU a) (hL a) i j

theorem P_effective {upper lower : α → ι → List Bool} {u v : α → List Bool}
    (hu : Primrec u) (hv : Primrec v)
    (hU : ∀ a, Primrec (fun x => upper x a))
    (hL : ∀ a, Primrec (fun x => lower x a)) (a : ι) (i j : State) :
    RationalPrimrec (fun x => P (upper x) (lower x) (u x) (v x) a i j) :=
  transition_effective (family_effective hu hv hU hL) (some a) i j

theorem initial_effective {upper lower : α → ι → List Bool} {u v : α → List Bool}
    (hu : Primrec u) (hv : Primrec v)
    (hU : ∀ a, Primrec (fun x => upper x a))
    (hL : ∀ a, Primrec (fun x => lower x a)) (j : State) :
    RationalPrimrec (fun x => initial (upper x) (lower x) (u x) (v x) j) :=
  RationalPrimrec.vecMul (fun i => RationalPrimrec.const (α := α) (start i))
    (transition_effective (family_effective hu hv hU hL) none) j

theorem relabel_P_effective {upper lower : α → ι → List Bool} {u v : α → List Bool}
    (hu : Primrec u) (hv : Primrec v)
    (hU : ∀ a, Primrec (fun x => upper x a))
    (hL : ∀ a, Primrec (fun x => lower x a)) (a : ι) (i j : Fin 7) :
    RationalPrimrec (fun x => relabelMatrix (P (upper x) (lower x) (u x) (v x) a) i j) :=
  P_effective hu hv hU hL a (stateEquiv i) (stateEquiv j)

theorem relabel_initial_effective {upper lower : α → ι → List Bool} {u v : α → List Bool}
    (hu : Primrec u) (hv : Primrec v)
    (hU : ∀ a, Primrec (fun x => upper x a))
    (hL : ∀ a, Primrec (fun x => lower x a)) (j : Fin 7) :
    RationalPrimrec (fun x => relabelRow (initial (upper x) (lower x) (u x) (v x)) j) :=
  initial_effective hu hv hU hL (stateEquiv j)

end MixedVolume.EffectivePFA
