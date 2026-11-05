module

public import Aesop
public import Lean.Elab.Command
public import Lean.Elab.Tactic.Omega
public import Lean.Meta.Basic
public import Lean.PrettyPrinter
public import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.Graph.Maps
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.Graph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Sigma.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Order.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Order.Sum.Order
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.UnitInterval

public import verified.parts.part016
import all verified.parts.part016

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart239
/- Source: Papers/GraphicalZonotopes/BooleanFace.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanFourier
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The three choices in each factor are exactly `1`, `uᵢ`, and `uᵢvᵢ`. -/
def tensorMonomial (a : I → Option Bool) (uv : Cube I × Cube I) : ℝ :=
  ∏ i, match a i with
    | none => 1
    | some false => spin (uv.1 i)
    | some true => spin (uv.1 i)*spin (uv.2 i)

/-- The actual tensor product of the three-dimensional one-part spaces,
realized as a subspace of functions on all independent signs. -/
def tensorSpace : Submodule ℝ ((Cube I × Cube I) → ℝ) :=
  Submodule.span ℝ (Set.range (tensorMonomial (I := I)))

def active (a : I → Option Bool) : Finset I := univ.filter (fun i => (a i).isSome)
def second (a : I → Option Bool) : Finset I := univ.filter (fun i => a i=some true)

theorem second_subset_active (a : I → Option Bool) : second a⊆active a := by
  intro i hi
  simp only [second,mem_filter,mem_univ,true_and] at hi
  simp [active,hi]

theorem tensorMonomial_eq (a : I → Option Bool) (uv : Cube I × Cube I) :
    tensorMonomial a uv=character (active a) uv.1*character (second a) uv.2 := by
  simp only [tensorMonomial,character,← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  cases h : a i with
  | none => simp [active,second,h]
  | some b => cases b <;> simp [active,second,h]

def coordinateChange : (Cube I × Cube I) ≃ (Cube I × Cube I) where
  toFun uv := (uv.1,fun i => Bool.xor (uv.1 i) (uv.2 i))
  invFun uv := (uv.1,fun i => Bool.xor (uv.1 i) (uv.2 i))
  left_inv uv := by
    apply Prod.ext
    · rfl
    · funext i
      change Bool.xor (uv.1 i) (Bool.xor (uv.1 i) (uv.2 i)) = uv.2 i
      cases uv.1 i <;> cases uv.2 i <;> rfl
  right_inv uv := by
    apply Prod.ext
    · rfl
    · funext i
      change Bool.xor (uv.1 i) (Bool.xor (uv.1 i) (uv.2 i)) = uv.2 i
      cases uv.1 i <;> cases uv.2 i <;> rfl

theorem spin_xor (a b : Bool) : spin (Bool.xor a b)=spin a*spin b := by
  cases a <;> cases b <;> norm_num [spin]

/-- This identifies the transformed tensor generators with the paper's
original factors `1,sᵢ₀,sᵢ₁`; the independent-coordinate change is an equivalence. -/
theorem tensorMonomial_coordinateChange (a : I → Option Bool) (s : Cube I × Cube I) :
    tensorMonomial a (coordinateChange s)=
      ∏ i,match a i with
        | none => 1
        | some false => spin (s.1 i)
        | some true => spin (s.2 i) := by
  apply prod_congr rfl
  intro i hi
  cases h : a i with
  | none => rfl
  | some b =>
    cases b
    · rfl
    · change spin (s.1 i)*spin (Bool.xor (s.1 i) (s.2 i))=spin (s.2 i)
      rw [spin_xor,← mul_assoc,spin_mul_self,one_mul]

def HasRestrictedExpansion (p : (Cube I × Cube I) → ℝ) : Prop :=
  ∃ P : Finset I → Cube I → ℝ,(∀ A,DependsOn A (P A)) ∧
    ∀ u v,p (u,v)=∑ A : Finset I,character A u*P A v

theorem tensorMonomial_expansion (a : I → Option Bool) :
    HasRestrictedExpansion (tensorMonomial a) := by
  refine ⟨fun A v => if A=active a then character (second a) v else 0,?_,?_⟩
  · intro A
    by_cases h : A=active a
    · subst A
      simpa using (dependsOn_character (second a)).mono (second_subset_active a)
    · simpa [h] using dependsOn_const A (0 : ℝ)
  · intro u v
    simp [tensorMonomial_eq]

theorem restrictedExpansion_of_mem_tensorSpace {p : (Cube I × Cube I) → ℝ}
    (hp : p∈tensorSpace) : HasRestrictedExpansion p := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨a,rfl⟩ := hp
    exact tensorMonomial_expansion a
  | zero =>
    refine ⟨fun _ _ => 0,fun A => dependsOn_const A 0,?_⟩
    simp
  | add p q hp hq ihp ihq =>
    obtain ⟨P,hP,hp⟩ := ihp
    obtain ⟨Q,hQ,hq⟩ := ihq
    refine ⟨fun A => P A+Q A,fun A => (hP A).add (hQ A),?_⟩
    intro u v
    simp only [Pi.add_apply,hp,hq,mul_add,sum_add_distrib]
  | smul c p hp ih =>
    obtain ⟨P,hP,hp⟩ := ih
    refine ⟨fun A => c • P A,fun A => (hP A).smul c,?_⟩
    intro u v
    simp only [Pi.smul_apply,smul_eq_mul,hp,mul_sum]
    apply sum_congr rfl
    intro A hA
    ring

theorem constant_mem_tensorSpace (c : ℝ) : (fun _ : Cube I × Cube I => c)∈tensorSpace := by
  have h : tensorMonomial (fun _ : I => none)∈tensorSpace :=
    Submodule.subset_span ⟨_,rfl⟩
  convert (tensorSpace (I := I)).smul_mem c h using 1
  funext uv
  simp [tensorMonomial]

theorem full_character_product_mem (B : Finset I) :
    (fun uv : Cube I × Cube I => character univ uv.1*character B uv.2)∈tensorSpace := by
  let a : I → Option Bool := fun i => if i∈B then some true else some false
  have h := (Submodule.subset_span (R := ℝ)
    (s := Set.range (tensorMonomial (I := I))) (⟨a,rfl⟩ : tensorMonomial a∈Set.range tensorMonomial))
  have ha : active a=univ := by
    ext i
    by_cases hi : i ∈ B <;> simp [active,a,hi]
  have hb : second a=B := by ext i; simp [second,a]
  have he : tensorMonomial a = (fun uv : Cube I × Cube I => character univ uv.1*character B uv.2) := by
    funext uv
    rw [tensorMonomial_eq,ha,hb]
  rw [he] at h
  exact h

def phase (G : Cube I → ℝ) (uv : Cube I × Cube I) : ℝ := character univ uv.1*G uv.2
def faceFunction (G : Cube I → ℝ) (uv : Cube I × Cube I) : ℝ := (1+phase G uv)/2

theorem phase_mem_tensorSpace (G : Cube I → ℝ) : phase G∈tensorSpace := by
  obtain ⟨c,hc⟩ := exists_character_expansion G
  have h : (∑ B : Finset I,c B •
      (fun uv : Cube I × Cube I => character univ uv.1*character B uv.2))∈tensorSpace :=
    (tensorSpace (I := I)).sum_mem fun B _ =>
      (tensorSpace (I := I)).smul_mem (c B) (full_character_product_mem B)
  convert h using 1
  funext uv
  simp only [phase,hc,mul_sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply sum_congr rfl
  intro B hB
  ring

theorem faceFunction_mem_tensorSpace (G : Cube I → ℝ) : faceFunction G∈tensorSpace := by
  have h := (tensorSpace (I := I)).smul_mem (1/2 : ℝ)
    ((tensorSpace (I := I)).add_mem (constant_mem_tensorSpace 1) (phase_mem_tensorSpace G))
  convert h using 1
  funext uv
  simp only [faceFunction,Pi.smul_apply,smul_eq_mul,Pi.add_apply]
  ring

/-- Nonfactorization across every nonempty proper partition. The factors are
arbitrary real functions of their respective variables. For a sign-valued
function, any factorization can equivalently be rescaled to sign factors. -/
def Nonseparable (G : Cube I → ℝ) : Prop :=
  ∀ A : Finset I,A.Nonempty → A≠ univ →
    ¬∃ H K : Cube I → ℝ,DependsOn A H ∧ DependsOn Aᶜ K ∧ ∀ v,G v=H v*K v

theorem factor_of_complementary_equation {G P Q : Cube I → ℝ} {A : Finset I}
    (hG : ∀ v,G v=1 ∨ G v=-1)
    (hP : DependsOn A P) (hQ : DependsOn Aᶜ Q)
    (heq : ∀ v,P v=G v*Q v) (v₀ : Cube I) (hc : P v₀≠0) :
    ∃ H K : Cube I → ℝ,DependsOn A H ∧ DependsOn Aᶜ K ∧ ∀ v,G v=H v*K v := by
  let c := P v₀
  let K : Cube I → ℝ := fun v => G (mix A v₀ v)
  let H : Cube I → ℝ := fun v => P v/c
  have hGsquare : ∀ v,G v*G v=1 := by
    intro v
    rcases hG v with h | h <;> rw [h] <;> norm_num
  have hKsquare : ∀ v,K v*K v=1 := fun v => hGsquare (mix A v₀ v)
  have hQc : ∀ v,Q v=K v*c := by
    intro v
    have h := heq (mix A v₀ v)
    rw [hP.mix_left,hQ.mix_right] at h
    have hh := congrArg (fun x : ℝ => K v*x) h
    change K v*c=K v*(K v*Q v) at hh
    rw [← mul_assoc,hKsquare,one_mul] at hh
    exact hh.symm
  refine ⟨H,K,?_,?_,?_⟩
  · intro u v huv
    change P u/c=P v/c
    rw [hP u v huv]
  · intro u v huv
    apply congrArg G
    funext i
    by_cases hi : i∈A
    · simp [mix,hi]
    · simp [mix,hi,huv i (by simpa using hi)]
  · intro v
    change G v=(P v/c)*K v
    rw [heq v,hQc v]
    have hc' : c≠0 := hc
    calc
      G v=G v*(K v*K v) := by rw [hKsquare,mul_one]
      _=(G v*(K v*c)/c)*K v := by field_simp [hc']

theorem restricted_components_equation {p : (Cube I × Cube I) → ℝ}
    {G : Cube I → ℝ} {P : Finset I → Cube I → ℝ}
    (hp : ∀ u v,p (u,v)=∑ A : Finset I,character A u*P A v)
    (hgp : ∀ u v,phase G (u,v)*p (u,v)=p (u,v)) :
    ∀ A v,P A v=G v*P Aᶜ v := by
  intro A v
  have hcoeff : ∀ B : Finset I,
      (∑ u : Cube I,character B u*p (u,v))=(2 : ℝ)^Fintype.card I*P B v := by
    intro B
    have hs : ∀ u,p (u,v)=∑ C : Finset I,P C v*character C u := by
      intro u
      rw [hp]
      apply sum_congr rfl
      intro C hC
      ring
    simp_rw [hs]
    exact coefficient_extraction (fun C => P C v) B
  have h := congrArg (fun f : Cube I → ℝ => ∑ u,character A u*f u)
    (funext fun u => hgp u v)
  have hleft : (∑ u : Cube I,character A u*(phase G (u,v)*p (u,v)))=
      G v*(∑ u : Cube I,character Aᶜ u*p (u,v)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro u hu
    rw [← character_compl]
    unfold phase
    ring
  change (∑ u : Cube I,character A u*(phase G (u,v)*p (u,v)))=
    ∑ u : Cube I,character A u*p (u,v) at h
  rw [hleft,hcoeff,hcoeff] at h
  have hn : (2 : ℝ)^Fintype.card I≠0 := pow_ne_zero _ (by norm_num)
  apply (mul_left_cancel₀ hn)
  calc
    (2 : ℝ)^Fintype.card I*P A v=G v*((2 : ℝ)^Fintype.card I*P Aᶜ v) := h.symm
    _=(2 : ℝ)^Fintype.card I*(G v*P Aᶜ v) := by ring

theorem phase_square {G : Cube I → ℝ} (hG : ∀ v,G v=1 ∨ G v=-1)
    (uv : Cube I × Cube I) : phase G uv*phase G uv=1 := by
  have hGv : G uv.2*G uv.2=1 := by
    rcases hG uv.2 with h | h <;> rw [h] <;> norm_num
  have hu := character_square (univ : Finset I) uv.1
  calc
    phase G uv*phase G uv=(character univ uv.1*character univ uv.1)*(G uv.2*G uv.2) := by
      unfold phase
      ring
    _=1 := by rw [hu,hGv]; norm_num

theorem vanishes_iff_phase_fixed {G : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v=-1) (p : (Cube I × Cube I) → ℝ) :
    (∀ uv,faceFunction G uv=0 → p uv=0) ↔
      ∀ u v,phase G (u,v)*p (u,v)=p (u,v) := by
  constructor
  · intro hp u v
    have hs := phase_square hG (u,v)
    have hsign : phase G (u,v)=1 ∨ phase G (u,v)=-1 := by
      have h : (phase G (u,v)-1)*(phase G (u,v)+1)=0 := by nlinarith
      rcases mul_eq_zero.mp h with h | h
      · left; linarith
      · right; linarith
    rcases hsign with h | h
    · simp [h]
    · have hz := hp (u,v) (by simp [faceFunction,h])
      simp [hz]
  · intro hp uv hf
    have h := hp uv.1 uv.2
    have hg : phase G uv=-1 := by unfold faceFunction at hf; linarith
    rw [hg] at h
    linarith

/-- Lemma9.9: the complete vanishing subspace is the one-dimensional line
through the Boolean function, for every nonempty finite index set. -/
theorem boolean_face_line [Nonempty I] {G : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v=-1) (hsep : Nonseparable G)
    (p : (Cube I × Cube I) → ℝ) (hp : p∈tensorSpace) :
    (∀ uv,faceFunction G uv=0 → p uv=0) ↔
      ∃ c : ℝ,p=c • faceFunction G := by
  constructor
  · intro hzero
    obtain ⟨P,hP,hp⟩ := restrictedExpansion_of_mem_tensorSpace hp
    have hgp := (vanishes_iff_phase_fixed hG p).mp hzero
    have hcomponents := restricted_components_equation hp hgp
    have hproper : ∀ A : Finset I,A≠∅ → A≠ univ → ∀ v,P A v=0 := by
      intro A hA htop v
      by_contra hv
      exact hsep A (nonempty_iff_ne_empty.mpr hA) htop
        (factor_of_complementary_equation hG (hP A) (hP Aᶜ)
          (hcomponents A) v hv)
    obtain ⟨c,hc⟩ := (dependsOn_empty_iff (P ∅)).mp (hP ∅)
    have hfull : ∀ v,P univ v=G v*c := by
      intro v
      simpa only [compl_univ,hc] using hcomponents univ v
    have hne : (∅ : Finset I)≠ univ := by
      exact ne_of_lt (empty_ssubset.mpr univ_nonempty)
    refine ⟨2*c,?_⟩
    funext uv
    rw [hp]
    have hs : (∑ A : Finset I,character A uv.1*P A uv.2)=
        character ∅ uv.1*P ∅ uv.2+character univ uv.1*P univ uv.2 := by
      have hh := sum_subset (f := fun A : Finset I => character A uv.1 * P A uv.2) (subset_univ ({∅,univ} : Finset (Finset I)))
        (fun A hAu hnot => by
          have hA : A≠∅ := by intro h; apply hnot; simp [h]
          have htop : A≠ univ := by intro h; apply hnot; simp [h]
          rw [hproper A hA htop,mul_zero])
      simpa only [sum_pair hne] using hh.symm
    rw [hs,character_empty,one_mul,hc,hfull]
    simp only [Pi.smul_apply,smul_eq_mul,faceFunction,phase]
    ring
  · rintro ⟨c,rfl⟩ uv huv
    simp [huv]

theorem faceFunction_boolean {G : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v=-1) (uv : Cube I × Cube I) :
    faceFunction G uv=0 ∨ faceFunction G uv=1 := by
  have hs := phase_square hG uv
  have hp : faceFunction G uv*(faceFunction G uv-1)=0 := by
    unfold faceFunction
    nlinarith [hs]
  rcases mul_eq_zero.mp hp with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem faceFunction_ne_zero [Nonempty I] {G : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v=-1) : faceFunction G≠0 := by
  let v₀ : Cube I := fun _ => false
  obtain ⟨i⟩ := ‹Nonempty I›
  have hvalue : ∃ u : Cube I,faceFunction G (u,v₀)=1 := by
    rcases hG v₀ with h | h
    · refine ⟨fun _ => false,?_⟩
      simp [faceFunction,phase,character,spin,h]
    · let u : Cube I := fun j => if j=i then true else false
      have hu : character univ u=-1 := by
        rw [character_univ,prod_eq_single i]
        · simp [u,spin]
        · intro j hj hji
          simp [u,hji,spin]
        · simp
      exact ⟨u,by simp [faceFunction,phase,hu,h]⟩
  obtain ⟨u,hu⟩ := hvalue
  intro hz
  rw [hz] at hu
  norm_num at hu

/-- All tensor polynomials vanishing on the literal zero set of `f`. -/
def faceKernel (G : Cube I → ℝ) : Submodule ℝ ((Cube I × Cube I) → ℝ) where
  carrier := {p | p∈tensorSpace ∧ ∀ uv,faceFunction G uv=0 → p uv=0}
  zero_mem' := ⟨(tensorSpace (I := I)).zero_mem,by simp⟩
  add_mem' hp hq := ⟨(tensorSpace (I := I)).add_mem hp.1 hq.1,by
    intro uv huv
    simp [hp.2 uv huv,hq.2 uv huv]⟩
  smul_mem' c p hp := ⟨(tensorSpace (I := I)).smul_mem c hp.1,by
    intro uv huv
    simp [hp.2 uv huv]⟩

theorem faceKernel_eq_span [Nonempty I] {G : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v=-1) (hsep : Nonseparable G) :
    faceKernel G=Submodule.span ℝ {faceFunction G} := by
  ext p
  constructor
  · intro hp
    obtain ⟨c,hc⟩ := (boolean_face_line hG hsep p hp.1).mp hp.2
    exact Submodule.mem_span_singleton.mpr ⟨c,hc.symm⟩
  · intro hp
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hp
    exact ⟨(tensorSpace (I := I)).smul_mem c (faceFunction_mem_tensorSpace G),
      fun uv huv => by simp [huv]⟩

theorem faceKernel_finrank [Nonempty I] {G : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v=-1) (hsep : Nonseparable G) :
    Module.finrank ℝ (faceKernel G)=1 := by
  rw [faceKernel_eq_span hG hsep]
  exact finrank_span_singleton (faceFunction_ne_zero hG)

theorem Nonseparable.neg {G : Cube I → ℝ} (hG : Nonseparable G) :
    Nonseparable (-G) := by
  intro A hA htop hfactor
  obtain ⟨H,K,hH,hK,h⟩ := hfactor
  apply hG A hA htop
  refine ⟨(-1 : ℝ) • H,K,hH.smul (-1),hK,?_⟩
  intro v
  have hv := h v
  change -G v=H v*K v at hv
  change G v=((-1 : ℝ)*H v)*K v
  linarith

/-- The nonfactorization convention is unchanged if the candidate factors
are required to be sign-valued: every real factorization of a sign function
has such a normalization. -/
theorem normalize_sign_factorization {G H K : Cube I → ℝ} {A : Finset I}
    (hG : ∀ v,G v=1 ∨ G v=-1)
    (hH : DependsOn A H) (hK : DependsOn Aᶜ K)
    (hfactor : ∀ v,G v=H v*K v) :
    ∃ H' K' : Cube I → ℝ,DependsOn A H' ∧ DependsOn Aᶜ K' ∧
      (∀ v,H' v=1 ∨ H' v=-1) ∧ (∀ v,K' v=1 ∨ K' v=-1) ∧
      ∀ v,G v=H' v*K' v := by
  let v₀ : Cube I := fun _ => false
  let H' : Cube I → ℝ := fun v => G (mix A v v₀)*G v₀
  let K' : Cube I → ℝ := fun v => G (mix A v₀ v)
  have hH' : DependsOn A H' := by
    intro u v huv
    change G (mix A u v₀)*G v₀=G (mix A v v₀)*G v₀
    congr 2
    funext i
    by_cases hi : i∈A
    · simp [mix,hi,huv i hi]
    · simp [mix,hi]
  have hK' : DependsOn Aᶜ K' := by
    intro u v huv
    apply congrArg G
    funext i
    by_cases hi : i∈A
    · simp [mix,hi]
    · simp [mix,hi,huv i (by simpa using hi)]
  refine ⟨H',K',hH',hK',?_,fun v => hG (mix A v₀ v),?_⟩
  · intro v
    rcases hG (mix A v v₀) with ha | ha <;>
      rcases hG v₀ with hb | hb <;> simp [H',ha,hb]
  · intro v
    have h₀ : G v₀*G v₀=1 := by
      rcases hG v₀ with h | h <;> rw [h] <;> norm_num
    change G v=(G (mix A v v₀)*G v₀)*G (mix A v₀ v)
    rw [hfactor (mix A v v₀),hfactor (mix A v₀ v),
      hH.mix_left,hH.mix_left,hK.mix_right,hK.mix_right]
    calc
      G v=G v*(G v₀*G v₀) := by rw [h₀,mul_one]
      _=(H v*K v₀*G v₀)*(H v₀*K v) := by rw [hfactor v,hfactor v₀]; ring

end BooleanFourier
end GraphicalZonotopes

end
end
end BundlePart239

section BundlePart240
/- Source: Papers/GraphicalZonotopes/TensorIndicators.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanFourier
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The local factors of the actual three-dimensional space in transformed
coordinates. -/
def tensorFactor (b : Option Bool) (u v : Bool) : ℝ :=
  match b with
  | none => 1
  | some false => spin u
  | some true => spin u*spin v

/-- Products of arbitrary local linear combinations lie in the actual tensor
space. The proof is the finite distributive law over all choices of factors. -/
theorem tensor_product_mem (w : I → Option Bool → ℝ) :
    (fun uv : Cube I × Cube I =>
      ∏ i,∑ b : Option Bool,w i b*tensorFactor b (uv.1 i) (uv.2 i))∈tensorSpace := by
  have h : (∑ a : I → Option Bool,(∏ i,w i (a i)) • tensorMonomial a)∈tensorSpace :=
    (tensorSpace (I := I)).sum_mem fun a _ =>
      (tensorSpace (I := I)).smul_mem _ (Submodule.subset_span ⟨a,rfl⟩)
  convert h using 1
  funext uv
  rw [Fintype.prod_sum]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,tensorMonomial]
  apply sum_congr rfl
  intro a ha
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  cases a i <;> rfl

/-- A selected original membership bit in each part, with no bit selected for
`none`. A clique of a graph with doubled parts has exactly this form. -/
def indicatorMonomial (a : I → Option Bool) (s : Cube I × Cube I) : ℝ :=
  ∏ i,match a i with
    | none => 1
    | some false => if s.1 i then 1 else 0
    | some true => if s.2 i then 1 else 0

def indicatorCoefficients (a : Option Bool) (b : Option Bool) : ℝ :=
  match a with
  | none => if b=none then 1 else 0
  | some q => if b=none then 1/2 else if b=some q then -1/2 else 0

theorem indicator_local_expansion (a : Option Bool) (u v : Bool) :
    (∑ b : Option Bool,indicatorCoefficients a b*tensorFactor b u v)=
      match a with
      | none => 1
      | some false => if u then 1 else 0
      | some true => if Bool.xor u v then 1 else 0 := by
  cases a with
  | none => simp [indicatorCoefficients,tensorFactor]
  | some q =>
    cases q <;> cases u <;> cases v <;>
      norm_num [indicatorCoefficients,tensorFactor,spin,Fintype.sum_option,Fintype.sum_bool]

/-- Actual membership monomials become tensor-space elements under the
invertible coordinate substitution `(u,v) ↦ (u,u xor v)`. -/
theorem indicatorMonomial_mem_tensorSpace (a : I → Option Bool) :
    (fun uv => indicatorMonomial a (coordinateChange.symm uv))∈tensorSpace := by
  have h := tensor_product_mem (fun i => indicatorCoefficients (a i))
  convert h using 1
  funext uv
  simp only [indicatorMonomial]
  apply prod_congr rfl
  intro i hi
  rw [indicator_local_expansion]
  cases a i with
  | none => rfl
  | some q => cases q <;> rfl

theorem indicatorMonomial_eq (a : I → Option Bool) (s : Cube I × Cube I) :
    indicatorMonomial a s=
      if (∀ i, a i=some false → s.1 i=true) ∧
        (∀ i,a i=some true → s.2 i=true) then 1 else 0 := by
  classical
  by_cases hall : (∀ i,a i=some false → s.1 i=true) ∧
      (∀ i,a i=some true → s.2 i=true)
  · rw [if_pos hall]
    apply prod_eq_one
    intro i hi
    cases h : a i with
    | none => rfl
    | some q =>
      cases q
      · simp [h,hall.1 i h]
      · simp [h,hall.2 i h]
  · rw [if_neg hall]
    have hn : (∃ i,a i=some false ∧ s.1 i≠ true) ∨
        (∃ i,a i=some true ∧ s.2 i≠ true) := by
      simpa only [not_and_or,not_forall,not_imp,exists_prop] using hall
    rcases hn with ⟨i,ha,hs⟩ | ⟨i,ha,hs⟩
    · apply Finset.prod_eq_zero (mem_univ i)
      simp [ha,hs]
    · apply Finset.prod_eq_zero (mem_univ i)
      simp [ha,hs]

end BooleanFourier
end GraphicalZonotopes

end
end
end BundlePart240

section BundlePart241
/- Source: Papers/GraphicalZonotopes/PairTensor.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The usual Boolean coordinates of an arbitrary subset of paired vertices. -/
def subsetOfBits (s : Cube I × Cube I) : Finset (I×Fin 2) :=
  univ.filter fun v => if v.2=0 then s.1 v.1=true else s.2 v.1=true

@[simp] theorem mem_subsetOfBits_zero (s : Cube I × Cube I) (i : I) :
    (i,0)∈subsetOfBits s ↔ s.1 i=true := by simp [subsetOfBits]

@[simp] theorem mem_subsetOfBits_one (s : Cube I × Cube I) (i : I) :
    (i,1)∈subsetOfBits s ↔ s.2 i=true := by simp [subsetOfBits]

def bitsOfSubset (S : Finset (I×Fin 2)) : Cube I × Cube I :=
  (fun i => decide ((i,0)∈S),fun i => decide ((i,1)∈S))

@[simp] theorem subsetOfBits_bitsOfSubset (S : Finset (I×Fin 2)) :
    subsetOfBits (bitsOfSubset S)=S := by
  ext v
  rcases v with ⟨i,b⟩
  fin_cases b <;> simp [bitsOfSubset]

@[simp] theorem bitsOfSubset_subsetOfBits (s : Cube I × Cube I) :
    bitsOfSubset (subsetOfBits s)=s := by
  apply Prod.ext
  · funext i
    simp [bitsOfSubset]
  · funext i
    simp [bitsOfSubset]

def selector (C : Finset (I×Fin 2)) (i : I) : Option Bool :=
  if (i,0)∈C then some false else if (i,1)∈C then some true else none

def IsPartialTransversal (C : Finset (I×Fin 2)) : Prop :=
  ∀ i,¬((i,0)∈C ∧ (i,1)∈C)

theorem clique_partialTransversal {C : Finset (I×Fin 2)}
    (hC : (graph I).IsClique C) : IsPartialTransversal C := by
  intro i hi
  exact hC hi.1 hi.2 (by simp) rfl

theorem selector_zero_iff (C : Finset (I×Fin 2)) (i : I) :
    selector C i=some false ↔ (i,0)∈C := by
  by_cases h0 : (i,0)∈C <;> by_cases h1 : (i,1)∈C <;> simp [selector,h0,h1]

theorem selector_one_iff {C : Finset (I×Fin 2)} (hC : IsPartialTransversal C) (i : I) :
    selector C i=some true ↔ (i,1)∈C := by
  by_cases h0 : (i,0)∈C
  · have h1 : (i,1)∉C := fun h => hC i ⟨h0,h⟩
    simp [selector,h0,h1]
  · simp [selector,h0]

theorem subset_subsetOfBits_iff (C : Finset (I×Fin 2)) (s : Cube I × Cube I) :
    C⊆subsetOfBits s ↔
      (∀ i,(i,0)∈C → s.1 i=true) ∧ (∀ i,(i,1)∈C → s.2 i=true) := by
  constructor
  · intro h
    exact ⟨fun i hi => (mem_subsetOfBits_zero s i).mp (h hi),
      fun i hi => (mem_subsetOfBits_one s i).mp (h hi)⟩
  · rintro ⟨h0,h1⟩ ⟨i,b⟩ hi
    fin_cases b
    · exact (mem_subsetOfBits_zero s i).mpr (h0 i hi)
    · exact (mem_subsetOfBits_one s i).mpr (h1 i hi)

theorem setMonomial_subsetOfBits {C : Finset (I×Fin 2)}
    (hC : IsPartialTransversal C) (s : Cube I × Cube I) :
    setMonomial C (subsetOfBits s)=indicatorMonomial (selector C) s := by
  rw [indicatorMonomial_eq]
  simp only [setMonomial,selector_zero_iff,selector_one_iff hC,subset_subsetOfBits_iff]

theorem setMonomial_mem_tensorSpace {C : Finset (I×Fin 2)}
    (hC : IsPartialTransversal C) :
    (fun uv => setMonomial C (subsetOfBits (coordinateChange.symm uv)))∈tensorSpace := by
  simpa only [setMonomial_subsetOfBits hC] using
    indicatorMonomial_mem_tensorSpace (selector C)

abbrev Remaining (u v : I×Fin 2) := {i : I // i≠ u.1 ∧ i≠ v.1}

def remainingEmbedding (u v : I×Fin 2) : Remaining u v × Fin 2 ↪ I×Fin 2 where
  toFun w := (w.1.1,w.2)
  inj' := by
    rintro ⟨i,a⟩ ⟨j,b⟩ h
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst h)
    · exact congrArg (fun z : I × Fin 2 => z.2) h

def edgeContext (u v : I×Fin 2)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) : Finset (I×Fin 2) :=
  (subsetOfBits s).map (remainingEmbedding u v)

@[simp] theorem left_not_mem_edgeContext (u v : I×Fin 2)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) : u∉edgeContext u v s := by
  rintro h
  obtain ⟨w,hw,he⟩ := mem_map.mp h
  exact w.1.2.1 (congrArg Prod.fst he)

@[simp] theorem right_not_mem_edgeContext (u v : I×Fin 2)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) : v∉edgeContext u v s := by
  rintro h
  obtain ⟨w,hw,he⟩ := mem_map.mp h
  exact w.1.2.2 (congrArg Prod.fst he)

def remainingPart (u v : I×Fin 2) (C : Finset (I×Fin 2)) :
    Finset (Remaining u v × Fin 2) :=
  univ.filter fun w => remainingEmbedding u v w∈C

@[simp] theorem mem_remainingPart (u v : I×Fin 2) (C : Finset (I×Fin 2))
    (w : Remaining u v × Fin 2) : w∈remainingPart u v C ↔ remainingEmbedding u v w∈C :=
  by simp [remainingPart]

theorem remainingPart_partialTransversal {u v : I×Fin 2} {C : Finset (I×Fin 2)}
    (hC : IsPartialTransversal C) : IsPartialTransversal (remainingPart u v C) := by
  intro i hi
  exact hC i.1 ⟨(mem_remainingPart _ _ _ _).mp hi.1,(mem_remainingPart _ _ _ _).mp hi.2⟩

theorem clique_edge_subset_iff {u v : I×Fin 2} {C : Finset (I×Fin 2)}
    (hC : (graph I).IsClique C) (hu : u∈C) (hv : v∈C)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) :
    C⊆insert u (insert v (edgeContext u v s)) ↔
      remainingPart u v C⊆subsetOfBits s := by
  constructor
  · intro h w hw
    have he := h ((mem_remainingPart _ _ _ _).mp hw)
    rcases mem_insert.mp he with he | he
    · exact False.elim (w.1.2.1 (congrArg Prod.fst he))
    · rcases mem_insert.mp he with he | he
      · exact False.elim (w.1.2.2 (congrArg Prod.fst he))
      · obtain ⟨w',hw',he⟩ := mem_map.mp he
        have hw'e : w'=w := (remainingEmbedding u v).injective he
        simpa only [hw'e] using hw'
  · intro h w hw
    by_cases hwu : w=u
    · simp [hwu]
    by_cases hwv : w=v
    · simp [hwv]
    have hpu : w.1≠ u.1 := hC hw hu hwu
    have hpv : w.1≠ v.1 := hC hw hv hwv
    let w' : Remaining u v × Fin 2 := (⟨w.1,hpu,hpv⟩,w.2)
    have hw' : w'∈remainingPart u v C := (mem_remainingPart _ _ _ _).mpr hw
    exact mem_insert_of_mem (mem_insert_of_mem (mem_map.mpr ⟨w',h hw',rfl⟩))

theorem delta_setMonomial_tensor {u v : I×Fin 2} (huv : u≠ v)
    {C : Finset (I×Fin 2)} (hC : (graph I).IsClique C) :
    (fun uv => delta (setMonomial C) u v
      (edgeContext u v (coordinateChange.symm uv)))∈tensorSpace := by
  by_cases hu : u∈C
  · by_cases hv : v∈C
    · have h := setMonomial_mem_tensorSpace
        (remainingPart_partialTransversal (u := u) (v := v) (clique_partialTransversal hC))
      convert h using 1
      funext uv
      rw [delta_setMonomial huv (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _)]
      simp only [hu,hv,true_and,clique_edge_subset_iff hC hu hv,setMonomial]
    · convert (tensorSpace (I := Remaining u v)).zero_mem using 1
      funext uv
      rw [delta_setMonomial huv (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _)]
      simp [hv]
  · convert (tensorSpace (I := Remaining u v)).zero_mem using 1
    funext uv
    rw [delta_setMonomial huv (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _)]
    simp [hu]

/-- Every actual elemental row of a normalized graphical function belongs to
the precise tensor space used by the Boolean face argument. No row-space
hypothesis is assumed: it follows from the original clique coefficients. -/
theorem graphical_edgeProfile_mem_tensorSpace {f : SetFunction (I×Fin 2)}
    (hn : TranslationNormalized f) (hG : Graphical (graph I) f)
    {u v : I×Fin 2} (huv : u≠ v) :
    (fun uv => delta f u v (edgeContext u v (coordinateChange.symm uv)))∈tensorSpace := by
  have hsupport := (mobius_cliqueSupported_iff (graph I) f).mpr ⟨hn,hG⟩
  have hsum : (∑ C : Finset (I×Fin 2),mobius f C •
      (fun uv => delta (setMonomial C) u v
        (edgeContext u v (coordinateChange.symm uv))))∈tensorSpace := by
    apply (tensorSpace (I := Remaining u v)).sum_mem
    intro C hC
    by_cases hc : mobius f C=0
    · simp only [hc,zero_smul]
      exact (tensorSpace (I := Remaining u v)).zero_mem
    · have hcl : (graph I).IsClique C := by
        by_contra hnC
        exact hc (coefficient_zero_of_not_clique hsupport C (by
          rintro ⟨_,h⟩
          exact hnC h))
      exact (tensorSpace (I := Remaining u v)).smul_mem _ (delta_setMonomial_tensor huv hcl)
  convert hsum using 1
  funext uv
  conv_lhs => rw [← zeta_mobius f,zeta_eq_sum_monomials]
  simp only [delta_sum,delta_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart241

section BundlePart242
/- Source: Papers/GraphicalZonotopes/PairRelabelling.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
open scoped BigOperators symmDiff
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def pairedEmbedding (e : I ↪ J) : I×Fin 2 ↪ J×Fin 2 :=
  e.prodMap (Function.Embedding.refl (Fin 2))

theorem firstSet_map (e : I ↪ J) (S : Finset (I×Fin 2)) :
    firstSet (S.map (pairedEmbedding e))=(firstSet S).map e := by
  ext j
  rw [mem_firstSet,mem_map,mem_map]
  constructor
  · rintro ⟨⟨i,b⟩,hi,h⟩
    have hb : b=0 := congrArg Prod.snd h
    subst b
    exact ⟨i,(mem_firstSet _ _).mpr hi,congrArg Prod.fst h⟩
  · rintro ⟨i,hi,h⟩
    exact ⟨(i,0),(mem_firstSet _ _).mp hi,Prod.ext h rfl⟩

theorem secondSet_map (e : I ↪ J) (S : Finset (I×Fin 2)) :
    secondSet (S.map (pairedEmbedding e))=(secondSet S).map e := by
  ext j
  rw [mem_secondSet,mem_map,mem_map]
  constructor
  · rintro ⟨⟨i,b⟩,hi,h⟩
    have hb : b=1 := congrArg Prod.snd h
    subst b
    exact ⟨i,(mem_secondSet _ _).mpr hi,congrArg Prod.fst h⟩
  · rintro ⟨i,hi,h⟩
    exact ⟨(i,1),(mem_secondSet _ _).mp hi,Prod.ext h rfl⟩

theorem integerData_map (e : I ↪ J) (S : Finset (I×Fin 2)) :
    integerData (S.map (pairedEmbedding e))=integerData S := by
  have h1 := integerData_count_identity (S.map (pairedEmbedding e))
  have h2 := integerData_count_identity S
  rw [firstSet_map,secondSet_map,← map_inter,card_map,card_map,card_map] at h1
  omega

def remainingPartEmbedding (u v : I×Fin 2) : Remaining u v ↪ I :=
  ⟨Subtype.val,Subtype.val_injective⟩

theorem remainingEmbedding_eq (u v : I×Fin 2) :
    remainingEmbedding u v=pairedEmbedding (remainingPartEmbedding u v) := by
  apply Function.Embedding.ext
  intro w
  rfl

theorem integerData_edgeContext (u v : I×Fin 2)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) :
    integerData (edgeContext u v s)=integerData (subsetOfBits s) := by
  rw [edgeContext,remainingEmbedding_eq,integerData_map]

@[simp] theorem edgeContext_card (u v : I×Fin 2)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) :
    (edgeContext u v s).card=(subsetOfBits s).card := by
  simp only [edgeContext,card_map]

theorem edgeContext_remainingPart (u v : I×Fin 2) (S : Finset (I×Fin 2)) :
    edgeContext u v (bitsOfSubset (remainingPart u v S))=
      S∩commonNeighbors (graph I) u v := by
  rw [edgeContext,subsetOfBits_bitsOfSubset]
  ext w
  constructor
  · intro hw
    obtain ⟨w',hw',rfl⟩ := mem_map.mp hw
    refine mem_inter.mpr ⟨(mem_remainingPart _ _ _ _).mp hw',?_⟩
    exact (mem_commonNeighbors _ _ _ _).mpr ⟨Ne.symm w'.1.2.1,Ne.symm w'.1.2.2⟩
  · intro hw
    rcases mem_inter.mp hw with ⟨hw,hn⟩
    rcases (mem_commonNeighbors _ _ _ _).mp hn with ⟨hu,hv⟩
    let w' : Remaining u v × Fin 2 := (⟨w.1,Ne.symm hu,Ne.symm hv⟩,w.2)
    exact mem_map.mpr ⟨w',(mem_remainingPart _ _ _ _).mpr hw,rfl⟩

theorem edgeContext_all_adj (u v : I×Fin 2)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) :
    ∀ w∈edgeContext u v s,(graph I).Adj u w ∧ (graph I).Adj v w := by
  intro w hw
  obtain ⟨w',hw',rfl⟩ := mem_map.mp hw
  exact ⟨Ne.symm w'.1.2.1,Ne.symm w'.1.2.2⟩

theorem integerData_insert_common (u : I×Fin 2) (S : Finset (I×Fin 2))
    (hu : u∉S) (ha : ∀ w∈S,(graph I).Adj u w) :
    integerData (insert u S)=integerData S+(S.card : ℤ)+firstWeight u := by
  apply Int.cast_injective (α := ℝ)
  push_cast
  simp only [cast_integerData]
  rw [graphFunction_insert _ u S hu]
  have he : (∑ w∈S,if (graph I).Adj u w then (1 : ℝ) else 0)=(S.card : ℝ) := by
    simp only [sum_ite_of_true ha,sum_const,nsmul_eq_mul,mul_one]
  rw [he]
  simp only [modular,subsetSum,sum_insert hu]
  ring

theorem firstWeight_isBit (u : I×Fin 2) : firstWeight u=0 ∨ firstWeight u=1 := by
  unfold firstWeight
  split_ifs <;> simp

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart242

section BundlePart243
/- Source: Papers/GraphicalZonotopes/LocalSlopes.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem mobius_sub (f g : SetFunction V) : mobius (f-g)=mobius f-mobius g := by
  exact (zetaEquiv (V := V)).symm.map_sub f g

@[simp] theorem mobius_smul (a : ℝ) (f : SetFunction V) : mobius (a • f)=a • mobius f := by
  exact (zetaEquiv (V := V)).symm.map_smul a f

/-- Equality of an entire elemental row determines every Möbius coefficient
containing its two endpoints. This is Boolean Möbius inversion, not a test on
selected contexts. -/
theorem mobius_scale_of_delta_scale {f z : SetFunction V} {u v : V}
    (huv : u≠ v) (a : ℝ)
    (h : ∀ S : Finset V,u∉S → v∉S → delta f u v S=a*delta z u v S)
    {C : Finset V} (hu : u∈C) (hv : v∈C) : mobius f C=a*mobius z C := by
  have hzero : ∀ S : Finset V,u∉S → v∉S → delta (f-a • z) u v S=0 := by
    intro S hSu hSv
    rw [delta_sub,delta_smul,h S hSu hSv,sub_self]
  have hcoeff := (nonedge_coefficients_zero_iff (mobius (f-a • z)) huv).mp
    (by simpa only [zeta_mobius] using hzero) C hu hv
  rw [mobius_sub,mobius_smul] at hcoeff
  change mobius f C-a*mobius z C=0 at hcoeff
  exact sub_eq_zero.mp hcoeff

abbrev SlopeEdge (G : SimpleGraph V) := {e : V×V // G.Adj e.1 e.2}

/-- Edge scales interact whenever the same nonzero original Möbius
coefficient contains both edges. -/
def coefficientEdgeGraph (G : SimpleGraph V) (z : SetFunction V) :
    SimpleGraph (SlopeEdge G) where
  Adj e f := e≠ f ∧ ∃ C : Finset V,mobius z C≠0 ∧
    e.1.1∈C ∧ e.1.2∈C ∧ f.1.1∈C ∧ f.1.2∈C
  symm := ⟨by
    rintro e f ⟨hef,C,hC,he₁,he₂,hf₁,hf₂⟩
    exact ⟨Ne.symm hef,C,hC,hf₁,hf₂,he₁,he₂⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A local-to-global extremality criterion used in the Boolean phase
construction. Each local hypothesis concerns every context of the actual
original elemental row. Connected nonzero coefficients then force all row
scales to agree. -/
theorem extremeSupermodular_of_local_row_lines {G : SimpleGraph V}
    {z : SetFunction V} (hn : TranslationNormalized z) (hs : Supermodular z)
    (hne : z≠0) (hG : Graphical G z)
    (hconn : (coefficientEdgeGraph G z).Connected)
    (hlocal : ∀ f : SetFunction V,TranslationNormalized f →
      (∀ u v,u≠ v → ∀ S : Finset V,u∉S → v∉S →
        delta z u v S=0 → delta f u v S=0) →
      ∀ e : SlopeEdge G,∃ a : ℝ,∀ S : Finset V,
        e.1.1∉S → e.1.2∉S → delta f e.1.1 e.1.2 S=a*delta z e.1.1 e.1.2 S) :
    ExtremeSupermodular z := by
  classical
  apply extremeSupermodular_of_tightEquations hn hs hne
  intro f hfn hzeros
  choose a ha using hlocal f hfn hzeros
  obtain ⟨e₀⟩ := hconn.nonempty
  have hedge : ∀ e d : SlopeEdge G,(coefficientEdgeGraph G z).Adj e d → a e=a d := by
    rintro e d ⟨hed,C,hC,he₁,he₂,hd₁,hd₂⟩
    have he := mobius_scale_of_delta_scale (G.ne_of_adj e.2) (a e) (ha e) he₁ he₂
    have hd := mobius_scale_of_delta_scale (G.ne_of_adj d.2) (a d) (ha d) hd₁ hd₂
    exact mul_right_cancel₀ hC (he.symm.trans hd)
  have hconst : ∀ e : SlopeEdge G,a e=a e₀ := by
    intro e
    have hr := hconn.preconnected e e₀
    rw [SimpleGraph.reachable_eq_reflTransGen] at hr
    induction hr with
    | refl => rfl
    | @tail d e hpath hde ih => exact ih.trans (hedge d e hde)
  have hrow : ∀ u v,u≠ v → ∀ S : Finset V,u∉S → v∉S →
      delta f u v S=a e₀*delta z u v S := by
    intro u v huv S hu hv
    by_cases hadj : G.Adj u v
    · let e : SlopeEdge G := ⟨(u,v),hadj⟩
      have h := ha e S hu hv
      rw [hconst e] at h
      exact h
    · have hz := hG u v huv hadj S hu hv
      rw [hzeros u v huv S hu hv hz,hz,mul_zero]
  have hwn : TranslationNormalized (f-a e₀ • z) := by
    refine ⟨?_,?_⟩
    · change f ∅-a e₀*z ∅=0
      rw [hfn.1,hn.1]
      ring
    · intro v
      change f {v}-a e₀*z {v}=0
      rw [hfn.2 v,hn.2 v]
      ring
  refine ⟨a e₀,sub_eq_zero.mp (normalized_zero_elemental_eq_zero hwn ?_)⟩
  intro u v huv S hu hv
  rw [delta_sub,delta_smul,hrow u v huv S hu hv,sub_self]

end GraphicalZonotopes

end
end
end BundlePart243

section BundlePart244
/- Source: Papers/GraphicalZonotopes/DoubledFourCoefficients.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem integerData_of_clique {C : Finset (I×Fin 2)} (hC : (graph I).IsClique C) :
    integerData C=(C.card.choose 2 : ℤ)+∑ v∈C,firstWeight v := by
  have he : firstSet C∩secondSet C=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    rcases mem_inter.mp hi with ⟨h0,h1⟩
    exact hC ((mem_firstSet _ _).mp h0) ((mem_secondSet _ _).mp h1) (by simp) rfl
  have h := integerData_count_identity C
  rw [he,card_empty,Int.natCast_zero,add_zero,← firstWeight_sum] at h
  exact h

def fourRoundedCoefficient (a b c d : ℤ) : ℤ :=
  (6+a+b+c+d)/2-(3+a+b+c)/2-(3+a+b+d)/2-(3+a+c+d)/2-(3+b+c+d)/2+
    (1+a+b)/2+(1+a+c)/2+(1+a+d)/2+(1+b+c)/2+(1+b+d)/2+(1+c+d)/2

/-- The only bounded calculation is a universal four-bit algebra identity;
its application below quantifies over every four-clique in every graph size. -/
theorem fourRoundedCoefficient_sign (a b c d : ℤ)
    (ha : a=0 ∨ a=1) (hb : b=0 ∨ b=1) (hc : c=0 ∨ c=1) (hd : d=0 ∨ d=1) :
    fourRoundedCoefficient a b c d=1 ∨ fourRoundedCoefficient a b c d= -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    norm_num [fourRoundedCoefficient]

theorem mobius_setFunction_four (a b c d : I×Fin 2)
    (hab : a≠ b) (hac : a≠ c) (had : a≠ d)
    (hbc : b≠ c) (hbd : b≠ d) (hcd : c≠ d)
    (hC : (graph I).IsClique ({a,b,c,d} : Finset (I×Fin 2))) :
    mobius setFunction {a,b,c,d}=
      (fourRoundedCoefficient (firstWeight a) (firstWeight b) (firstWeight c) (firstWeight d) : ℝ) := by
  have hform (T : Finset (I×Fin 2)) (hT : T⊆{a,b,c,d}) :
      integerData T=(T.card.choose 2 : ℤ)+∑ v∈T,firstWeight v := by
    apply integerData_of_clique
    intro x hx y hy hxy
    exact hC (hT hx) (hT hy) hxy
  rw [mobius_four_normalized setFunction setFunction_translationNormalized hab hac had hbc hbd hcd]
  norm_num [setFunction,hform,hab,hac,had,hbc,hbd,hcd,fourRoundedCoefficient,
    Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.choose]
  <;> ring

/-- Every tetrahedral coefficient is nonzero, in every number of doubled
parts, for every choice of the four selected endpoint sides. -/
theorem mobius_setFunction_four_sign {C : Finset (I×Fin 2)}
    (hcard : C.card=4) (hC : (graph I).IsClique C) :
    mobius setFunction C=1 ∨ mobius setFunction C= -1 := by
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,rfl⟩ := card_eq_four.mp hcard
  rw [mobius_setFunction_four a b c d hab hac had hbc hbd hcd hC]
  rcases fourRoundedCoefficient_sign (firstWeight a) (firstWeight b) (firstWeight c) (firstWeight d)
      (firstWeight_isBit a) (firstWeight_isBit b) (firstWeight_isBit c) (firstWeight_isBit d) with h | h
  · exact Or.inl (by exact_mod_cast h)
  · exact Or.inr (by exact_mod_cast h)

theorem mobius_setFunction_four_ne_zero {C : Finset (I×Fin 2)}
    (hcard : C.card=4) (hC : (graph I).IsClique C) : mobius setFunction C≠0 := by
  rcases mobius_setFunction_four_sign hcard hC with h | h <;> rw [h] <;> norm_num

theorem mobius_graphFunction_four_zero {C : Finset (I×Fin 2)} (hcard : C.card=4) :
    mobius (graphFunction (graph I)) C=0 := by
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,rfl⟩ := card_eq_four.mp hcard
  rw [mobius_four_eq _ hab hac had hbc hbd hcd]
  rw [graphFunction_delta _ hab (by simp [hac,had]) (by simp [hbc,hbd]),
    graphFunction_delta _ hab (by simp [hac]) (by simp [hbc]),
    graphFunction_delta _ hab (by simp [had]) (by simp [hbd]),
    graphFunction_delta _ hab (by simp) (by simp)]
  ring

theorem mobius_complementFunction_four_ne_zero {C : Finset (I×Fin 2)}
    (hcard : C.card=4) (hC : (graph I).IsClique C) : mobius complementFunction C≠0 := by
  rw [complementFunction,mobius_sub]
  change mobius (graphFunction (graph I)) C-mobius setFunction C≠0
  rw [mobius_graphFunction_four_zero hcard,zero_sub]
  exact neg_ne_zero.mpr (mobius_setFunction_four_ne_zero hcard hC)

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart244

section BundlePart245
/- Source: Papers/GraphicalZonotopes/FloorPhase.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace GraphicalZonotopes
namespace FloorHalf

/-- Exact remainder characterization, including negative integers. -/
theorem even_iff_mod_two (m : ℤ) : Even m ↔ m%2=0 := by
  constructor
  · rintro ⟨k,hk⟩
    omega
  · intro hm
    exact ⟨m/2,by omega⟩

theorem sign_zpow_mod_two (m : ℤ) :
    (-1 : ℝ)^m=if m%2=0 then 1 else -1 := by
  simp only [neg_one_zpow_eq_ite,even_iff_mod_two]

/-- Floor division as its linear part plus the exact parity correction. -/
theorem floor_half_phase (m : ℤ) :
    ((m/2 : ℤ) : ℝ)=(m : ℝ)/2+((-1 : ℝ)^m-1)/4 := by
  rw [sign_zpow_mod_two]
  by_cases hm : m%2=0
  · rw [if_pos hm]
    have he : m=2*(m/2) := by omega
    have hc : (m : ℝ)=2*((m/2 : ℤ) : ℝ) := by exact_mod_cast he
    linarith
  · rw [if_neg hm]
    have he : m=2*(m/2)+1 := by omega
    have hc : (m : ℝ)=2*((m/2 : ℤ) : ℝ)+1 := by exact_mod_cast he
    linarith

def edgePhaseInteger (m t a b : ℤ) : ℤ :=
  if a=b then
    if a=1 then (if (m+t)%2=0 then 1 else -1)
    else -(if (m+t)%2=0 then 1 else -1)
  else if m%2=0 then 1 else -1

theorem rounded_edge_phase_integer (m t a b : ℤ)
    (ha : a=0 ∨ a=1) (hb : b=0 ∨ b=1) :
    2*((m+2*t+a+b+1)/2+m/2-(m+t+a)/2-(m+t+b)/2)=
      1+edgePhaseInteger m t a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp only [edgePhaseInteger] <;> split_ifs <;> omega

/-- The exact original row profile, with all four endpoint-side choices.
Only the two endpoint bits are split; `m` and the context size are arbitrary. -/
theorem rounded_edge_phase (m t a b : ℤ)
    (ha : a=0 ∨ a=1) (hb : b=0 ∨ b=1) :
    (((m+2*t+a+b+1)/2 : ℤ) : ℝ)+((m/2 : ℤ) : ℝ)-
        (((m+t+a)/2 : ℤ) : ℝ)-(((m+t+b)/2 : ℤ) : ℝ)=
      (1+(if a=b then if a=1 then (-1 : ℝ)^(m+t) else -(-1 : ℝ)^(m+t)
        else (-1 : ℝ)^m))/2 := by
  have h := rounded_edge_phase_integer m t a b ha hb
  have hc : 2*((((m+2*t+a+b+1)/2 : ℤ) : ℝ)+((m/2 : ℤ) : ℝ)-
      (((m+t+a)/2 : ℤ) : ℝ)-(((m+t+b)/2 : ℤ) : ℝ))=
      1+(edgePhaseInteger m t a b : ℝ) := by exact_mod_cast h
  have hp : (edgePhaseInteger m t a b : ℝ)=
      if a=b then if a=1 then (-1 : ℝ)^(m+t) else -(-1 : ℝ)^(m+t)
      else (-1 : ℝ)^m := by
    rw [sign_zpow_mod_two,sign_zpow_mod_two]
    unfold edgePhaseInteger
    split_ifs <;> norm_num
  rw [hp] at hc
  linarith

end FloorHalf
end GraphicalZonotopes

end
end BundlePart245

section BundlePart246
/- Source: Papers/GraphicalZonotopes/CompleteBooleanPhase.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanFourier
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

def vertexOfSet (S : Finset I) : Cube I := fun i => decide (i∈S)
def trueSet (v : Cube I) : Finset I := univ.filter (fun i => v i=true)

@[simp] theorem trueSet_vertexOfSet (S : Finset I) : trueSet (vertexOfSet S)=S := by
  ext i
  simp [trueSet,vertexOfSet]

@[simp] theorem character_vertex_empty (A : Finset I) : character A (vertexOfSet ∅)=1 := by
  simp [character,vertexOfSet,spin]

theorem character_vertex_singleton (A : Finset I) (i : I) :
    character A (vertexOfSet {i})=if i∈A then -1 else 1 := by
  unfold character
  rw [prod_eq_single i]
  · simp [vertexOfSet,spin]
  · intro j hj hji
    simp [vertexOfSet,spin,hji]
  · simp

theorem character_vertex_pair (A : Finset I) {i j : I} (hij : i≠ j) :
    character A (vertexOfSet {i,j})=
      character A (vertexOfSet {i})*character A (vertexOfSet {j}) := by
  simp only [character,← prod_mul_distrib]
  apply prod_congr rfl
  intro k hk
  by_cases hA : k∈A
  · by_cases hi : k=i
    · subst k
      simp [vertexOfSet,spin,hA,hij]
    · by_cases hj : k=j
      · subst k
        simp [vertexOfSet,spin,hA,Ne.symm hij]
      · simp [vertexOfSet,spin,hA,hi,hj]
  · simp [hA]

/-- A quadratic Boolean phase with every mixed pair present, arbitrary linear
part `L`, and an arbitrary nonzero constant multiplier. The exponent is the
number of pairs of true bits, so this is precisely the complete quadratic form. -/
def completePhase (c : ℝ) (L : Finset I) (v : Cube I) : ℝ :=
  c*(-1 : ℝ)^((trueSet v).card.choose 2)*character L v

@[simp] theorem completePhase_empty (c : ℝ) (L : Finset I) :
    completePhase c L (vertexOfSet ∅)=c := by
  simp [completePhase]

theorem completePhase_singleton (c : ℝ) (L : Finset I) (i : I) :
    completePhase c L (vertexOfSet {i})=c*character L (vertexOfSet {i}) := by
  simp [completePhase]

theorem completePhase_pair (c : ℝ) (L : Finset I) {i j : I} (hij : i≠ j) :
    completePhase c L (vertexOfSet {i,j})=
      -c*character L (vertexOfSet {i})*character L (vertexOfSet {j}) := by
  rw [completePhase,trueSet_vertexOfSet,card_pair hij]
  norm_num
  rw [character_vertex_pair L hij]
  ring

theorem completePhase_ne_zero {c : ℝ} (hc : c≠0) (L : Finset I) (v : Cube I) :
    completePhase c L v≠0 := by
  exact mul_ne_zero (mul_ne_zero hc (pow_ne_zero _ (by norm_num)))
    (character_ne_zero L v)

theorem completePhase_isSign {c : ℝ} (hc : c=1 ∨ c=-1) (L : Finset I) (v : Cube I) :
    completePhase c L v=1 ∨ completePhase c L v=-1 := by
  have hp : ∀ n : ℕ,(-1 : ℝ)^n=1 ∨ (-1 : ℝ)^n=-1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rcases ih with h | h <;> simp [pow_succ,h]
  have hchar : character L v=1 ∨ character L v=-1 := by
    have hsq := character_square L v
    have hprod : (character L v-1)*(character L v+1)=0 := by nlinarith [hsq]
    rcases mul_eq_zero.mp hprod with h | h
    · left; linarith
    · right; linarith
  rcases hc with hc | hc <;> rcases hp ((trueSet v).card.choose 2) with hp | hp <;>
    rcases hchar with hchar | hchar <;> simp [completePhase,hc,hp,hchar]

/-- The four-corner identity of a genuine separated function. Only the
defining coordinate dependence of the two factors is used. -/
theorem separated_four_corner {G H K : Cube I → ℝ} {A : Finset I}
    (hH : DependsOn A H) (hK : DependsOn Aᶜ K)
    (hfactor : ∀ v,G v=H v*K v) {i j : I} (hi : i∈A) (hj : j∉A) :
    G (vertexOfSet ∅)*G (vertexOfSet {i,j})=
      G (vertexOfSet {i})*G (vertexOfSet {j}) := by
  have hij : i≠ j := by intro h; exact hj (h ▸ hi)
  have hH₀ : H (vertexOfSet {j})=H (vertexOfSet ∅) := by
    apply hH
    intro k hk
    have hkj : k≠ j := by intro h; exact hj (h ▸ hk)
    simp [vertexOfSet,hkj]
  have hH₁ : H (vertexOfSet {i,j})=H (vertexOfSet {i}) := by
    apply hH
    intro k hk
    have hkj : k≠ j := by intro h; exact hj (h ▸ hk)
    simp [vertexOfSet,hkj]
  have hK₀ : K (vertexOfSet {i})=K (vertexOfSet ∅) := by
    apply hK
    intro k hk
    have hki : k≠ i := by
      intro h
      have hn : k∉A := mem_compl.mp hk
      exact hn (h.symm ▸ hi)
    simp [vertexOfSet,hki]
  have hK₁ : K (vertexOfSet {i,j})=K (vertexOfSet {j}) := by
    apply hK
    intro k hk
    have hki : k≠ i := by
      intro h
      have hn : k∉A := mem_compl.mp hk
      exact hn (h.symm ▸ hi)
    simp [vertexOfSet,hki]
  rw [hfactor,hfactor,hfactor,hfactor,hH₀,hH₁,hK₀,hK₁]
  ring

/-- Every complete quadratic phase is nonseparable across every nonempty
proper partition, in every finite number of variables. This is the exact
nonfactorization property used by Theorem9.8 after the Walsh calculation. -/
theorem completePhase_nonseparable {c : ℝ} (hc : c≠0) (L : Finset I) :
    Nonseparable (completePhase c L) := by
  intro A hA htop hfactor
  obtain ⟨i,hi⟩ := hA
  obtain ⟨j,hj⟩ : ∃ j : I,j∉A := by
    by_contra! hall
    apply htop
    ext j
    simp [hall j]
  obtain ⟨H,K,hH,hK,hsep⟩ := hfactor
  have hij : i≠ j := by intro h; exact hj (h ▸ hi)
  have hs := separated_four_corner hH hK hsep hi hj
  have hm : completePhase c L (vertexOfSet ∅)*completePhase c L (vertexOfSet {i,j})=
      -(completePhase c L (vertexOfSet {i})*completePhase c L (vertexOfSet {j})) := by
    rw [completePhase_empty,completePhase_pair c L hij,
      completePhase_singleton,completePhase_singleton]
    ring
  have hzero : completePhase c L (vertexOfSet {i})*completePhase c L (vertexOfSet {j})=0 := by
    linarith [hs,hm]
  exact (mul_ne_zero (completePhase_ne_zero hc L _) (completePhase_ne_zero hc L _)) hzero

end BooleanFourier
end GraphicalZonotopes

end
end
end BundlePart246

section BundlePart247
/- Source: Papers/GraphicalZonotopes/DoubledPhase.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
open scoped BigOperators symmDiff
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem character_univ_parity (s : Cube I) :
    character univ s=QuadraticSign.parity (trueSet s).card := by
  rw [character_univ]
  have hf : ∀ i : I,spin (s i)=if i∈trueSet s then (-1 : ℝ) else 1 := by
    intro i
    cases hs : s i <;> simp [spin,trueSet,hs]
  simp_rw [hf]
  rw [prod_ite_mem_eq]
  simp [QuadraticSign.parity]

theorem trueSet_xor (s t : Cube I) :
    trueSet (fun i => Bool.xor (s i) (t i))=trueSet s∆trueSet t := by
  ext i
  cases hs : s i <;> cases ht : t i <;> simp [trueSet,Finset.mem_symmDiff,hs,ht]

@[simp] theorem firstSet_subsetOfBits (s : Cube I × Cube I) :
    firstSet (subsetOfBits s)=trueSet s.1 := by
  ext i
  simp [trueSet]

@[simp] theorem secondSet_subsetOfBits (s : Cube I × Cube I) :
    secondSet (subsetOfBits s)=trueSet s.2 := by
  ext i
  simp [trueSet]

theorem transformed_firstSet (uv : Cube I × Cube I) :
    firstSet (subsetOfBits (coordinateChange.symm uv))=trueSet uv.1 := by
  rw [firstSet_subsetOfBits]
  rfl

theorem transformed_secondSet (uv : Cube I × Cube I) :
    secondSet (subsetOfBits (coordinateChange.symm uv))=trueSet uv.1∆trueSet uv.2 := by
  rw [secondSet_subsetOfBits]
  exact trueSet_xor uv.1 uv.2

theorem integerData_transformed_phase (uv : Cube I × Cube I) :
    (-1 : ℝ)^integerData (subsetOfBits (coordinateChange.symm uv))=
      phase (completePhase 1 ∅) uv := by
  rw [integerData_phase,transformed_firstSet,transformed_secondSet,
    symmDiff_symmDiff_cancel_left,← character_univ_parity]
  simp [phase,completePhase,QuadraticSign.complete,QuadraticSign.triangle,
    QuadraticSign.parity]

theorem transformed_card_phase (uv : Cube I × Cube I) :
    (-1 : ℝ)^((subsetOfBits (coordinateChange.symm uv)).card)=character univ uv.2 := by
  change QuadraticSign.parity _=_
  rw [card_eq_first_add_second,transformed_firstSet,transformed_secondSet,
    QuadraticSign.parity_add,QuadraticSign.parity_card_symmDiff,
    ← mul_assoc,QuadraticSign.parity_square,one_mul,character_univ_parity]

/-- The complete quadratic phase occurring in an original edge row. Its
linear part depends only on whether the endpoint sides agree. -/
def rowPhase (u v : I×Fin 2) : Cube (Remaining u v) → ℝ :=
  completePhase (if u.2=1 ∧ v.2=1 then -1 else 1)
    (if u.2=v.2 then univ else ∅)

theorem rowPhase_isSign (u v : I×Fin 2) (x : Cube (Remaining u v)) :
    rowPhase u v x=1 ∨ rowPhase u v x= -1 := by
  apply completePhase_isSign
  split_ifs <;> simp

theorem rowPhase_nonseparable (u v : I×Fin 2) : Nonseparable (rowPhase u v) := by
  apply completePhase_nonseparable
  split_ifs <;> norm_num

theorem setFunction_edgeContext_rounded {u v : I×Fin 2} (huv : (graph I).Adj u v)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) :
    delta setFunction u v (edgeContext u v s)=
      (1+(if firstWeight u=firstWeight v then
          if firstWeight u=1 then
            (-1 : ℝ)^(integerData (edgeContext u v s)+(edgeContext u v s).card)
          else -(-1 : ℝ)^(integerData (edgeContext u v s)+(edgeContext u v s).card)
        else (-1 : ℝ)^integerData (edgeContext u v s)))/2 := by
  let S := edgeContext u v s
  have hmu := integerData_insert_common u S (left_not_mem_edgeContext _ _ _)
    (fun w hw => (edgeContext_all_adj u v s w hw).1)
  have hmv := integerData_insert_common v S (right_not_mem_edgeContext _ _ _)
    (fun w hw => (edgeContext_all_adj u v s w hw).2)
  have hd := integerData_mixed ((graph I).ne_of_adj huv)
    (left_not_mem_edgeContext u v s) (right_not_mem_edgeContext u v s)
  rw [if_pos huv] at hd
  have hmuv : integerData (insert u (insert v S))=
      integerData S+2*(S.card : ℤ)+firstWeight u+firstWeight v+1 := by
    change integerData (insert u (insert v S))+integerData S-
      integerData (insert u S)-integerData (insert v S)=1 at hd
    omega
  rw [delta_setFunction]
  change ((integerData (insert u (insert v S))/2+integerData S/2-
    integerData (insert u S)/2-integerData (insert v S)/2 : ℤ) : ℝ)=_
  rw [hmuv,hmu,hmv]
  push_cast
  exact FloorHalf.rounded_edge_phase _ _ _ _ (firstWeight_isBit u) (firstWeight_isBit v)

/-- The original elemental difference is exactly the Boolean tensor face
function after an explicitly invertible change of all remaining bits. -/
theorem setFunction_edgeProfile {u v : I×Fin 2} (huv : (graph I).Adj u v)
    (uv : Cube (Remaining u v) × Cube (Remaining u v)) :
    delta setFunction u v (edgeContext u v (coordinateChange.symm uv))=
      faceFunction (rowPhase u v) uv := by
  rw [setFunction_edgeContext_rounded huv,integerData_edgeContext,edgeContext_card,
    zpow_add₀ (by norm_num),zpow_natCast,integerData_transformed_phase,transformed_card_phase]
  rcases u with ⟨i,a⟩
  rcases v with ⟨j,b⟩
  fin_cases a <;> fin_cases b <;>
    simp [firstWeight,rowPhase,faceFunction,phase,completePhase] <;> ring

theorem complementFunction_edgeProfile {u v : I×Fin 2} (huv : (graph I).Adj u v)
    (uv : Cube (Remaining u v) × Cube (Remaining u v)) :
    delta complementFunction u v (edgeContext u v (coordinateChange.symm uv))=
      faceFunction (-rowPhase u v) uv := by
  rw [complementFunction,delta_sub,graphFunction_delta _ ((graph I).ne_of_adj huv)
    (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _),if_pos huv,
    setFunction_edgeProfile huv]
  simp only [faceFunction,phase,Pi.neg_apply]
  ring

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart247

section BundlePart248
/- Source: Papers/GraphicalZonotopes/DoubledLocalLines.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem remaining_nonempty (hI : 3≤ Fintype.card I) (u v : I×Fin 2) :
    Nonempty (Remaining u v) := by
  have hcard : ({u.1,v.1} : Finset I).card<(univ : Finset I).card := by
    have h : ({u.1,v.1} : Finset I).card≤2 := card_le_two
    simpa only [card_univ] using (lt_of_le_of_lt h (by omega : 2< Fintype.card I))
  obtain ⟨i,hi,hn⟩ := exists_mem_notMem_of_card_lt_card hcard
  have he : i≠ u.1 ∧ i≠ v.1 := by simpa using hn
  exact ⟨⟨i,he⟩⟩

theorem complementFunction_graphical : Graphical (graph I) (complementFunction (I := I)) := by
  intro u v huv hnon S hu hv
  rw [complementFunction,delta_sub,graphFunction_delta _ huv hu hv,
    if_neg hnon,setFunction_graphical u v huv hnon S hu hv,sub_self]

/-- A complete original row is forced to a single scale by its exact Boolean
zero pattern. All nonedge constraints are recovered before the tensor lemma
is used. -/
theorem local_row_line_of_phase {z : SetFunction (I×Fin 2)}
    (hzn : TranslationNormalized z) (hzG : Graphical (graph I) z)
    {u v : I×Fin 2} (huv : (graph I).Adj u v) [Nonempty (Remaining u v)]
    (H : Cube (Remaining u v) → ℝ) (hH : ∀ x,H x=1 ∨ H x= -1)
    (hsep : Nonseparable H)
    (hprofile : ∀ uv,delta z u v (edgeContext u v (coordinateChange.symm uv))=
      faceFunction H uv)
    (f : SetFunction (I×Fin 2)) (hfn : TranslationNormalized f)
    (hzero : ∀ a b,a≠ b → ∀ S : Finset (I×Fin 2),a∉S → b∉S →
      delta z a b S=0 → delta f a b S=0) :
    ∃ c : ℝ,∀ S : Finset (I×Fin 2),u∉S → v∉S → delta f u v S=c*delta z u v S := by
  have hfG : Graphical (graph I) f := by
    intro a b hab hnon S ha hb
    exact hzero a b hab S ha hb (hzG a b hab hnon S ha hb)
  let p : (Cube (Remaining u v) × Cube (Remaining u v)) → ℝ :=
    fun uv => delta f u v (edgeContext u v (coordinateChange.symm uv))
  have hp : p∈tensorSpace :=
    graphical_edgeProfile_mem_tensorSpace hfn hfG ((graph I).ne_of_adj huv)
  have hzeros : ∀ uv,faceFunction H uv=0 → p uv=0 := by
    intro uv he
    apply hzero u v ((graph I).ne_of_adj huv) _
      (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _)
    rwa [hprofile]
  obtain ⟨c,hc⟩ := (boolean_face_line hH hsep p hp).mp hzeros
  refine ⟨c,?_⟩
  intro S hu hv
  let s := bitsOfSubset (remainingPart u v S)
  let uv := coordinateChange s
  have he := congrFun hc uv
  change delta f u v (edgeContext u v (coordinateChange.symm uv))=
    c*faceFunction H uv at he
  rw [← hprofile uv] at he
  have hcontext : edgeContext u v (coordinateChange.symm uv)=
      S∩commonNeighbors (graph I) u v := by
    rw [show coordinateChange.symm uv=s by simp [uv]]
    exact edgeContext_remainingPart u v S
  rw [hcontext] at he
  rw [delta_commonNeighbors hfn hfG ((graph I).ne_of_adj huv) hu hv,
    delta_commonNeighbors hzn hzG ((graph I).ne_of_adj huv) hu hv]
  exact he

theorem setFunction_local_row_lines (hI : 3≤ Fintype.card I)
    (f : SetFunction (I×Fin 2)) (hfn : TranslationNormalized f)
    (hzero : ∀ a b,a≠ b → ∀ S : Finset (I×Fin 2),a∉S → b∉S →
      delta setFunction a b S=0 → delta f a b S=0)
    (e : SlopeEdge (graph I)) :
    ∃ c : ℝ,∀ S : Finset (I×Fin 2),e.1.1∉S → e.1.2∉S →
      delta f e.1.1 e.1.2 S=c*delta setFunction e.1.1 e.1.2 S := by
  letI := remaining_nonempty hI e.1.1 e.1.2
  exact local_row_line_of_phase setFunction_translationNormalized setFunction_graphical e.2
    (rowPhase e.1.1 e.1.2) (rowPhase_isSign _ _) (rowPhase_nonseparable _ _)
    (setFunction_edgeProfile e.2) f hfn hzero

theorem complementFunction_local_row_lines (hI : 3≤ Fintype.card I)
    (f : SetFunction (I×Fin 2)) (hfn : TranslationNormalized f)
    (hzero : ∀ a b,a≠ b → ∀ S : Finset (I×Fin 2),a∉S → b∉S →
      delta complementFunction a b S=0 → delta f a b S=0)
    (e : SlopeEdge (graph I)) :
    ∃ c : ℝ,∀ S : Finset (I×Fin 2),e.1.1∉S → e.1.2∉S →
      delta f e.1.1 e.1.2 S=c*delta complementFunction e.1.1 e.1.2 S := by
  letI := remaining_nonempty hI e.1.1 e.1.2
  apply local_row_line_of_phase complementFunction_translationNormalized complementFunction_graphical e.2
    (-rowPhase e.1.1 e.1.2) _ (rowPhase_nonseparable _ _).neg
    (complementFunction_edgeProfile e.2) f hfn hzero
  intro x
  rcases rowPhase_isSign e.1.1 e.1.2 x with h | h
  · exact Or.inr (by simpa using congrArg Neg.neg h)
  · exact Or.inl (by simpa using congrArg Neg.neg h)

theorem exists_nonzero_slack_of_phase {z : SetFunction (I×Fin 2)}
    {u v : I×Fin 2} [Nonempty (Remaining u v)]
    (H : Cube (Remaining u v) → ℝ) (hH : ∀ x,H x=1 ∨ H x= -1)
    (hprofile : ∀ uv,delta z u v (edgeContext u v (coordinateChange.symm uv))=
      faceFunction H uv) :
    ∃ S : Finset (I×Fin 2),u∉S ∧ v∉S ∧ delta z u v S≠0 := by
  have hne := faceFunction_ne_zero hH
  have hex : ∃ uv,faceFunction H uv≠0 := by
    by_contra! hall
    apply hne
    funext uv
    exact hall uv
  obtain ⟨uv,huv⟩ := hex
  refine ⟨edgeContext u v (coordinateChange.symm uv),
    left_not_mem_edgeContext _ _ _,right_not_mem_edgeContext _ _ _,?_⟩
  rwa [hprofile]

theorem setFunction_nonzero_slack (hI : 3≤ Fintype.card I) {u v : I×Fin 2}
    (huv : (graph I).Adj u v) :
    ∃ S : Finset (I×Fin 2),u∉S ∧ v∉S ∧ delta setFunction u v S≠0 := by
  letI := remaining_nonempty hI u v
  exact exists_nonzero_slack_of_phase (rowPhase u v) (rowPhase_isSign u v)
    (setFunction_edgeProfile huv)

theorem complementFunction_nonzero_slack (hI : 3≤ Fintype.card I) {u v : I×Fin 2}
    (huv : (graph I).Adj u v) :
    ∃ S : Finset (I×Fin 2),u∉S ∧ v∉S ∧ delta complementFunction u v S≠0 := by
  letI := remaining_nonempty hI u v
  apply exists_nonzero_slack_of_phase (-rowPhase u v) _ (complementFunction_edgeProfile huv)
  intro x
  rcases rowPhase_isSign u v x with h | h
  · exact Or.inr (by simpa using congrArg Neg.neg h)
  · exact Or.inl (by simpa using congrArg Neg.neg h)

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart248

section BundlePart249
/- Source: Papers/GraphicalZonotopes/DoubledConnectivity.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

def selectedClique (T : Finset I) (b : I → Fin 2) : Finset (I×Fin 2) :=
  T.image fun i => (i,b i)

@[simp] theorem mem_selectedClique (T : Finset I) (b : I → Fin 2) (w : I×Fin 2) :
    w∈selectedClique T b ↔ w.1∈T ∧ b w.1=w.2 := by
  constructor
  · intro hw
    obtain ⟨i,hi,he⟩ := mem_image.mp hw
    have h1 : i=w.1 := congrArg Prod.fst he
    have h2 : b i=w.2 := congrArg Prod.snd he
    simpa [h1] using And.intro hi h2
  · rintro ⟨hi,hb⟩
    exact mem_image.mpr ⟨w.1,hi,Prod.ext rfl hb⟩

@[simp] theorem selectedClique_card (T : Finset I) (b : I → Fin 2) :
    (selectedClique T b).card=T.card :=
  card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)

theorem selectedClique_isClique (T : Finset I) (b : I → Fin 2) :
    (graph I).IsClique (selectedClique T b) := by
  intro u hu v hv huv
  have hu' := (mem_selectedClique T b u).mp hu
  have hv' := (mem_selectedClique T b v).mp hv
  intro he
  apply huv
  apply Prod.ext he
  rw [← hu'.2,← hv'.2,he]

def canonicalEdge (e : SlopeEdge (graph I)) : SlopeEdge (graph I) :=
  ⟨((e.1.1.1,0),(e.1.2.1,0)),e.2⟩

theorem shared_four_reachable {z : SetFunction (I×Fin 2)}
    (hnon : ∀ C : Finset (I×Fin 2),C.card=4 → (graph I).IsClique C → mobius z C≠0)
    (e f : SlopeEdge (graph I)) {C : Finset (I×Fin 2)}
    (hcard : C.card=4) (hC : (graph I).IsClique C)
    (he₁ : e.1.1∈C) (he₂ : e.1.2∈C) (hf₁ : f.1.1∈C) (hf₂ : f.1.2∈C) :
    (coefficientEdgeGraph (graph I) z).Reachable e f := by
  by_cases hef : e=f
  · subst f
    exact SimpleGraph.Reachable.rfl
  · exact SimpleGraph.Adj.reachable ⟨hef,C,hnon C hcard hC,he₁,he₂,hf₁,hf₂⟩

theorem edge_reachable_canonical (hI : 4≤ Fintype.card I)
    {z : SetFunction (I×Fin 2)}
    (hnon : ∀ C : Finset (I×Fin 2),C.card=4 → (graph I).IsClique C → mobius z C≠0)
    (e : SlopeEdge (graph I)) :
    (coefficientEdgeGraph (graph I) z).Reachable e (canonicalEdge e) := by
  let a := e.1.1.1
  let b := e.1.2.1
  have hab : a≠ b := e.2
  obtain ⟨T,hST,hTU,hT⟩ := exists_subsuperset_card_eq
    (subset_univ ({a,b} : Finset I))
    (show ({a,b} : Finset I).card≤4 by simp [card_pair hab])
    (show 4≤(univ : Finset I).card by simpa using hI)
  have hD : (T\{a,b}).card=2 := by rw [card_sdiff_of_subset hST,hT,card_pair hab]
  obtain ⟨i,j,hij,hDij⟩ := card_eq_two.mp hD
  have hi : i∈T ∧ i≠ a ∧ i≠ b := by
    have h : i∈T\{a,b} := by rw [hDij]; simp
    simpa using h
  have hj : j∈T ∧ j≠ a ∧ j≠ b := by
    have h : j∈T\{a,b} := by rw [hDij]; simp
    simpa using h
  have haT : a∈T := hST (by simp)
  have hbT : b∈T := hST (by simp)
  let f : SlopeEdge (graph I) := ⟨((i,0),(j,0)),hij⟩
  let bits : I → Fin 2 := fun k => if k=a then e.1.1.2 else if k=b then e.1.2.2 else 0
  have hfirst : (coefficientEdgeGraph (graph I) z).Reachable e f := by
    apply shared_four_reachable hnon e f (C := selectedClique T bits)
      (by simpa using hT) (selectedClique_isClique T bits)
    · simp [bits,a,haT]
    · simp [bits,b,a,hbT,Ne.symm hab]
    · simp [f,bits,hi.1,hi.2.1,hi.2.2]
    · simp [f,bits,hj.1,hj.2.1,hj.2.2]
  have hsecond : (coefficientEdgeGraph (graph I) z).Reachable f (canonicalEdge e) := by
    apply shared_four_reachable hnon f (canonicalEdge e) (C := selectedClique T (fun _ => 0))
      (by simpa using hT) (selectedClique_isClique T (fun _ => 0))
    · simp [f,hi.1]
    · simp [f,hj.1]
    · simpa [canonicalEdge,a] using haT
    · simpa [canonicalEdge,b] using hbT
  exact hfirst.trans hsecond

theorem canonical_edges_reachable (hI : 4≤ Fintype.card I)
    {z : SetFunction (I×Fin 2)}
    (hnon : ∀ C : Finset (I×Fin 2),C.card=4 → (graph I).IsClique C → mobius z C≠0)
    (e f : SlopeEdge (graph I)) :
    (coefficientEdgeGraph (graph I) z).Reachable (canonicalEdge e) (canonicalEdge f) := by
  let S : Finset I := {e.1.1.1,e.1.2.1,f.1.1.1,f.1.2.1}
  obtain ⟨T,hST,hTU,hT⟩ := exists_subsuperset_card_eq
    (subset_univ S) (show S.card≤4 from card_le_four) (by simpa using hI)
  apply shared_four_reachable hnon (canonicalEdge e) (canonicalEdge f)
    (C := selectedClique T (fun _ => 0)) (by simpa using hT)
    (selectedClique_isClique T (fun _ => 0))
  · simpa [canonicalEdge] using hST (by simp [S] : e.1.1.1∈S)
  · simpa [canonicalEdge] using hST (by simp [S] : e.1.2.1∈S)
  · simpa [canonicalEdge] using hST (by simp [S] : f.1.1.1∈S)
  · simpa [canonicalEdge] using hST (by simp [S] : f.1.2.1∈S)

theorem slopeEdge_nonempty (hI : 2≤ Fintype.card I) : Nonempty (SlopeEdge (graph I)) := by
  obtain ⟨S,hS,hcard⟩ := exists_subset_card_eq
    (show 2≤(univ : Finset I).card by simpa using hI)
  obtain ⟨i,j,hij,rfl⟩ := card_eq_two.mp hcard
  exact ⟨⟨((i,0),(j,0)),hij⟩⟩

/-- Nonzero tetrahedral coefficients connect all actual edge scales, with no
bound on the number of doubled parts. -/
theorem coefficientEdgeGraph_connected (hI : 4≤ Fintype.card I)
    {z : SetFunction (I×Fin 2)}
    (hnon : ∀ C : Finset (I×Fin 2),C.card=4 → (graph I).IsClique C → mobius z C≠0) :
    (coefficientEdgeGraph (graph I) z).Connected := by
  letI := slopeEdge_nonempty (by omega : 2≤ Fintype.card I)
  refine ⟨?_⟩
  intro e f
  exact (edge_reachable_canonical hI hnon e).trans
    ((canonical_edges_reachable hI hnon e f).trans (edge_reachable_canonical hI hnon f).symm)

theorem graph_connected (hI : 2≤ Fintype.card I) : (graph I).Connected := by
  obtain ⟨e⟩ := slopeEdge_nonempty hI
  letI : Nonempty (I×Fin 2) := ⟨e.1.1⟩
  refine ⟨?_⟩
  intro u v
  by_cases huv : u.1≠ v.1
  · exact SimpleGraph.Adj.reachable huv
  · have he : u.1=v.1 := not_not.mp huv
    obtain ⟨i,hi,hn⟩ := exists_mem_notMem_of_card_lt_card
      (show ({u.1} : Finset I).card<(univ : Finset I).card by simpa using (show 1 < Fintype.card I by omega))
    have hiu : i≠ u.1 := by simpa using hn
    have hiv : i≠ v.1 := by simpa only [he] using hiu
    exact (SimpleGraph.Adj.reachable (show (graph I).Adj u (i,0) from Ne.symm hiu)).trans
      (SimpleGraph.Adj.reachable (show (graph I).Adj (i,0) v from hiv))

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart249

section BundlePart250
/- Source: Papers/GraphicalZonotopes/DoubledStarScales.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem exists_four_clique_containing_three (hI : 4≤ Fintype.card I)
    (a b c : I×Fin 2) (hab : a.1≠ b.1) (hac : a.1≠ c.1) (hbc : b.1≠ c.1) :
    ∃ C : Finset (I×Fin 2),C.card=4 ∧ (graph I).IsClique C ∧ a∈C ∧ b∈C ∧ c∈C := by
  obtain ⟨T,hST,hTU,hT⟩ := exists_subsuperset_card_eq
    (subset_univ ({a.1,b.1,c.1} : Finset I))
    (show ({a.1,b.1,c.1} : Finset I).card≤4 by
      have h : ({a.1,b.1,c.1} : Finset I).card≤3 := card_le_three
      omega)
    (show 4≤(univ : Finset I).card by simpa using hI)
  let bits : I → Fin 2 := fun i => if i=a.1 then a.2 else if i=b.1 then b.2
    else if i=c.1 then c.2 else 0
  refine ⟨selectedClique T bits,by simpa using hT,selectedClique_isClique T bits,?_,?_,?_⟩
  · simp [bits,hST (by simp : a.1∈({a.1,b.1,c.1} : Finset I))]
  · simp [bits,Ne.symm hab,hST (by simp : b.1∈({a.1,b.1,c.1} : Finset I))]
  · simp [bits,Ne.symm hac,Ne.symm hbc,
      hST (by simp : c.1∈({a.1,b.1,c.1} : Finset I))]

abbrev AtVertex (a : I×Fin 2) := {v : I×Fin 2 // (graph I).Adj a v}

theorem exists_star_vertex (hI : 2≤ Fintype.card I) (a : I×Fin 2) : Nonempty (AtVertex a) := by
  obtain ⟨i,hi,hn⟩ := exists_mem_notMem_of_card_lt_card
    (show ({a.1} : Finset I).card<(univ : Finset I).card by simp only [card_singleton,card_univ]; omega)
  have hia : i≠ a.1 := by simpa using hn
  exact ⟨⟨(i,0),Ne.symm hia⟩⟩

/-- Every locally determined scale on an edge at one fixed vertex is the
same, using only nonzero four-clique coefficients and arbitrary r≥4. -/
theorem star_scales_constant (hI : 4≤ Fintype.card I) (a : I×Fin 2)
    (z f : SetFunction (I×Fin 2))
    (hnon : ∀ C : Finset (I×Fin 2),C.card=4 → (graph I).IsClique C → mobius z C≠0)
    (scale : AtVertex a → ℝ)
    (hscale : ∀ v : AtVertex a,∀ S : Finset (I×Fin 2),a∉S → v.1∉S →
      delta f a v.1 S=scale v*delta z a v.1 S) :
    ∃ t : ℝ,∀ v : AtVertex a,scale v=t := by
  letI := exists_star_vertex (by omega : 2≤ Fintype.card I) a
  obtain ⟨v₀⟩ := ‹Nonempty (AtVertex a)›
  have hdiff (v w : AtVertex a) (hvw : v.1.1≠ w.1.1) : scale v=scale w := by
    obtain ⟨C,hcard,hC,ha,hv,hw⟩ :=
      exists_four_clique_containing_three hI a v.1 w.1 v.2 w.2 hvw
    have hv' := mobius_scale_of_delta_scale ((graph I).ne_of_adj v.2)
      (scale v) (hscale v) ha hv
    have hw' := mobius_scale_of_delta_scale ((graph I).ne_of_adj w.2)
      (scale w) (hscale w) ha hw
    exact mul_right_cancel₀ (hnon C hcard hC) (hv'.symm.trans hw')
  refine ⟨scale v₀,?_⟩
  intro v
  by_cases hparts : v.1.1≠ v₀.1.1
  · exact hdiff v v₀ hparts
  · obtain ⟨i,hi,hn⟩ := exists_mem_notMem_of_card_lt_card
      (show ({a.1,v.1.1} : Finset I).card<(univ : Finset I).card by
        have h : ({a.1,v.1.1} : Finset I).card≤2 := card_le_two
        simpa only [card_univ] using (lt_of_le_of_lt h (by omega : 2< Fintype.card I)))
    have hn' : i≠ a.1 ∧ i≠ v.1.1 := by simpa using hn
    let w : AtVertex a := ⟨(i,0),Ne.symm hn'.1⟩
    have hp : v.1.1=v₀.1.1 := not_not.mp hparts
    exact (hdiff v w (Ne.symm hn'.2)).trans (hdiff w v₀ (by simpa [w,← hp] using hn'.2))

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart250

section BundlePart251
/- Source: Papers/GraphicalZonotopes/IgnoredVertices.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vanishing of all original elemental rows at a normalized vertex means
the function is independent of that vertex, on every subset. -/
theorem insert_eq_of_zero_incident {f : SetFunction V} (hn : TranslationNormalized f)
    (a : V) (hzero : ∀ v,a≠ v → ∀ S : Finset V,a∉S → v∉S → delta f a v S=0) :
    ∀ S : Finset V,f (insert a S)=f S := by
  intro S
  by_cases ha : a∈S
  · rw [insert_eq_of_mem ha]
  · revert ha
    induction S using Finset.induction_on with
    | empty => simp only [insert_empty_eq,show f ∅=0 from hn.1,hn.2,implies_true]
    | @insert v S hv ih =>
      intro ha
      have hav : a≠ v := fun he => ha (by simp [he])
      have haS : a∉S := fun h => ha (mem_insert_of_mem h)
      have hd := hzero v hav S haS hv
      have hi := ih haS
      unfold delta at hd
      linarith

theorem erase_eq_of_insert_eq {f : SetFunction V} {a : V}
    (hf : ∀ S : Finset V,f (insert a S)=f S) (S : Finset V) : f (S.erase a)=f S := by
  by_cases ha : a∈S
  · have h := hf (S.erase a)
    rw [insert_erase ha] at h
    exact h.symm
  · rw [erase_eq_of_notMem ha]

theorem delta_insert_eq_of_insert_eq {f : SetFunction V} {a : V}
    (hf : ∀ S : Finset V,f (insert a S)=f S) (u v : V) (S : Finset V) :
    delta f u v (insert a S)=delta f u v S := by
  simp only [delta,insert_comm u a,insert_comm v a,hf]

theorem delta_zero_of_insert_eq {f : SetFunction V} {a : V}
    (hf : ∀ S : Finset V,f (insert a S)=f S) (v : V) (S : Finset V) :
    delta f a v S=0 := by
  simp only [delta,hf]
  ring

namespace VertexDeletion

abbrev Retained (d : V) := {v : V // v≠ d}

def embedding (d : V) : Retained d ↪ V := Function.Embedding.subtype _

@[simp] theorem deleted_not_range (d : V) : d∉Set.range (embedding d) := by
  rintro ⟨v,hv⟩
  exact v.2 hv

theorem map_pullSet (d : V) (S : Finset V) :
    (SetFunctionEmbedding.pullSet (embedding d) S).map (embedding d)=S.erase d := by
  ext v
  simp only [mem_map,SetFunctionEmbedding.mem_pullSet,mem_erase]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w.2,hw⟩
  · rintro ⟨hv,hS⟩
    exact ⟨⟨v,hv⟩,hS,rfl⟩

theorem extend_restrict (d : V) (f : SetFunction V) (S : Finset V) :
    SetFunctionEmbedding.extend (embedding d)
      (SetFunctionEmbedding.restrict (embedding d) f) S=f (S.erase d) := by
  simp only [SetFunctionEmbedding.extend,SetFunctionEmbedding.restrict,map_pullSet]

theorem delta_erase_function {f : SetFunction V} (d u v : V)
    (hu : u≠ d) (hv : v≠ d) (S : Finset V) :
    delta (fun T => f (T.erase d)) u v S=delta f u v (S.erase d) := by
  simp only [delta,erase_insert_of_ne hu,erase_insert_of_ne hv]

theorem delta_erase_eq_of_insert_eq {f : SetFunction V} {a : V}
    (hf : ∀ S : Finset V,f (insert a S)=f S) (u v : V)
    (hu : u≠ a) (hv : v≠ a) (S : Finset V) :
    delta f u v (S.erase a)=delta f u v S := by
  rw [← delta_erase_function a u v hu hv]
  have he : (fun T => f (T.erase a))=f := funext (erase_eq_of_insert_eq hf)
  rw [he]

theorem extended_tight_zero (d : V) (z : SetFunction V)
    (f : SetFunction (Retained d))
    (hzero : ∀ u v : Retained d,u≠ v → ∀ S : Finset (Retained d),u∉S → v∉S →
      delta (SetFunctionEmbedding.restrict (embedding d) z) u v S=0 → delta f u v S=0)
    {u v : V} (huv : u≠ v) (hud : u≠ d) (hvd : v≠ d)
    {S : Finset V} (hu : u∉S) (hv : v∉S) (hd : d∉S) (hz : delta z u v S=0) :
    delta (SetFunctionEmbedding.extend (embedding d) f) u v S=0 := by
  let u' : Retained d := ⟨u,hud⟩
  let v' : Retained d := ⟨v,hvd⟩
  have he := hzero u' v' (fun h => huv (congrArg Subtype.val h))
    (SetFunctionEmbedding.pullSet (embedding d) S) (by simpa [u',embedding] using hu) (by simpa [v',embedding] using hv)
  have hsmall : delta (SetFunctionEmbedding.restrict (embedding d) z) u' v'
      (SetFunctionEmbedding.pullSet (embedding d) S)=0 := by
    rw [SetFunctionEmbedding.delta_restrict,map_pullSet,erase_eq_of_notMem hd]
    exact hz
  have h := he hsmall
  simpa only [← SetFunctionEmbedding.delta_extend,embedding,u',v',Function.Embedding.coe_subtype] using h

/-- A graphical row is insensitive to deleting a nonneighbor of its first
endpoint. This follows from the full clique-coordinate dictionary. -/
theorem delta_delete_nonNeighbor {G : SimpleGraph V} {f : SetFunction V}
    (hn : TranslationNormalized f) (hG : Graphical G f)
    {d u v : V} (huv : u≠ v) (hu : u≠ d) (hv : v≠ d) (hd : ¬G.Adj u d)
    {S : Finset V} (huS : u∉S) (hvS : v∉S) :
    delta (fun T => f (T.erase d)) u v S=delta f u v S := by
  rw [delta_erase_function d u v hu hv]
  rw [delta_commonNeighbors hn hG huv (by simpa [hu] using huS) (by simpa [hv] using hvS),
    delta_commonNeighbors hn hG huv huS hvS]
  have he : S.erase d∩commonNeighbors G u v=S∩commonNeighbors G u v := by
    ext w
    simp only [mem_inter,mem_erase]
    constructor
    · exact fun h => ⟨h.1.2,h.2⟩
    · intro h
      refine ⟨⟨?_,h.1⟩,h.2⟩
      intro hwd
      subst w
      exact hd ((mem_commonNeighbors G u v d).mp h.2).1
  rw [he]

end VertexDeletion
end GraphicalZonotopes

end
end
end BundlePart251

section BundlePart252
/- Source: Papers/GraphicalZonotopes/BooleanSliceIntersection.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanFourier
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem faceFunction_injective : Function.Injective (faceFunction (I := I)) := by
  intro G H he
  funext v
  have hv : (1+G v)/2=(1+H v)/2 := by
    simpa [faceFunction,phase,character,spin] using
      congrFun he ((fun _ => false),v)
  linarith

/-- Two distinct Boolean functions cannot span the same nonzero real ray
or line. This elementary fact is applied to literal elemental-row slices. -/
theorem eq_zero_of_two_boolean_lines {X : Type*} {f g p : X → ℝ}
    (hf : ∀ x,f x=0 ∨ f x=1) (hg : ∀ x,g x=0 ∨ g x=1)
    (hfg : f≠ g) (hp : ∃ c : ℝ,p=c • f) (hq : ∃ d : ℝ,p=d • g) : p=0 := by
  obtain ⟨c,hc⟩ := hp
  obtain ⟨d,hd⟩ := hq
  by_cases hp0 : p=0
  · exact hp0
  have hc0 : c≠0 := by
    intro h
    apply hp0
    simpa [h] using hc
  have hf0 : f≠0 := by
    intro h
    apply hp0
    simpa [h] using hc
  obtain ⟨x,hx⟩ : ∃ x,f x=1 := by
    by_contra! hn
    apply hf0
    funext x
    exact (hf x).resolve_right (hn x)
  have he : c • f=d • g := hc.symm.trans hd
  have hx' := congrFun he x
  simp only [Pi.smul_apply,smul_eq_mul,hx,mul_one] at hx'
  have hcd : c=d := by
    rcases hg x with hgx | hgx
    · rw [hgx,mul_zero] at hx'
      exact False.elim (hc0 hx')
    · simpa only [hgx,mul_one] using hx'
  apply False.elim
  apply hfg
  funext y
  have hy := congrFun he y
  simp only [Pi.smul_apply,smul_eq_mul,← hcd] at hy
  exact mul_left_cancel₀ hc0 hy

/-- The two-slice elimination used in Corollaries9.10 and9.11: the same
tensor polynomial satisfying both complete zero sets must vanish. -/
theorem boolean_slice_intersection [Nonempty I] {G H : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v= -1) (hH : ∀ v,H v=1 ∨ H v= -1)
    (hsepG : Nonseparable G) (hsepH : Nonseparable H) (hGH : G≠ H)
    (p : (Cube I × Cube I) → ℝ) (hp : p∈tensorSpace)
    (hzeroG : ∀ uv,faceFunction G uv=0 → p uv=0)
    (hzeroH : ∀ uv,faceFunction H uv=0 → p uv=0) : p=0 := by
  exact eq_zero_of_two_boolean_lines (faceFunction_boolean hG) (faceFunction_boolean hH)
    (fun h => hGH (faceFunction_injective h))
    ((boolean_face_line hG hsepG p hp).mp hzeroG)
    ((boolean_face_line hH hsepH p hp).mp hzeroH)

/-- Multiplication by the parity character is nonconstant in every positive
number of variables, even when accompanied by an arbitrary constant sign. -/
theorem ne_parity_multiple [Nonempty I] {G : Cube I → ℝ}
    (hG : ∀ v,G v≠0) (c : ℝ) : G≠ fun v => c*character univ v*G v := by
  intro he
  have h0 := congrFun he (vertexOfSet ∅)
  rw [character_vertex_empty,mul_one] at h0
  have hc : c=1 := by
    apply (mul_right_cancel₀ (hG (vertexOfSet ∅)))
    simpa only [one_mul] using h0.symm
  obtain ⟨i⟩ := ‹Nonempty I›
  have h1 := congrFun he (vertexOfSet {i})
  rw [hc,one_mul,character_vertex_singleton,if_pos (mem_univ i)] at h1
  have hz : G (vertexOfSet {i})=0 := by linarith
  exact hG _ hz

end BooleanFourier
end GraphicalZonotopes

end
end
end BundlePart252

section BundlePart253
/- Source: Papers/GraphicalZonotopes/BooleanSlicing.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanFourier
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev DeletedIndex (a : I) := {i : I // i≠ a}

def extendCube (a : I) (b : Bool) (v : Cube (DeletedIndex a)) : Cube I :=
  fun i => if h : i=a then b else v ⟨i,h⟩

@[simp] theorem extendCube_at (a : I) (b : Bool) (v : Cube (DeletedIndex a)) :
    extendCube a b v a=b := by simp [extendCube]

@[simp] theorem extendCube_other (a : I) (b : Bool) (v : Cube (DeletedIndex a))
    (i : DeletedIndex a) : extendCube a b v i=v i := by simp [extendCube,i.2]

theorem prod_split_deleted (a : I) (f : I → ℝ) :
    (∏ i,f i)=f a*∏ i : DeletedIndex a,f i := by
  rw [← mul_prod_erase univ f (mem_univ a)]
  rw [prod_subtype (p := fun i : I => i≠ a) (univ.erase a) (by simp) f]

def deletedSet (a : I) (L : Finset I) : Finset (DeletedIndex a) :=
  univ.filter fun i => i.1∈L

@[simp] theorem mem_deletedSet (a : I) (L : Finset I) (i : DeletedIndex a) :
    i∈deletedSet a L ↔ i.1∈L := by simp [deletedSet]

@[simp] theorem deletedSet_univ (a : I) : deletedSet a univ=univ := by
  ext i
  simp

theorem character_extendCube (a : I) (b : Bool) (v : Cube (DeletedIndex a)) (L : Finset I) :
    character L (extendCube a b v)=
      (if a∈L then spin b else 1)*character (deletedSet a L) v := by
  unfold character
  rw [prod_split_deleted a]
  simp only [extendCube_at,extendCube_other,mem_deletedSet]

theorem trueSet_extendCube_false (a : I) (v : Cube (DeletedIndex a)) :
    trueSet (extendCube a false v)=(trueSet v).map (Function.Embedding.subtype _) := by
  ext i
  by_cases hi : i=a
  · subst i
    simp [trueSet]
  · simp only [trueSet,mem_filter,mem_univ,true_and,mem_map]
    constructor
    · intro h
      exact ⟨⟨i,hi⟩,by simpa [extendCube,hi] using h,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      simpa using hj

theorem trueSet_extendCube_true (a : I) (v : Cube (DeletedIndex a)) :
    trueSet (extendCube a true v)=insert a ((trueSet v).map (Function.Embedding.subtype _)) := by
  ext i
  by_cases hi : i=a
  · subst i
    simp [trueSet]
  · simp only [trueSet,mem_filter,mem_univ,true_and,mem_insert,hi,false_or,mem_map]
    constructor
    · intro h
      exact ⟨⟨i,hi⟩,by simpa [extendCube,hi] using h,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      simpa using hj

@[simp] theorem trueSet_extendCube_false_card (a : I) (v : Cube (DeletedIndex a)) :
    (trueSet (extendCube a false v)).card=(trueSet v).card := by
  rw [trueSet_extendCube_false,card_map]

@[simp] theorem trueSet_extendCube_true_card (a : I) (v : Cube (DeletedIndex a)) :
    (trueSet (extendCube a true v)).card=(trueSet v).card+1 := by
  rw [trueSet_extendCube_true,card_insert_of_notMem,card_map]
  simp

theorem completePhase_extendCube_false (a : I) (c : ℝ) (L : Finset I)
    (v : Cube (DeletedIndex a)) :
    completePhase c L (extendCube a false v)=completePhase c (deletedSet a L) v := by
  simp [completePhase,character_extendCube,spin]

theorem completePhase_extendCube_true (a : I) (c : ℝ) (L : Finset I)
    (v : Cube (DeletedIndex a)) :
    completePhase c L (extendCube a true v)=
      (if a∈L then -1 else 1)*character univ v*completePhase c (deletedSet a L) v := by
  simp only [completePhase,trueSet_extendCube_true_card,character_extendCube,spin,ite_true]
  have hp : (-1 : ℝ)^((trueSet v).card+1).choose 2=
      (-1 : ℝ)^((trueSet v).card.choose 2)*(-1 : ℝ)^((trueSet v).card) := by
    simpa [QuadraticSign.triangle,QuadraticSign.parity] using
      QuadraticSign.triangle_succ (trueSet v).card
  rw [hp,DoubledParts.character_univ_parity]
  change _=(if a∈L then -1 else 1)*(-1 : ℝ)^((trueSet v).card)*_
  ring

def slicePhase (a : I) (c : ℝ) (L : Finset I) (b : Bool) : Cube (DeletedIndex a) → ℝ :=
  if b then completePhase (-(if a∈L then -1 else 1)*c) (deletedSet a L)ᶜ
  else completePhase c (deletedSet a L)

/-- Fixing the two original signs of a deleted part to `(b, false)` fixes
both transformed bits to `b`; its two actual slices are again Boolean faces. -/
theorem faceFunction_slice (a : I) (c : ℝ) (L : Finset I) (b : Bool)
    (uv : Cube (DeletedIndex a) × Cube (DeletedIndex a)) :
    faceFunction (completePhase c L)
        (extendCube a b uv.1,extendCube a b uv.2)=faceFunction (slicePhase a c L b) uv := by
  cases b
  · simp [faceFunction,phase,character_extendCube,completePhase_extendCube_false,slicePhase,spin]
  · rw [faceFunction,phase,character_extendCube,deletedSet_univ,
      completePhase_extendCube_true]
    simp only [mem_univ,ite_true,spin]
    rw [faceFunction,phase]
    simp only [slicePhase,ite_true]
    simp only [completePhase]
    rw [← character_compl]
    ring

theorem slicePhase_isSign (a : I) {c : ℝ} (hc : c=1 ∨ c= -1) (L : Finset I)
    (b : Bool) (v : Cube (DeletedIndex a)) :
    slicePhase a c L b v=1 ∨ slicePhase a c L b v= -1 := by
  cases b
  · exact completePhase_isSign hc _ _
  · apply completePhase_isSign
    rcases hc with rfl | rfl <;> split_ifs <;> norm_num

theorem slicePhase_nonseparable (a : I) {c : ℝ} (hc : c≠0) (L : Finset I) (b : Bool) :
    Nonseparable (slicePhase a c L b) := by
  cases b
  · exact completePhase_nonseparable hc _
  · apply completePhase_nonseparable
    apply mul_ne_zero _ hc
    split_ifs <;> norm_num

theorem slicePhase_distinct (a : I) [Nonempty (DeletedIndex a)] {c : ℝ}
    (hc : c≠0) (L : Finset I) : slicePhase a c L false≠ slicePhase a c L true := by
  have he : slicePhase a c L true=(fun v =>
      -(if a∈L then -1 else 1)*character univ v*completePhase c (deletedSet a L) v) := by
    funext v
    simp only [slicePhase,ite_true]
    simp only [completePhase]
    rw [← character_compl]
    ring
  rw [he]
  exact ne_parity_multiple (completePhase_ne_zero hc _) _

/-- Evaluation at arbitrary fixed values of the removed transformed bits
preserves the exact tensor space on the remaining coordinates. -/
theorem tensorSpace_slice (a : I) (b c : Bool) {p : (Cube I × Cube I) → ℝ}
    (hp : p∈tensorSpace) :
    (fun uv : Cube (DeletedIndex a) × Cube (DeletedIndex a) =>
      p (extendCube a b uv.1,extendCube a c uv.2))∈tensorSpace := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨s,rfl⟩ := hp
    let k : ℝ := match s a with
      | none => 1
      | some false => spin b
      | some true => spin b*spin c
    have ht : tensorMonomial (fun i : DeletedIndex a => s i)∈tensorSpace :=
      Submodule.subset_span ⟨_,rfl⟩
    convert (tensorSpace (I := DeletedIndex a)).smul_mem k ht using 1
    funext uv
    simp only [tensorMonomial,Pi.smul_apply,smul_eq_mul]
    rw [prod_split_deleted a]
    simp only [extendCube_at,extendCube_other]
    rfl
  | zero =>
    exact (tensorSpace (I := DeletedIndex a)).zero_mem
  | add p q hp hq ihp ihq =>
    exact (tensorSpace (I := DeletedIndex a)).add_mem ihp ihq
  | smul r p hp ih =>
    exact (tensorSpace (I := DeletedIndex a)).smul_mem r ih

end BooleanFourier
end GraphicalZonotopes

end
end
end BundlePart253

section BundlePart254
/- Source: Papers/GraphicalZonotopes/DoubledRestrictedLines.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Only the contexts in the actual remaining-part cube are needed for one
row-line argument; graphicality itself is an independently proved premise. -/
theorem graphical_row_line_of_profile {z f : SetFunction (I×Fin 2)}
    (hzn : TranslationNormalized z) (hzG : Graphical (graph I) z)
    (hfn : TranslationNormalized f) (hfG : Graphical (graph I) f)
    {u v : I×Fin 2} (huv : (graph I).Adj u v) [Nonempty (Remaining u v)]
    (H : Cube (Remaining u v) → ℝ) (hH : ∀ x,H x=1 ∨ H x= -1)
    (hsep : Nonseparable H)
    (hprofile : ∀ uv,delta z u v (edgeContext u v (coordinateChange.symm uv))=faceFunction H uv)
    (hzero : ∀ uv,faceFunction H uv=0 →
      delta f u v (edgeContext u v (coordinateChange.symm uv))=0) :
    ∃ t : ℝ,∀ S : Finset (I×Fin 2),u∉S → v∉S → delta f u v S=t*delta z u v S := by
  let p : (Cube (Remaining u v) × Cube (Remaining u v)) → ℝ :=
    fun uv => delta f u v (edgeContext u v (coordinateChange.symm uv))
  have hp : p∈tensorSpace :=
    graphical_edgeProfile_mem_tensorSpace hfn hfG ((graph I).ne_of_adj huv)
  obtain ⟨t,ht⟩ := (boolean_face_line hH hsep p hp).mp hzero
  refine ⟨t,?_⟩
  intro S hu hv
  let s := bitsOfSubset (remainingPart u v S)
  let uv := coordinateChange s
  have h := congrFun ht uv
  change delta f u v (edgeContext u v (coordinateChange.symm uv))=t*faceFunction H uv at h
  rw [← hprofile] at h
  have he : edgeContext u v (coordinateChange.symm uv)=S∩commonNeighbors (graph I) u v := by
    rw [show coordinateChange.symm uv=s by simp [uv]]
    exact edgeContext_remainingPart u v S
  rw [he] at h
  rw [delta_commonNeighbors hfn hfG ((graph I).ne_of_adj huv) hu hv,
    delta_commonNeighbors hzn hzG ((graph I).ne_of_adj huv) hu hv]
  exact h

theorem same_part_not_mem_edgeContext {a d v : I×Fin 2} (hd : d.1=a.1)
    (s : Cube (Remaining a v) × Cube (Remaining a v)) : d∉edgeContext a v s := by
  intro hm
  obtain ⟨w,hw,he⟩ := mem_map.mp hm
  have hh : w.1.1=a.1 := (congrArg Prod.fst he).trans hd
  exact w.1.2.1 hh

/-- Every edge at the singleton retains exactly its full Boolean-face line
after the other vertex in that part is deleted. The kernel vector is lifted
from the actual retained coordinate space. -/
theorem deletion_incident_row_line (hI : 3≤ Fintype.card I)
    (a d : I×Fin 2) (had : a≠ d) (hpart : d.1=a.1)
    {z : SetFunction (I×Fin 2)} (hzn : TranslationNormalized z)
    (hzG : Graphical (graph I) z)
    (hlocalPhase : ∀ v : AtVertex a,∃ H : Cube (Remaining a v.1) → ℝ,
      (∀ x,H x=1 ∨ H x= -1) ∧ Nonseparable H ∧
      ∀ uv,delta z a v.1 (edgeContext a v.1 (coordinateChange.symm uv))=faceFunction H uv)
    (f : SetFunction (VertexDeletion.Retained d)) (hfn : TranslationNormalized f)
    (hzero : ∀ u v : VertexDeletion.Retained d,u≠ v →
      ∀ S : Finset (VertexDeletion.Retained d),u∉S → v∉S →
      delta (SetFunctionEmbedding.restrict (VertexDeletion.embedding d) z) u v S=0 →
      delta f u v S=0) :
    ∀ v : AtVertex a,∃ t : ℝ,∀ S : Finset (I×Fin 2),a∉S → v.1∉S →
      delta (SetFunctionEmbedding.extend (VertexDeletion.embedding d) f) a v.1 S=
        t*delta z a v.1 S := by
  let e := VertexDeletion.embedding d
  have hfG : Graphical ((graph I).comap e) f := by
    intro u v huv hnon S hu hv
    exact hzero u v huv S hu hv
      (SetFunctionEmbedding.restrict_graphical e hzG u v huv hnon S hu hv)
  have hFn := SetFunctionEmbedding.extend_translationNormalized e hfn
  have hFG := SetFunctionEmbedding.extend_graphical e hfG
  intro v
  letI := remaining_nonempty hI a v.1
  obtain ⟨H,hH,hsep,hprofile⟩ := hlocalPhase v
  apply graphical_row_line_of_profile hzn hzG hFn hFG v.2 H hH hsep hprofile
  intro uv hz
  let S := edgeContext a v.1 (coordinateChange.symm uv)
  have hdS : d∉S := same_part_not_mem_edgeContext hpart _
  have hvd : v.1≠ d := by
    intro he
    exact v.2 ((congrArg Prod.fst he).trans hpart).symm
  let a' : VertexDeletion.Retained d := ⟨a,had⟩
  let v' : VertexDeletion.Retained d := ⟨v.1,hvd⟩
  have hav' : a'≠ v' := fun he => (graph I).ne_of_adj v.2 (congrArg Subtype.val he)
  have haS : a'∉SetFunctionEmbedding.pullSet e S := by
    simpa only [SetFunctionEmbedding.mem_pullSet,e,S,a',VertexDeletion.embedding,Function.Embedding.coe_subtype] using left_not_mem_edgeContext a v.1 _
  have hvS : v'∉SetFunctionEmbedding.pullSet e S := by
    simpa only [SetFunctionEmbedding.mem_pullSet,e,S,v',VertexDeletion.embedding,Function.Embedding.coe_subtype] using right_not_mem_edgeContext a v.1 _
  have hsmall : delta (SetFunctionEmbedding.restrict e z) a' v'
      (SetFunctionEmbedding.pullSet e S)=0 := by
    rw [SetFunctionEmbedding.delta_restrict]
    change delta z a v.1 ((SetFunctionEmbedding.pullSet e S).map e)=0
    rw [VertexDeletion.map_pullSet,erase_eq_of_notMem hdS]
    exact (hprofile uv).trans hz
  have he := hzero a' v' hav' _ haS hvS hsmall
  simpa only [← SetFunctionEmbedding.delta_extend,e,S,a',v',VertexDeletion.embedding,Function.Embedding.coe_subtype] using he

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart254
