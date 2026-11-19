module
public import Papers.RichLineGeometry
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FieldSimp

@[expose] public section

noncomputable section

open Matrix Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.PlaneRationalization

abbrev V := PlaneVector

def RatScalar (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x
def RatVector (x : V) : Prop := ∀ i, RatScalar (x i)
def RatConfiguration (q : Fin 8 → V) : Prop := ∀ i, RatVector (q i)

theorem RatScalar.zero : RatScalar 0 := ⟨0,by simp⟩
theorem RatScalar.add {x y : ℝ} (hx : RatScalar x) (hy : RatScalar y) :
    RatScalar (x+y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact ⟨a+b,by simp⟩

theorem RatScalar.sub {x y : ℝ} (hx : RatScalar x) (hy : RatScalar y) :
    RatScalar (x-y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact ⟨a-b,by simp⟩

theorem RatScalar.mul {x y : ℝ} (hx : RatScalar x) (hy : RatScalar y) :
    RatScalar (x*y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact ⟨a*b,by simp⟩

theorem RatScalar.div {x y : ℝ} (hx : RatScalar x) (hy : RatScalar y) :
    RatScalar (x/y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact ⟨a/b,by simp⟩

theorem RatVector.sub {x y : V} (hx : RatVector x) (hy : RatVector y) :
    RatVector (x-y) := fun i => (hx i).sub (hy i)

theorem RatVector.smul {c : ℝ} {x : V} (hc : RatScalar c) (hx : RatVector x) :
    RatVector (c • x) := fun i => hc.mul (hx i)

theorem RatVector.dot {x y : V} (hx : RatVector x) (hy : RatVector y) :
    RatScalar (dotProduct x y) := by
  simpa [dotProduct,Fin.sum_univ_three,add_assoc] using
    ((hx 0).mul (hy 0)).add (((hx 1).mul (hy 1)).add ((hx 2).mul (hy 2)))

theorem RatVector.cross {x y : V} (hx : RatVector x) (hy : RatVector y) :
    RatVector (crossProduct x y) := by
  intro i
  fin_cases i
  · simpa [cross_apply] using ((hx 1).mul (hy 2)).sub ((hx 2).mul (hy 1))
  · simpa [cross_apply] using ((hx 2).mul (hy 0)).sub ((hx 0).mul (hy 2))
  · simpa [cross_apply] using ((hx 0).mul (hy 1)).sub ((hx 1).mul (hy 0))

theorem ratVector_dense : Dense {x : V | RatVector x} := by
  have h : DenseRange (fun q : Fin 3 → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  apply h.mono
  rintro _ ⟨q,rfl⟩ i
  exact ⟨q i,rfl⟩

theorem ratConfiguration_dense : Dense {q : Fin 8 → V | RatConfiguration q} := by
  have h : DenseRange
      (fun q : Fin 8 → Fin 3 → ℚ => fun i j => (q i j : ℝ)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => Rat.denseRange_cast
  apply h.mono
  rintro _ ⟨q,rfl⟩ i j
  exact ⟨q i j,rfl⟩

theorem continuous_dot : Continuous (fun z : V × V => dotProduct z.1 z.2) := by
  simp only [dotProduct,Fin.sum_univ_three]
  fun_prop

theorem continuous_cross : Continuous (fun z : V × V => crossProduct z.1 z.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [cross_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two] <;> fun_prop

/-- The rational orthogonal projection to one homogeneous line. -/
def projectOne (l w : V) : V :=
  w - (dotProduct l w / dotProduct l l) • l

/-- The rational orthogonal projection to the intersection of two distinct lines. -/
def projectTwo (l m w : V) : V :=
  (dotProduct w (crossProduct l m) /
    dotProduct (crossProduct l m) (crossProduct l m)) • crossProduct l m

theorem projectOne_incident (l w : V) (hl : l ≠ 0) :
    dotProduct l (projectOne l w) = 0 := by
  have hd : dotProduct l l ≠ 0 := mt dotProduct_self_eq_zero.mp hl
  simp only [projectOne,dotProduct_sub,dotProduct_smul,smul_eq_mul]
  field_simp [hd]
  ring

theorem projectOne_fixed (l w : V) (h : dotProduct l w = 0) :
    projectOne l w = w := by
  simp [projectOne,h]

theorem projectTwo_left_incident (l m w : V) :
    dotProduct l (projectTwo l m w) = 0 := by
  simp [projectTwo,dotProduct_smul,dot_self_cross]

theorem projectTwo_right_incident (l m w : V) :
    dotProduct m (projectTwo l m w) = 0 := by
  simp [projectTwo,dotProduct_smul,dot_cross_self]

theorem common_kernel_eq_smul_cross (l m w : V)
    (hlm : LinearIndependent ℝ ![l,m])
    (hlw : dotProduct l w = 0) (hmw : dotProduct m w = 0) :
    ∃ c : ℝ, c • crossProduct l m = w := by
  have hn : crossProduct l m ≠ 0 :=
    crossProduct_ne_zero_iff_linearIndependent.mpr hlm
  have hdep : ¬ LinearIndependent ℝ ![crossProduct l m,w] := by
    intro hli
    exact independent_incidence_pair_impossible l m (crossProduct l m) w hlm hli
      (dot_self_cross _ _) hlw (dot_cross_self _ _) hmw
  rw [LinearIndependent.pair_iff' hn] at hdep
  push_neg at hdep
  exact hdep

theorem projectTwo_fixed (l m w : V)
    (hlm : LinearIndependent ℝ ![l,m])
    (hlw : dotProduct l w = 0) (hmw : dotProduct m w = 0) :
    projectTwo l m w = w := by
  have hn : crossProduct l m ≠ 0 :=
    crossProduct_ne_zero_iff_linearIndependent.mpr hlm
  have hd : dotProduct (crossProduct l m) (crossProduct l m) ≠ 0 :=
    mt dotProduct_self_eq_zero.mp hn
  obtain ⟨c,rfl⟩ := common_kernel_eq_smul_cross l m w hlm hlw hmw
  simp [projectTwo,smul_dotProduct,smul_eq_mul,hd,mul_div_cancel_right₀]

theorem RatVector.projectOne {l w : V} (hl : RatVector l) (hw : RatVector w) :
    RatVector (projectOne l w) :=
  hw.sub (RatVector.smul ((hl.dot hw).div (hl.dot hl)) hl)

theorem RatVector.projectTwo {l m w : V}
    (hl : RatVector l) (hm : RatVector m) (hw : RatVector w) :
    RatVector (projectTwo l m w) :=
  RatVector.smul ((hw.dot (hl.cross hm)).div ((hl.cross hm).dot (hl.cross hm))) (hl.cross hm)

theorem continuousAt_projectOne (l w : V) (hl : l ≠ 0) :
    ContinuousAt (fun z : V × V => projectOne z.1 z.2) (l,w) := by
  have hd : dotProduct l l ≠ 0 := mt dotProduct_self_eq_zero.mp hl
  unfold projectOne
  have hnum : ContinuousAt (fun z : V×V => dotProduct z.1 z.2) (l,w) :=
    continuous_dot.continuousAt
  have hden : ContinuousAt (fun z : V×V => dotProduct z.1 z.1) (l,w) :=
    (continuous_dot.comp (continuous_fst.prodMk continuous_fst)).continuousAt
  exact continuousAt_snd.sub
    ((hnum.div hden hd).smul continuousAt_fst)

theorem continuousAt_projectTwo (l m w : V)
    (hlm : LinearIndependent ℝ ![l,m]) :
    ContinuousAt (fun z : (V × V) × V => projectTwo z.1.1 z.1.2 z.2) ((l,m),w) := by
  have hn : crossProduct l m ≠ 0 :=
    crossProduct_ne_zero_iff_linearIndependent.mpr hlm
  have hd : dotProduct (crossProduct l m) (crossProduct l m) ≠ 0 :=
    mt dotProduct_self_eq_zero.mp hn
  have hc : Continuous (fun z : (V × V) × V => crossProduct z.1.1 z.1.2) :=
    continuous_cross.comp continuous_fst
  unfold projectTwo
  have hnum : ContinuousAt (fun z : (V×V)×V =>
      dotProduct z.2 (crossProduct z.1.1 z.1.2)) ((l,m),w) :=
    (continuous_dot.comp (continuous_snd.prodMk hc)).continuousAt
  have hden : ContinuousAt (fun z : (V×V)×V =>
      dotProduct (crossProduct z.1.1 z.1.2) (crossProduct z.1.1 z.1.2)) ((l,m),w) :=
    (continuous_dot.comp (hc.prodMk hc)).continuousAt
  exact (hnum.div hden hd).smul hc.continuousAt

theorem mem_closure_inter_of_eventually {X : Type*} [TopologicalSpace X]
    {A B : Set X} {a : X} (ha : a ∈ closure A) (hB : ∀ᶠ x in 𝓝 a, x ∈ B) :
    a ∈ closure (A ∩ B) := by
  rw [mem_closure_iff_frequently] at ha ⊢
  exact ha.and_eventually hB

end Papers.RationalityTen.PlaneRationalization
