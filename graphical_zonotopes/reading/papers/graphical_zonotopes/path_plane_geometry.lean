module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Module

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace PathDrawing

abbrev Space := Fin 3 → ℝ

def unit (i : Fin 3) : Space := fun j => if j = i then 1 else 0

def rotate : Space →ₗ[ℝ] Space where
  toFun x i := if i = 0 then x 1-x 0 else if i = 1 then x 2-x 0 else 3*x 0
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp <;> ring

def point : ℕ → Space
  | 0 => unit 0
  | 1 => unit 1
  | 2 => unit 2
  | n+3 => (1/3 : ℝ) • (point n + point (n+1) + point (n+2))
termination_by n => n
decreasing_by all_goals omega

theorem point_step (n : ℕ) :
    point (n+3) = (1/3 : ℝ) • (point n+point (n+1)+point (n+2)) := by
  rw [point]

def frame : ℕ → Space →ₗ[ℝ] Space
  | 0 => LinearMap.id
  | n+1 => rotate ∘ₗ frame n

@[simp] theorem rotate_unit_one : rotate (unit 1) = unit 0 := by
  funext i
  fin_cases i <;> norm_num [rotate,unit]

@[simp] theorem rotate_unit_two : rotate (unit 2) = unit 1 := by
  funext i
  fin_cases i <;> norm_num [rotate,unit]

@[simp] theorem rotate_average :
    rotate ((1/3 : ℝ) • (unit 0+unit 1+unit 2)) = unit 2 := by
  funext i
  fin_cases i <;> norm_num [rotate,unit]

theorem frame_vertices (n : ℕ) :
    frame n (point n) = unit 0 ∧
      frame n (point (n+1)) = unit 1 ∧ frame n (point (n+2)) = unit 2 := by
  induction n with
  | zero => simp [frame,point]
  | succ n ih =>
    constructor
    · change rotate (frame n (point (n+1))) = unit 0
      rw [ih.2.1,rotate_unit_one]
    · constructor
      · change rotate (frame n (point (n+2))) = unit 1
        rw [ih.2.2,rotate_unit_two]
      · change rotate (frame n (point (n+3))) = unit 2
        rw [point_step,map_smul,map_add,map_add,ih.1,ih.2.1,ih.2.2,rotate_average]

@[simp] theorem frame_point_self (n : ℕ) : frame n (point n) = unit 0 :=
  (frame_vertices n).1

@[simp] theorem frame_point_next (n : ℕ) : frame n (point (n+1)) = unit 1 :=
  (frame_vertices n).2.1

@[simp] theorem frame_point_next_two (n : ℕ) : frame n (point (n+2)) = unit 2 :=
  (frame_vertices n).2.2

@[simp] theorem frame_point_next_three (n : ℕ) :
    frame n (point (n+3)) = (1/3 : ℝ) • (unit 0+unit 1+unit 2) := by
  rw [point_step,map_smul,map_add,map_add,frame_point_self,frame_point_next,
    frame_point_next_two]

def tailCone (n : ℕ) : Set Space := {x | ∀ i, 0 ≤ frame n x i}

theorem tailCone_convex (n : ℕ) : Convex ℝ (tailCone n) := by
  intro x hx y hy a b ha hb hab
  intro i
  simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

theorem point_offset_mem (n d : ℕ) : point (n+d) ∈ tailCone n := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hd : d < 3
    · rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl
      · simp [tailCone,unit]; intro i; split <;> norm_num
      · simp [tailCone,unit]; intro i; split <;> norm_num
      · simp [tailCone,unit]; intro i; split <;> norm_num
    · have h3 : 3 ≤ d := by omega
      have h0 := ih (d-3) (by omega)
      have h1 := ih (d-2) (by omega)
      have h2 := ih (d-1) (by omega)
      have he : n+d = (n+(d-3))+3 := by omega
      have he1 : n+(d-3)+1 = n+(d-2) := by omega
      have he2 : n+(d-3)+2 = n+(d-1) := by omega
      rw [he,point_step,he1,he2]
      intro i
      simp only [map_smul,map_add,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
      exact mul_nonneg (by norm_num) (add_nonneg (add_nonneg (h0 i) (h1 i)) (h2 i))

theorem point_later_mem {n m : ℕ} (h : n ≤ m) : point m ∈ tailCone n := by
  simpa only [Nat.add_sub_of_le h] using point_offset_mem n (m-n)

theorem point_not_nextCone (n : ℕ) : point n ∉ tailCone (n+1) := by
  intro h
  have h0 := h (0 : Fin 3)
  change 0 ≤ rotate (frame n (point n)) 0 at h0
  rw [frame_point_self] at h0
  norm_num [rotate,unit] at h0

theorem point_injective : Function.Injective point := by
  intro n m hnm
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := point_later_mem (show n+1 ≤ m by omega)
    rw [← hnm] at h
    exact point_not_nextCone n h
  · have h := point_later_mem (show m+1 ≤ n by omega)
    rw [hnm] at h
    exact point_not_nextCone m h

def total (x : Space) : ℝ := x 0+x 1+x 2

theorem total_rotate (x : Space) : total (rotate x) = total x := by
  simp [total,rotate]
  ring

theorem total_frame (n : ℕ) (x : Space) : total (frame n x) = total x := by
  induction n with
  | zero => rfl
  | succ n ih => exact (total_rotate (frame n x)).trans ih

theorem point_total (n : ℕ) : total (point n) = 1 := by
  have h := congrArg total (frame_point_self n)
  rw [total_frame] at h
  simpa [total,unit] using h

/-- Every edge from the oldest vertex to one of its three successors enters
the next tail cone only at its other endpoint. This is the separation statement
that prevents edges added later from crossing it. -/
theorem segment_meets_tail_at_endpoint {n m : ℕ} (hnm : n < m) (hm : m ≤ n+3)
    {x : Space} (hx : x ∈ segment ℝ (point n) (point m))
    (ht : x ∈ tailCone (n+1)) : x = point m := by
  obtain ⟨a,b,ha,hb,hab,hx⟩ := hx
  have hold : frame (n+1) (point n) = rotate (unit 0) := by
    change rotate (frame n (point n)) = _
    rw [frame_point_self]
  have hcases : m = n+1 ∨ m = n+2 ∨ m = n+3 := by omega
  rcases hcases with hm1 | hm2 | hm3
  · subst m
    have h := ht (1 : Fin 3)
    rw [← hx,map_add,map_smul,map_smul,hold,frame_point_self] at h
    norm_num [rotate,unit,Pi.add_apply,Pi.smul_apply] at h
    have ha0 : a = 0 := by linarith
    have hb1 : b = 1 := by linarith
    simpa [ha0,hb1] using hx.symm
  · subst m
    have h := ht (0 : Fin 3)
    have hnext : frame (n+1) (point (n+2)) = unit 1 := by
      simpa only [Nat.add_assoc] using frame_point_next (n+1)
    rw [← hx,map_add,map_smul,map_smul,hold,hnext] at h
    norm_num [rotate,unit,Pi.add_apply,Pi.smul_apply] at h
    have ha0 : a = 0 := by linarith
    have hb1 : b = 1 := by linarith
    simpa [ha0,hb1] using hx.symm
  · subst m
    have h := ht (0 : Fin 3)
    have hnext : frame (n+1) (point (n+3)) = unit 2 := by
      simpa only [Nat.add_assoc] using frame_point_next_two (n+1)
    rw [← hx,map_add,map_smul,map_smul,hold,hnext] at h
    norm_num [rotate,unit,Pi.add_apply,Pi.smul_apply] at h
    have ha0 : a = 0 := by linarith
    have hb1 : b = 1 := by linarith
    simpa [ha0,hb1] using hx.symm

theorem vertex_not_on_edge {i j k : ℕ} (hij : i < j) (hj : j ≤ i+3)
    (hki : k ≠ i) (hkj : k ≠ j) : point k ∉ segment ℝ (point i) (point j) := by
  intro hmem
  rcases lt_or_gt_of_ne hki with hki' | hik
  · have hi := point_later_mem (show k+1 ≤ i by omega)
    have hj' := point_later_mem (show k+1 ≤ j by omega)
    exact point_not_nextCone k ((tailCone_convex (k+1)).segment_subset hi hj' hmem)
  · have ht := point_later_mem (show i+1 ≤ k by omega)
    exact hkj (point_injective (segment_meets_tail_at_endpoint hij hj hmem ht))

def coordinate (n : ℕ) (i : Fin 3) : Space →ₗ[ℝ] ℝ where
  toFun x := frame n x i
  map_add' x y := by simp
  map_smul' a x := by simp

theorem segment_meet_start_of_linear {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p q r x : E} (l : E →ₗ[ℝ] ℝ) (hp : l p = 0) (hq : l q = 0)
    (hr : l r ≠ 0) (hx : x ∈ segment ℝ p q) (hy : x ∈ segment ℝ p r) : x = p := by
  obtain ⟨a,b,ha,hb,hab,he⟩ := hx
  have hlx : l x = 0 := by
    rw [← he,map_add,map_smul,map_smul,hp,hq]
    simp
  obtain ⟨c,d,hc,hd,hcd,he'⟩ := hy
  have h := congrArg l he'
  simp only [map_add,map_smul,smul_eq_mul,hp,hlx,mul_zero,zero_add] at h
  have hd0 : d = 0 := (mul_eq_zero.mp h).resolve_right hr
  have hc1 : c = 1 := by linarith
  simpa [hd0,hc1] using he'.symm

theorem common_start_ordered {n m l : ℕ} (hnm : n < m) (hml : m < l)
    (hl : l ≤ n+3) {x : Space} (hx : x ∈ segment ℝ (point n) (point m))
    (hy : x ∈ segment ℝ (point n) (point l)) : x = point n := by
  by_cases hm : m = n+1
  · subst m
    apply segment_meet_start_of_linear (coordinate n 2) _ _ _ hx hy
    · simp [coordinate,unit]
    · simp [coordinate,unit]
    · rcases (show l = n+2 ∨ l = n+3 by omega) with rfl | rfl
      · norm_num [coordinate,unit]
      · norm_num [coordinate,unit]
  · have hm2 : m = n+2 := by omega
    have hl3 : l = n+3 := by omega
    subst m
    subst l
    apply segment_meet_start_of_linear (coordinate n 1) _ _ _ hx hy
    · simp [coordinate,unit]
    · simp [coordinate,unit]
    · norm_num [coordinate,unit]

theorem common_start {n m l : ℕ} (hnm : n < m) (hnl : n < l)
    (hm : m ≤ n+3) (hl : l ≤ n+3) (hml : m ≠ l)
    {x : Space} (hx : x ∈ segment ℝ (point n) (point m))
    (hy : x ∈ segment ℝ (point n) (point l)) : x = point n := by
  rcases lt_or_gt_of_ne hml with h | h
  · exact common_start_ordered hnm h hl hx hy
  · exact common_start_ordered hnl h hm hy hx

theorem ordered_edges_meet {i j k l : ℕ} (hij : i < j) (hj : j ≤ i+3)
    (hkl : k < l) (hl : l ≤ k+3) {x : Space}
    (hx : x ∈ segment ℝ (point i) (point j))
    (hy : x ∈ segment ℝ (point k) (point l)) :
    (i = k ∧ j = l) ∨
      ∃ w, (w = i ∨ w = j) ∧ (w = k ∨ w = l) ∧ x = point w := by
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l
    · exact Or.inl ⟨rfl,hjl⟩
    · exact Or.inr ⟨i,Or.inl rfl,Or.inl rfl,common_start hij hkl hj hl hjl hx hy⟩
  · rcases lt_or_gt_of_ne hik with hik' | hki
    · have hk := point_later_mem (show i+1 ≤ k by omega)
      have hl' := point_later_mem (show i+1 ≤ l by omega)
      have ht := (tailCone_convex (i+1)).segment_subset hk hl' hy
      have hxj := segment_meets_tail_at_endpoint hij hj hx ht
      have hjmem : point j ∈ segment ℝ (point k) (point l) := hxj ▸ hy
      have hjends : j = k ∨ j = l := by
        by_contra hn
        push_neg at hn
        exact vertex_not_on_edge hkl hl hn.1 hn.2 hjmem
      exact Or.inr ⟨j,Or.inr rfl,hjends,hxj⟩
    · have hi := point_later_mem (show k+1 ≤ i by omega)
      have hj' := point_later_mem (show k+1 ≤ j by omega)
      have ht := (tailCone_convex (k+1)).segment_subset hi hj' hx
      have hxl := segment_meets_tail_at_endpoint hkl hl hy ht
      have hlmem : point l ∈ segment ℝ (point i) (point j) := hxl ▸ hx
      have hlends : l = i ∨ l = j := by
        by_contra hn
        push_neg at hn
        exact vertex_not_on_edge hij hj hn.1 hn.2 hlmem
      exact Or.inr ⟨l,hlends,Or.inr rfl,hxl⟩

abbrev Plane := Fin 2 → ℝ

def project (x : Space) : Plane := fun i => x (Fin.castLE (by decide : 2 ≤ 3) i)

def planePoint (n : ℕ) : Plane := project (point n)

theorem project_injective_on_plane {x y : Space} (hx : total x = 1) (hy : total y = 1)
    (he : project x = project y) : x = y := by
  have h0 := congrFun he (0 : Fin 2)
  have h1 := congrFun he (1 : Fin 2)
  change x 0 = y 0 at h0
  change x 1 = y 1 at h1
  have h2 : x 2 = y 2 := by
    unfold total at hx hy
    linarith
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem planePoint_injective : Function.Injective planePoint := by
  intro n m h
  exact point_injective (project_injective_on_plane (point_total n) (point_total m) h)

@[simp] theorem total_add (x y : Space) : total (x+y) = total x+total y := by
  simp [total]
  ring

@[simp] theorem total_smul (a : ℝ) (x : Space) : total (a • x) = a * total x := by
  simp [total]
  ring

theorem total_segment {p q x : Space} (hp : total p = 1) (hq : total q = 1)
    (hx : x ∈ segment ℝ p q) : total x = 1 := by
  obtain ⟨a,b,ha,hb,hab,rfl⟩ := hx
  simpa [hp,hq] using hab

theorem plane_segment_preimage {p q : Space} {x : Plane}
    (hx : x ∈ segment ℝ (project p) (project q)) :
    ∃ y ∈ segment ℝ p q, project y = x := by
  obtain ⟨a,b,ha,hb,hab,he⟩ := hx
  exact ⟨a • p+b • q,⟨a,b,ha,hb,hab,rfl⟩,he⟩

theorem plane_vertex_not_on_edge {i j k : ℕ} (hij : i < j) (hj : j ≤ i+3)
    (hki : k ≠ i) (hkj : k ≠ j) : planePoint k ∉ segment ℝ (planePoint i) (planePoint j) := by
  intro h
  obtain ⟨x,hx,hxp⟩ := plane_segment_preimage h
  have hx' := project_injective_on_plane
    (total_segment (point_total i) (point_total j) hx) (point_total k) hxp
  rw [hx'] at hx
  exact vertex_not_on_edge hij hj hki hkj hx

theorem plane_ordered_edges_meet {i j k l : ℕ} (hij : i < j) (hj : j ≤ i+3)
    (hkl : k < l) (hl : l ≤ k+3) {x : Plane}
    (hx : x ∈ segment ℝ (planePoint i) (planePoint j))
    (hy : x ∈ segment ℝ (planePoint k) (planePoint l)) :
    (i = k ∧ j = l) ∨
      ∃ w, (w = i ∨ w = j) ∧ (w = k ∨ w = l) ∧ x = planePoint w := by
  obtain ⟨p,hp,hpx⟩ := plane_segment_preimage hx
  obtain ⟨q,hq,hqx⟩ := plane_segment_preimage hy
  have hpq : p = q := project_injective_on_plane
    (total_segment (point_total i) (point_total j) hp)
    (total_segment (point_total k) (point_total l) hq) (hpx.trans hqx.symm)
  rw [← hpq] at hq
  rcases ordered_edges_meet hij hj hkl hl hp hq with he | ⟨w,hw,hv,hpw⟩
  · exact Or.inl he
  · refine Or.inr ⟨w,hw,hv,?_⟩
    rw [hpw] at hpx
    exact hpx.symm

end PathDrawing
end GraphicalZonotopes
