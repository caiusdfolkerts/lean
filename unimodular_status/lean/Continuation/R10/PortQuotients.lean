module

public import Recovery.Unimodular.PriorExtensions.SignedSumsQuotient
public import Recovery.Unimodular.PriorExtensions.SignedSumsBinary
public import Recovery.Unimodular.ProductVectorMatroid
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.Abel

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! # Port spaces after contraction on both sides

Contraction by columns on the two sides cannot increase their common port
dimension.  The statements below concern genuine images and kernels of linear
maps and require no matroid-rank assumptions.
-/

noncomputable section
open scoped Matroid

namespace Unimodular.SignedSums.MinorPorts

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Images of two subspaces still meet only along their old intersection when
the kernel splits into one contracted subspace on each side. -/
theorem map_inf_of_split_kernel (q : V →ₗ[K] W) (S T C D : Submodule K V)
    (hC : C ≤ S) (hD : D ≤ T) (hker : LinearMap.ker q = C ⊔ D) :
    S.map q ⊓ T.map q = (S ⊓ T).map q := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := Submodule.mem_map.mp hx.1
    obtain ⟨t, ht, htx⟩ := Submodule.mem_map.mp hx.2
    have hst : s - t ∈ C ⊔ D := by
      rw [← hker]
      apply LinearMap.mem_ker.mpr
      rw [map_sub, hsx, htx, sub_self]
    obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.mp hst
    have hsrep : s = c + d + t := (sub_eq_iff_eq_add).mp hcd.symm
    have hz : s - c = t + d := by rw [hsrep]; abel
    have hqc : q c = 0 := by
      apply LinearMap.mem_ker.mp
      rw [hker]
      exact (show C ≤ C ⊔ D from le_sup_left) hc
    apply Submodule.mem_map.mpr
    refine ⟨s - c, ⟨S.sub_mem hs (hC hc), ?_⟩, ?_⟩
    · rw [hz]
      exact T.add_mem ht (hD hd)
    · rw [map_sub, hqc, sub_zero, hsx]
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hx
    exact ⟨Submodule.mem_map.mpr ⟨z, hz.1, rfl⟩,
      Submodule.mem_map.mpr ⟨z, hz.2, rfl⟩⟩

/-- A preimage distributes over a sum if one summand is contained in the image.
The other summand need not lie in that image. -/
theorem comap_sup_of_right_le_range (f : V →ₗ[K] W) (C D : Submodule K W)
    (hD : D ≤ LinearMap.range f) :
    (C ⊔ D).comap f = C.comap f ⊔ D.comap f := by
  apply le_antisymm
  · intro x hx
    obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.mp hx
    obtain ⟨y, hy⟩ := hD hd
    apply Submodule.mem_sup.mpr
    refine ⟨x - y, ?_, y, ?_, by abel⟩
    · change f (x - y) ∈ C
      rw [map_sub, hy, ← hcd]
      simpa using hc
    · change f y ∈ D
      rw [hy]
      exact hd
  · intro x hx
    obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hx
    change f (c + d) ∈ C ⊔ D
    rw [map_add]
    exact Submodule.mem_sup.mpr ⟨f c, hc, f d, hd, rfl⟩

variable {P A B : Type*} [AddCommGroup P] [Module K P]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]

def portInclusion : P →ₗ[K] P × (A × B) where
  toFun p := (p, (0, 0))
  map_add' p q := by simp
  map_smul' a p := by simp

theorem portInclusion_injective :
    Function.Injective (portInclusion (K := K) (P := P) (A := A) (B := B)) :=
  fun p q hpq => congrArg Prod.fst hpq

theorem mem_range_sumLeft (x : P × (A × B)) :
    x ∈ LinearMap.range (sumLeft (R := K) (P := P) (A := A) (B := B)) ↔ x.2.2 = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro hx
    refine ⟨(x.1, x.2.1), ?_⟩
    change (x.1, (x.2.1, (0 : B))) = x
    exact Prod.ext rfl (Prod.ext rfl hx.symm)

theorem mem_range_sumRight (x : P × (A × B)) :
    x ∈ LinearMap.range (sumRight (R := K) (P := P) (A := A) (B := B)) ↔ x.2.1 = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro hx
    refine ⟨(x.1, x.2.2), ?_⟩
    change (x.1, ((0 : A), x.2.2)) = x
    exact Prod.ext rfl (Prod.ext hx.symm rfl)

theorem ranges_intersect_in_port :
    LinearMap.range (sumLeft (R := K) (P := P) (A := A) (B := B)) ⊓
      LinearMap.range (sumRight (R := K) (P := P) (A := A) (B := B)) =
      LinearMap.range (portInclusion (K := K) (P := P) (A := A) (B := B)) := by
  ext x
  constructor
  · intro hx
    have hb := (mem_range_sumLeft x).mp hx.1
    have ha := (mem_range_sumRight x).mp hx.2
    exact ⟨x.1, Prod.ext rfl (Prod.ext ha.symm hb.symm)⟩
  · rintro ⟨p, rfl⟩
    exact ⟨⟨(p, 0), rfl⟩, ⟨(p, 0), rfl⟩⟩

theorem quotient_side_intersection (q : (P × (A × B)) →ₗ[K] W)
    (C D : Submodule K (P × (A × B)))
    (hC : C ≤ LinearMap.range (sumLeft (R := K)))
    (hD : D ≤ LinearMap.range (sumRight (R := K)))
    (hker : LinearMap.ker q = C ⊔ D) :
    (LinearMap.range (sumLeft (R := K))).map q ⊓
      (LinearMap.range (sumRight (R := K))).map q =
      (LinearMap.range (portInclusion (K := K))).map q := by
  rw [map_inf_of_split_kernel q _ _ C D hC hD hker, ranges_intersect_in_port]

theorem quotient_side_intersection_dimension [Module.Finite K P]
    (q : (P × (A × B)) →ₗ[K] W) (C D : Submodule K (P × (A × B)))
    (hC : C ≤ LinearMap.range (sumLeft (R := K)))
    (hD : D ≤ LinearMap.range (sumRight (R := K)))
    (hker : LinearMap.ker q = C ⊔ D) :
    Module.finrank K ((LinearMap.range (sumLeft (R := K))).map q ⊓
      (LinearMap.range (sumRight (R := K))).map q : Submodule K W) ≤
        Module.finrank K P := by
  rw [quotient_side_intersection q C D hC hD hker]
  exact (Submodule.finrank_map_le q _).trans_eq
    (LinearMap.finrank_range_of_inj portInclusion_injective)

/-- The kernel seen by the right factor consists of its own contractions and
the part of the left contracted subspace lying in the common port. -/
theorem right_quotient_kernel (q : (P × (A × B)) →ₗ[K] W)
    (C D : Submodule K (P × (A × B)))
    (hD : D ≤ LinearMap.range (sumRight (R := K)))
    (hker : LinearMap.ker q = C ⊔ D) :
    LinearMap.ker (q.comp (sumRight (R := K))) =
      C.comap (sumRight (R := K)) ⊔ D.comap (sumRight (R := K)) := by
  rw [LinearMap.ker_comp, hker]
  exact comap_sup_of_right_le_range _ C D hD

variable {T : Type*}

/-- The port columns include every nonzero vector of the port space.  This is
the special feature of the empty, single, and binary triangle ports. -/
def CompletePorts (ports : T → P) : Prop := ∀ p : P, p = 0 ∨ ∃ t, ports t = p

theorem singlePort_complete : CompletePorts Binary.singlePort := by
  unfold CompletePorts
  decide

theorem trianglePort_complete : CompletePorts Binary.trianglePort := by
  unfold CompletePorts
  decide

theorem emptyPort_complete :
    CompletePorts (fun i : Fin 0 => (Fin.elim0 i : Fin 0 → Binary.F)) := by
  intro p
  left
  ext i
  exact Fin.elim0 i

theorem span_ports_in_subspace (ports : T → P) (hports : CompletePorts ports)
    (S : Submodule K P) :
    Submodule.span K (ports '' {t | ports t ∈ S}) = S := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro p ⟨t, ht, rfl⟩
    exact ht
  · intro p hp
    rcases hports p with rfl | ⟨t, rfl⟩
    · exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨t, hp, rfl⟩

theorem right_comap_left_subspace (C : Submodule K (P × (A × B)))
    (hC : C ≤ LinearMap.range (sumLeft (R := K))) :
    C.comap (sumRight (R := K)) =
      (C.comap (portInclusion (K := K))).map (LinearMap.inl K P B) := by
  apply le_antisymm
  · intro x hx
    change sumRight (R := K) x ∈ C at hx
    have hb : x.2 = 0 := (mem_range_sumLeft _).mp (hC hx)
    apply Submodule.mem_map.mpr
    refine ⟨x.1, ?_, ?_⟩
    · change portInclusion x.1 ∈ C
      simpa [portInclusion, sumRight, hb] using hx
    · exact Prod.ext rfl hb.symm
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    exact hp

theorem right_comap_generated_by_ports (C : Submodule K (P × (A × B)))
    (hC : C ≤ LinearMap.range (sumLeft (R := K)))
    (ports : T → P) (hports : CompletePorts ports) :
    C.comap (sumRight (R := K)) =
      Submodule.span K ((fun t => (ports t, (0 : B))) ''
        {t | portInclusion (K := K) (A := A) (B := B) (ports t) ∈ C}) := by
  rw [right_comap_left_subspace C hC,
    ← span_ports_in_subspace ports hports (C.comap (portInclusion (K := K))),
    Submodule.map_span, Set.image_image]
  rfl

theorem sumRight_injective :
    Function.Injective (sumRight (R := K) (P := P) (A := A) (B := B)) := by
  intro x y h
  exact Prod.ext (congrArg (fun z : P × (A × B) => z.1) h)
    (congrArg (fun z : P × (A × B) => z.2.2) h)

/-- Restriction of the quotient to the right factor is contraction by actual
right-factor vectors together with actual port columns. -/
theorem right_kernel_generated (q : (P × (A × B)) →ₗ[K] W)
    (C : Submodule K (P × (A × B))) (D : Submodule K (P × B))
    (hC : C ≤ LinearMap.range (sumLeft (R := K)))
    (hker : LinearMap.ker q = C ⊔ D.map (sumRight (R := K)))
    (ports : T → P) (hports : CompletePorts ports) :
    LinearMap.ker (q.comp (sumRight (R := K))) =
      Submodule.span K ((fun t => (ports t, (0 : B))) ''
        {t | portInclusion (K := K) (A := A) (B := B) (ports t) ∈ C}) ⊔ D := by
  rw [right_quotient_kernel q C _ LinearMap.map_le_range hker,
    right_comap_generated_by_ports C hC ports hports,
    Submodule.comap_map_eq_of_injective sumRight_injective]

theorem left_quotient_kernel (q : (P × (A × B)) →ₗ[K] W)
    (C D : Submodule K (P × (A × B)))
    (hC : C ≤ LinearMap.range (sumLeft (R := K)))
    (hker : LinearMap.ker q = C ⊔ D) :
    LinearMap.ker (q.comp (sumLeft (R := K))) =
      C.comap (sumLeft (R := K)) ⊔ D.comap (sumLeft (R := K)) := by
  rw [LinearMap.ker_comp, hker, sup_comm C D,
    comap_sup_of_right_le_range _ D C hC, sup_comm]

theorem left_comap_right_subspace (C : Submodule K (P × (A × B)))
    (hC : C ≤ LinearMap.range (sumRight (R := K))) :
    C.comap (sumLeft (R := K)) =
      (C.comap (portInclusion (K := K))).map (LinearMap.inl K P A) := by
  apply le_antisymm
  · intro x hx
    change sumLeft (R := K) x ∈ C at hx
    have ha : x.2 = 0 := (mem_range_sumRight _).mp (hC hx)
    apply Submodule.mem_map.mpr
    refine ⟨x.1, ?_, ?_⟩
    · change portInclusion x.1 ∈ C
      simpa [portInclusion, sumLeft, ha] using hx
    · exact Prod.ext rfl ha.symm
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    exact hp

theorem left_comap_generated_by_ports (C : Submodule K (P × (A × B)))
    (hC : C ≤ LinearMap.range (sumRight (R := K)))
    (ports : T → P) (hports : CompletePorts ports) :
    C.comap (sumLeft (R := K)) =
      Submodule.span K ((fun t => (ports t, (0 : A))) ''
        {t | portInclusion (K := K) (A := A) (B := B) (ports t) ∈ C}) := by
  rw [left_comap_right_subspace C hC,
    ← span_ports_in_subspace ports hports (C.comap (portInclusion (K := K))),
    Submodule.map_span, Set.image_image]
  rfl

theorem sumLeft_injective :
    Function.Injective (sumLeft (R := K) (P := P) (A := A) (B := B)) := by
  intro x y h
  exact Prod.ext (congrArg (fun z : P × (A × B) => z.1) h)
    (congrArg (fun z : P × (A × B) => z.2.1) h)

theorem left_kernel_generated (q : (P × (A × B)) →ₗ[K] W)
    (C : Submodule K (P × (A × B))) (D : Submodule K (P × A))
    (hC : C ≤ LinearMap.range (sumRight (R := K)))
    (hker : LinearMap.ker q = D.map (sumLeft (R := K)) ⊔ C)
    (ports : T → P) (hports : CompletePorts ports) :
    LinearMap.ker (q.comp (sumLeft (R := K))) =
      Submodule.span K ((fun t => (ports t, (0 : A))) ''
        {t | portInclusion (K := K) (A := A) (B := B) (ports t) ∈ C}) ⊔ D := by
  rw [left_quotient_kernel q _ C LinearMap.map_le_range hker,
    Submodule.comap_map_eq_of_injective sumLeft_injective,
    left_comap_generated_by_ports C hC ports hports, sup_comm]

/-- Every nonzero vector of the quotient-side intersection is represented by
an uncontracted original port column. -/
theorem intersection_nonzero_is_port (q : (P × (A × B)) →ₗ[K] W)
    (C D : Submodule K (P × (A × B)))
    (hC : C ≤ LinearMap.range (sumLeft (R := K)))
    (hD : D ≤ LinearMap.range (sumRight (R := K)))
    (hker : LinearMap.ker q = C ⊔ D) (ports : T → P) (hports : CompletePorts ports)
    {x : W} (hx : x ∈ (LinearMap.range (sumLeft (R := K))).map q ⊓
      (LinearMap.range (sumRight (R := K))).map q) (hzero : x ≠ 0) :
    ∃ t, q (portInclusion (K := K) (ports t)) = x ∧
      portInclusion (K := K) (A := A) (B := B) (ports t) ∉ LinearMap.ker q := by
  rw [quotient_side_intersection q C D hC hD hker] at hx
  obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp hx
  obtain ⟨p, rfl⟩ := hz
  rcases hports p with rfl | ⟨t, rfl⟩
  · exact False.elim (hzero (by simpa only [map_zero] using hzx.symm))
  · refine ⟨t, hzx, ?_⟩
    intro ht
    exact hzero (hzx.symm.trans (LinearMap.mem_ker.mp ht))

/-- A represented target whose left-side surviving vectors already lie in the
right quotient span is an ordinary minor of the right factor.  Nonzero,
distinct target vectors ensure that the replacement port labels survive and
are injectively labelled. -/
theorem lift_minor_to_right {L R I : Type*}
    (u : L → P × A) (v : R → P × B) (ports : T → P)
    (hports : CompletePorts ports)
    (q : (P × (A × B)) →ₗ[K] W)
    (C : Submodule K (P × (A × B))) (D : Set R)
    (hC : C ≤ LinearMap.range (sumLeft (R := K)))
    (hker : LinearMap.ker q = C ⊔ (Submodule.span K (v '' D)).map (sumRight (R := K)))
    (w : I → W) (g : I → L ⊕ R)
    (hw : Function.Injective w) (hnz : ∀ i, w i ≠ 0)
    (himage : ∀ i, q (joinedFamily (R := K) u v (g i)) = w i)
    (hleft : ∀ i l, g i = Sum.inl l →
      w i ∈ (LinearMap.range (sumRight (R := K))).map q) :
    ∃ f : I ↪ T ⊕ R,
      (VectorMatroid.ofFamily (K := K) w).mapEmbedding f ≤m
        VectorMatroid.ofFamily (K := K) (Sum.elim (fun t => (ports t, (0 : B))) v) := by
  classical
  let side : T ⊕ R → P × B := Sum.elim (fun t => (ports t, (0 : B))) v
  let qr : (P × B) →ₗ[K] W := q.comp (sumRight (R := K))
  let E : Set (T ⊕ R) :=
    (Sum.inl '' {t | portInclusion (K := K) (A := A) (B := B) (ports t) ∈ C}) ∪
      (Sum.inr '' D)
  have hspan : Submodule.span K (side '' E) =
      Submodule.span K ((fun t => (ports t, (0 : B))) ''
        {t | portInclusion (K := K) (A := A) (B := B) (ports t) ∈ C}) ⊔
      Submodule.span K (v '' D) := by
    dsimp only [E]
    rw [Set.image_union, Submodule.span_union, Set.image_image, Set.image_image]
    rfl
  have hkr : LinearMap.ker qr = Submodule.span K (side '' E) := by
    rw [hspan]
    exact right_kernel_generated q C (Submodule.span K (v '' D)) hC hker ports hports
  have hex : ∀ i, ∃ a : T ⊕ R, qr (side a) = w i := by
    intro i
    cases hg : g i with
    | inl l =>
      have hwl : w i ∈ (LinearMap.range (sumLeft (R := K))).map q := by
        apply Submodule.mem_map.mpr
        refine ⟨sumLeft (R := K) (u l), ⟨u l, rfl⟩, ?_⟩
        simpa only [joinedFamily, hg, Sum.elim_inl] using himage i
      obtain ⟨t, ht, _⟩ := intersection_nonzero_is_port q C
        ((Submodule.span K (v '' D)).map (sumRight (R := K)))
        hC LinearMap.map_le_range hker ports hports ⟨hwl, hleft i l hg⟩ (hnz i)
      exact ⟨Sum.inl t, ht⟩
    | inr r =>
      refine ⟨Sum.inr r, ?_⟩
      simpa only [qr, side, LinearMap.comp_apply, joinedFamily, hg, Sum.elim_inr]
        using himage i
  choose labels hlabels using hex
  let f : I ↪ T ⊕ R :=
    ⟨labels, by
      intro i j hij
      apply hw
      rw [← hlabels i, ← hlabels j, hij]⟩
  have hR : Set.range f ⊆ Set.univ \ E := by
    rintro a ⟨i, rfl⟩
    refine ⟨Set.mem_univ _, ?_⟩
    intro he
    have hk : side (f i) ∈ LinearMap.ker qr := by
      rw [hkr]
      exact Submodule.subset_span ⟨f i, he, rfl⟩
    exact hnz i ((hlabels i).symm.trans (LinearMap.mem_ker.mp hk))
  refine ⟨f, ?_⟩
  exact VectorMatroid.mapEmbedding_isMinor_of_kernel_image side w
    (E := Set.univ) (C := E) (Set.subset_univ _) f hR qr hkr hlabels

/-- The symmetric lifting statement for a target whose right portion is already
in the left quotient span. -/
theorem lift_minor_to_left {L R I : Type*}
    (u : L → P × A) (v : R → P × B) (ports : T → P)
    (hports : CompletePorts ports)
    (q : (P × (A × B)) →ₗ[K] W)
    (C : Submodule K (P × (A × B))) (D : Set L)
    (hC : C ≤ LinearMap.range (sumRight (R := K)))
    (hker : LinearMap.ker q = (Submodule.span K (u '' D)).map (sumLeft (R := K)) ⊔ C)
    (w : I → W) (g : I → L ⊕ R)
    (hw : Function.Injective w) (hnz : ∀ i, w i ≠ 0)
    (himage : ∀ i, q (joinedFamily (R := K) u v (g i)) = w i)
    (hright : ∀ i r, g i = Sum.inr r →
      w i ∈ (LinearMap.range (sumLeft (R := K))).map q) :
    ∃ f : I ↪ T ⊕ L,
      (VectorMatroid.ofFamily (K := K) w).mapEmbedding f ≤m
        VectorMatroid.ofFamily (K := K) (Sum.elim (fun t => (ports t, (0 : A))) u) := by
  classical
  let side : T ⊕ L → P × A := Sum.elim (fun t => (ports t, (0 : A))) u
  let ql : (P × A) →ₗ[K] W := q.comp (sumLeft (R := K))
  let E : Set (T ⊕ L) :=
    (Sum.inl '' {t | portInclusion (K := K) (A := A) (B := B) (ports t) ∈ C}) ∪
      (Sum.inr '' D)
  have hspan : Submodule.span K (side '' E) =
      Submodule.span K ((fun t => (ports t, (0 : A))) ''
        {t | portInclusion (K := K) (A := A) (B := B) (ports t) ∈ C}) ⊔
      Submodule.span K (u '' D) := by
    dsimp only [E]
    rw [Set.image_union, Submodule.span_union, Set.image_image, Set.image_image]
    rfl
  have hkl : LinearMap.ker ql = Submodule.span K (side '' E) := by
    rw [hspan]
    exact left_kernel_generated q C (Submodule.span K (u '' D)) hC hker ports hports
  have hex : ∀ i, ∃ a : T ⊕ L, ql (side a) = w i := by
    intro i
    cases hg : g i with
    | inl l =>
      refine ⟨Sum.inr l, ?_⟩
      simpa only [ql, side, LinearMap.comp_apply, joinedFamily, hg, Sum.elim_inl,
        Sum.elim_inr] using himage i
    | inr r =>
      have hwr : w i ∈ (LinearMap.range (sumRight (R := K))).map q := by
        apply Submodule.mem_map.mpr
        refine ⟨sumRight (R := K) (v r), ⟨v r, rfl⟩, ?_⟩
        simpa only [joinedFamily, hg, Sum.elim_inr] using himage i
      obtain ⟨t, ht, _⟩ := intersection_nonzero_is_port q
        ((Submodule.span K (u '' D)).map (sumLeft (R := K))) C
        LinearMap.map_le_range hC hker ports hports ⟨hright i r hg, hwr⟩ (hnz i)
      exact ⟨Sum.inl t, ht⟩
  choose labels hlabels using hex
  let f : I ↪ T ⊕ L :=
    ⟨labels, by
      intro i j hij
      apply hw
      rw [← hlabels i, ← hlabels j, hij]⟩
  have hR : Set.range f ⊆ Set.univ \ E := by
    rintro a ⟨i, rfl⟩
    refine ⟨Set.mem_univ _, ?_⟩
    intro he
    have hk : side (f i) ∈ LinearMap.ker ql := by
      rw [hkl]
      exact Submodule.subset_span ⟨f i, he, rfl⟩
    exact hnz i ((hlabels i).symm.trans (LinearMap.mem_ker.mp hk))
  refine ⟨f, ?_⟩
  exact VectorMatroid.mapEmbedding_isMinor_of_kernel_image side w
    (E := Set.univ) (C := E) (Set.subset_univ _) f hR ql hkl hlabels

#print axioms quotient_side_intersection_dimension
#print axioms right_quotient_kernel
#print axioms right_kernel_generated
#print axioms intersection_nonzero_is_port
#print axioms lift_minor_to_right
#print axioms lift_minor_to_left
end Unimodular.SignedSums.MinorPorts
