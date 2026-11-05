import cubical.generic_rigidity
import cubical.vertex_splitting

/-!
# Generic vertex splitting and relabelling

The geometric splitting theorem combines with generic placements in
general position. Relabelling is explicit, so the final theorem applies
to arbitrary finite vertex types and a collapse with one double fiber.
-/

namespace Cubical.Rigidity

open Module

variable {V W E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Relabelling every vertex by an equivalence preserves genuine rigidity. -/
theorem isRigid_comap_iff (G : SimpleGraph W) (e : V ≃ W) (p : W → E) :
    IsRigid (G.comap e) (p ∘ e) ↔ IsRigid G p := by
  constructor
  · intro h u hu
    have hm : IsMotion (G.comap e) (p ∘ e) (u ∘ e) := by
      intro a b hab
      exact hu (e a) (e b) hab
    obtain ⟨t, A, hA, h⟩ := h _ hm
    exact ⟨t, A, hA, fun w => by simpa using h (e.symm w)⟩
  · intro h u hu
    have hm : IsMotion G p (u ∘ e.symm) := by
      intro a b hab
      have hab' : (G.comap e).Adj (e.symm a) (e.symm b) := by simpa using hab
      simpa using hu (e.symm a) (e.symm b) hab'
    obtain ⟨t, A, hA, h⟩ := h _ hm
    exact ⟨t, A, hA, fun v => by simpa using h (e v)⟩

/-- Generic rigidity is invariant under bijective vertex relabelling. -/
theorem genericallyRigid_comap_iff (G : SimpleGraph W) (e : V ≃ W) :
    GenericallyRigid (G.comap e) E ↔ GenericallyRigid G E := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p ∘ e.symm, (isRigid_comap_iff G e _).mp ?_⟩
    simpa only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using hp
  · rintro ⟨p, hp⟩
    exact ⟨p ∘ e, (isRigid_comap_iff G e p).mpr hp⟩

/-- Splitting one vertex preserves generic rigidity when the two split
vertices are adjacent and have `dim E - 1` distinct common neighbors. -/
theorem GenericallyRigid.vertex_split_option [Fintype V] [FiniteDimensional ℝ E]
    {G : SimpleGraph V} {H : SimpleGraph (Option V)} (hG : GenericallyRigid G E)
    (root : V) (hroot : H.Adj none (some root))
    (hcover : ∀ a b, G.Adj a b → ∃ x y : Option V,
      collapseVertex root x = a ∧ collapseVertex root y = b ∧ H.Adj x y)
    {C : Type*} [Fintype C] (c : C → V) (hc : Function.Injective c)
    (hleft : ∀ i, H.Adj none (some (c i)))
    (hright : ∀ i, H.Adj (some root) (some (c i)))
    (hdim : finrank ℝ E = Fintype.card C + 1) :
    GenericallyRigid H E := by
  obtain ⟨p, hp, hpos⟩ := hG.exists_in_general_position
  have hne : ∀ i, c i ≠ root := by
    intro i hi
    have h := hright i
    rw [hi] at h
    exact H.irrefl h
  have hind := hpos.differences root c hc hne (by omega)
  obtain ⟨q, hq, _⟩ := exists_rigid_vertex_split p root hp hroot hcover c
    hleft hright hind (by omega)
  exact ⟨q, hq⟩

/-- Enlarging a graph without changing its vertices preserves generic
rigidity. -/
theorem GenericallyRigid.mono {G H : SimpleGraph V}
    (hG : GenericallyRigid G E) (hGH : G ≤ H) : GenericallyRigid H E := by
  obtain ⟨p, hp⟩ := hG
  exact ⟨p, hp.mono hGH⟩

/-- Transport generic rigidity through a graph isomorphism. -/
theorem GenericallyRigid.of_iso {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : GenericallyRigid G E) (e : G ≃g H) : GenericallyRigid H E := by
  apply (genericallyRigid_comap_iff H e.toEquiv).mp
  have he : H.comap e.toEquiv = G := by
    ext a b
    exact e.map_adj_iff
  rwa [he]

/-- A collapse with exactly one double fiber can be undone while
preserving generic rigidity, provided the split edge and enough common
neighbors are present. -/
theorem GenericallyRigid.of_vertex_collapse [Fintype V] [Fintype W]
    [FiniteDimensional ℝ E] {G : SimpleGraph W} {H : SimpleGraph V}
    (hG : GenericallyRigid G E) (f : V → W) (a b : V) (hab : a ≠ b)
    (hfsurj : Function.Surjective f)
    (hfiber : ∀ x y, f x = f y ↔ x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a))
    (hedge : H.Adj a b)
    (hcover : ∀ w z, G.Adj w z → ∃ x y, f x = w ∧ f y = z ∧ H.Adj x y)
    {C : Type*} [Fintype C] (c : C → V) (hc : Function.Injective c)
    (hcommon : ∀ i, H.Adj a (c i) ∧ H.Adj b (c i))
    (hdim : finrank ℝ E = Fintype.card C + 1) :
    GenericallyRigid H E := by
  classical
  have hfab : f a = f b := (hfiber a b).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have hex : ∀ w, ∃ x, f x = w ∧ x ≠ b := by
    intro w
    obtain ⟨x, hx⟩ := hfsurj w
    by_cases hxb : x = b
    · exact ⟨a, by simpa only [hxb, ← hfab] using hx, hab⟩
    · exact ⟨x, hx, hxb⟩
  choose s hsf hsne using hex
  have hsinj : Function.Injective s := by
    intro w z h
    calc w = f (s w) := (hsf w).symm
         _ = f (s z) := congrArg f h
         _ = z := hsf z
  have hsection : ∀ x, x ≠ b → s (f x) = x := by
    intro x hxb
    rcases (hfiber (s (f x)) x).mp (hsf (f x)) with h | ⟨_, hx⟩ | ⟨hs, _⟩
    · exact h
    · exact False.elim (hxb hx)
    · exact False.elim (hsne (f x) hs)
  let e : Option W ≃ V := Equiv.ofBijective (fun w => w.elim b s) (by
    constructor
    · intro w z h
      cases w with
      | none =>
        cases z with
        | none => rfl
        | some z => exact False.elim (hsne z h.symm)
      | some w =>
        cases z with
        | none => exact False.elim (hsne w h)
        | some z => exact congrArg some (hsinj h)
    · intro x
      by_cases hxb : x = b
      · exact ⟨none, hxb.symm⟩
      · exact ⟨some (f x), hsection x hxb⟩)
  have he_none : e none = b := rfl
  have he_some : ∀ w, e (some w) = s w := fun _ => rfl
  have he_root : e (some (f a)) = a := hsection a hab
  have hcomm : ∀ z : Option W, collapseVertex (f a) z = f (e z) := by
    intro z
    cases z with
    | none => exact hfab
    | some w => exact (hsf w).symm
  let H' := H.comap e
  have hedge' : H'.Adj none (some (f a)) := by
    change H.Adj (e none) (e (some (f a)))
    rw [he_none, he_root]
    exact hedge.symm
  have hcover' : ∀ w z, G.Adj w z → ∃ x y : Option W,
      collapseVertex (f a) x = w ∧ collapseVertex (f a) y = z ∧ H'.Adj x y := by
    intro w z hwz
    obtain ⟨x, y, hx, hy, hxy⟩ := hcover w z hwz
    refine ⟨e.symm x, e.symm y, ?_, ?_, ?_⟩
    · simpa only [hcomm, Equiv.apply_symm_apply] using hx
    · simpa only [hcomm, Equiv.apply_symm_apply] using hy
    · change H.Adj (e (e.symm x)) (e (e.symm y))
      simpa only [Equiv.apply_symm_apply] using hxy
  have hc' : Function.Injective (f ∘ c) := by
    intro i j hij
    rcases (hfiber (c i) (c j)).mp hij with h | ⟨hi, _⟩ | ⟨hi, _⟩
    · exact hc h
    · exact False.elim ((hcommon i).1.ne' hi)
    · exact False.elim ((hcommon i).2.ne' hi)
  have hleft : ∀ i, H'.Adj none (some ((f ∘ c) i)) := by
    intro i
    change H.Adj b (s (f (c i)))
    rw [hsection (c i) (hcommon i).2.ne']
    exact (hcommon i).2
  have hright : ∀ i, H'.Adj (some (f a)) (some ((f ∘ c) i)) := by
    intro i
    change H.Adj (s (f a)) (s (f (c i)))
    rw [hsection a hab, hsection (c i) (hcommon i).2.ne']
    exact (hcommon i).1
  have hH' := hG.vertex_split_option (f a) hedge' hcover' (f ∘ c) hc' hleft hright hdim
  exact (genericallyRigid_comap_iff H e).mp hH'

/-- Finset version of vertex splitting: any set of at least `dim E - 1`
common neighbors supplies the required independent subfamily. -/
theorem GenericallyRigid.of_vertex_collapse_finset [Fintype V] [Fintype W]
    [FiniteDimensional ℝ E] {G : SimpleGraph W} {H : SimpleGraph V}
    (hG : GenericallyRigid G E) (f : V → W) (a b : V) (hab : a ≠ b)
    (hfsurj : Function.Surjective f)
    (hfiber : ∀ x y, f x = f y ↔ x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a))
    (hedge : H.Adj a b)
    (hcover : ∀ w z, G.Adj w z → ∃ x y, f x = w ∧ f y = z ∧ H.Adj x y)
    (common : Finset V) (hcommon : ∀ x ∈ common, H.Adj a x ∧ H.Adj b x)
    (hdim : 0 < finrank ℝ E) (hcard : finrank ℝ E ≤ common.card + 1) :
    GenericallyRigid H E := by
  classical
  obtain ⟨c, hcsub, hccard⟩ := Finset.exists_subset_card_eq
    (s := common) (n := finrank ℝ E - 1) (by omega)
  exact hG.of_vertex_collapse f a b hab hfsurj hfiber hedge hcover
    (fun x : c => x.val) Subtype.val_injective
    (fun x => hcommon x.val (hcsub x.property)) (by simpa using (by omega :
      finrank ℝ E = c.card + 1))

end Cubical.Rigidity
