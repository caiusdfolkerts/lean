module

public import Papers.GraphicalZonotopes.PathCoefficients
public import Papers.GraphicalZonotopes.LocalDeltas

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open Finset
open scoped BigOperators

abbrev vertex (n i k : ℕ) (h : i+k<n) : Fin n := ⟨i+k,h⟩

theorem window_pair_eq {n i a b : ℕ} (ha : i+a<n) (hb : i+b<n) :
    window n i {a,b} = {vertex n i a ha, vertex n i b hb} := by
  ext v
  simp only [mem_window, mem_insert, mem_singleton, vertex, Fin.ext_iff]
  omega

theorem window_triple_eq {n i a b c : ℕ}
    (ha : i+a<n) (hb : i+b<n) (hc : i+c<n) :
    window n i {a,b,c} = {vertex n i a ha, vertex n i b hb, vertex n i c hc} := by
  ext v
  simp only [mem_window, mem_insert, mem_singleton, vertex, Fin.ext_iff]
  omega

theorem window_quad_eq {n i a b c d : ℕ}
    (ha : i+a<n) (hb : i+b<n) (hc : i+c<n) (hd : i+d<n) :
    window n i {a,b,c,d} =
      {vertex n i a ha, vertex n i b hb, vertex n i c hc, vertex n i d hd} := by
  ext v
  simp only [mem_window, mem_insert, mem_singleton, vertex, Fin.ext_iff]
  omega

theorem delta_edge1 (y : SetFunction (Fin n)) (i : Fin (n-1)) :
    delta (zeta y) (vertex n i.val 0 (by omega)) (vertex n i.val 1 (by omega)) ∅ =
      (coordinates y).edge1 i := by
  rw [delta_zeta_empty y (by simp [vertex, Fin.ext_iff])]
  exact congrArg y (window_pair_eq (by omega) (by omega)).symm

theorem delta_edge2 (y : SetFunction (Fin n)) (i : Fin (n-2)) :
    delta (zeta y) (vertex n i.val 0 (by omega)) (vertex n i.val 2 (by omega)) ∅ =
      (coordinates y).edge2 i := by
  rw [delta_zeta_empty y (by simp [vertex, Fin.ext_iff])]
  exact congrArg y (window_pair_eq (by omega) (by omega)).symm

theorem delta_edge3 (y : SetFunction (Fin n)) (i : Fin (n-3)) :
    delta (zeta y) (vertex n i.val 0 (by omega)) (vertex n i.val 3 (by omega)) ∅ =
      (coordinates y).edge3 i := by
  rw [delta_zeta_empty y (by simp [vertex, Fin.ext_iff])]
  exact congrArg y (window_pair_eq (by omega) (by omega)).symm

theorem delta_row013 (y : SetFunction (Fin n)) (i : Fin (n-3)) :
    delta (zeta y) (vertex n i.val 0 (by omega)) (vertex n i.val 3 (by omega))
      {vertex n i.val 1 (by omega)} =
      (coordinates y).edge3 i + (coordinates y).tri013 i := by
  rw [delta_zeta_singleton y (by simp [vertex, Fin.ext_iff])
    (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])]
  dsimp [coordinates]
  rw [window_pair_eq (by omega) (by omega),
    window_triple_eq (by omega) (by omega) (by omega)]
  congr 1
  congr 1
  ext v
  simp [or_comm, or_left_comm, or_assoc]

theorem delta_row01 (y : SetFunction (Fin n)) (i : Fin (n-3)) :
    delta (zeta y) (vertex n i.val 0 (by omega)) (vertex n i.val 1 (by omega))
      {vertex n i.val 2 (by omega), vertex n i.val 3 (by omega)} =
      (coordinates y).edge1 ⟨i.val, by omega⟩ +
      (coordinates y).tri012 ⟨i.val, by omega⟩ +
      (coordinates y).tri013 i + (coordinates y).tetra i := by
  rw [delta_zeta_pair y (by simp [vertex, Fin.ext_iff])
    (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])
    (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])
    (by simp [vertex, Fin.ext_iff])]
  dsimp [coordinates]
  rw [window_pair_eq (by omega) (by omega),
    window_triple_eq (by omega) (by omega) (by omega),
    window_triple_eq (by omega) (by omega) (by omega),
    window_quad_eq (by omega) (by omega) (by omega) (by omega)]

theorem delta_row13 (y : SetFunction (Fin n)) (i : Fin (n-3)) :
    delta (zeta y) (vertex n i.val 1 (by omega)) (vertex n i.val 3 (by omega))
      {vertex n i.val 0 (by omega), vertex n i.val 2 (by omega)} =
      (coordinates y).edge2 ⟨i.val+1, by omega⟩ +
      (coordinates y).tri013 i +
      (coordinates y).tri012 ⟨i.val+1, by omega⟩ + (coordinates y).tetra i := by
  rw [delta_zeta_pair y (by simp [vertex, Fin.ext_iff])
    (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])
    (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])
    (by simp [vertex, Fin.ext_iff])]
  dsimp [coordinates]
  rw [window_pair_eq (by omega) (by omega),
    window_triple_eq (by omega) (by omega) (by omega),
    window_triple_eq (by omega) (by omega) (by omega),
    window_quad_eq (by omega) (by omega) (by omega) (by omega)]
  simp only [vertex, Nat.add_zero, Nat.add_assoc]
  apply congrArg₂ (fun x y : ℝ => x+y)
  · apply congrArg₂ (fun x y : ℝ => x+y)
    · apply congrArg₂ (fun x y : ℝ => x+y)
      · apply congrArg y
        ext v
        simp only [mem_insert,mem_singleton,vertex,Fin.ext_iff] <;> omega
      · apply congrArg y
        ext v
        simp only [mem_insert,mem_singleton,vertex,Fin.ext_iff] <;> omega
    · apply congrArg y
      ext v
      simp only [mem_insert,mem_singleton,vertex,Fin.ext_iff] <;> omega
  · apply congrArg y
    ext v
    simp only [mem_insert,mem_singleton,vertex,Fin.ext_iff] <;> omega

theorem delta_row03 (y : SetFunction (Fin n)) (i : Fin (n-3)) :
    delta (zeta y) (vertex n i.val 0 (by omega)) (vertex n i.val 3 (by omega))
      {vertex n i.val 1 (by omega), vertex n i.val 2 (by omega)} =
      (coordinates y).edge3 i + (coordinates y).tri013 i +
      (coordinates y).tri023 i + (coordinates y).tetra i := by
  rw [delta_zeta_pair y (by simp [vertex, Fin.ext_iff])
    (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])
    (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])
    (by simp [vertex, Fin.ext_iff])]
  dsimp [coordinates]
  rw [window_pair_eq (by omega) (by omega),
    window_triple_eq (by omega) (by omega) (by omega),
    window_triple_eq (by omega) (by omega) (by omega),
    window_quad_eq (by omega) (by omega) (by omega) (by omega)]
  apply congrArg₂ (fun x y : ℝ => x+y)
  · apply congrArg₂ (fun x y : ℝ => x+y)
    · apply congrArg₂ (fun x y : ℝ => x+y)
      · apply congrArg y
        ext v
        simp only [mem_insert,mem_singleton,vertex,Fin.ext_iff] <;> omega
      · apply congrArg y
        ext v
        simp only [mem_insert,mem_singleton,vertex,Fin.ext_iff] <;> omega
    · apply congrArg y
      ext v
      simp only [mem_insert,mem_singleton,vertex,Fin.ext_iff] <;> omega
  · apply congrArg y
    ext v
    simp only [mem_insert,mem_singleton,vertex,Fin.ext_iff] <;> omega

/-- Every zero equation used for propagation is a genuine zero elemental row
of the displayed path function, including the zero pair coordinates. -/
theorem tight_of_preserves_zeros {n : ℕ} (f : SetFunction (Fin n))
    (hz : ∀ u v, u ≠ v → ∀ S, u ∉ S → v ∉ S →
      delta (setFunction n) u v S = 0 → delta f u v S = 0) :
    Tight n (coordinates (mobius f)) := by
  have he := coordinates_coefficients n
  have hedge1 (i : Fin (n-1)) : (coordinates (mobius f)).edge1 i = 0 := by
    rw [← delta_edge1, zeta_mobius]
    apply hz _ _ (by simp [vertex, Fin.ext_iff]) ∅ (by simp) (by simp)
    rw [setFunction, delta_edge1, he]
    rfl
  have hedge2 (i : Fin (n-2)) : (coordinates (mobius f)).edge2 i = 0 := by
    rw [← delta_edge2, zeta_mobius]
    apply hz _ _ (by simp [vertex, Fin.ext_iff]) ∅ (by simp) (by simp)
    rw [setFunction, delta_edge2, he]
    rfl
  have hedge3 (i : Fin (n-3)) : (coordinates (mobius f)).edge3 i = 0 := by
    rw [← delta_edge3, zeta_mobius]
    apply hz _ _ (by simp [vertex, Fin.ext_iff]) ∅ (by simp) (by simp)
    rw [setFunction, delta_edge3, he]
    rfl
  refine ⟨hedge1, hedge2, hedge3, ?_⟩
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← delta_row013, zeta_mobius]
    apply hz _ _ (by simp [vertex, Fin.ext_iff]) _
      (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])
    rw [setFunction, delta_row013, he]
    norm_num [scale]
  · rw [← delta_row01, zeta_mobius]
    apply hz _ _ (by simp [vertex, Fin.ext_iff]) _
      (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])
    rw [setFunction, delta_row01, he]
    norm_num [scale]
  · rw [← delta_row13, zeta_mobius]
    apply hz _ _ (by simp [vertex, Fin.ext_iff]) _
      (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])
    rw [setFunction, delta_row13, he]
    norm_num [scale]
  · rw [← delta_row03, zeta_mobius]
    apply hz _ _ (by simp [vertex, Fin.ext_iff]) _
      (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])
    rw [setFunction, delta_row03, he]
    norm_num [scale]

theorem coefficients_smul_supported {n : ℕ} (a : ℝ) :
    CliqueSupported (graph n) (a • coefficients n) := by
  obtain ⟨he, hs, hn⟩ := coefficients_supported n
  refine ⟨by simp [he], fun v => by simp [hs v], ?_⟩
  intro C u v hu hv huv hnon
  simp [hn C u v hu hv huv hnon]

theorem coordinates_smul_coefficients (n : ℕ) (a : ℝ) :
    coordinates (a • coefficients n) = scale n a := by
  have h := coordinates_coefficients n
  apply Coordinates.ext <;> funext i
  · have he := congrFun (congrArg Coordinates.edge1 h) i
    change a * coefficients n _ = 0
    rw [show coefficients n _ = 0 from he]
    simp
  · have he := congrFun (congrArg Coordinates.edge2 h) i
    change a * coefficients n _ = 0
    rw [show coefficients n _ = 0 from he]
    simp
  · have he := congrFun (congrArg Coordinates.edge3 h) i
    change a * coefficients n _ = 0
    rw [show coefficients n _ = 0 from he]
    simp
  · have he := congrFun (congrArg Coordinates.tri012 h) i
    change a * coefficients n _ = a
    rw [show coefficients n _ = 1 from he]
    simp
  · have he := congrFun (congrArg Coordinates.tri013 h) i
    change a * coefficients n _ = 0
    rw [show coefficients n _ = 0 from he]
    simp
  · have he := congrFun (congrArg Coordinates.tri023 h) i
    change a * coefficients n _ = a
    rw [show coefficients n _ = 1 from he]
    simp
  · have he := congrFun (congrArg Coordinates.tetra h) i
    change a * coefficients n _ = -a
    rw [show coefficients n _ = -1 from he]
    ring

/-- The complete normalized common-zero space is a line, not merely the
restriction of that space to the displayed nonzero coordinates. -/
theorem complete_tight_kernel {n : ℕ} (hn : 4 ≤ n) (f : SetFunction (Fin n))
    (hfn : TranslationNormalized f)
    (hz : ∀ u v, u ≠ v → ∀ S, u ∉ S → v ∉ S →
      delta (setFunction n) u v S = 0 → delta f u v S = 0) :
    ∃ a : ℝ, f = a • setFunction n := by
  have hG : Graphical (graph n) f := by
    intro u v huv hnon S hu hv
    exact hz u v huv S hu hv (setFunction_graphical n u v huv hnon S hu hv)
  have hsup : CliqueSupported (graph n) (mobius f) :=
    (mobius_cliqueSupported_iff _ _).mpr ⟨hfn, hG⟩
  obtain ⟨a, ha⟩ := (tight_iff_exists_scale hn _).mp (tight_of_preserves_zeros f hz)
  have hcoeff : mobius f = a • coefficients n :=
    coordinates_injective_on_supported hsup (coefficients_smul_supported a)
      (ha.trans (coordinates_smul_coefficients n a).symm)
  refine ⟨a, ?_⟩
  have hzeta := congrArg zeta hcoeff
  rw [zeta_mobius] at hzeta
  calc
    f = zeta (a • coefficients n) := hzeta
    _ = a • setFunction n := zetaLinear.map_smul a (coefficients n)

end Path
end GraphicalZonotopes
