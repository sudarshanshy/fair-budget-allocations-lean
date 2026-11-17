import Mathlib.Data.List.Sort
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Budget-constrained fair allocation: basic definitions

Formalization of Barman, Khan, Shyam and Sreenivas,
*Finding Fair Allocations under Budget Constraints* (AAAI 2023),
https://arxiv.org/abs/2208.08168.

Bundles are lists in allocation order. Valid allocations have no repeated goods.
A sublist therefore represents an arbitrary subset, with its inherited order.
`EF k v u Z` says that deleting at most `k` entries from `Z` leaves value at most `u`.
In particular, EF2 permits deleting two goods together.
-/

namespace FairAllocation

variable {G : Type*}

/-- Additive weight of a bundle. -/
def total (w : G → ℚ) (L : List G) : ℚ := (L.map w).sum

@[simp] theorem total_nil (w : G → ℚ) : total w [] = 0 := rfl

@[simp] theorem total_cons (w : G → ℚ) (g : G) (L : List G) :
    total w (g :: L) = w g + total w L := rfl

@[simp] theorem total_append (w : G → ℚ) (L K : List G) :
    total w (L ++ K) = total w L + total w K := by
  simp [total]

@[simp] theorem total_singleton (w : G → ℚ) (g : G) : total w [g] = w g := by
  simp [total]

theorem total_nonneg {w : G → ℚ} {L : List G}
    (hw : ∀ g ∈ L, 0 ≤ w g) : 0 ≤ total w L := by
  induction L with
  | nil => simp
  | cons g L ih =>
    simp only [total_cons]
    exact add_nonneg (hw g (by simp)) (ih (fun x hx => hw x (by simp [hx])))

theorem total_mono {w w' : G → ℚ} {L : List G}
    (h : ∀ g ∈ L, w g ≤ w' g) : total w L ≤ total w' L := by
  induction L with
  | nil => simp
  | cons g L ih =>
    simp only [total_cons]
    exact add_le_add (h g (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem total_sublist {w : G → ℚ} (hw : ∀ g, 0 ≤ w g)
    {L K : List G} (h : L.Sublist K) : total w L ≤ total w K := by
  induction h with
  | slnil => simp
  | cons a h ih =>
    simp only [total_cons]
    linarith [hw a]
  | cons_cons a h ih =>
    simp only [total_cons]
    linarith

theorem total_le_of_mem {w : G → ℚ} (hw : ∀ g, 0 ≤ w g)
    {L : List G} {g : G} (hg : g ∈ L) : w g ≤ total w L := by
  induction L with
  | nil => simp at hg
  | cons a L ih =>
    rcases List.mem_cons.mp hg with h | h
    · subst g
      simp only [total_cons]
      linarith [total_nonneg (L := L) (fun x _ => hw x)]
    · have := ih h
      simp only [total_cons]
      linarith [hw a]

theorem total_const (c : ℚ) (L : List G) :
    total (fun _ => c) L = (L.length : ℚ) * c := by
  induction L with
  | nil => simp
  | cons g L ih => simp [ih, Nat.cast_add, add_mul]; ring

theorem total_mul (c : ℚ) (w : G → ℚ) (L : List G) :
    total (fun g => c * w g) L = c * total w L := by
  induction L with
  | nil => simp
  | cons g L ih => simp [ih, mul_add]

theorem total_congr {w w' : G → ℚ} {L : List G}
    (h : ∀ g ∈ L, w g = w' g) : total w L = total w' L := by
  exact le_antisymm (total_mono (fun g hg => (h g hg).le))
    (total_mono (fun g hg => (h g hg).ge))

/-- Envy can be eliminated by deleting at most `k` goods. -/
def EF (k : ℕ) (v : G → ℚ) (u : ℚ) (Z : List G) : Prop :=
  ∃ K : List G, K.Sublist Z ∧ Z.length ≤ K.length + k ∧ total v K ≤ u

theorem EF.mono_value {k : ℕ} {v : G → ℚ} {u u' : ℚ} {Z : List G}
    (h : EF k v u Z) (hu : u ≤ u') : EF k v u' Z := by
  obtain ⟨K, hK, hn, hv⟩ := h
  exact ⟨K, hK, hn, hv.trans hu⟩

theorem EF.mono_count {k k' : ℕ} {v : G → ℚ} {u : ℚ} {Z : List G}
    (h : EF k v u Z) (hk : k ≤ k') : EF k' v u Z := by
  obtain ⟨K, hK, hn, hv⟩ := h
  exact ⟨K, hK, by omega, hv⟩

theorem ef_of_total_le {k : ℕ} {v : G → ℚ} {u : ℚ} {Z : List G}
    (h : total v Z ≤ u) : EF k v u Z :=
  ⟨Z, List.Sublist.refl _, by omega, h⟩

@[simp] theorem ef_nil {k : ℕ} {v : G → ℚ} {u : ℚ} (hu : 0 ≤ u) :
    EF k v u [] := ef_of_total_le hu

theorem ef_of_length_le {k : ℕ} {v : G → ℚ} {u : ℚ} {Z : List G}
    (hu : 0 ≤ u) (hk : Z.length ≤ k) : EF k v u Z := by
  exact ⟨[], List.nil_sublist _, by simpa, by simpa⟩

theorem EF.append {k l : ℕ} {v : G → ℚ} {u w : ℚ} {Y Z : List G}
    (hY : EF k v u Y) (hZ : EF l v w Z) : EF (k + l) v (u + w) (Y ++ Z) := by
  obtain ⟨K, hK, hnK, hvK⟩ := hY
  obtain ⟨L, hL, hnL, hvL⟩ := hZ
  refine ⟨K ++ L, hK.append hL, ?_, ?_⟩
  · simp only [List.length_append]; omega
  · simpa using add_le_add hvK hvL

theorem EF.append_good {k : ℕ} {v : G → ℚ} {u : ℚ} {Z : List G}
    (h : EF k v u Z) (g : G) : EF k v (u + v g) (Z ++ [g]) := by
  simpa using h.append (ef_of_total_le (k := 0) (le_refl (total v [g])))

theorem EF.discard_good {k : ℕ} {v : G → ℚ} {u : ℚ} {Z : List G}
    (h : EF k v u Z) (g : G) : EF (k + 1) v u (Z ++ [g]) := by
  obtain ⟨K, hK, hn, hv⟩ := h
  refine ⟨K, hK.trans (List.sublist_append_left _ _), ?_, hv⟩
  simp only [List.length_append, List.length_singleton]
  omega

/-- Agent-specific sizes include the common-size model of the main text. -/
structure Instance (A G : Type*) where
  value : G → ℚ
  size : A → G → ℚ
  budget : A → ℚ
  value_pos : ∀ g, 0 < value g
  size_pos : ∀ a g, 0 < size a g
  budget_nonneg : ∀ a, 0 ≤ budget a

namespace Instance

variable {A : Type*} (I : Instance A G)

def density (a : A) (g : G) : ℚ := I.value g / I.size a g

theorem value_nonneg (g : G) : 0 ≤ I.value g := (I.value_pos g).le
theorem size_nonneg (a : A) (g : G) : 0 ≤ I.size a g := (I.size_pos a g).le
theorem density_pos (a : A) (g : G) : 0 < I.density a g :=
  div_pos (I.value_pos g) (I.size_pos a g)

/-- Every feasible subset of every other bundle and of charity is tested. -/
def Fair (k : ℕ) (bundle : A → List G) (charity : List G) : Prop :=
  (∀ a b Z, Z.Sublist (bundle b) → total (I.size a) Z ≤ I.budget a →
    EF k I.value (total I.value (bundle a)) Z) ∧
  (∀ a Z, Z.Sublist charity → total (I.size a) Z ≤ I.budget a →
    EF k I.value (total I.value (bundle a)) Z)

def Feasible (bundle : A → List G) : Prop :=
  ∀ a, total (I.size a) (bundle a) ≤ I.budget a

end Instance
end FairAllocation
