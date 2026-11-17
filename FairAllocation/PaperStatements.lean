import FairAllocation.Main

set_option autoImplicit false

/-!
# The paper's exact-removal convention

For a comparison set containing at least two goods, the witnesses can be
chosen as two distinct goods, as in Definition 1. Against a nonempty subset
of charity, a single actual good suffices.
-/

namespace FairAllocation

open scoped BigOperators

variable {G : Type*} [DecidableEq G]

theorem SetEF.exact_removal {k : ℕ} {v : G → ℚ} {u : ℚ} {F : Finset G}
    (h : SetEF k v u F) (hv : ∀ g, 0 ≤ v g) (hk : k ≤ F.card) :
    ∃ R ⊆ F, R.card = k ∧ ∑ g ∈ F \ R, v g ≤ u := by
  obtain ⟨R, hRF, hRk, hval⟩ := h
  obtain ⟨T, hRT, hTF, hcard⟩ := Finset.exists_subsuperset_card_eq hRF hRk hk
  refine ⟨T, hTF, hcard, ?_⟩
  have hsub : F \ T ⊆ F \ R := by
    intro g hg
    obtain ⟨hgF, hgT⟩ := Finset.mem_sdiff.mp hg
    exact Finset.mem_sdiff.mpr ⟨hgF, fun hgR => hgT (hRT hgR)⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => hv g)).trans hval

theorem SetEF.two_goods {v : G → ℚ} {u : ℚ} {F : Finset G}
    (h : SetEF 2 v u F) (hv : ∀ g, 0 ≤ v g) (hF : 2 ≤ F.card) :
    ∃ x ∈ F, ∃ y ∈ F, x ≠ y ∧ ∑ g ∈ F \ {x, y}, v g ≤ u := by
  obtain ⟨R, hRF, hcard, hval⟩ := h.exact_removal hv hF
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
  exact ⟨x, hRF (by simp), y, hRF (by simp), hxy, hval⟩

theorem SetEF.one_good {v : G → ℚ} {u : ℚ} {F : Finset G}
    (h : SetEF 1 v u F) (hv : ∀ g, 0 ≤ v g) (hF : F.Nonempty) :
    ∃ x ∈ F, ∑ g ∈ F.erase x, v g ≤ u := by
  obtain ⟨R, hRF, hcard, hval⟩ := h.exact_removal hv (Finset.one_le_card.mpr hF)
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard
  exact ⟨x, hRF (by simp), by simpa [Finset.sdiff_singleton_eq_erase] using hval⟩

/-- Definition 1's two distinct deletion witnesses for every feasible subset. -/
theorem ef2_removal_witnesses {n m : ℕ} (I : Instance (Fin n) (Fin m))
    (a b : Fin n) (F : Finset (Fin m))
    (hsub : F ⊆ ((densestGreedy I).bundle b).toFinset)
    (hfit : (∑ g ∈ F, I.size a g) ≤ I.budget a) (hcard : 2 ≤ F.card) :
    ∃ x ∈ F, ∃ y ∈ F, x ≠ y ∧
      ∑ g ∈ F \ {x, y}, I.value g ≤
        ∑ g ∈ ((densestGreedy I).bundle a).toFinset, I.value g := by
  exact ((densestGreedy_correct_finset I).1.1 a b F hsub hfit).two_goods I.value_nonneg hcard

/-- Lemma 11's single-good witness for every nonempty feasible charity subset. -/
theorem charity_removal_witness {n m : ℕ} (I : Instance (Fin n) (Fin m))
    (a : Fin n) (F : Finset (Fin m))
    (hsub : F ⊆ (densestGreedy I).pool.toFinset)
    (hfit : (∑ g ∈ F, I.size a g) ≤ I.budget a) (hne : F.Nonempty) :
    ∃ x ∈ F, ∑ g ∈ F.erase x, I.value g ≤
      ∑ g ∈ ((densestGreedy I).bundle a).toFinset, I.value g := by
  exact ((densestGreedy_correct_finset I).2 a F hsub hfit).one_good I.value_nonneg hne

end FairAllocation
