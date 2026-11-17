import FairAllocation.Basic

set_option autoImplicit false

namespace FairAllocation

variable {G : Type*}

/-- `P` is precisely the prefix preceding this occurrence of good `g` in `X`. -/
def Before (X P : List G) (g : G) : Prop := ∃ Q, X = P ++ g :: Q

theorem Before.sublist {X P : List G} {g : G} (h : Before X P g) : P.Sublist X := by
  obtain ⟨Q, rfl⟩ := h
  exact List.sublist_append_left _ _

theorem Before.mem {X P : List G} {g : G} (h : Before X P g) : g ∈ X := by
  obtain ⟨Q, rfl⟩ := h
  simp

theorem Before.total_le {w : G → ℚ} (hw : ∀ g, 0 ≤ w g)
    {X P : List G} {g : G} (h : Before X P g) : total w P + w g ≤ total w X := by
  obtain ⟨Q, rfl⟩ := h
  simp only [total_append, total_cons]
  linarith [total_nonneg (L := Q) (fun g _ => hw g)]

theorem Before.append {X P : List G} {g : G} (h : Before X P g) (Y : List G) :
    Before (X ++ Y) P g := by
  obtain ⟨Q, rfl⟩ := h
  exact ⟨Q ++ Y, by simp⟩

theorem before_last (X : List G) (g : G) : Before (X ++ [g]) X g := ⟨[], rfl⟩

@[simp] theorem not_before_nil (P : List G) (g : G) : ¬ Before [] P g := by
  rintro ⟨Q, h⟩
  have := congrArg List.length h
  simp at this

theorem before_append_singleton {X P : List G} {x g : G}
    (h : Before (X ++ [g]) P x) : Before X P x ∨ (P = X ∧ x = g) := by
  obtain ⟨Q, h⟩ := h
  induction X generalizing P with
  | nil =>
    cases P with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      exact Or.inr ⟨rfl, h.1.symm⟩
    | cons p P =>
      have := congrArg List.length h
      simp at this
  | cons a X ih =>
    cases P with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      exact Or.inl ⟨X, by simp [h.1]⟩
    | cons p P =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      rcases ih h with h | ⟨rfl, rfl⟩
      · obtain ⟨R, hR⟩ := h
        exact Or.inl ⟨R, by simp [hR]⟩
      · exact Or.inr ⟨rfl, rfl⟩

/-- A prefix of a selected subbundle precedes a corresponding occurrence in
the original bundle, whose preceding value can only be larger. -/
theorem Before.of_sublist {X Y P : List G} {g : G}
    (h : Before X P g) (hXY : X.Sublist Y) :
    ∃ Q, Before Y Q g ∧ P.Sublist Q := by
  obtain ⟨R, rfl⟩ := h
  obtain ⟨Y₁, Y₂, rfl, hP, hR⟩ := List.append_sublist_iff.mp hXY
  have hg : g ∈ Y₂ := List.mem_of_cons_sublist hR
  obtain ⟨L, K, hLK, _⟩ := List.eq_append_cons_of_mem hg
  refine ⟨Y₁ ++ L, ⟨K, ?_⟩, hP.trans (List.sublist_append_left _ _)⟩
  simp [hLK, List.append_assoc]

/-- Nonincreasing density, with ties allowed. -/
def DensitySorted (v s : G → ℚ) (X : List G) : Prop :=
  X.Pairwise (fun x y => v y / s y ≤ v x / s x)

/-- Split a density-sorted bundle at an arbitrary density threshold. -/
theorem density_split {v s : G → ℚ} {X : List G}
    (hX : DensitySorted v s X) (d : ℚ) :
    ∃ P Q, X = P ++ Q ∧
      (∀ g ∈ P, d ≤ v g / s g) ∧ (∀ g ∈ Q, v g / s g < d) := by
  induction X with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons x X ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hX
    by_cases hx : d ≤ v x / s x
    · obtain ⟨P, Q, h, hP, hQ⟩ := ih htail
      refine ⟨x :: P, Q, by simp [h], ?_, hQ⟩
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hx
      · exact hP g hg
    · refine ⟨[], x :: X, rfl, by simp, ?_⟩
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact lt_of_not_ge hx
      · exact (hhead g hg).trans_lt (lt_of_not_ge hx)

theorem exists_max_weight (w : G → ℚ) {X : List G} (hX : X ≠ []) :
    ∃ g ∈ X, ∀ x ∈ X, w x ≤ w g := by
  induction X with
  | nil => contradiction
  | cons a X ih =>
    by_cases ht : X = []
    · subst X
      exact ⟨a, by simp, by simp⟩
    · obtain ⟨g, hg, hmax⟩ := ih ht
      by_cases h : w a ≤ w g
      · refine ⟨g, by simp [hg], ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h
        · exact hmax x hx
      · refine ⟨a, by simp, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact (hmax x hx).trans (le_of_not_ge h)

end FairAllocation
