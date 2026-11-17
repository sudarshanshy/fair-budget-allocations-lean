import FairAllocation.Algorithm
import FairAllocation.Pairwise
import FairAllocation.Charity

set_option autoImplicit false

/-!
# Deriving the appendix's comparison properties from Algorithm 2

All hypotheses of `pairwise_ef2` and `charity_ef1` are maintained by the
executable loop. In particular, no fairness property is included in the
input assumptions or in the choice rule.
-/

namespace FairAllocation

variable {A G : Type*}

theorem Priority.append_left {v s : G → ℚ} {B : ℚ} {X Y : List G}
    (h : Priority v s B X Y) (ht : TerminalPriority v s B X Y) (g : G) :
    Priority v s B (X ++ [g]) Y := by
  intro P x Q y hX hY hv hf
  rcases before_append_singleton hX with hX | ⟨rfl, rfl⟩
  · exact h P x Q y hX hY hv hf
  · exact ((not_lt_of_ge hf) (ht Q y hY hv)).elim

theorem Priority.append_right {v s : G → ℚ} {B : ℚ} {X Y C : List G}
    (h : Priority v s B X Y) (hp : PoolPriority v s B X C) {g : G} (hg : g ∈ C) :
    Priority v s B X (Y ++ [g]) := by
  intro P x Q y hX hY hv hf
  rcases before_append_singleton hY with hY | ⟨rfl, rfl⟩
  · exact h P x Q y hX hY hv hf
  · exact hp P x y hX hg hf

theorem TerminalPriority.append_left {v s : G → ℚ}
    (hv : ∀ g, 0 ≤ v g) (hs : ∀ g, 0 ≤ s g)
    {B : ℚ} {X Y : List G} (h : TerminalPriority v s B X Y) (g : G) :
    TerminalPriority v s B (X ++ [g]) Y := by
  intro Q y hY hval
  have hX : total v X < total v Q := by
    simp only [total_append, total_singleton] at hval
    linarith [hv g]
  have hbound := h Q y hY hX
  simp only [total_append, total_singleton]
  linarith [hs g]

theorem TerminalPriority.append_right {v s : G → ℚ} {B : ℚ} {X Y : List G}
    (h : TerminalPriority v s B X Y) {g : G}
    (hnew : total v X < total v Y → B < total s X + s g) :
    TerminalPriority v s B X (Y ++ [g]) := by
  intro Q y hY hval
  rcases before_append_singleton hY with hY | ⟨rfl, rfl⟩
  · exact h Q y hY hval
  · exact hnew hval

theorem PoolPriority.append_left {v s : G → ℚ} {B : ℚ} {X C : List G}
    (h : PoolPriority v s B X C) {g : G}
    (hnew : ∀ y ∈ C, total s X + s y ≤ B → v y / s y ≤ v g / s g) :
    PoolPriority v s B (X ++ [g]) C := by
  intro P x y hX hy hfit
  rcases before_append_singleton hX with hX | ⟨rfl, rfl⟩
  · exact h P x y hX hy hfit
  · exact hnew y hy hfit

theorem PoolPriority.subset_right {v s : G → ℚ} {B : ℚ} {X C C' : List G}
    (h : PoolPriority v s B X C) (hsub : C' ⊆ C) : PoolPriority v s B X C' := by
  intro P x y hX hy hfit
  exact h P x y hX (hsub hy) hfit

theorem DensitySorted.append_good {v s : G → ℚ} (hs : ∀ g, 0 ≤ s g)
    {B : ℚ} {X C : List G} (h : DensitySorted v s X)
    (hp : PoolPriority v s B X C) {g : G} (hg : g ∈ C)
    (hfit : total s X + s g ≤ B) : DensitySorted v s (X ++ [g]) := by
  apply List.pairwise_append.mpr
  refine ⟨h, by simp, ?_⟩
  intro x hx y hy
  have hy' : y = g := by simpa using hy
  subst y
  obtain ⟨P, Q, hPQ, _⟩ := List.eq_append_cons_of_mem hx
  have hbefore : Before X P x := ⟨Q, hPQ⟩
  apply hp P x g hbefore hg
  have hle := total_sublist hs hbefore.sublist
  linarith

namespace Instance

variable (I : Instance A G)

/-- An invariant of every reachable state, established without assuming EFk. -/
structure Invariant (S : State A G) : Prop where
  feasible : I.Feasible S.bundle
  ordered : ∀ a, DensitySorted I.value (I.size a) (S.bundle a)
  poolPriority : ∀ a, PoolPriority I.value (I.size a) (I.budget a) (S.bundle a) S.pool
  priority : ∀ a b, a ≠ b →
    Priority I.value (I.size a) (I.budget a) (S.bundle a) (S.bundle b)
  terminalPriority : ∀ a b, a ≠ b →
    TerminalPriority I.value (I.size a) (I.budget a) (S.bundle a) (S.bundle b)
  inactive : ∀ a, a ∉ S.active → NoFit (I.size a) (I.budget a) (S.bundle a) S.pool

theorem initial_invariant (agents : List A) (goods : List G) (hall : ∀ a, a ∈ agents) :
    I.Invariant (initial agents goods) := by
  constructor
  · intro a
    simpa [initial] using I.budget_nonneg a
  · intro a
    simp [initial, DensitySorted]
  · intro a P x y h
    exact (not_before_nil P x h).elim
  · intro a b hab P x Q y h
    exact (not_before_nil P x h).elim
  · intro a b hab Q y h
    exact (not_before_nil Q y h).elim
  · intro a ha
    exact (ha (hall a)).elim

variable [DecidableEq A] [DecidableEq G]

omit [DecidableEq G] in
theorem Invariant.retire {S : State A G} (hS : I.Invariant S) {a : A}
    (hc : I.Chosen S (.retire a)) : I.Invariant (I.retire S a) := by
  refine ⟨hS.feasible, hS.ordered, hS.poolPriority, hS.priority, hS.terminalPriority, ?_⟩
  intro b hb g hg
  by_cases hba : b = a
  · subst b
    exact lt_of_not_ge (hc.2 g hg)
  · apply hS.inactive b ?_ g hg
    intro hmem
    apply hb
    exact (List.mem_erase_of_ne hba).mpr hmem

theorem Invariant.give {S : State A G} (hS : I.Invariant S) {a : A} {g : G}
    (hc : I.Chosen S (.give a g)) : I.Invariant (I.give S a g) := by
  have hactive : a ∈ S.active := hc.1.1
  have hmin := hc.1.2
  have hgp : g ∈ S.pool := hc.2.1
  have hfit : I.Fits S a g := hc.2.2.1
  have hbest := hc.2.2.2
  have hpool : S.pool.erase g ⊆ S.pool := List.erase_subset
  constructor
  · intro b
    by_cases hba : b = a
    · subst b
      simpa [Instance.give, Feasible, Fits] using hfit
    · simpa [Instance.give, hba] using hS.feasible b
  · intro b
    by_cases hba : b = a
    · subst b
      simpa [Instance.give] using (hS.ordered a).append_good (I.size_nonneg a)
        (hS.poolPriority a) hgp hfit
    · simpa [Instance.give, hba] using hS.ordered b
  · intro b
    by_cases hba : b = a
    · subst b
      have hp := (hS.poolPriority a).append_left hbest
      simpa [Instance.give] using hp.subset_right hpool
    · simpa [Instance.give, hba] using (hS.poolPriority b).subset_right hpool
  · intro b c hbc
    by_cases hba : b = a
    · subst b
      have hca : c ≠ a := Ne.symm hbc
      simpa [Instance.give, hca] using
        (hS.priority a c hbc).append_left (hS.terminalPriority a c hbc) g
    · by_cases hca : c = a
      · subst c
        simpa [Instance.give, hba] using
          (hS.priority b a hba).append_right (hS.poolPriority b) hgp
      · simpa [Instance.give, hba, hca] using hS.priority b c hbc
  · intro b c hbc
    by_cases hba : b = a
    · subst b
      have hca : c ≠ a := Ne.symm hbc
      simpa [Instance.give, hca] using
        (hS.terminalPriority a c hbc).append_left I.value_nonneg (I.size_nonneg a) g
    · by_cases hca : c = a
      · subst c
        have hnew : total I.value (S.bundle b) < total I.value (S.bundle a) →
            I.budget b < total (I.size b) (S.bundle b) + I.size b g := by
          intro hv
          by_cases hb : b ∈ S.active
          · exact (not_lt_of_ge (hmin b hb) hv).elim
          · exact hS.inactive b hb g hgp
        simpa [Instance.give, hba] using (hS.terminalPriority b a hba).append_right hnew
      · simpa [Instance.give, hba, hca] using hS.terminalPriority b c hbc
  · intro b hb
    have hba : b ≠ a := by intro h; subst b; exact hb hactive
    intro y hy
    have h := hS.inactive b hb y (hpool hy)
    simpa [Instance.give, hba] using h

theorem run_invariant {S : State A G} (hS : I.Invariant S) (t : ℕ) :
    I.Invariant (I.run t S) :=
  I.run_preserves (P := I.Invariant) (fun _ _ h hc => h.retire I hc)
    (fun _ _ _ h hc => h.give I hc) t hS

omit [DecidableEq G] in
/-- Every terminal reachable state is EF2, and EF1 towards charity. -/
theorem Invariant.fair {S : State A G} (hS : I.Invariant S) (ht : S.Terminal) :
    I.Fair 2 S.bundle S.pool ∧
      ∀ a Z, Z.Sublist S.pool → total (I.size a) Z ≤ I.budget a →
        EF 1 I.value (total I.value (S.bundle a)) Z := by
  have hcharity : ∀ a Z, Z.Sublist S.pool → total (I.size a) Z ≤ I.budget a →
      EF 1 I.value (total I.value (S.bundle a)) Z := by
    intro a Z hZ hfit
    have hnofit : NoFit (I.size a) (I.budget a) (S.bundle a) S.pool := by
      rcases ht with hp | ha
      · intro g hg
        simp [hp] at hg
      · exact hS.inactive a (by simp [ha])
    exact charity_ef1 I.value_nonneg (I.size_pos a) (hS.ordered a)
      (hS.poolPriority a) hnofit hZ hfit
  refine ⟨⟨?_, ?_⟩, hcharity⟩
  · intro a b Z hZ hfit
    by_cases hab : a = b
    · subst b
      exact ef_of_total_le (total_sublist I.value_nonneg hZ)
    · exact pairwise_ef2 I.value_nonneg (I.size_pos a) (hS.ordered a)
        ((hS.priority a b hab).sublist_right I.value_nonneg hZ)
        ((hS.terminalPriority a b hab).sublist_right I.value_nonneg hZ) hfit
  · intro a Z hZ hfit
    exact (hcharity a Z hZ hfit).mono_count (by omega)

end Instance

end FairAllocation
