import FairAllocation.Invariants
import FairAllocation.Partition
import FairAllocation.FiniteSets
import FairAllocation.Runtime

set_option autoImplicit false

/-!
# Theorem 5: agent-specific sizes

For every finite instance with positive rational values and agent-specific
positive rational sizes, density greedy returns a feasible partition that
is EF2 among all agents and EF1 against charity. Budgets may be zero.
No distinct-density hypothesis, existence oracle, or assumed fairness
certificate is needed.
-/

namespace FairAllocation

variable {n m : ℕ}

theorem densestGreedy_invariant (I : Instance (Fin n) (Fin m)) :
    I.Invariant (densestGreedy I) :=
  I.run_invariant (I.initial_invariant _ _ (fun a => List.mem_finRange a)) _

/-- Appendix C, Theorem 5, including Lemma 11's stronger charity guarantee. -/
theorem densestGreedy_correct (I : Instance (Fin n) (Fin m)) :
    let S := densestGreedy I
    S.Valid ∧ I.Feasible S.bundle ∧ I.Fair 2 S.bundle S.pool ∧
      (∀ a Z, Z.Sublist S.pool → total (I.size a) Z ≤ I.budget a →
        EF 1 I.value (total I.value (S.bundle a)) Z) := by
  have h := densestGreedy_invariant I
  have hf := h.fair I (densestGreedy_terminal I)
  exact ⟨densestGreedy_valid I, h.feasible, hf.1, hf.2⟩

/-- Universal existence follows from the executable construction. -/
theorem exists_feasible_ef2 (I : Instance (Fin n) (Fin m)) :
    ∃ S : State (Fin n) (Fin m), S.Valid ∧ I.Feasible S.bundle ∧
      I.Fair 2 S.bundle S.pool ∧
      (∀ a Z, Z.Sublist S.pool → total (I.size a) Z ≤ I.budget a →
        EF 1 I.value (total I.value (S.bundle a)) Z) :=
  ⟨densestGreedy I, densestGreedy_correct I⟩

/-- Theorem 5 in finite-set notation, quantifying over every feasible subset. -/
theorem densestGreedy_correct_finset (I : Instance (Fin n) (Fin m)) :
    let S := densestGreedy I
    I.FairSets 2 (fun a => (S.bundle a).toFinset) S.pool.toFinset ∧
      (∀ a F, F ⊆ S.pool.toFinset →
        (∑ g ∈ F, I.size a g) ≤ I.budget a →
        SetEF 1 I.value (∑ g ∈ (S.bundle a).toFinset, I.value g) F) := by
  have h := densestGreedy_correct I
  refine ⟨I.fair_toFinset h.1 h.2.2.1, ?_⟩
  intro a F hF hsize
  exact I.subset_fair_toFinset (h.1.bundle_nodup a) h.1.pool_nodup
    (h.2.2.2 a) F hF hsize

/-- The main text's common-size model is a direct specialization. -/
def commonSizeInstance (v s : Fin m → ℚ) (B : Fin n → ℚ)
    (hv : ∀ g, 0 < v g) (hs : ∀ g, 0 < s g) (hB : ∀ a, 0 ≤ B a) :
    Instance (Fin n) (Fin m) := ⟨v, fun _ => s, B, hv, fun _ => hs, hB⟩

theorem commonSize_exists_ef2 (v s : Fin m → ℚ) (B : Fin n → ℚ)
    (hv : ∀ g, 0 < v g) (hs : ∀ g, 0 < s g) (hB : ∀ a, 0 ≤ B a) :
    ∃ S : State (Fin n) (Fin m), S.Valid ∧
      (commonSizeInstance v s B hv hs hB).Feasible S.bundle ∧
      (commonSizeInstance v s B hv hs hB).Fair 2 S.bundle S.pool := by
  obtain ⟨S, hvalid, hfeas, hfair, _⟩ :=
    exists_feasible_ef2 (commonSizeInstance v s B hv hs hB)
  exact ⟨S, hvalid, hfeas, hfair⟩

end FairAllocation
