import FairAllocation.Algorithm

set_option autoImplicit false

/-!
# Termination and comparison complexity

We count loop iterations and rational order comparisons in the two minimum
scans and the feasibility filter. This is an arithmetic/comparison model,
not a machine-instruction or rational bit-complexity model.
-/

namespace FairAllocation

variable {A G : Type*}

def pickMinComparisons {α : Type*} (w : α → ℚ) : List α → ℕ
  | [] => 0
  | _ :: L => pickMinComparisons w L + if (pickMin w L).isSome then 1 else 0

theorem pickMinComparisons_le {α : Type*} (w : α → ℚ) (L : List α) :
    pickMinComparisons w L ≤ L.length := by
  induction L with
  | nil => simp [pickMinComparisons]
  | cons a L ih =>
    simp only [pickMinComparisons, List.length_cons]
    split_ifs <;> omega

namespace Instance

variable (I : Instance A G)

def decisionComparisons (S : State A G) : ℕ :=
  if S.pool.isEmpty then 0
  else pickMinComparisons (fun a => total I.value (S.bundle a)) S.active +
    match pickMin (fun a => total I.value (S.bundle a)) S.active with
    | none => 0
    | some a => S.pool.length + pickMinComparisons (fun g => -I.density a g)
        (S.pool.filter (fun g => decide (I.Fits S a g)))

theorem decisionComparisons_le (S : State A G) :
    I.decisionComparisons S ≤ 2 * S.rank := by
  have ha := pickMinComparisons_le (fun a => total I.value (S.bundle a)) S.active
  unfold decisionComparisons
  split_ifs
  · omega
  · cases h : pickMin (fun a => total I.value (S.bundle a)) S.active with
    | none => simp only; unfold State.rank; omega
    | some a =>
      have hg := pickMinComparisons_le (fun g => -I.density a g)
        (S.pool.filter (fun g => decide (I.Fits S a g)))
      have hlen := List.length_filter_le (fun g => decide (I.Fits S a g)) S.pool
      simp only
      unfold State.rank
      omega

variable [DecidableEq A] [DecidableEq G]

def iterations (I : Instance A G) : ℕ → State A G → ℕ
  | 0, _ => 0
  | t + 1, S => match I.choose S with
    | .stop => 0
    | .retire a => 1 + I.iterations t (I.retire S a)
    | .give a g => 1 + I.iterations t (I.give S a g)

def comparisonCost (I : Instance A G) : ℕ → State A G → ℕ
  | 0, _ => 0
  | t + 1, S => I.decisionComparisons S + match I.choose S with
    | .stop => 0
    | .retire a => I.comparisonCost t (I.retire S a)
    | .give a g => I.comparisonCost t (I.give S a g)

theorem iterations_le (t : ℕ) (S : State A G) : I.iterations t S ≤ t := by
  induction t generalizing S with
  | zero => simp [iterations]
  | succ t ih =>
    simp only [iterations]
    cases I.choose S with
    | stop => simp only; omega
    | retire a => simp only; have := ih (I.retire S a); omega
    | give a g => simp only; have := ih (I.give S a g); omega

theorem rank_run_add_iterations (t : ℕ) (S : State A G) :
    (I.run t S).rank + I.iterations t S = S.rank := by
  induction t generalizing S with
  | zero => simp [run, iterations]
  | succ t ih =>
    have hspec := I.choose_spec S
    cases hc : I.choose S with
    | stop => simp [run, iterations, hc]
    | retire a =>
      have hs : I.Chosen S (.retire a) := by simpa [hc] using hspec
      have hr := I.rank_retire S hs.1.1
      have hi := ih (I.retire S a)
      simp only [run, iterations, hc]
      omega
    | give a g =>
      have hs : I.Chosen S (.give a g) := by simpa [hc] using hspec
      have hr := I.rank_give (a := a) S hs.2.1
      have hi := ih (I.give S a g)
      simp only [run, iterations, hc]
      omega

theorem comparisonCost_le (t : ℕ) (S : State A G) :
    I.comparisonCost t S ≤ 2 * t * S.rank := by
  induction t generalizing S with
  | zero => simp [comparisonCost]
  | succ t ih =>
    have hcost := I.decisionComparisons_le S
    have hspec := I.choose_spec S
    cases hc : I.choose S with
    | stop =>
      simp only [comparisonCost, hc, Nat.add_zero]
      nlinarith
    | retire a =>
      have hs : I.Chosen S (.retire a) := by simpa [hc] using hspec
      have hr := I.rank_retire S hs.1.1
      have hi := ih (I.retire S a)
      simp only [comparisonCost, hc]
      nlinarith
    | give a g =>
      have hs : I.Chosen S (.give a g) := by simpa [hc] using hspec
      have hr := I.rank_give (a := a) S hs.2.1
      have hi := ih (I.give S a g)
      simp only [comparisonCost, hc]
      nlinarith

end Instance

/-- At most one iteration per good or agent. -/
theorem densestGreedy_iterations_le {n m : ℕ} (I : Instance (Fin n) (Fin m)) :
    I.iterations (m + n) (initial (List.finRange n) (List.finRange m)) ≤ m + n :=
  I.iterations_le _ _

/-- A concrete polynomial bound on rational order comparisons. -/
theorem densestGreedy_comparisons_le {n m : ℕ} (I : Instance (Fin n) (Fin m)) :
    I.comparisonCost (m + n) (initial (List.finRange n) (List.finRange m)) ≤
      2 * (m + n) ^ 2 := by
  have h := I.comparisonCost_le (m + n) (initial (List.finRange n) (List.finRange m))
  simpa [initial, State.rank, pow_two, Nat.mul_assoc] using h

end FairAllocation
