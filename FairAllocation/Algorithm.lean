import FairAllocation.Basic
import Mathlib.Data.List.FinRange

set_option autoImplicit false

/-!
# Algorithm 2: executable density greedy

Both selections are linear scans. Ties are broken by the order of the input
list. Each nonterminal iteration removes one good or one active agent.
-/

namespace FairAllocation

variable {A G : Type*}

/-- Return a minimum-weight entry, breaking ties towards the head. -/
def pickMin {α : Type*} (w : α → ℚ) : List α → Option α
  | [] => none
  | a :: L => match pickMin w L with
    | none => some a
    | some b => some (if w a ≤ w b then a else b)

theorem pickMin_eq_none {α : Type*} (w : α → ℚ) (L : List α) :
    pickMin w L = none ↔ L = [] := by
  cases L with
  | nil => simp [pickMin]
  | cons a L => cases h : pickMin w L <;> simp [pickMin, h]

theorem pickMin_spec {α : Type*} (w : α → ℚ) {L : List α} {a : α}
    (h : pickMin w L = some a) : a ∈ L ∧ ∀ b ∈ L, w a ≤ w b := by
  induction L generalizing a with
  | nil => simp [pickMin] at h
  | cons x L ih =>
    cases hb : pickMin w L with
    | none =>
      have hL := (pickMin_eq_none w L).mp hb
      subst L
      simp only [pickMin, Option.some.injEq] at h
      subst a
      simp
    | some y =>
      obtain ⟨hy, hmin⟩ := ih hb
      simp only [pickMin, hb] at h
      split_ifs at h with hxy
      · simp only [Option.some.injEq] at h
        subst a
        refine ⟨by simp, ?_⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · rfl
        · exact hxy.trans (hmin b hb)
      · simp only [Option.some.injEq] at h
        subst a
        refine ⟨by simp [hy], ?_⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact le_of_not_ge hxy
        · exact hmin b hb

structure State (A G : Type*) where
  bundle : A → List G
  pool : List G
  active : List A

def State.rank (S : State A G) : ℕ := S.pool.length + S.active.length

def State.Terminal (S : State A G) : Prop := S.pool = [] ∨ S.active = []

inductive Action (A G : Type*) where
  | stop
  | retire (a : A)
  | give (a : A) (g : G)
  deriving DecidableEq

namespace Instance

variable (I : Instance A G)

def Fits (S : State A G) (a : A) (g : G) : Prop :=
  total (I.size a) (S.bundle a) + I.size a g ≤ I.budget a

instance (S : State A G) (a : A) (g : G) : Decidable (I.Fits S a g) :=
  inferInstanceAs (Decidable (_ ≤ _))

def minimumAgent (S : State A G) (a : A) : Prop :=
  a ∈ S.active ∧ ∀ b ∈ S.active, total I.value (S.bundle a) ≤ total I.value (S.bundle b)

def densestGood (S : State A G) (a : A) (g : G) : Prop :=
  g ∈ S.pool ∧ I.Fits S a g ∧
    ∀ h ∈ S.pool, I.Fits S a h → I.density a h ≤ I.density a g

def choose (S : State A G) : Action A G :=
  if S.pool.isEmpty then .stop
  else match pickMin (fun a => total I.value (S.bundle a)) S.active with
    | none => .stop
    | some a => match pickMin (fun g => -I.density a g)
        (S.pool.filter (fun g => decide (I.Fits S a g))) with
      | none => .retire a
      | some g => .give a g

/-- Exact, local specification of a single iteration. -/
def Chosen (S : State A G) : Action A G → Prop
  | .stop => S.Terminal
  | .retire a => I.minimumAgent S a ∧ ∀ g ∈ S.pool, ¬ I.Fits S a g
  | .give a g => I.minimumAgent S a ∧ I.densestGood S a g

theorem choose_spec (S : State A G) : I.Chosen S (I.choose S) := by
  unfold choose
  split_ifs with hempty
  · exact Or.inl (List.isEmpty_iff.mp hempty)
  · cases ha : pickMin (fun a => total I.value (S.bundle a)) S.active with
    | none => exact Or.inr ((pickMin_eq_none _ _).mp ha)
    | some a =>
      have hamin := pickMin_spec _ ha
      cases hg : pickMin (fun g => -I.density a g)
          (S.pool.filter (fun g => decide (I.Fits S a g))) with
      | none =>
        simp only [Chosen, hg]
        refine ⟨hamin, ?_⟩
        intro g hgp hfit
        have hmem : g ∈ S.pool.filter (fun g => decide (I.Fits S a g)) := by
          simp [hgp, hfit]
        rw [(pickMin_eq_none _ _).mp hg] at hmem
        simp at hmem
      | some g =>
        simp only [Chosen, hg]
        obtain ⟨hgm, hbest⟩ := pickMin_spec _ hg
        have hgood : g ∈ S.pool ∧ I.Fits S a g := by simpa using hgm
        refine ⟨hamin, hgood.1, hgood.2, ?_⟩
        intro h hhp hfit
        have := hbest h (by simp [hhp, hfit])
        linarith

variable [DecidableEq A] [DecidableEq G]

def give (_I : Instance A G) (S : State A G) (a : A) (g : G) : State A G :=
  ⟨Function.update S.bundle a (S.bundle a ++ [g]), S.pool.erase g, S.active⟩

def retire (_I : Instance A G) (S : State A G) (a : A) : State A G :=
  ⟨S.bundle, S.pool, S.active.erase a⟩

def execute (S : State A G) : Action A G → State A G
  | .stop => S
  | .retire a => I.retire S a
  | .give a g => I.give S a g

/-- Fuel is a proved bound, not an assumption on termination. -/
def run (I : Instance A G) : ℕ → State A G → State A G
  | 0, S => S
  | t + 1, S => match I.choose S with
    | .stop => S
    | .retire a => I.run t (I.retire S a)
    | .give a g => I.run t (I.give S a g)

omit [DecidableEq G] in
theorem rank_retire (S : State A G) {a : A} (ha : a ∈ S.active) :
    (I.retire S a).rank + 1 = S.rank := by
  have hlen := List.length_erase_of_mem ha
  simp only [retire, State.rank]
  have hpos : 0 < S.active.length := List.length_pos_of_mem ha
  omega

theorem rank_give (S : State A G) {a : A} {g : G} (hg : g ∈ S.pool) :
    (I.give S a g).rank + 1 = S.rank := by
  have hlen := List.length_erase_of_mem hg
  simp only [give, State.rank]
  have hpos : 0 < S.pool.length := List.length_pos_of_mem hg
  omega

theorem run_terminal {t : ℕ} {S : State A G} (ht : S.rank ≤ t) :
    (I.run t S).Terminal := by
  induction t generalizing S with
  | zero =>
    have hp : S.pool.length = 0 := by unfold State.rank at ht; omega
    exact Or.inl (List.length_eq_zero_iff.mp hp)
  | succ t ih =>
    have hspec := I.choose_spec S
    cases hc : I.choose S with
    | stop => simpa [run, hc] using (show S.Terminal by simpa [hc, Chosen] using hspec)
    | retire a =>
      have ha : a ∈ S.active := (show I.Chosen S (.retire a) by simpa [hc] using hspec).1.1
      have hr := I.rank_retire S ha
      simpa [run, hc] using ih (S := I.retire S a) (by omega)
    | give a g =>
      have hg : g ∈ S.pool := (show I.Chosen S (.give a g) by simpa [hc] using hspec).2.1
      have hr := I.rank_give (a := a) S hg
      simpa [run, hc] using ih (S := I.give S a g) (by omega)

theorem run_preserves {P : State A G → Prop}
    (hretire : ∀ S a, P S → I.Chosen S (.retire a) → P (I.retire S a))
    (hgive : ∀ S a g, P S → I.Chosen S (.give a g) → P (I.give S a g))
    (t : ℕ) {S : State A G} (hS : P S) : P (I.run t S) := by
  induction t generalizing S with
  | zero => exact hS
  | succ t ih =>
    have hspec := I.choose_spec S
    cases hc : I.choose S with
    | stop => simpa [run, hc] using hS
    | retire a =>
      simpa [run, hc] using ih (hretire S a hS (by simpa [hc] using hspec))
    | give a g =>
      simpa [run, hc] using ih (hgive S a g hS (by simpa [hc] using hspec))

end Instance

def initial (agents : List A) (goods : List G) : State A G := ⟨fun _ => [], goods, agents⟩

/-- Algorithm 2, for `n` agents and `m` goods. -/
def densestGreedy {n m : ℕ} (I : Instance (Fin n) (Fin m)) : State (Fin n) (Fin m) :=
  I.run (m + n) (initial (List.finRange n) (List.finRange m))

theorem densestGreedy_terminal {n m : ℕ} (I : Instance (Fin n) (Fin m)) :
    (densestGreedy I).Terminal := by
  apply I.run_terminal
  simp [initial, State.rank]

end FairAllocation
