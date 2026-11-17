import FairAllocation.Basic

set_option autoImplicit false

/-!
# Fractional prefixes (Appendix C, Definition 3)

`prefixValue v s X t` is the value of the first `t` units of size of `X`,
in allocation order. Thresholds are rational, as are all item sizes and
all thresholds used in the proof. The endpoint good may be fractional.
-/

namespace FairAllocation

variable {G : Type*}

def prefixValue (v s : G → ℚ) : List G → ℚ → ℚ
  | [], _ => 0
  | g :: X, t => min (max t 0) (s g) * (v g / s g) + prefixValue v s X (t - s g)

@[simp] theorem prefixValue_nil (v s : G → ℚ) (t : ℚ) :
    prefixValue v s [] t = 0 := rfl

@[simp] theorem prefixValue_cons (v s : G → ℚ) (g : G) (X : List G) (t : ℚ) :
    prefixValue v s (g :: X) t =
      min (max t 0) (s g) * (v g / s g) + prefixValue v s X (t - s g) := rfl

theorem prefixValue_nonneg {v s : G → ℚ} (hs : ∀ g, 0 < s g)
    {X : List G} (hv : ∀ g ∈ X, 0 ≤ v g) (t : ℚ) :
    0 ≤ prefixValue v s X t := by
  induction X generalizing t with
  | nil => simp
  | cons g X ih =>
    simp only [prefixValue_cons]
    apply add_nonneg
    · exact mul_nonneg (le_min (le_max_right _ _) (hs g).le)
        (div_nonneg (hv g (by simp)) (hs g).le)
    · exact ih (fun x hx => hv x (by simp [hx])) _

theorem prefixValue_of_nonpos {v s : G → ℚ} (hs : ∀ g, 0 < s g)
    (X : List G) {t : ℚ} (ht : t ≤ 0) : prefixValue v s X t = 0 := by
  induction X generalizing t with
  | nil => rfl
  | cons g X ih =>
    rw [prefixValue_cons, max_eq_right ht, min_eq_left (hs g).le, zero_mul,
      ih (by linarith [hs g]), zero_add]

@[simp] theorem prefixValue_zero {v s : G → ℚ} (hs : ∀ g, 0 < s g)
    (X : List G) : prefixValue v s X 0 = 0 :=
  prefixValue_of_nonpos hs X le_rfl

theorem prefixValue_mono {v s : G → ℚ} (hs : ∀ g, 0 < s g)
    {X : List G} (hv : ∀ g ∈ X, 0 ≤ v g) {t u : ℚ} (h : t ≤ u) :
    prefixValue v s X t ≤ prefixValue v s X u := by
  induction X generalizing t u with
  | nil => simp
  | cons g X ih =>
    simp only [prefixValue_cons]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right (min_le_min_right _ (max_le_max_right _ h))
        (div_nonneg (hv g (by simp)) (hs g).le)
    · exact ih (fun x hx => hv x (by simp [hx])) (sub_le_sub_right h _)

theorem prefixValue_append (v s : G → ℚ) (X Y : List G) (t : ℚ) :
    prefixValue v s (X ++ Y) t =
      prefixValue v s X t + prefixValue v s Y (t - total s X) := by
  induction X generalizing t with
  | nil => simp
  | cons g X ih =>
    simp only [List.cons_append, prefixValue_cons, total_cons, ih]
    have he : t - s g - total s X = t - (s g + total s X) := by ring
    rw [he]
    ring

theorem prefixValue_full {v s : G → ℚ} (hs : ∀ g, 0 < s g)
    (X : List G) {t : ℚ} (ht : total s X ≤ t) : prefixValue v s X t = total v X := by
  induction X generalizing t with
  | nil => simp
  | cons g X ih =>
    have hn : 0 ≤ total s X := total_nonneg (fun x _ => (hs x).le)
    simp only [total_cons] at ht ⊢
    have hg : s g ≤ t := by linarith
    have h0 : 0 ≤ t := (hs g).le.trans hg
    rw [prefixValue_cons, max_eq_left h0, min_eq_right hg, ih (by linarith)]
    have hmul : s g * (v g / s g) = v g := by
      rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt (hs g))]
    rw [hmul]

theorem prefixValue_le_total {v s : G → ℚ} (hs : ∀ g, 0 < s g)
    {X : List G} (hv : ∀ g ∈ X, 0 ≤ v g) (t : ℚ) :
    prefixValue v s X t ≤ total v X := by
  calc
    prefixValue v s X t ≤ prefixValue v s X (max t (total s X)) :=
      prefixValue_mono hs hv (le_max_left _ _)
    _ = total v X := prefixValue_full hs X (le_max_right _ _)

theorem prefixValue_append_of_le {v s : G → ℚ} (hs : ∀ g, 0 < s g)
    (X Y : List G) {t : ℚ} (ht : t ≤ total s X) :
    prefixValue v s (X ++ Y) t = prefixValue v s X t := by
  rw [prefixValue_append, prefixValue_of_nonpos hs Y (sub_nonpos.mpr ht), add_zero]

theorem prefixValue_size {s : G → ℚ} (hs : ∀ g, 0 < s g)
    (X : List G) (t : ℚ) :
    prefixValue s s X t = min (max t 0) (total s X) := by
  induction X generalizing t with
  | nil => simp
  | cons g X ih =>
    simp only [prefixValue_cons, div_self (ne_of_gt (hs g)), mul_one, ih, total_cons]
    have hn : 0 ≤ total s X := total_nonneg (fun x _ => (hs x).le)
    by_cases ht : t ≤ 0
    · have hts : t - s g ≤ 0 := by linarith [hs g]
      simp [max_eq_right ht, max_eq_right hts, min_eq_left (hs g).le,
        min_eq_left hn, min_eq_left (show 0 ≤ s g + total s X by linarith [hs g])]
    · have ht0 : 0 ≤ t := le_of_lt (lt_of_not_ge ht)
      rw [max_eq_left ht0]
      by_cases hg : s g ≤ t
      · rw [min_eq_right hg, max_eq_left (sub_nonneg.mpr hg)]
        by_cases hsum : t ≤ s g + total s X
        · rw [min_eq_left hsum, min_eq_left (show t - s g ≤ total s X by linarith)]
          ring
        · rw [min_eq_right (le_of_not_ge hsum),
            min_eq_right (show total s X ≤ t - s g by linarith)]
      · have htg : t ≤ s g := le_of_lt (lt_of_not_ge hg)
        rw [min_eq_left htg, max_eq_right (sub_nonpos.mpr htg), min_eq_left hn,
          min_eq_left (show t ≤ s g + total s X by linarith), add_zero]

theorem prefixValue_sub_mul (v s : G → ℚ) (d : ℚ) (X : List G) (t : ℚ) :
    prefixValue (fun g => v g - d * s g) s X t =
      prefixValue v s X t - d * prefixValue s s X t := by
  induction X generalizing t with
  | nil => simp
  | cons g X ih =>
    simp only [prefixValue_cons, ih, sub_div, mul_div_assoc]
    ring

/-- A fractional segment of goods of density at least `d` has value at least
its size multiplied by `d`. -/
theorem prefixValue_increment {v s : G → ℚ} (hs : ∀ g, 0 < s g)
    {X : List G} {d t u : ℚ} (hd : ∀ g ∈ X, d * s g ≤ v g)
    (ht : 0 ≤ t) (htu : t ≤ u) (hu : u ≤ total s X) :
    d * (u - t) ≤ prefixValue v s X u - prefixValue v s X t := by
  have hmono := prefixValue_mono (v := fun g => v g - d * s g) hs
    (fun g hg => sub_nonneg.mpr (hd g hg)) htu
  rw [prefixValue_sub_mul, prefixValue_sub_mul, prefixValue_size hs,
    prefixValue_size hs, max_eq_left ht, max_eq_left (ht.trans htu),
    min_eq_left (htu.trans hu), min_eq_left hu] at hmono
  linarith

theorem density_mul_size {v s : G → ℚ} (hs : ∀ g, 0 < s g) (g : G) :
    (v g / s g) * s g = v g := div_mul_cancel₀ _ (ne_of_gt (hs g))

theorem le_density_iff {v s : G → ℚ} (hs : ∀ g, 0 < s g) {d : ℚ} {g : G} :
    d ≤ v g / s g ↔ d * s g ≤ v g := le_div_iff₀ (hs g)

theorem density_le_iff {v s : G → ℚ} (hs : ∀ g, 0 < s g) {d : ℚ} {g : G} :
    v g / s g ≤ d ↔ v g ≤ d * s g := div_le_iff₀ (hs g)

end FairAllocation
