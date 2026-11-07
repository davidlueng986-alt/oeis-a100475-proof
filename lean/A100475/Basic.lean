/-
OEIS A100475: no positive starting value leads to a loop.

Original Lean code in this file is released under the MIT License (see the repository LICENSE).
The definitions `reverseDigits`, `aStartAt` and `IsUltimatelyPeriodic` restate, unchanged, the
definitions of `FormalConjectures/OEIS/100475.lean` in google-deepmind/formal-conjectures
(git blob a2a7c03062ae8dd107182c0d11662134bdf7924f), Copyright 2026 The Formal Conjectures
Authors, Apache License 2.0. They are restated so that the statement proved here is literally the
negation of the upstream `OeisA100475.conjecture`.
-/
import Mathlib

namespace A100475

open Nat Real

/-! ## Definitions (as in formal-conjectures) -/

/-- Reverses the base 10 digits of a natural number. -/
def reverseDigits (k : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 k |>.reverse)

/-- The sequence started at `x`: `a(t+1) = reverseDigits (p_{a(t)})`, with `p_1 = 2`. -/
noncomputable def aStartAt (x : ℕ) : ℕ → ℕ
  | 0 => x
  | n + 1 =>
    let k := aStartAt x n
    if k = 0 then 0
    else reverseDigits (Nat.nth Nat.Prime (k - 1))

/-- Ultimately periodic sequences. -/
def IsUltimatelyPeriodic (f : ℕ → ℕ) : Prop :=
  ∃ N P, P > 0 ∧ ∀ n, n ≥ N → f (n + P) = f n

lemma aStartAt_succ (x n : ℕ) :
    aStartAt x (n + 1) =
      if aStartAt x n = 0 then 0 else reverseDigits (Nat.nth Nat.Prime (aStartAt x n - 1)) :=
  rfl

/-! ## Digit reversal keeps the number of digits when the last digit is nonzero -/

lemma digits_reverseDigits {m : ℕ} (hm : m % 10 ≠ 0) :
    Nat.digits 10 (reverseDigits m) = (Nat.digits 10 m).reverse := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  unfold reverseDigits
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro l hl
    exact Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp hl)
  · intro h
    simp [Nat.digits_def' (by norm_num : 1 < 10) (Nat.pos_of_ne_zero hm0),
      hm]

lemma length_digits_reverseDigits {m : ℕ} (hm : m % 10 ≠ 0) :
    (Nat.digits 10 (reverseDigits m)).length = (Nat.digits 10 m).length := by
  rw [digits_reverseDigits hm, List.length_reverse]

/-- If `m` has at least `e + 1` digits and does not end in `0`, its reversal is `≥ 10^e`. -/
lemma pow_le_reverseDigits {m e : ℕ} (hm : m % 10 ≠ 0) (he : 10 ^ e ≤ m) :
    10 ^ e ≤ reverseDigits m := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hlt : m < 10 ^ (Nat.digits 10 m).length := Nat.lt_base_pow_length_digits (by norm_num)
  have hlen : e + 1 ≤ (Nat.digits 10 m).length := by
    by_contra h
    push Not at h
    have : 10 ^ (Nat.digits 10 m).length ≤ 10 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hr0 : reverseDigits m ≠ 0 := by
    intro h
    have := length_digits_reverseDigits hm
    rw [h, Nat.digits_zero, List.length_nil] at this
    exact hm0 (Nat.digits_eq_nil_iff_eq_zero.mp (List.length_eq_zero_iff.mp this.symm))
  have key := Nat.base_pow_length_digits_le 10 (reverseDigits m) (by norm_num) hr0
  rw [length_digits_reverseDigits hm] at key
  have : 10 ^ (e + 1) ≤ 10 * reverseDigits m :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hlen) key
  rw [pow_succ] at this
  omega

lemma Prime.mod_ten_ne_zero {p : ℕ} (hp : p.Prime) : p % 10 ≠ 0 := by
  intro h
  have h2 : 2 ∣ p := by omega
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
  omega

/-! ## Prime counting: `π(10^d) < 10^(d-1)` for every `d ≥ 5`

Below, `Nat.count Nat.Prime n` is the number of primes `< n`. The cases `d = 5, 6, 7` are
computed; every `d ≥ 8` follows from the case `d - 1` and Chebyshev's bound
`θ(x) ≤ x log 4` (`Chebyshev.theta_le_log4_mul_x` in Mathlib). No bound of Rosser type is used. -/

lemma count_prime_1e5 : Nat.count Nat.Prime (10 ^ 5) < 10 ^ 4 := by native_decide
lemma count_prime_1e6 : Nat.count Nat.Prime (10 ^ 6) < 10 ^ 5 := by native_decide
lemma count_prime_1e7 : Nat.count Nat.Prime (10 ^ 7) < 10 ^ 6 := by native_decide

/-- `(π(x) - π(y)) · log y ≤ θ(x)` for `1 ≤ y ≤ x`, with `π` counting primes `< ·`. -/
lemma count_sub_mul_log_le_theta {y x : ℕ} (hy : 1 ≤ y) (hyx : y ≤ x) :
    ((Nat.count Nat.Prime x - Nat.count Nat.Prime y : ℕ) : ℝ) * Real.log y ≤
      Chebyshev.theta x := by
  set S : Finset ℕ := (Finset.Ico y x).filter Nat.Prime with hS
  have hcard : ((Finset.Ico y x).filter Nat.Prime).card = Nat.count Nat.Prime x - Nat.count Nat.Prime y := by
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    have hsplit : Finset.range x = Finset.range y ∪ Finset.Ico y x := by
      ext n; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.range y) (Finset.Ico y x) := by
      rw [Finset.disjoint_left]; intro n h1 h2
      simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisj), Nat.add_sub_cancel_left]
  have hsub : S ⊆ (Finset.Ioc 0 ⌊(x : ℝ)⌋₊).filter Nat.Prime := by
    intro p hp
    simp only [hS, Finset.mem_filter, Finset.mem_Ico] at hp
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.floor_natCast]
    exact ⟨⟨hp.2.pos, hp.1.2.le⟩, hp.2⟩
  have hlog : ∀ p ∈ S, Real.log y ≤ Real.log p := by
    intro p hp
    simp only [hS, Finset.mem_filter, Finset.mem_Ico] at hp
    exact Real.log_le_log (by exact_mod_cast hy) (by exact_mod_cast hp.1.1)
  calc ((Nat.count Nat.Prime x - Nat.count Nat.Prime y : ℕ) : ℝ) * Real.log y
      = ∑ _p ∈ S, Real.log y := by rw [hS, ← hcard, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ S, Real.log p := Finset.sum_le_sum hlog
    _ ≤ ∑ p ∈ (Finset.Ioc 0 ⌊(x : ℝ)⌋₊).filter Nat.Prime, Real.log p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro p hp _
        simp only [Finset.mem_filter] at hp
        exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
    _ = Chebyshev.theta x := rfl

lemma log_two_mul_33_lt : 33 * Real.log 2 < 10 * Real.log 10 := by
  have h : ((2 : ℝ) ^ 33) < (10 : ℝ) ^ 10 := by norm_num
  have := Real.log_lt_log (by positivity) h
  rwa [Real.log_pow, Real.log_pow] at this

/-- Inductive step: `π(10^(k+1)) < 10^k` implies `π(10^(k+2)) < 10^(k+1)` once `k ≥ 6`. -/
lemma count_prime_step {k : ℕ} (hk : 6 ≤ k) (ih : Nat.count Nat.Prime (10 ^ (k + 1)) < 10 ^ k) :
    Nat.count Nat.Prime (10 ^ (k + 2)) < 10 ^ (k + 1) := by
  set cy := Nat.count Nat.Prime (10 ^ (k + 1))
  set cx := Nat.count Nat.Prime (10 ^ (k + 2))
  have hmono : cy ≤ cx := Nat.count_monotone _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h1 := count_sub_mul_log_le_theta (y := 10 ^ (k + 1)) (x := 10 ^ (k + 2))
    (Nat.one_le_pow _ _ (by norm_num)) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 := Chebyshev.theta_le_log4_mul_x (x := ((10 ^ (k + 2) : ℕ) : ℝ)) (by positivity)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlogy : Real.log ((10 ^ (k + 1) : ℕ) : ℝ) = (k + 1 : ℝ) * Real.log 10 := by
    push_cast; rw [Real.log_pow]; push_cast; ring
  rw [hlogy] at h1
  rw [hlog4] at h2
  have hl10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h33 := log_two_mul_33_lt
  set D : ℝ := ((cx - cy : ℕ) : ℝ)
  have hD : 0 ≤ D := by positivity
  set X : ℝ := ((10 ^ (k + 2) : ℕ) : ℝ)
  have hX : 0 < X := by positivity
  -- D (k+1) log 10 ≤ 2 log 2 · X, and 66 log 2 < 20 log 10, hence 33 D (k+1) < 20 X.
  have key : 33 * D * (k + 1) * Real.log 10 < 20 * X * Real.log 10 := by
    have : D * ((k + 1 : ℝ) * Real.log 10) ≤ 2 * Real.log 2 * X := le_trans h1 h2
    nlinarith
  have key' : 33 * D * (k + 1) < 20 * X := lt_of_mul_lt_mul_right key hl10.le
  have keyN : 33 * (cx - cy) * (k + 1) < 20 * 10 ^ (k + 2) := by
    have : ((33 * (cx - cy) * (k + 1) : ℕ) : ℝ) < ((20 * 10 ^ (k + 2) : ℕ) : ℝ) := by
      push_cast at key' ⊢
      simpa [D, X, Nat.cast_sub hmono] using key'
    exact_mod_cast this
  have hM : 10 ^ (k + 2) = 100 * 10 ^ k := by ring
  have hM1 : 10 ^ (k + 1) = 10 * 10 ^ k := by ring
  rw [hM] at keyN
  rw [hM1]
  have h7 : 33 * (cx - cy) * 7 ≤ 33 * (cx - cy) * (k + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- `π(10^d) < 10^(d-1)` for every `d ≥ 5`. -/
theorem count_prime_pow_ten_lt (d : ℕ) (hd : 5 ≤ d) :
    Nat.count Nat.Prime (10 ^ d) < 10 ^ (d - 1) := by
  induction d, hd using Nat.le_induction with
  | base => exact count_prime_1e5
  | succ d hd ih =>
    rcases (show d = 5 ∨ d = 6 ∨ 7 ≤ d by omega) with rfl | rfl | h7
    · exact count_prime_1e6
    · exact count_prime_1e7
    · obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
      have := count_prime_step (k := k) (by omega) (by simpa using ih)
      simpa using this

/-! ## The tail: above `10^4` the map strictly increases -/

/-- For `n ≥ 10^4`: `p_n ≥ 10^d`, where `n` has `d` digits; hence `reverseDigits p_n > n`. -/
theorem lt_step_of_ge {n : ℕ} (hn : 10 ^ 4 ≤ n) :
    n < reverseDigits (Nat.nth Nat.Prime (n - 1)) := by
  set d := (Nat.digits 10 n).length
  have hn0 : n ≠ 0 := by omega
  have hlt : n < 10 ^ d := Nat.lt_base_pow_length_digits (by norm_num)
  have hle : 10 ^ d ≤ 10 * n := Nat.base_pow_length_digits_le 10 n (by norm_num) hn0
  have hd5 : 5 ≤ d := by
    by_contra h
    push Not at h
    have : 10 ^ d ≤ 10 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hlow : 10 ^ (d - 1) ≤ n := by
    obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    rw [he, pow_succ] at hle
    rw [he]; simp only [Nat.add_sub_cancel]; omega
  set p := Nat.nth Nat.Prime (n - 1)
  have hp : p.Prime := Nat.prime_nth_prime _
  have hcount : Nat.count Nat.Prime p = n - 1 :=
    Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime _
  have hpbig : 10 ^ d ≤ p := by
    by_contra h
    push Not at h
    have h1 : Nat.count Nat.Prime (p + 1) ≤ Nat.count Nat.Prime (10 ^ d) :=
      Nat.count_monotone _ h
    rw [Nat.count_succ, hcount, ite_eq_left_of_eq_true _ _ (eq_true hp)] at h1
    have := count_prime_pow_ten_lt d hd5
    omega
  have := pow_le_reverseDigits (Prime.mod_ten_ne_zero hp) hpbig
  omega

/-! ## The finite part: every start `1 ≤ n < 10^4` reaches `≥ 10^4` -/

/-- The first 9999 primes, `p_1, …, p_9999` (`p_9999 = 104723`). -/
def primeTable : Array ℕ := ((List.range 104724).filter Nat.Prime).toArray

def tab (k : ℕ) : ℕ := primeTable.getD k 0

/-- Exact check of the table: it starts at 2, entries are prime, consecutive entries increase,
and there is exactly one prime in each half-open gap `[tab k, tab (k+1))`. -/
lemma tab_check :
    tab 0 = 2 ∧ (∀ k < 9999, (tab k).Prime) ∧
      ∀ k < 9998, tab k < tab (k + 1) ∧
        Nat.count (fun j => Nat.Prime (tab k + j)) (tab (k + 1) - tab k) = 1 := by
  native_decide

lemma count_tab : ∀ k < 9999, Nat.count Nat.Prime (tab k) = k := by
  obtain ⟨h0, -, hstep⟩ := tab_check
  intro k hk
  induction k with
  | zero => rw [h0]; decide
  | succ k ih =>
    obtain ⟨hlt, hc⟩ := hstep k (by omega)
    have := Nat.count_add (p := Nat.Prime) (tab k) (tab (k + 1) - tab k)
    rw [Nat.add_sub_cancel' hlt.le, hc, ih (by omega)] at this
    exact this

lemma nth_prime_eq_tab {k : ℕ} (hk : k < 9999) : Nat.nth Nat.Prime k = tab k := by
  have h := Nat.nth_count (p := Nat.Prime) (tab_check.2.1 k hk)
  rwa [count_tab k hk] at h

/-- Computable copy of the map on `1 ≤ k ≤ 9999`. -/
def stepC (k : ℕ) : ℕ := reverseDigits (tab (k - 1))

/-- `esc f k = true` certifies that iterating from `k` reaches `≥ 10^4` within `f` steps. -/
def esc : ℕ → ℕ → Bool
  | 0, k => decide (10 ^ 4 ≤ k)
  | f + 1, k => if 10 ^ 4 ≤ k then true else if k = 0 then false else esc f (stepC k)

lemma esc_all : ∀ k < 10 ^ 4, 0 < k → esc 10 k = true := by native_decide

lemma reaches_of_esc :
    ∀ f k, esc f k = true → ∀ x t, aStartAt x t = k → ∃ t', 10 ^ 4 ≤ aStartAt x t' := by
  intro f
  induction f with
  | zero =>
    intro k hk x t ht
    exact ⟨t, by simpa [esc, ht] using hk⟩
  | succ f ih =>
    intro k hk x t ht
    by_cases hbig : 10 ^ 4 ≤ k
    · exact ⟨t, ht ▸ hbig⟩
    · have hk0 : k ≠ 0 := by
        intro h0; subst h0; simp [esc] at hk
      have hk' : esc f (stepC k) = true := by
        simp only [esc] at hk
        rwa [ite_eq_right_of_eq_false _ _ (eq_false hbig), ite_eq_right_of_eq_false _ _ (eq_false hk0)] at hk
      apply ih _ hk' x (t + 1)
      rw [aStartAt_succ, ht, ite_eq_right_of_eq_false _ _ (eq_false hk0), stepC, nth_prime_eq_tab (by omega)]

/-! ## Main theorems -/

lemma tail_invariant {x t : ℕ} (h : 10 ^ 4 ≤ aStartAt x t) :
    aStartAt x t < aStartAt x (t + 1) := by
  rw [aStartAt_succ, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  exact lt_step_of_ge h

/-- Every positive start eventually reaches the region `≥ 10^4`. -/
theorem exists_large (x : ℕ) (hx : 0 < x) : ∃ t, 10 ^ 4 ≤ aStartAt x t := by
  by_cases h : 10 ^ 4 ≤ x
  · exact ⟨0, h⟩
  · exact reaches_of_esc 10 x (esc_all x (by omega) hx) x 0 rfl

/-- **Theorem.** For every positive start, the orbit is eventually strictly increasing. -/
theorem eventually_strictly_increasing (x : ℕ) (hx : 0 < x) :
    ∃ T, ∀ t, T ≤ t → 10 ^ 4 ≤ aStartAt x t ∧ aStartAt x t < aStartAt x (t + 1) := by
  obtain ⟨T, hT⟩ := exists_large x hx
  refine ⟨T, fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => exact ⟨hT, tail_invariant hT⟩
  | succ t _ ih =>
    have h1 : 10 ^ 4 ≤ aStartAt x (t + 1) := le_trans ih.1 ih.2.le
    exact ⟨h1, tail_invariant h1⟩

lemma add_le_of_increasing {x T : ℕ}
    (hT : ∀ t, T ≤ t → 10 ^ 4 ≤ aStartAt x t ∧ aStartAt x t < aStartAt x (t + 1))
    (n : ℕ) (hn : T ≤ n) (j : ℕ) : aStartAt x n + j ≤ aStartAt x (n + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have := (hT (n + j) (by omega)).2
    rw [show n + (j + 1) = n + j + 1 by omega]
    omega

/-- **Theorem.** No positive start (including `1`) gives an ultimately periodic orbit. -/
theorem not_ultimatelyPeriodic (x : ℕ) (hx : 0 < x) : ¬ IsUltimatelyPeriodic (aStartAt x) := by
  rintro ⟨N, P, hP, hper⟩
  obtain ⟨T, hT⟩ := eventually_strictly_increasing x hx
  have h1 := hper (max N T) (le_max_left _ _)
  have h2 := add_le_of_increasing hT (max N T) (le_max_right _ _) P
  omega

/-- **Answer to the OEIS A100475 question:** the negation of `OeisA100475.conjecture`
from formal-conjectures. -/
theorem answer : ¬ ∃ x : ℕ, 0 < x ∧ x ≠ 1 ∧ IsUltimatelyPeriodic (aStartAt x) := by
  rintro ⟨x, hx, -, hper⟩
  exact not_ultimatelyPeriodic x hx hper

/-- Orbits of positive starts tend to infinity. -/
theorem tendsto_atTop (x : ℕ) (hx : 0 < x) :
    Filter.Tendsto (aStartAt x) Filter.atTop Filter.atTop := by
  obtain ⟨T, hT⟩ := eventually_strictly_increasing x hx
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨T + b, fun t ht => ?_⟩
  have := add_le_of_increasing hT T le_rfl (t - T)
  rw [Nat.add_sub_cancel' (by omega)] at this
  omega

end A100475
