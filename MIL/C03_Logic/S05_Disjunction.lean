import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with xp | xn
  · rw [abs_of_nonneg xp]
  · rw [abs_of_neg xn]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with xp | xn
  · rw [abs_of_nonneg xp]
    linarith
  · rw [abs_of_neg xn]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x+y) with hp | hn
  · rw [abs_of_nonneg hp]
    linarith [le_abs_self x,le_abs_self y]
  · rw [abs_of_neg hn]
    linarith [neg_le_abs_self x,neg_le_abs_self y]

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor <;> intro h
  · rcases le_or_gt 0 y with yp | yn
    · left
      linarith [abs_of_nonneg yp]
    · right
      linarith [abs_of_neg yn]
  · rcases le_or_gt 0 y with yp | yn
    · rcases h with hxy | hxny <;> linarith [abs_of_nonneg yp]
    · rcases h with hxy | hxny <;> linarith [abs_of_neg yn]


theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor <;> intro h
  · rcases le_or_gt 0 x with xp | xn
    · constructor <;> linarith [abs_of_nonneg xp]
    · constructor <;> linarith [abs_of_neg xn]
  · rcases le_or_gt 0 x with xp | xn
    · linarith [abs_of_nonneg xp]
    · linarith [abs_of_neg xn]

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by rcases h with ⟨x,⟨y,h|h⟩⟩ <;> rw [h] <;> linarith [pow_two_nonneg x,pow_two_nonneg y]


example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  rcases lt_trichotomy x 1 with xlt | xeq | xgt
  · rcases lt_trichotomy x (-1) with xlt' | xeq' | xgt'
    · have hf: x ^ 2 > 1
      · rw [<-neg_pow_two]; apply one_lt_pow₀ <;> linarith
      linarith
    · exact sq_eq_one_iff.mp h
    · have hf: x ^ 2 < 1
      · rcases le_or_gt 0 x with xp | xn
        · apply pow_lt_one₀ xp xlt; linarith
        · rw [<-neg_pow_two]; apply pow_lt_one₀ <;> linarith
      linarith
  · left; exact xeq
  · have hf: x ^ 2 > 1 := by apply one_lt_pow₀ xgt; linarith
    linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h : x ^ 2 - y ^ 2 = 0 := sub_eq_zero_of_eq h
  have h' : (x+y)*(x-y) = x ^ 2 - y ^ 2 :=
    calc
      (x+y)*(x-y) = x*x + y*x - x*y - y*y := by ring
      _ = x*x - y*y := by ring
      _ = x ^ 2 - y ^ 2 := by repeat rw[<-pow_two]
  rw [<-h'] at h
  rcases mul_eq_zero.mp h with xpy | xmy
  · right; linarith
  · left; linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h : x ^ 2 - 1 = 0 := sub_eq_zero_of_eq h
  have h' : (x+1)*(x-1) = x ^ 2 - 1 :=
    calc
      (x+1)*(x-1) = x*x - 1 := by ring
      _ = x ^ 2 - 1 := by rw[<-pow_two]
  rw [<-h'] at h
  rcases mul_eq_zero.mp h with xpy | xmy
  · right; exact eq_neg_of_add_eq_zero_left xpy
  · left; exact eq_of_sub_eq_zero xmy

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h : x ^ 2 - y ^ 2 = 0 := sub_eq_zero_of_eq h
  have h' : (x+y)*(x-y) = x ^ 2 - y ^ 2 :=
    calc
      (x+y)*(x-y) = x*x - y*y := by ring
      _ = x ^ 2 - y ^ 2 := by repeat rw[<-pow_two]
  rw [<-h'] at h
  rcases mul_eq_zero.mp h with xpy | xmy
  · right; exact eq_neg_of_add_eq_zero_left xpy
  · left; exact eq_of_sub_eq_zero xmy

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases h' : P
    · right
      exact h h'
    · left
      exact h'
  · intro h p
    rcases h with hnp | q
    · exact False.elim (hnp p)
    · assumption
