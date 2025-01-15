import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n nmax
  have hs' := hs n (le_of_max_le_left nmax)
  have ht' := ht n (le_of_max_le_right nmax)
  rw [abs_lt] at *
  constructor <;> linarith

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε hε
  dsimp
  have cs := cs (ε/|c|) (by field_simp[h])
  rcases cs with ⟨N,cs⟩
  use N
  intro n nN
  have cs := cs n nN
  rw [abs_lt] at *
  field_simp[h] at cs
  rcases le_or_gt 0 c with cp | cn
  · rw[abs_of_nonneg cp] at *
    constructor
    · have h' := (mul_lt_mul_iff_of_pos_right acpos).mpr cs.1
      rw [div_mul_cancel₀ _ h] at h'
      linarith
    · have h' := (mul_lt_mul_iff_of_pos_right acpos).mpr cs.2
      rw [div_mul_cancel₀ _ h] at h'
      linarith
  · rw[abs_of_neg cn] at *
    have hminc0 : -c ≠ 0 := neg_ne_zero.mpr h
    constructor
    · have h' := (mul_lt_mul_iff_of_pos_right acpos).mpr cs.2
      rw [div_mul_cancel₀ _ hminc0] at h'
      linarith
    · have h' := (mul_lt_mul_iff_of_pos_right acpos).mpr cs.1
      rw [div_mul_cancel₀ _ hminc0] at h'
      linarith


theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n Nn
  have h' := h n Nn
  rw [<-sub_add_cancel (s n) a]
  apply lt_of_le_of_lt
  apply abs_add_le (s n - a) a
  linarith


theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₁ N₀--Nat.sqrt (N₁*N₀)
  intro n nNN
  have h₀' := h₀ n (le_of_max_le_right nNN)
  have h₁' := h₁ n (le_of_max_le_left nNN)
  norm_num at *
  rw [abs_mul,<-@mul_div_cancel₀ _ _ B ε (by linarith)]
  apply mul_lt_mul' (le_of_lt h₀') h₁' (abs_nonneg _) Bpos


theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := abs_sub_pos.mpr abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa N (le_max_left _ _)
  have absb : |s N - b| < ε := hNb N (le_max_right _ _)
  have : |a - b| < |a - b| :=
    calc
      |a - b| = |(s N - b) - (s N - a)| := by congr 1; ring
      _ ≤ |s N - b| + |s N - a| := by apply abs_sub
      _ < ε + ε := by exact add_lt_add absb absa
      _ = |a - b| := by unfold ε; rw [<-mul_two]; apply div_mul_cancel_of_invertible
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
