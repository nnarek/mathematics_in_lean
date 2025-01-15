import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f :=
by
  intro flb
  unfold FnHasLb at *
  unfold FnLb at *
  rcases flb with ⟨a,flb⟩
  rcases h a with ⟨x,hfxa⟩
  linarith [flb x]


example : ¬FnHasUb fun x ↦ x :=
by
  intro flb
  unfold FnHasUb at *
  unfold FnUb at *
  dsimp at flb
  rcases flb with ⟨a,flb⟩
  linarith [flb (a+1)]


#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  unfold Monotone at *
  apply lt_of_not_ge
  intro hf
  linarith [h hf]


example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro hm
  linarith [hm h]

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by intro x b hxb; unfold f; linarith
  have h' : f 1 ≤ f 0 := le_refl _
  linarith [@h f monof 1 0 h']

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro hx0
  linarith [h x hx0]

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x px
  apply h
  use x

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro he
  rcases he with ⟨x,px⟩
  apply h x px

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra hne
  apply h
  intro x
  by_contra
  apply hne
  use x

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro hpx
  rcases h with ⟨x,npx⟩
  apply npx
  apply hpx

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  by_contra
  apply h
  assumption

example (h : Q) : ¬¬Q := by
  intro nq
  apply nq h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  unfold FnHasUb at *
  unfold FnUb at *
  by_contra hf
  apply h
  use a
  intro x
  apply le_of_not_gt
  intro _
  apply hf
  use x


example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  unfold Monotone at *
  push_neg at h
  assumption

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
