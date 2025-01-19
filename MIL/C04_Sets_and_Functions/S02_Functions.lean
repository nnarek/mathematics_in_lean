import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x xs; simp at *; exact h xs
  · rintro h x ⟨a,as,hfax⟩; have h' := h as; simp[*] at *; assumption

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro _ ⟨_,_,fafx⟩
  rw [<-h fafx]
  assumption

example : f '' (f ⁻¹' u) ⊆ u := by
  intro _ ⟨_,_,_⟩
  simp[*] at *
  assumption

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro x xu
  rcases h x with ⟨a,fax⟩
  use a
  simp [*] at *

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro x ⟨a,as,fax⟩
  use a
  simp [*] at *
  exact h as

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x xfu
  exact h xfu

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  repeat
    rintro (h | h) <;> simp
    · left; assumption
    · right; assumption

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro x ⟨a,⟨_,_⟩,rfl⟩
  simp
  constructor <;> use a


example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro x ⟨⟨a,at',rfl⟩,⟨b,bt,fafb⟩⟩
  simp at *
  use a
  rw [h fafb] at bt
  trivial

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro x ⟨⟨a,_,rfl⟩,nfxfa⟩
  simp at *
  use a
  simp
  constructor
  · assumption
  · intro h; exact nfxfa a h rfl

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro x ⟨_,_⟩
  simp at *
  constructor <;> assumption

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext x
  constructor
  · rintro ⟨⟨a,_,rfl⟩,_⟩
    simp
    use a
  · rintro ⟨a,⟨_,_⟩,rfl⟩
    simp at *
    constructor
    · use a
    · assumption


example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro x ⟨a,⟨_,_⟩,rfl⟩
  simp at *
  constructor
  · use a
  · assumption

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨_,_⟩
  simp at *
  constructor
  · use x
  · assumption

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (_|_) <;> simp
  · left; use x
  · right; assumption

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext x
  constructor
  · rintro ⟨x,⟨_,⟨i,rfl⟩,_⟩,rfl⟩
    simp at *
    use i,x
  · rintro ⟨_,⟨i,rfl⟩,x,_,rfl⟩
    simp at *
    use x
    simp
    use i

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  rintro _ ⟨x,xai,rfl⟩ _ ⟨i,rfl⟩
  simp at *
  use x
  simp
  exact xai i


example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  rintro _ h
  simp at h
  rcases h i with ⟨a,_,rfl⟩
  simp
  use a
  simp
  intro i'
  rcases h i' with ⟨b,_,fbfa⟩
  apply injf at fbfa
  simp[*] at *
  assumption

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  constructor
  · rintro ⟨_,⟨i,rfl⟩,_⟩
    simp at *
    use i
  · rintro ⟨_,⟨i,rfl⟩,_⟩
    simp at *
    use i

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext _
  constructor
  repeat
  · rintro h i ⟨_,rfl⟩
    simp at *
    apply h


example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xp y yp sxeqsy
  simp at *
  calc
    x = (√x) ^ 2 := Eq.symm (sq_sqrt xp)
    _ = (√y) ^ 2 := by congr
    _ = y := sq_sqrt yp

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xp y yp x2eqy2
  simp at *
  calc
    x = √(x ^ 2) := Eq.symm (sqrt_sq xp)
    _ = √(y ^ 2) := by congr
    _ = y := sqrt_sq yp


example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext x
  constructor
  · rintro ⟨y,yp,syeqx⟩
    simp at *
    rw [←syeqx]
    exact sqrt_nonneg y
  · rintro xp
    simp at *
    use x ^ 2
    constructor
    · exact sq_nonneg x
    · exact sqrt_sq xp


example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext x
  constructor
  · intro ⟨y,y2eqx⟩
    simp at *
    rw [<-y2eqx]
    exact sq_nonneg y
  · intro xp
    simp at *
    use sqrt x
    apply sq_sqrt xp

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

#print inverse

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f :=
by
  constructor
  · intro injf x
    simp at *
    apply injf
    apply inverse_spec
    use x
  · intro h x y fxfy
    unfold LeftInverse at h
    rw [←h x,←h y,fxfy]


example : Surjective f ↔ RightInverse (inverse f) f :=
by
  constructor
  · unfold Surjective
    intro surjf x
    apply inverse_spec
    rcases surjf x with ⟨a,fax⟩
    use a
  · unfold RightInverse
    unfold LeftInverse
    intro h x
    use inverse f x
    apply h x

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction

  have h₂ : j ∈ S
  · unfold S at *
    simp at *
    assumption

  rw [h] at *
  contradiction

-- COMMENTS: TODO: improve this
end
