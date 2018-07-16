import data.sigma.basic

namespace sigma
universes u v
variables {α : Type u} {β : α → Type v}

theorem eq_fst {s₁ s₂ : sigma β} : s₁ = s₂ → s₁.1 = s₂.1 :=
by cases s₁; cases s₂; cc

theorem eq_snd {s₁ s₂ : sigma β} : s₁ = s₂ → s₁.2 == s₂.2 :=
by cases s₁; cases s₂; cc

section
variables {α₁ : Type u} {α₂ : Type u} {β₁ : α₁ → Type v} {β₂ : α₂ → Type v}

/-- A fst-stable function preserves equality on `fst`s. -/
def fst_stable (f : sigma β₁ → sigma β₂) : Prop :=
∀ ⦃s t : sigma β₁⦄, s.1 = t.1 → (f s).1 = (f t).1

/-- A fst-injective function: equal result `fst`s imply equal argument `fst`s. -/
def fst_injective (f : sigma β₁ → sigma β₂) : Prop :=
∀ ⦃s t : sigma β₁⦄, (f s).1 = (f t).1 → s.1 = t.1

end

section
variables {β₁ β₂ : α → Type v}

def map_snd (f : ∀ (a : α), β₁ a → β₂ a) : sigma β₁ → sigma β₂ :=
have sigma β₁ → sigma (id β₂) := map id f, by exact this

theorem map_snd_fst_iff {s₁ s₂ : sigma β₁} (f : ∀ (a : α), β₁ a → β₂ a) :
  (map_snd f s₁).1 = (map_snd f s₂).1 ↔ s₁.1 = s₂.1 :=
by cases s₁; cases s₂; exact iff.rfl

theorem fst_stable_snd (f : ∀ (a : α), β₁ a → β₂ a) : fst_stable (map_snd f) :=
λ _ _, (map_snd_fst_iff f).mpr

theorem fst_injective_snd (f : ∀ (a : α), β₁ a → β₂ a) : fst_injective (map_snd f) :=
λ _ _, (map_snd_fst_iff f).mp

end

/-- A relation `R` on `fst` values lifted to the `sigma`. -/
def on_fst (R : α → α → Prop) (s₁ s₂ : sigma β) : Prop :=
R s₁.1 s₂.1

variables {R : α → α → Prop} {s₁ s₂ : sigma β}

@[simp] theorem on_fst_eq : on_fst R s₁ s₂ = R s₁.1 s₂.1 :=
rfl

instance [d : decidable_rel R] : decidable_rel (@on_fst α β R)
| s₁ s₂ := @d s₁.1 s₂.1

theorem on_fst.refl (h : reflexive R) : reflexive (@on_fst α β R) :=
λ s, h s.1

theorem on_fst.symm (h : symmetric R) : symmetric (@on_fst α β R) :=
λ s₁ s₂ (p : R s₁.1 s₂.1), h p

theorem on_fst.trans (h : transitive R) : transitive (@on_fst α β R) :=
λ s₁ s₂ s₃ (p : R s₁.1 s₂.1) (q : R s₂.1 s₃.1), h p q

end sigma
