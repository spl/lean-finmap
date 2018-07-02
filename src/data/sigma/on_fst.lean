namespace sigma
universes u v
variables {α : Type u} {β : α → Type v}

/-- A relation `R` on `fst` values lifted to the `sigma`. -/
def on_fst (R : α → α → Prop) (s₁ s₂ : sigma β) : Prop :=
R s₁.1 s₂.1

variables {R : α → α → Prop} {s₁ s₂ : sigma β}

@[simp] theorem on_fst_eq : on_fst R s₁ s₂ = R s₁.1 s₂.1 :=
rfl

theorem on_fst.refl (h : reflexive R) : reflexive (@on_fst α β R) :=
λ s, h s.1

theorem on_fst.symm (h : symmetric R) : symmetric (@on_fst α β R) :=
λ s₁ s₂ (p : R s₁.1 s₂.1), h p

theorem on_fst.trans (h : transitive R) : transitive (@on_fst α β R) :=
λ s₁ s₂ s₃ (p : R s₁.1 s₂.1) (q : R s₂.1 s₃.1), h p q

end sigma
