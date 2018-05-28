namespace sigma
universes u v
variables {α : Type u} {β : α → Type v}

def on_fst (R : α → α → Prop) (s₁ : sigma β) (s₂ : sigma β) : Prop :=
R s₁.1 s₂.1

theorem on_fst.refl {R : α → α → Prop} (h : reflexive R) : reflexive (@on_fst α β R) :=
λ s, h s.1

theorem on_fst.symm {R : α → α → Prop} (h : symmetric R) : symmetric (@on_fst α β R) :=
λ s₁ s₂ (p : R s₁.1 s₂.1), h p

theorem on_fst.trans {R : α → α → Prop} (h : transitive R) : transitive (@on_fst α β R) :=
λ s₁ s₂ s₃ (p : R s₁.1 s₂.1) (q : R s₂.1 s₃.1), h p q

end sigma
