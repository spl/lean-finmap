import data.sigma.basic

namespace sigma
universes u v

section
variables {α : Type u} {β : α → Type v}

theorem eq_fst {s₁ s₂ : sigma β} : s₁ = s₂ → s₁.1 = s₂.1 :=
by cases s₁; cases s₂; cc

theorem eq_snd {s₁ s₂ : sigma β} : s₁ = s₂ → s₁.2 == s₂.2 :=
by cases s₁; cases s₂; cc

end

section
variables {α₁ α₂ : Type u} {β₁ : α₁ → Type v} {β₂ : α₂ → Type v}

/-- A function on `sigma`s that is functional on `fst`s (preserves equality from
argument to result). -/
def functional (f : sigma β₁ → sigma β₂) : Prop :=
∀ ⦃s t : sigma β₁⦄, s.1 = t.1 → (f s).1 = (f t).1

/-- A function on `sigma`s that is injective on `fst`s (preserves equality from
result to argument). -/
def injective (f : sigma β₁ → sigma β₂) : Prop :=
∀ ⦃s t : sigma β₁⦄, (f s).1 = (f t).1 → s.1 = t.1

end

/-- A function on `sigma`s bundled with its `fst`-injectivity property. -/
structure embedding {α₁ α₂ : Type u} (β₁ : α₁ → Type v) (β₂ : α₂ → Type v) :=
(to_fun : sigma β₁ → sigma β₂)
(inj    : injective to_fun)

infixr ` s↪ `:25 := embedding

namespace embedding
variables {α₁ α₂ : Type u} {β₁ : α₁ → Type v} {β₂ : α₂ → Type v}

instance : has_coe_to_fun (β₁ s↪ β₂) :=
⟨_, embedding.to_fun⟩

@[simp] theorem to_fun_eq_coe (f : β₁ s↪ β₂) : f.to_fun = f :=
rfl

@[simp] theorem coe_fn_mk (f : sigma β₁ → sigma β₂) (i : injective f) :
  (mk f i : sigma β₁ → sigma β₂) = f :=
rfl

theorem inj' : ∀ (f : β₁ s↪ β₂), injective f
| ⟨_, h⟩ := h

end embedding

section
variables {α : Type u} {β₁ β₂ : α → Type v}

/-- Map `id` over `fst` and a function over `snd`. -/
def map_snd (f : ∀ (a : α), β₁ a → β₂ a) : sigma β₁ → sigma β₂ :=
have sigma β₁ → sigma (id β₂) := map id f, by exact this

theorem map_snd_fst_iff {s₁ s₂ : sigma β₁} (f : ∀ (a : α), β₁ a → β₂ a) :
  (map_snd f s₁).1 = (map_snd f s₂).1 ↔ s₁.1 = s₂.1 :=
by cases s₁; cases s₂; exact iff.rfl

theorem map_snd_functional (f : ∀ (a : α), β₁ a → β₂ a) : functional (map_snd f) :=
λ _ _, (map_snd_fst_iff f).mpr

theorem map_snd_injective (f : ∀ (a : α), β₁ a → β₂ a) : injective (map_snd f) :=
λ _ _, (map_snd_fst_iff f).mp

/-- Construct an `embedding` with `id` on `fst`. -/
def embedding.mk₂ (f : ∀ (a : α), β₁ a → β₂ a) : embedding β₁ β₂ :=
⟨_, map_snd_injective f⟩

end

section
variables {α : Type u} {β : α → Type v} {R : α → α → Prop}

/-- A relation `R` on `fst` values lifted to the `sigma`. This is useful where
you might otherwise use the term `λ s₁ s₂, R s₁.1 s₂.1`. -/
def rel (R : α → α → Prop) (s₁ s₂ : sigma β) : Prop :=
R s₁.1 s₂.1

@[simp] theorem rel_eq {s₁ s₂ : sigma β} : rel R s₁ s₂ = R s₁.1 s₂.1 :=
rfl

instance [d : decidable_rel R] : decidable_rel (@rel _ β R)
| s₁ s₂ := @d s₁.1 s₂.1

theorem rel.refl (h : reflexive R) : reflexive (@rel _ β R) :=
λ s, h s.1

theorem rel.symm (h : symmetric R) : symmetric (@rel _ β R) :=
λ s₁ s₂ (p : R s₁.1 s₂.1), h p

theorem rel.trans (h : transitive R) : transitive (@rel _ β R) :=
λ s₁ s₂ s₃ (p : R s₁.1 s₂.1) (q : R s₂.1 s₃.1), h p q

end

section
variables {α : Type u} {β : α → Type v}

theorem functional_id : functional (@id (sigma β)) :=
λ s t h, h

theorem injective_id : injective (@id (sigma β)) :=
λ s t h, h

@[refl] protected def embedding.refl (β : α → Type v) : β s↪ β :=
⟨_, injective_id⟩

@[simp] theorem embedding.refl_apply (s : sigma β) : embedding.refl β s = s :=
rfl

end

section
variables {α₁ α₂ α₃ : Type u}
variables {β₁ : α₁ → Type v} {β₂ : α₂ → Type v} {β₃ : α₃ → Type v}
variables {g : sigma β₂ → sigma β₃} {f : sigma β₁ → sigma β₂}

theorem functional_comp (gf : functional g) (ff : functional f) : functional (g ∘ f) :=
λ s t h, gf (ff h)

theorem injective_comp (gi : injective g) (fi : injective f) : injective (g ∘ f) :=
λ s t h, fi (gi h)

@[trans] protected def embedding.trans (f : β₁ s↪ β₂) (g : β₂ s↪ β₃) : β₁ s↪ β₃ :=
⟨_, injective_comp g.inj f.inj⟩

@[simp] theorem embedding.trans_apply (f : β₁ s↪ β₂) (g : β₂ s↪ β₃) (s : sigma β₁) :
  (f.trans g) s = g (f s) :=
rfl

end

end sigma
