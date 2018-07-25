import data.sigma.basic

namespace sigma
universes u v

section
variables {α : Type u} {β : α → Type v}

theorem eq_fst {s₁ s₂ : sigma β} : s₁ = s₂ → s₁.1 = s₂.1 :=
by cases s₁; cases s₂; cc

theorem eq_snd {s₁ s₂ : sigma β} : s₁ = s₂ → s₁.2 == s₂.2 :=
by cases s₁; cases s₂; cc

/-- `sigma`s of type `β` behave as functions, preserving equality from argument
(`fst`) to result (`snd`). -/
def functional (β : α → Type v) : Prop :=
∀ ⦃s t : sigma β⦄ (h : s.1 = t.1), (eq.rec_on h s.2 : β t.1) = t.2

theorem injective_fst (h : functional β) : function.injective (@fst _ β) :=
λ s₁ s₂ p, sigma.eq p (h p)

@[simp] theorem fst_eq_of_functional {a : α} {s : sigma β} (h : functional β) :
  (∃ (b : β a), mk a b = s) ↔ a = s.1 :=
match s with ⟨a', b'⟩ :=
  ⟨λ ⟨b, e⟩, eq_fst e,
   λ (e : a = a'), ⟨(eq.rec_on e.symm b' : β a), sigma.eq e $ @h ⟨a, _⟩ ⟨a', _⟩ e⟩⟩
end

end

section
variables {α₁ α₂ : Type u} {β₁ : α₁ → Type v} {β₂ : α₂ → Type v}

/-- A function on `sigma`s that is functional on `fst`s (preserves equality from
argument to result). -/
def fst_functional (f : sigma β₁ → sigma β₂) : Prop :=
∀ ⦃s t : sigma β₁⦄, s.1 = t.1 → (f s).1 = (f t).1

/-- A function on `sigma`s that is injective on `fst`s (preserves equality from
result to argument). -/
def fst_injective (f : sigma β₁ → sigma β₂) : Prop :=
∀ ⦃s t : sigma β₁⦄, (f s).1 = (f t).1 → s.1 = t.1

end

/-- A function on `sigma`s bundled with its `fst`-injectivity property. -/
structure embedding {α₁ α₂ : Type u} (β₁ : α₁ → Type v) (β₂ : α₂ → Type v) :=
(to_fun : sigma β₁ → sigma β₂)
(inj    : fst_injective to_fun)

infixr ` s↪ `:25 := embedding

namespace embedding
variables {α₁ α₂ : Type u} {β₁ : α₁ → Type v} {β₂ : α₂ → Type v}

instance : has_coe_to_fun (β₁ s↪ β₂) :=
⟨_, embedding.to_fun⟩

@[simp] theorem to_fun_eq_coe (f : β₁ s↪ β₂) : f.to_fun = f :=
rfl

@[simp] theorem coe_fn_mk (f : sigma β₁ → sigma β₂) (i : fst_injective f) :
  (mk f i : sigma β₁ → sigma β₂) = f :=
rfl

theorem inj' : ∀ (f : β₁ s↪ β₂), fst_injective f
| ⟨_, h⟩ := h

end embedding

section
variables {α : Type u} {β₁ β₂ : α → Type v}

/-- Map `id` over `fst` and a function over `snd`. -/
def map_snd (f : ∀ (a : α), β₁ a → β₂ a) : sigma β₁ → sigma β₂ :=
have sigma β₁ → sigma (id β₂) := map id f, by exact this

theorem map_snd_eq_fst_iff {s₁ s₂ : sigma β₁} (f : ∀ (a : α), β₁ a → β₂ a) :
  (map_snd f s₁).1 = (map_snd f s₂).1 ↔ s₁.1 = s₂.1 :=
by cases s₁; cases s₂; exact iff.rfl

theorem map_snd_fst_functional (f : ∀ (a : α), β₁ a → β₂ a) :
  fst_functional (map_snd f) :=
λ _ _, (map_snd_eq_fst_iff f).mpr

theorem map_snd_fst_injective (f : ∀ (a : α), β₁ a → β₂ a) :
  fst_injective (map_snd f) :=
λ _ _, (map_snd_eq_fst_iff f).mp

/-- Construct an `embedding` with `id` on `fst`. -/
def embedding.mk₂ (f : ∀ (a : α), β₁ a → β₂ a) : embedding β₁ β₂ :=
⟨_, map_snd_fst_injective f⟩

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

theorem fst_functional_id : fst_functional (@id (sigma β)) :=
λ s t h, h

theorem fst_injective_id : fst_injective (@id (sigma β)) :=
λ s t h, h

@[refl] protected def embedding.refl (β : α → Type v) : β s↪ β :=
⟨_, fst_injective_id⟩

@[simp] theorem embedding.refl_apply (s : sigma β) : embedding.refl β s = s :=
rfl

end

section
variables {α₁ α₂ α₃ : Type u}
variables {β₁ : α₁ → Type v} {β₂ : α₂ → Type v} {β₃ : α₃ → Type v}
variables {g : sigma β₂ → sigma β₃} {f : sigma β₁ → sigma β₂}

theorem fst_functional_comp (gf : fst_functional g) (ff : fst_functional f) :
  fst_functional (g ∘ f) :=
λ s t h, gf (ff h)

theorem fst_injective_comp (gi : fst_injective g) (fi : fst_injective f) :
  fst_injective (g ∘ f) :=
λ s t h, fi (gi h)

@[trans] protected def embedding.trans (f : β₁ s↪ β₂) (g : β₂ s↪ β₃) : β₁ s↪ β₃ :=
⟨_, fst_injective_comp g.inj f.inj⟩

@[simp] theorem embedding.trans_apply (f : β₁ s↪ β₂) (g : β₂ s↪ β₃) (s : sigma β₁) :
  (f.trans g) s = g (f s) :=
rfl

theorem injective_fst_comp (h : functional β₁) (fi : fst_injective f) :
  function.injective (fst ∘ f) :=
λ s t p, @injective_fst _ _ h _ _ (fi p)

theorem injective_of_fst_injective (h : functional β₁) (fi : fst_injective f) :
  function.injective f :=
λ s t e, let p := fi (eq_fst e) in sigma.eq p $ h p

theorem fst_injective_of_injective (h : functional β₂) (fi : function.injective f) :
  fst_injective f :=
λ s t p, eq_fst $ fi $ sigma.eq p $ h p

theorem fst_injective_iff_injective (h₁ : functional β₁) (h₂ : functional β₂) :
  fst_injective f ↔ function.injective f :=
⟨injective_of_fst_injective h₁, fst_injective_of_injective h₂⟩

end

end sigma
