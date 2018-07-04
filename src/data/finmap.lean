import data.alist

universes u v

def finmap (α : Type u) (β : α → Type v) : Type (max u v) :=
quotient (alist.setoid α β)

namespace finmap
variables {α : Type u} {β : α → Type v}

instance [decidable_eq α] [∀ a, decidable_eq (β a)] : decidable_eq (finmap α β)
| f g := quotient.rec_on_subsingleton₂ f g $
  λ _ _, decidable_of_iff' _ quotient.eq

def keys [decidable_eq α] (f : finmap α β) : finset α :=
quot.lift_on f alist.keyset (λ _ _, alist.eq_keyset_of_perm)

protected def mem (a : sigma β) (f : finmap α β) : Prop :=
quot.lift_on f (has_mem.mem a)
               (λ _ _, propext ∘ alist.mem_of_perm)

instance : has_mem (sigma β) (finmap α β) :=
⟨finmap.mem⟩

protected def empty : finmap α β :=
⟦∅⟧

instance : has_emptyc (finmap α β) := ⟨finmap.empty⟩

section empty
variables [decidable_eq α]

@[simp] theorem not_mem_empty (s : sigma β) : s ∉ (∅ : finmap α β) :=
id

end empty

instance : has_subset (finmap α β) := ⟨λ f g, ∀ ⦃s : sigma β⦄, s ∈ f → s ∈ g⟩

def lookup [decidable_eq α] (a : α) (f : finmap α β) : option (β a) :=
quot.lift_on f (alist.lookup a) (λ _ _, alist.eq_lookup_of_perm a)

def erase [decidable_eq α] (a : α) (f : finmap α β) : finmap α β :=
quot.lift_on f (quot.mk _ ∘ alist.erase a)
               (λ _ _, quot.sound ∘ alist.perm_erase a)

def insert [decidable_eq α] (s : sigma β) (f : finmap α β) : finmap α β :=
quot.lift_on f (quot.mk _ ∘ alist.insert s)
               (λ _ _, quot.sound ∘ alist.perm_insert s)

section insert
variables [decidable_eq α]
variables {s₁ s₂ : sigma β} {f : finmap α β}

@[simp] theorem mem_insert : s₁ ∈ insert s₂ f ↔ s₁ = s₂ ∨ s₁ ∈ erase s₂.1 f :=
quot.induction_on f $ λ l, alist.mem_insert

end insert

def replace [decidable_eq α] (s : sigma β) (f : finmap α β) : finmap α β :=
quot.lift_on f (quot.mk _ ∘ alist.replace s)
               (λ _ _, quot.sound ∘ alist.perm_replace s)

def union [decidable_eq α] (f : finmap α β) (g : finmap α β) : finmap α β :=
quotient.lift_on₂ f g
  (λ l₁ l₂, ⟦l₁ ++ l₂⟧)
  (λ _ _ _ _ p₁ p₂, quot.sound $ alist.perm_append p₁ p₂)

end finmap
