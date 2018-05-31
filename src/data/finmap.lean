import data.alist

universes u v

def finmap (α : Type u) (β : α → Type v) : Type (max u v) :=
quotient (alist.setoid α β)

namespace finmap
variables {α : Type u} {β : α → Type v}

instance [decidable_eq α] [∀ a, decidable_eq (β a)] : decidable_eq (finmap α β)
| f g := quotient.rec_on_subsingleton₂ f g $
  λ l₁ l₂, decidable_of_iff' _ quotient.eq

def lookup [decidable_eq α] (a : α) (f : finmap α β) : option (β a) :=
quot.lift_on f (alist.lookup a) (λ _ _, alist.perm_of_lookup a)

def contains [decidable_eq α] (f : finmap α β) (a : α) : bool :=
(f.lookup a).is_some

instance : has_emptyc (finmap α β) := ⟨⟦∅⟧⟩

instance [decidable_eq α] : has_mem α (finmap α β) :=
⟨λ a f, f.contains a⟩

def keys [decidable_eq α] (f : finmap α β) : finset α :=
quot.lift_on f alist.keys (λ _ _, alist.perm_of_keys)

end finmap
