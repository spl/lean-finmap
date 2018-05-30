import data.alist

universes u v

def finmap (α : Type u) (β : α → Type v) : Type (max u v) :=
quotient (alist.setoid α β)

namespace finmap
variables {α : Type u} {β : α → Type v}

def lookup [decidable_eq α] (a : α) (f : finmap α β) : option (β a) :=
quot.lift_on f (alist.lookup a) $
  λ ⟨l₁, nd₁⟩ ⟨l₂, nd₂⟩ (p : l₁ ~ l₂), list.dict_lookup_eq_of_perm a nd₁ nd₂ p

end finmap
