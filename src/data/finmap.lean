import data.finset
import data.multiset.dict
import data.quot

universes u v

structure finmap (α : Type u) (β : α → Type v) : Type (max u v) :=
(val        : list (sigma β))
(nodup_keys : val.nodup_keys)

namespace finmap
variables {α : Type u} {β : α → Type v}

def to_finset (f : finmap α β) : finset (sigma β) :=
⟨⟦f.val⟧, multiset.nodup_of_nodup_keys f.nodup_keys⟩

theorem eq_of_veq : ∀ {f g : finmap α β}, f.val = g.val → f = g
| ⟨s, _⟩ ⟨t, _⟩ h := by congr; assumption

@[simp] theorem val_inj {f g : finmap α β} : f.val = g.val ↔ f = g :=
⟨eq_of_veq, congr_arg _⟩

instance [decidable_eq α] [∀ a, decidable_eq (β a)] : decidable_eq (finmap α β)
| f g := decidable_of_iff _ val_inj

instance : has_emptyc (finmap α β) := ⟨⟨∅, list.nodup_keys_nil⟩⟩

def lookup [decidable_eq α] (a : α) (f : finmap α β) : option (β a) :=
list.dict_lookup a f.val

def contains [decidable_eq α] (f : finmap α β) (a : α) : bool :=
(f.lookup a).is_some

instance has_mem [decidable_eq α] : has_mem α (finmap α β) :=
⟨λ a f, f.contains a⟩

def dom [decidable_eq α] (f : finmap α β) : finset α :=
f.val.dict_keys.to_finset

def perm (f : finmap α β) (g : finmap α β) : Prop :=
list.perm f.1 g.1

@[refl] protected theorem perm.refl (f : finmap α β) : perm f f :=
list.perm.refl f.1

@[symm] protected theorem perm.symm {f g : finmap α β} (p : perm f g) : perm g f :=
list.perm.symm p

@[trans] protected theorem perm.trans {f g h : finmap α β} (p : perm f g) (q : perm g h) : perm f h :=
list.perm.trans p q

theorem perm.equiv (α : Type u) (β : α → Type v) : equivalence (@perm α β) :=
mk_equivalence (@perm α β) (@perm.refl α β) (@perm.symm α β) (@perm.trans α β)

instance (α : Type u) (β : α → Type v) : setoid (finmap α β) :=
setoid.mk (@perm α β) (perm.equiv α β)

def finmap' (α : Type u) (β : α → Type v) : Type (max u v) :=
quotient (finmap.setoid α β)

def lookup' [decidable_eq α] (a : α) (f : finmap' α β) : option (β a) :=
quot.lift_on f (lookup a) $
  λ ⟨l₁, nd₁⟩ ⟨l₂, nd₂⟩ (p : l₁ ~ l₂), list.dict_lookup_eq_of_perm a nd₁ nd₂ p

end finmap
