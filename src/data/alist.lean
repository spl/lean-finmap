import data.finset
import data.multiset.dict

universes u v

def alist (α : Type u) (β : α → Type v) : Type (max u v) :=
{ l : list (sigma β) // l.nodup_keys }

namespace alist
variables {α : Type u} {β : α → Type v}
variables {l₁ l₂ l₃ : alist α β}

theorem eq_of_veq : ∀ {l₁ l₂ : alist α β}, l₁.val = l₂.val → l₁ = l₂
| ⟨s, _⟩ ⟨t, _⟩ h := by congr; assumption

@[simp] theorem val_inj : l₁.val = l₂.val ↔ l₁ = l₂ :=
⟨eq_of_veq, congr_arg _⟩

instance [decidable_eq α] [∀ a, decidable_eq (β a)] : decidable_eq (alist α β)
| l₁ l₂ := decidable_of_iff _ val_inj

instance : has_emptyc (alist α β) := ⟨⟨∅, list.nodup_keys_nil⟩⟩

def lookup [decidable_eq α] (a : α) (l : alist α β) : option (β a) :=
l.val.dict_lookup a

def contains [decidable_eq α] (l : alist α β) (a : α) : bool :=
(l.lookup a).is_some

instance [decidable_eq α] : has_mem α (alist α β) :=
⟨λ a l, l.contains a⟩

def keys [decidable_eq α] (l : alist α β) : finset α :=
l.val.dict_keys.to_finset

def insert [decidable_eq α] (s : sigma β) (l : alist α β) : alist α β :=
⟨l.val.dict_insert s, (list.nodup_keys_dict_insert s).mpr l.property⟩

def erase [decidable_eq α] (a : α) (l : alist α β) : alist α β :=
⟨l.val.dict_erase a, list.nodup_keys_dict_erase a l.property⟩

def replace [decidable_eq α] (s : sigma β) (l : alist α β) : alist α β :=
⟨l.val.dict_replace s, list.nodup_keys_dict_replace s l.property⟩

def perm (l₁ : alist α β) (l₂ : alist α β) : Prop :=
list.perm l₁.1 l₂.1

@[refl] protected theorem perm.refl (l : alist α β) : perm l l :=
list.perm.refl l.1

@[symm] protected theorem perm.symm (p : perm l₁ l₂) : perm l₂ l₁ :=
list.perm.symm p

@[trans] protected theorem perm.trans (p : perm l₁ l₂) (q : perm l₂ l₃) : perm l₁ l₃ :=
list.perm.trans p q

theorem perm.equivalence (α : Type u) (β : α → Type v) : equivalence (@perm α β) :=
mk_equivalence (@perm α β) (@perm.refl α β) (@perm.symm α β) (@perm.trans α β)

instance (α : Type u) (β : α → Type v) : setoid (alist α β) :=
setoid.mk (@perm α β) (perm.equivalence α β)

instance decidable_perm [decidable_eq α] [∀ a, decidable_eq (β a)] (l₁ l₂ : alist α β) :
  decidable (perm l₁ l₂) :=
list.decidable_perm l₁.val l₂.val

theorem eq_keys_of_perm [decidable_eq α] (p : perm l₁ l₂) :
  alist.keys l₁ = alist.keys l₂ :=
finset.eq_of_veq $ quot.sound $ list.perm_erase_dup_of_perm $
  list.dict_keys_eq_of_perm l₁.property l₂.property p

theorem eq_lookup_of_perm [decidable_eq α] (a : α) (p : perm l₁ l₂) :
  l₁.lookup a = l₂.lookup a :=
list.dict_lookup_eq_of_perm a l₁.property l₂.property p

theorem perm_erase [decidable_eq α] (a : α) (p : perm l₁ l₂) :
  perm (l₁.erase a) (l₂.erase a) :=
list.perm_dict_erase a l₁.property l₂.property p

theorem perm_replace [decidable_eq α] (s : sigma β) (p : perm l₁ l₂) :
  perm (l₁.replace s) (l₂.replace s) :=
list.perm_dict_replace s l₁.property l₂.property p

end alist

namespace finset
variables {α : Type u} {β : α → Type v}

def of_alist (l : alist α β) : finset (sigma β) :=
⟨⟦l.val⟧, multiset.nodup_of_nodup_keys l.property⟩

end finset
