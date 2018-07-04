import data.finset
import data.multiset.dict

universes u v

def alist (α : Type u) (β : α → Type v) : Type (max u v) :=
{ l : list (sigma β) // l.nodup_keys }

variables {α : Type u} {β : α → Type v}
variables {a : α} {s s₁ s₂ : sigma β} {l l₁ l₂ l₃ l₄ : alist α β}

namespace alist

theorem eq_of_veq : ∀ {l₁ l₂ : alist α β}, l₁.val = l₂.val → l₁ = l₂
| ⟨s, _⟩ ⟨t, _⟩ h := by congr; assumption

@[simp] theorem val_inj : l₁.val = l₂.val ↔ l₁ = l₂ :=
⟨eq_of_veq, congr_arg _⟩

instance [decidable_eq α] [∀ a, decidable_eq (β a)] : decidable_eq (alist α β)
| l₁ l₂ := decidable_of_iff _ val_inj

protected def empty : alist α β :=
⟨[], list.nodup_keys_nil⟩

instance : has_emptyc (alist α β) :=
⟨alist.empty⟩

section empty

@[simp] theorem empty_val : (∅ : alist α β).val = [] :=
rfl

end empty

def lookup [decidable_eq α] (a : α) (l : alist α β) : option (β a) :=
l.val.klookup a

section lookup
variables [decidable_eq α]

@[simp] theorem lookup_empty (a : α) : lookup a (∅ : alist α β) = none :=
rfl

@[simp] theorem lookup_eq (a : α) (l : alist α β) :
  lookup a l = none ∨ ∃ (b : β a), lookup a l = some b :=
by cases l; simp [lookup]

end lookup

def keys [decidable_eq α] (l : alist α β) : list α :=
l.val.keys

section keys
variables [decidable_eq α]

@[simp] theorem keys_empty : keys (∅ : alist α β) = [] :=
rfl

@[simp] theorem keys_nodup (l : alist α β) : l.keys.nodup :=
list.keys_nodup_of_nodup_keys l.property

end keys

def keyset [decidable_eq α] (l : alist α β) : finset α :=
l.val.keys.to_finset

instance : has_mem (sigma β) (alist α β) :=
⟨λ s l, s ∈ l.val⟩

section mem
variables [decidable_eq α]

theorem mem_def : s ∈ l = (s ∈ l.val) :=
rfl

@[simp] theorem not_mem_empty (s : sigma β) : s ∉ (∅ : alist α β) :=
id

@[simp] theorem ne_empty_of_mem {s : sigma β} {l : alist α β} (h : s ∈ l) : l ≠ ∅
| e := not_mem_empty s $ e ▸ h

end mem

instance : has_subset (alist α β) :=
⟨λ l₁ l₂, l₁.val ⊆ l₂.val⟩

theorem subset_def : l₁ ⊆ l₂ ↔ l₁.val ⊆ l₂.val :=
iff.rfl

@[simp] theorem subset.refl (l : alist α β) : l ⊆ l :=
list.subset.refl l.val

theorem subset.trans {l₁ l₂ l₃ : alist α β} : l₁ ⊆ l₂ → l₂ ⊆ l₃ → l₁ ⊆ l₃ :=
list.subset.trans

instance [has_lt (sigma β)] : has_lt (alist α β) :=
⟨λ l₁ l₂, list.lex (<) l₁.val l₂.val⟩

theorem lt_def [has_lt (sigma β)] : l₁ < l₂ ↔ list.lex (<) l₁.val l₂.val :=
iff.rfl

instance is_asymm [has_lt (sigma β)] [is_asymm (sigma β) (<)] :
  is_asymm (alist α β) (<) :=
⟨λ l₁ l₂, by simp only [lt_def]; exact is_asymm.asymm l₁.val l₂.val⟩

instance is_order_connected [has_lt (sigma β)] [is_order_connected (sigma β) (<)]
  [is_trichotomous (sigma β) (<)] : is_order_connected (alist α β) (<) :=
⟨λ l₁ l₂ l₃, by simp only [lt_def]; exact is_order_connected.conn l₁.val l₂.val l₃.val⟩

instance is_trichotomous [has_lt (sigma β)] [is_trichotomous (sigma β) (<)] :
  is_trichotomous (alist α β) (<) :=
⟨λ l₁ l₂,
 by simp only [lt_def];
    rw ←val_inj;
    exact is_trichotomous.trichotomous (<) l₁.val l₂.val⟩

instance is_strict_total_order [has_lt (sigma β)] [is_strict_total_order' (sigma β) (<)] :
  is_strict_total_order' (alist α β) (<) :=
{..is_strict_weak_order_of_is_order_connected}

instance [linear_order (sigma β)] : linear_order (alist α β) :=
linear_order_of_STO' (<)

instance [decidable_linear_order (sigma β)] : decidable_linear_order (alist α β) :=
decidable_linear_order_of_STO' (<)

def erase [decidable_eq α] (a : α) (l : alist α β) : alist α β :=
⟨l.val.kerase a, list.nodup_keys_kerase a l.property⟩

protected def insert [decidable_eq α] (s : sigma β) (l : alist α β) : alist α β :=
⟨l.val.kinsert s, list.nodup_keys_kinsert s l.property⟩

instance [decidable_eq α] : has_insert (sigma β) (alist α β) :=
⟨alist.insert⟩

section insert
variables [decidable_eq α]

@[simp] theorem insert_val (s : sigma β) (l : alist α β) :
  (insert s l).val = l.val.kinsert s :=
rfl

@[simp] theorem mem_insert : s₁ ∈ insert s₂ l ↔ s₁ = s₂ ∨ s₁ ∈ l.erase s₂.1 :=
list.mem_kinsert

end insert

protected def append [decidable_eq α] (l₁ : alist α β) (l₂ : alist α β) : alist α β :=
⟨l₁.val.kappend l₂.val, list.nodup_keys_kappend l₁.property l₂.property⟩

instance [decidable_eq α] : has_append (alist α β) :=
⟨alist.append⟩

section append
variables [decidable_eq α]

@[simp] theorem append_val (l₁ l₂ : alist α β) : (l₁ ++ l₂).val = l₁.val.kappend l₂.val :=
rfl

@[simp] theorem empty_append (l : alist α β) : ∅ ++ l = l :=
eq_of_veq rfl

@[simp] theorem append_empty (l : alist α β) : l ++ ∅ = l :=
eq_of_veq $ by simp

@[simp] theorem insert_append (s : sigma β) (l₁ l₂ : alist α β) :
  insert s l₁ ++ l₂ = insert s (l₁ ++ l₂) :=
eq_of_veq $ by simp

@[simp] theorem append_assoc (l₁ l₂ l₃ : alist α β) : (l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃) :=
eq_of_veq $ by simp

end append

def replace [decidable_eq α] (s : sigma β) (l : alist α β) : alist α β :=
⟨l.val.kreplace s, list.nodup_keys_kreplace s l.property⟩

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

theorem perm_keys_of_perm [decidable_eq α] (p : perm l₁ l₂) : l₁.keys ~ l₂.keys :=
list.perm_map sigma.fst p

theorem eq_keyset_of_perm [decidable_eq α] (p : perm l₁ l₂) : l₁.keyset = l₂.keyset :=
finset.eq_of_veq $ quot.sound $ list.perm_erase_dup_of_perm $
  list.perm_keys_of_perm l₁.property l₂.property p

theorem subset_of_perm [decidable_eq α] (p : perm l₁ l₂) : l₁ ⊆ l₂ :=
list.perm_subset p

theorem mem_of_perm (p : perm l₁ l₂) : s ∈ l₁ ↔ s ∈ l₂ :=
list.mem_of_perm p

theorem eq_lookup_of_perm [decidable_eq α] (a : α) (p : perm l₁ l₂) :
  l₁.lookup a = l₂.lookup a :=
list.klookup_eq_of_perm a l₁.property l₂.property p

theorem perm_erase [decidable_eq α] (a : α) (p : perm l₁ l₂) :
  perm (l₁.erase a) (l₂.erase a) :=
list.perm_kerase a l₁.property l₂.property p

theorem perm_insert [decidable_eq α] (s : sigma β) (p : perm l₁ l₂) :
  perm (l₁.insert s) (l₂.insert s) :=
list.perm_kinsert s l₁.property l₂.property p

theorem perm_append [decidable_eq α] (p₁₂ : perm l₁ l₂) (p₃₄ : perm l₃ l₄) :
  perm (l₁ ++ l₃) (l₂ ++ l₄) :=
list.perm_kappend l₃.property l₄.property p₁₂ p₃₄

theorem perm_replace [decidable_eq α] (s : sigma β) (p : perm l₁ l₂) :
  perm (l₁.replace s) (l₂.replace s) :=
list.perm_kreplace s l₁.property l₂.property p

def to_finset (l : alist α β) : finset (sigma β) :=
⟨⟦l.val⟧, multiset.nodup_of_nodup_keys l.property⟩

end alist
