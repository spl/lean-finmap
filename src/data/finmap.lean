import data.finset data.list.dict data.quot

local attribute [-simp] sigma.forall

universes u v

def finmap (α : Type u) (β : α → Type v) : Type (max u v) :=
quotient (@list.subtype_setoid (sigma β) list.nodup_keys)

namespace finmap
variables {α : Type u} {β : α → Type v}

instance [decidable_eq α] [∀ a, decidable_eq (β a)] : decidable_eq (finmap α β)
| f g := quotient.rec_on_subsingleton₂ f g $ λ _ _, decidable_of_iff' _ quotient.eq

instance : has_emptyc (finmap α β) :=
⟨⟦⟨[], list.nodup_keys_nil⟩⟧⟩

def keys [decidable_eq α] (f : finmap α β) : finset α :=
quot.lift_on f
  (list.to_finset ∘ list.keys ∘ subtype.val)
  (λ l₁ l₂, finset.eq_of_veq ∘ quot.sound ∘ list.perm_erase_dup_of_perm ∘
    list.perm_keys_of_perm l₁.property l₂.property)

section keys
variables [decidable_eq α]

@[simp] theorem keys_empty : keys (∅ : finmap α β) = ∅ :=
rfl

end keys

protected def mem (s : sigma β) (f : finmap α β) : Prop :=
quot.lift_on f (λ l, has_mem.mem s l.val) (λ _ _, propext ∘ list.mem_of_perm)

instance : has_mem (sigma β) (finmap α β) :=
⟨finmap.mem⟩

section mem

@[simp] theorem not_mem_empty (s : sigma β) : s ∉ (∅ : finmap α β) :=
id

theorem ext {f g : finmap α β} : f = g ↔ ∀ (s : sigma β), s ∈ f ↔ s ∈ g :=
quotient.induction_on₂ f g $ λ l₁ l₂, quotient.eq.trans $
  list.perm_ext (list.nodup_of_nodup_keys l₁.property) (list.nodup_of_nodup_keys l₂.property)

@[extensionality]
theorem ext' {f g : finmap α β} : (∀ (s : sigma β), s ∈ f ↔ s ∈ g) → f = g :=
ext.mpr

instance decidable_mem [decidable_eq α] [∀ a, decidable_eq (β a)] (s : sigma β) (f : finmap α β) :
  decidable (s ∈ f) :=
quot.rec_on_subsingleton f $ λ l, list.decidable_mem s l.val

end mem

instance : has_subset (finmap α β) :=
⟨λ f g, ∀ ⦃s : sigma β⦄, s ∈ f → s ∈ g⟩

def lookup [decidable_eq α] (a : α) (f : finmap α β) : option (β a) :=
quot.lift_on f
  (list.klookup a ∘ subtype.val)
  (λ l₁ l₂, list.klookup_eq_of_perm a l₁.property l₂.property)

section lookup
variables [decidable_eq α]

theorem lookup_empty (a : α) : lookup a (∅ : finmap α β) = none :=
rfl

end lookup

def erase [decidable_eq α] (a : α) (f : finmap α β) : finmap α β :=
quot.lift_on f
  (λ l, ⟦subtype.mk (l.val.kerase a) (list.nodup_keys_kerase a l.property)⟧)
  (λ l₁ l₂, quot.sound ∘ list.perm_kerase a l₁.property l₂.property)

section erase
variables [decidable_eq α]

theorem erase_empty (a : α) : erase a (∅ : finmap α β) = ∅ :=
rfl

end erase

protected def insert [decidable_eq α] (s : sigma β) (f : finmap α β) : finmap α β :=
quot.lift_on f
  (λ l, ⟦subtype.mk (l.val.kinsert s) (list.nodup_keys_kinsert s l.property)⟧)
  (λ l₁ l₂, quot.sound ∘ list.perm_kinsert s l₁.property l₂.property)

instance [decidable_eq α] : has_insert (sigma β) (finmap α β) :=
⟨finmap.insert⟩

section insert
variables [decidable_eq α]
variables {s₁ s₂ : sigma β} {f : finmap α β}

@[simp] theorem insert_empty (s : sigma β) : insert s (∅ : finmap α β) = {s} :=
rfl

@[simp] theorem mem_insert : s₁ ∈ insert s₂ f ↔ s₁ = s₂ ∨ s₁ ∈ erase s₂.1 f :=
quot.induction_on f $ λ _, list.mem_kinsert

end insert

def replace [decidable_eq α] (s : sigma β) (f : finmap α β) : finmap α β :=
quot.lift_on f
  (λ l, ⟦subtype.mk (l.val.kreplace s) (list.nodup_keys_kreplace s l.property)⟧)
  (λ l₁ l₂, quot.sound ∘ list.perm_kreplace s l₁.property l₂.property)

section replace
variables [decidable_eq α]

@[simp] theorem replace_empty (s : sigma β) : replace s ∅ = ∅ :=
rfl

end replace

section map
variables {α₁ : Type u} {β₁ : α₁ → Type v} {α₂ : Type u} {β₂ : α₂ → Type v} {g : sigma β₁ → sigma β₂}

def map (gi : sigma.fst_injective g) (f : finmap α₁ β₁) : finmap α₂ β₂ :=
quot.lift_on f
  (λ l, ⟦subtype.mk (l.val.map g) (list.nodup_keys_map gi l.property)⟧)
  (λ l₁ l₂, quot.sound ∘ list.perm_map g)

@[simp] theorem map_empty (gi : sigma.fst_injective g) : map gi ∅ = ∅ :=
rfl

end map

section map_val
variables {β₁ β₂ : α → Type v}

def map_val (g : ∀ (a : α), β₁ a → β₂ a) : finmap α β₁ → finmap α β₂ :=
map (sigma.fst_injective_snd g)

@[simp] theorem map_val_empty (g : ∀ (a : α), β₁ a → β₂ a) : map_val g ∅ = ∅ :=
rfl

end map_val

protected def union [decidable_eq α] (f : finmap α β) (g : finmap α β) : finmap α β :=
quotient.lift_on₂ f g
  (λ l₁ l₂, ⟦subtype.mk (l₁.val.kappend l₂.val) (list.nodup_keys_kappend l₁.property l₂.property)⟧)
  (λ l₁ l₂ l₃ l₄ p₁₃ p₂₄, quot.sound $ list.perm_kappend l₂.property l₄.property p₁₃ p₂₄)

instance [decidable_eq α] : has_union (finmap α β) :=
⟨finmap.union⟩

end finmap
