import data.list.dict
import data.multiset
import data.pfun

namespace multiset
universes u v
variables {α : Type u} {β : α → Type v}

open function list

def nodup_keys (m : multiset (sigma β)) : Prop :=
quotient.lift_on m nodup_keys (λ _ _, propext ∘ perm_nodup_keys)

theorem nodup_of_nodup_keys {m : multiset (sigma β)} : m.nodup_keys → m.nodup :=
quotient.induction_on m $ λ _, nodup_of_nodup_keys

@[simp] theorem nodup_keys_zero : @nodup_keys _ β 0 :=
pairwise.nil _

theorem nodup_keys_singleton : ∀ (s : sigma β), nodup_keys (s :: 0) :=
nodup_keys_singleton

def krec_on {γ : Sort*} (m : multiset (sigma β))
  (φ : ∀ {l : list (sigma β)}, l.nodup_keys → γ)
  (c : ∀ {l₁ l₂} (p : l₁ ~ l₂) (d₁ : l₁.nodup_keys) (d₂ : l₂.nodup_keys), φ d₁ = φ d₂) :
  m.nodup_keys → γ :=
@quotient.hrec_on _ _ (λ (m : multiset (sigma β)), m.nodup_keys → γ) m (λ _, φ) $
  λ _ _ p, hfunext (by rw perm_nodup_keys p) $
    λ d₁ d₂ _, heq_of_eq $ c p d₁ d₂

@[simp] theorem krec_on_val {γ : Sort*} {l : list (sigma β)} (d : l.nodup_keys)
  (φ : ∀ {l : list (sigma β)}, l.nodup_keys → γ)
  (c : ∀ {l₁ l₂} (p : l₁ ~ l₂) (d₁ : l₁.nodup_keys) (d₂ : l₂.nodup_keys), φ d₁ = φ d₂) :
  krec_on ⟦l⟧ @φ @c d = φ d :=
rfl

def krec_on₂ {γ : Sort*} (m₁ m₂ : multiset (sigma β))
  (φ : ∀ {l₁ l₂ : list (sigma β)}, l₁.nodup_keys → l₂.nodup_keys → γ)
  (cl : ∀ {l l₁ l₂ : list (sigma β)} (p : l₁ ~ l₂) (d : l.nodup_keys) (d₁ : l₁.nodup_keys) (d₂ : l₂.nodup_keys), φ d₁ d = φ d₂ d)
  (cr : ∀ {l l₁ l₂ : list (sigma β)} (p : l₁ ~ l₂) (d : l.nodup_keys) (d₁ : l₁.nodup_keys) (d₂ : l₂.nodup_keys), φ d d₁ = φ d d₂) :
  m₁.nodup_keys → m₂.nodup_keys → γ :=
krec_on m₁
  (λ l d, krec_on m₂ (λ l₂ d₂, φ d d₂) (λ l₁ l₂ p d₁ d₂, cr p d d₁ d₂))
  (λ l₁ l₂ p d₁ d₂, by congr; funext l; funext d; exact cl p d d₁ d₂)

@[simp] theorem krec_on₂_val {γ : Sort*} {l₁ l₂ : list (sigma β)} (d₁ : l₁.nodup_keys) (d₂ : l₂.nodup_keys)
  (φ : ∀ {l₁ l₂ : list (sigma β)}, l₁.nodup_keys → l₂.nodup_keys → γ)
  (cl : ∀ {l l₁ l₂ : list (sigma β)} (p : l₁ ~ l₂) (d : l.nodup_keys) (d₁ : l₁.nodup_keys) (d₂ : l₂.nodup_keys), φ d₁ d = φ d₂ d)
  (cr : ∀ {l l₁ l₂ : list (sigma β)} (p : l₁ ~ l₂) (d : l.nodup_keys) (d₁ : l₁.nodup_keys) (d₂ : l₂.nodup_keys), φ d d₁ = φ d d₂) :
  krec_on₂ ⟦l₁⟧ ⟦l₂⟧ @φ @cl @cr d₁ d₂ = φ d₁ d₂ :=
rfl

def keys : multiset (sigma β) → multiset α :=
map sigma.fst

@[simp] theorem keys_coe (l : list (sigma β)) :
  keys (l : multiset (sigma β)) = (l.keys : multiset α) :=
rfl

theorem mem_keys_of_mem {s : sigma β} {m : multiset (sigma β)} : s ∈ m → s.1 ∈ m.keys :=
mem_map_of_mem sigma.fst

theorem exists_mem_of_mem_keys {a : α} {m : multiset (sigma β)} (h : a ∈ m.keys) :
  ∃ (b : β a), sigma.mk a b ∈ m :=
let ⟨⟨a', b'⟩, m, e⟩ := mem_map.mp h in
eq.rec_on e (exists.intro b' m)

theorem mem_keys {a : α} {m : multiset (sigma β)} : a ∈ m.keys ↔ ∃ (b : β a), sigma.mk a b ∈ m :=
⟨exists_mem_of_mem_keys, λ ⟨_, h⟩, mem_keys_of_mem h⟩

theorem nodup_keys_iff {m : multiset (sigma β)} : m.keys.nodup ↔ m.nodup_keys :=
quotient.induction_on m $ λ _, list.nodup_keys_iff

section kerase
variables [decidable_eq α]

def kerase {m : multiset (sigma β)} (a : α) : m.nodup_keys → multiset (sigma β) :=
krec_on m (λ l _, (l.kerase a : multiset (sigma β))) $ λ _ _ p d₁ d₂,
  quotient.sound $ perm_kerase a d₁ d₂ p

@[simp] theorem kerase_val {l : list (sigma β)} (d : l.nodup_keys) (a : α) : @kerase _ _ _ ⟦l⟧ a d = ⟦l.kerase a⟧ :=
rfl

theorem kerase_le {m : multiset (sigma β)} (a : α) : ∀ (nd : m.nodup_keys), kerase a nd ≤ m :=
quotient.induction_on m $ λ l _, subperm_of_sublist (kerase_sublist a l)

@[simp] theorem nodup_keys_kerase {m : multiset (sigma β)} (a : α) :
  ∀ (nd : m.nodup_keys), (kerase a nd).nodup_keys :=
quotient.induction_on m $ λ _, nodup_keys_kerase a

theorem kerase_eq_filter {m : multiset (sigma β)} (a : α) :
  ∀ (nd : m.nodup_keys), kerase a nd = filter (λ x, x.1 ≠ a) m :=
quotient.induction_on m $ λ _, congr_arg coe ∘ nodup_keys_kerase_eq_filter a

@[simp] theorem mem_kerase {m : multiset (sigma β)} {s : sigma β} {a : α}
  (nd : m.nodup_keys) : s ∈ kerase a nd ↔ s.1 ≠ a ∧ s ∈ m :=
by rw kerase_eq_filter a nd; simp [and_comm]

@[simp] theorem mem_keys_kerase {a₁ a₂ : α} {m : multiset (sigma β)} (d : m.nodup_keys) :
  a₁ ∈ (kerase a₂ d).keys ↔ a₁ ≠ a₂ ∧ a₁ ∈ m.keys :=
by simp [keys]

theorem kerase_subset (a : α) {m : multiset (sigma β)} (nd : m.nodup_keys) :
  kerase a nd ⊆ m :=
subset_of_le (kerase_le a nd)

theorem mem_of_mem_kerase {s : sigma β} (a : α) {m : multiset (sigma β)}
  (nd : m.nodup_keys) : s ∈ kerase a nd → s ∈ m :=
mem_of_subset (kerase_subset _ _)

theorem kerase_comm {m : multiset (sigma β)} (a₁ a₂ : α) : ∀ (nd : m.nodup_keys),
  kerase a₂ (nodup_keys_kerase a₁ nd) = kerase a₁ (nodup_keys_kerase a₂ nd) :=
quotient.induction_on m $ λ l _, congr_arg coe $ l.kerase_comm a₁ a₂

theorem kerase_le_kerase {m₁ m₂ : multiset (sigma β)} (a : α) (h : m₁ ≤ m₂) :
  ∀ (d₁ : m₁.nodup_keys) (d₂ : m₂.nodup_keys), kerase a d₁ ≤ kerase a d₂ :=
le_induction_on h $ λ _ _ ih _ _, subperm_of_sublist $ kerase_sublist_kerase a ih

end kerase

section kerase_all
variables [decidable_eq α]

def kerase_all (m : multiset (sigma β)) (a : α) : multiset (sigma β) :=
quotient.lift_on m
  (λ l, (l.kerase_all a : multiset (sigma β)))
  (λ _ _, quotient.sound ∘ perm_kerase_all a)

end kerase_all

section kinsert
variables [decidable_eq α] {m : multiset (sigma β)}

def kinsert (s : sigma β) : m.nodup_keys → multiset (sigma β) :=
krec_on m (λ l _, (l.kinsert s : multiset (sigma β))) $ λ _ _ p d₁ d₂,
  quotient.sound $ perm_kinsert s d₁ d₂ p

@[simp] theorem kinsert_val {l : list (sigma β)} (d : l.nodup_keys) (s : sigma β) : @kinsert _ _ _ ⟦l⟧ s d = ⟦l.kinsert s⟧ :=
rfl

@[simp] theorem nodup_keys_kinsert (s : sigma β) :
  ∀ (d : m.nodup_keys), (kinsert s d).nodup_keys :=
quotient.induction_on m $ λ _, nodup_keys_kinsert s

@[simp] theorem mem_kinsert {m : multiset (sigma β)} {s₁ s₂ : sigma β} :
  ∀ (d : m.nodup_keys), s₁ ∈ kinsert s₂ d ↔ s₁ = s₂ ∨ s₁ ∈ kerase s₂.1 d :=
quotient.induction_on m $ λ _ _, mem_kinsert

@[simp] theorem mem_keys_kinsert {a : α} {s : sigma β}
  {m : multiset (sigma β)} (d : m.nodup_keys) :
  a ∈ (kinsert s d).keys ↔ a = s.1 ∨ a ∈ m.keys :=
by cases s with a' b'; by_cases h' : a = a'; simp [keys, exists_or_distrib, h']

end kinsert

section klookup
variables [decidable_eq α] {m : multiset (sigma β)}

def klookup (a : α) : m.nodup_keys → option (β a) :=
krec_on m (λ l _, l.klookup a) $ λ _ _ p d₁ d₂, perm_klookup a d₁ d₂ p

end klookup

section klookup_all
variables [decidable_eq α]

def klookup_all (a : α) (m : multiset (sigma β)) : multiset (β a) :=
quotient.lift_on m
  (λ l, (l.klookup_all a : multiset (β a)))
  (λ _ _, quotient.sound ∘ perm_klookup_all a)

end klookup_all

section kreplace
variables [decidable_eq α] {m : multiset (sigma β)}

def kreplace (s : sigma β) : m.nodup_keys → multiset (sigma β) :=
krec_on m (λ l _, (l.kreplace s : multiset (sigma β))) $ λ _ _ p d₁ d₂,
  quotient.sound $ perm_kreplace s d₁ d₂ p

@[simp] theorem nodup_keys_kreplace (s : sigma β) :
  ∀ (d : m.nodup_keys), (kreplace s d).nodup_keys :=
quotient.induction_on m $ λ _, nodup_keys_kreplace s

end kreplace

section kunion
variables [decidable_eq α] {a : α} {s : sigma β} {l₁ l₂ : list (sigma β)} {m m₁ m₂ : multiset (sigma β)}

def kunion : m₁.nodup_keys → m₂.nodup_keys → multiset (sigma β) :=
krec_on₂ m₁ m₂ (λ l₁ l₂ d₁ d₂, (l₁.kunion l₂ : multiset (sigma β)))
  (λ _ _ _ p d _ _, quotient.sound $ perm_kunion d d p (perm.refl _))
  (λ _ _ _ p _ d₁ d₂, quotient.sound $ perm_kunion d₁ d₂ (perm.refl _) p)

local infixr ` k∪ `:67 := kunion

@[simp] theorem kunion_val
   (d₁ : (l₁ : multiset (sigma β)).nodup_keys) (d₂ : (l₂ : multiset (sigma β)).nodup_keys) :
   d₁ k∪ d₂ = (l₁.kunion l₂ : multiset (sigma β)) :=
rfl

@[simp] theorem zero_kunion : ∀ (d : m.nodup_keys), nodup_keys_zero k∪ d = m :=
quotient.induction_on m $ λ _ _, rfl

@[simp] theorem kunion_zero : ∀ (d : m.nodup_keys), d k∪ nodup_keys_zero = m :=
quotient.induction_on m $ λ _ _, by simp [kunion_val]

@[simp] theorem mem_kunion : ∀ (d₁ : m₁.nodup_keys) (d₂ : m₂.nodup_keys),
  disjoint m₁.keys m₂.keys → (s ∈ d₁ k∪ d₂ ↔ s ∈ m₁ ∨ s ∈ m₂) :=
quotient.induction_on₂ m₁ m₂ $ λ _ _ _ _, mem_kunion_iff

@[simp] theorem nodup_keys_kunion : ∀ (d₁ : m₁.nodup_keys) (d₂ : m₂.nodup_keys),
  (d₁ k∪ d₂).nodup_keys :=
quotient.induction_on₂ m₁ m₂ $ λ _ _, nodup_keys_kunion

@[simp] theorem mem_keys_kunion : ∀ (d₁ : m₁.nodup_keys) (d₂ : m₂.nodup_keys),
  a ∈ keys (d₁ k∪ d₂) ↔ a ∈ m₁.keys ∨ a ∈ m₂.keys :=
quotient.induction_on₂ m₁ m₂ $ λ _ _ _ _, mem_keys_kunion

end kunion

section α₁α₂β₁β₂
variables {α₁ α₂ : Type u} {β₁ : α₁ → Type v} {β₂ : α₂ → Type v}

section map
variables {s : sigma β₁} {f : sigma β₁ → sigma β₂} {m m₁ m₂ : multiset (sigma β₁)}

theorem nodup_keys_map (fi : sigma.fst_injective f) : m.nodup_keys → (m.map f).nodup_keys :=
quotient.induction_on m $ λ _, nodup_keys_map fi

theorem mem_keys_map (ff : sigma.fst_functional f) : s.1 ∈ m.keys → (f s).1 ∈ (m.map f).keys :=
quotient.induction_on m $ λ _, mem_keys_map ff

theorem mem_keys_of_mem_keys_map (fi : sigma.fst_injective f) :
  (f s).1 ∈ (m.map f).keys → s.1 ∈ m.keys :=
quotient.induction_on m $ λ _, mem_keys_of_mem_keys_map fi

theorem mem_keys_map_iff (ff : sigma.fst_functional f) (fi : sigma.fst_injective f) :
  (f s).1 ∈ (m.map f).keys ↔ s.1 ∈ m.keys :=
⟨mem_keys_of_mem_keys_map fi, mem_keys_map ff⟩

theorem map_disjoint_keys (ff : sigma.fst_functional f) (fi : sigma.fst_injective f) :
  disjoint (m₁.map f).keys (m₂.map f).keys ↔ disjoint m₁.keys m₂.keys :=
quotient.induction_on₂ m₁ m₂ $ λ _ _, map_disjoint_keys ff fi

end map

section map_decidable_eq_α₁α₂
variables [decidable_eq α₁] [decidable_eq α₂]
variables {s : sigma β₁} {f : sigma β₁ → sigma β₂} {m : multiset (sigma β₁)}

@[simp] theorem map_kerase (ff : sigma.fst_functional f) (fi : sigma.fst_injective f) :
  ∀ (d : m.nodup_keys), (kerase s.1 d).map f = kerase (f s).1 (nodup_keys_map fi d) :=
quotient.induction_on m $ λ _ _, by simp [ff, fi]

@[simp] theorem map_kinsert (ff : sigma.fst_functional f) (fi : sigma.fst_injective f) :
  ∀ (d : m.nodup_keys), (kinsert s d).map f = kinsert (f s) (nodup_keys_map fi d) :=
quotient.induction_on m $ λ _ _, by simp [ff, fi]

end map_decidable_eq_α₁α₂

end α₁α₂β₁β₂

section map_id
variables {β₁ β₂ : α → Type v} {s : sigma β₁} {m : multiset (sigma β₁)}

@[simp] theorem map_id_keys (f : ∀ a, β₁ a → β₂ a) : (m.map (sigma.map id f)).keys = m.keys :=
by simp [keys]

end map_id

end multiset
