import data.list.dict
import data.multiset

namespace multiset
universes u v
variables {α : Type u} {β : α → Type v}

open function list

def nodup_keys (s : multiset (sigma β)) : Prop :=
quotient.lift_on s nodup_keys (λ _ _, propext ∘ perm_nodup_keys)

theorem nodup_of_nodup_keys {s : multiset (sigma β)} : s.nodup_keys → s.nodup :=
quotient.induction_on s $ λ _, nodup_of_nodup_keys

@[simp] theorem nodup_keys_zero : @nodup_keys α β 0 := pairwise.nil _

theorem nodup_keys_singleton : ∀ (s : sigma β), nodup_keys (s :: 0) :=
nodup_keys_singleton

def keys : multiset (sigma β) → multiset α :=
map sigma.fst

theorem nodup_keys_iff {s : multiset (sigma β)} : s.keys.nodup ↔ s.nodup_keys :=
quotient.induction_on s $ λ _, list.nodup_keys_iff

section kerase
variables [decidable_eq α]

def kerase {m : multiset (sigma β)} (a : α) : m.nodup_keys → multiset (sigma β) :=
quotient.hrec_on m (λ l _, (l.kerase a : multiset (sigma β))) $ λ l₁ l₂ p,
  have ⟦l₁⟧ = ⟦l₂⟧ := (coe_eq_coe l₁ l₂).mpr p,
  hfunext (by rw this) $
  λ h₁ h₂ _, heq_of_eq $ quotient.sound $ perm_kerase a h₁ h₂ p

theorem kerase_le {m : multiset (sigma β)} (a : α) : ∀ (nd : m.nodup_keys), kerase a nd ≤ m :=
quotient.induction_on m $ λ l _, subperm_of_sublist (kerase_sublist a l)

@[simp] theorem nodup_keys_kerase {m : multiset (sigma β)} (a : α) :
  ∀ (nd : m.nodup_keys), (kerase a nd).nodup_keys :=
quotient.induction_on m $ λ _, nodup_keys_kerase a

theorem kerase_eq_filter {m : multiset (sigma β)} (a : α) :
  ∀ (nd : m.nodup_keys), kerase a nd = filter (λ x, x.1 ≠ a) m :=
quotient.induction_on m $ λ _, congr_arg coe ∘ nodup_keys_kerase_eq_filter a

theorem mem_kerase {m : multiset (sigma β)} {s : sigma β} {a : α}
  (nd : m.nodup_keys) : s ∈ kerase a nd ↔ s.1 ≠ a ∧ s ∈ m :=
by rw kerase_eq_filter a nd; simp [and_comm]

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

def kerase_all (s : multiset (sigma β)) (a : α) : multiset (sigma β) :=
quotient.lift_on s
  (λ l, (l.kerase_all a : multiset (sigma β)))
  (λ _ _, quotient.sound ∘ perm_kerase_all a)

end kerase_all

section kinsert
variables [decidable_eq α] {m : multiset (sigma β)}

def kinsert (s : sigma β) : m.nodup_keys → multiset (sigma β) :=
quotient.hrec_on m (λ l _, (l.kinsert s : multiset (sigma β))) $ λ l₁ l₂ p,
  have ⟦l₁⟧ = ⟦l₂⟧ := (coe_eq_coe l₁ l₂).mpr p,
  hfunext (by rw this) $
  λ d₁ d₂ _, heq_of_eq $ quotient.sound $ perm_kinsert s d₁ d₂ p

@[simp] theorem nodup_keys_kinsert (s : sigma β) :
  ∀ (d : m.nodup_keys), (kinsert s d).nodup_keys :=
quotient.induction_on m $ λ _, nodup_keys_kinsert s

@[simp] theorem mem_kinsert {m : multiset (sigma β)} {s₁ s₂ : sigma β} :
  ∀ (d : m.nodup_keys), s₁ ∈ kinsert s₂ d ↔ s₁ = s₂ ∨ s₁ ∈ kerase s₂.1 d :=
quotient.induction_on m $ λ _ _, mem_kinsert

end kinsert

section klookup
variables [decidable_eq α] {m : multiset (sigma β)}

def klookup (a : α) : m.nodup_keys → option (β a) :=
quotient.hrec_on m (λ l _, l.klookup a) $ λ l₁ l₂ p,
  have ⟦l₁⟧ = ⟦l₂⟧ := (coe_eq_coe l₁ l₂).mpr p,
  hfunext (by rw this) $
  λ d₁ d₂ _, heq_of_eq $ perm_klookup a d₁ d₂ p

end klookup

section klookup_all
variables [decidable_eq α]

def klookup_all (a : α) (s : multiset (sigma β)) : multiset (β a) :=
quotient.lift_on s
  (λ l, (l.klookup_all a : multiset (β a)))
  (λ _ _, quotient.sound ∘ perm_klookup_all a)

end klookup_all

section kreplace
variables [decidable_eq α] {m : multiset (sigma β)}

def kreplace (s : sigma β) : m.nodup_keys → multiset (sigma β) :=
quotient.hrec_on m (λ l _, (l.kreplace s : multiset (sigma β))) $ λ l₁ l₂ p,
  have ⟦l₁⟧ = ⟦l₂⟧ := (coe_eq_coe l₁ l₂).mpr p,
  hfunext (by rw this) $
  λ d₁ d₂ _, heq_of_eq $ quotient.sound $ perm_kreplace s d₁ d₂ p

@[simp] theorem nodup_keys_kreplace (s : sigma β) :
  ∀ (d : m.nodup_keys), (kreplace s d).nodup_keys :=
quotient.induction_on m $ λ _, nodup_keys_kreplace s

end kreplace

section kunion
variables [decidable_eq α] {m₁ m₂ : multiset (sigma β)}

def kunion : m₁.nodup_keys → m₂.nodup_keys → multiset (sigma β) :=
@quotient.hrec_on₂ _ _ _ _
  (λ (m₁ m₂ : multiset (sigma β)), m₁.nodup_keys → m₂.nodup_keys → multiset (sigma β))
  m₁ m₂
  (λ l₁ l₂ (d₁ : l₁.nodup_keys) (d₂ : l₂.nodup_keys), l₁.kappend l₂) $
    λ l₁ l₂ l₃ l₄ p₁₃ p₂₄,
    hfunext (by rw perm_nodup_keys p₁₃) $
      λ (d₁ : l₁.nodup_keys) (d₃ : l₃.nodup_keys) _,
      hfunext (by rw perm_nodup_keys p₂₄) $
        λ (d₂ : l₂.nodup_keys) (d₄ : l₄.nodup_keys) _,
        heq_of_eq $ quotient.sound $ perm_kappend d₂ d₄ p₁₃ p₂₄

@[simp] theorem nodup_keys_kunion :
  ∀ (d₁ : m₁.nodup_keys) (d₂ : m₂.nodup_keys), (kunion d₁ d₂).nodup_keys :=
quotient.induction_on₂ m₁ m₂ $ λ _ _, nodup_keys_kappend

end kunion

section map
variables {α₁ : Type u} {β₁ : α₁ → Type v} {α₂ : Type u} {β₂ : α₂ → Type v} {f : sigma β₁ → sigma β₂}
variables {m : multiset (sigma β₁)}

theorem nodup_keys_map (fi : sigma.injective f) : m.nodup_keys → (m.map f).nodup_keys :=
quotient.induction_on m $ λ _, nodup_keys_map fi

end map

end multiset
