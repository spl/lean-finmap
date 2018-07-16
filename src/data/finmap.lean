import data.finset data.multiset.dict

open multiset

universes u v

structure finmap (α : Type u) (β : α → Type v) : Type (max u v) :=
(val : multiset (sigma β))
(nodup_keys : val.nodup_keys)

namespace finmap
variables {α : Type u} {β : α → Type v}

section val
variables {f g : finmap α β}

theorem eq_of_veq : ∀ {f g : finmap α β}, f.val = g.val → f = g
| ⟨s, _⟩ ⟨t, _⟩ h := by congr; exact h

@[simp] theorem val_inj : f.val = g.val ↔ f = g :=
⟨eq_of_veq, congr_arg _⟩

end val

instance has_decidable_eq [decidable_eq α] [∀ a, decidable_eq (β a)] :
  decidable_eq (finmap α β)
| f g := decidable_of_iff _ val_inj

/- membership -/

section mem

instance : has_mem (sigma β) (finmap α β) :=
⟨λ s f, s ∈ f.val⟩

variables {s : sigma β} {m : multiset (sigma β)} {f : finmap α β}

theorem mem_def : s ∈ f ↔ s ∈ f.val :=
iff.rfl

@[simp] theorem mem_mk {nd : m.nodup_keys} :
  @has_mem.mem _ (finmap α β) _ s (finmap.mk m nd) ↔ s ∈ m :=
iff.rfl

instance decidable_mem [decidable_eq α] [∀ a, decidable_eq (β a)] (s : sigma β) (f : finmap α β) :
  decidable (s ∈ f) :=
multiset.decidable_mem _ _

end mem

/- set coercion -/

section set

def to_set (s : finmap α β) : set (sigma β) := {x | x ∈ s}

instance : has_lift (finmap α β) (set (sigma β)) := ⟨to_set⟩

variables {s : sigma β} {f : finmap α β}

@[simp] lemma mem_coe : s ∈ (↑f : set (sigma β)) ↔ s ∈ f :=
iff.rfl

end set

/- extensionality -/

section ext
variables {f g : finmap α β}

theorem ext : f = g ↔ ∀ s, s ∈ f ↔ s ∈ g :=
val_inj.symm.trans $
  nodup_ext (nodup_of_nodup_keys f.nodup_keys) (nodup_of_nodup_keys g.nodup_keys)

@[extensionality]
theorem ext' : (∀ s, s ∈ f ↔ s ∈ g) → f = g :=
ext.mpr

end ext

/- subset -/

section subset

instance : has_subset (finmap α β) :=
⟨λ f g, ∀ ⦃s : sigma β⦄, s ∈ f → s ∈ g⟩

variables {s : sigma β} {f g h : finmap α β}

theorem subset_def : f ⊆ g ↔ f.val ⊆ g.val :=
iff.rfl

@[simp] theorem subset.refl (f : finmap α β) : f ⊆ f :=
subset.refl _

theorem subset.trans : f ⊆ g → g ⊆ h → f ⊆ h :=
subset.trans

theorem mem_of_subset : f ⊆ g → s ∈ f → s ∈ g :=
mem_of_subset

theorem subset.antisymm (H₁ : f ⊆ g) (H₂ : g ⊆ f) : f = g :=
ext.mpr $ λ a, ⟨@H₁ a, @H₂ a⟩

theorem subset_iff : f ⊆ g ↔ ∀ ⦃x⦄, x ∈ f → x ∈ g :=
iff.rfl

@[simp] theorem coe_subset : (↑f : set (sigma β)) ⊆ ↑g ↔ f ⊆ g :=
iff.rfl

@[simp] theorem val_le_iff : f.val ≤ g.val ↔ f ⊆ g :=
le_iff_subset (nodup_of_nodup_keys f.nodup_keys)

instance : has_ssubset (finmap α β) :=
⟨λa b, a ⊆ b ∧ ¬ b ⊆ a⟩

instance : partial_order (finmap α β) :=
{ le := (⊆),
  lt := (⊂),
  le_refl := subset.refl,
  le_trans := @subset.trans _ _,
  le_antisymm := @subset.antisymm _ _ }

@[simp] theorem le_iff_subset : f ≤ g ↔ f ⊆ g := iff.rfl
@[simp] theorem lt_iff_ssubset : f < g ↔ f ⊂ g := iff.rfl

@[simp] theorem val_lt_iff : f.val < g.val ↔ f ⊂ g :=
and_congr val_le_iff $ not_congr val_le_iff

end subset

/- empty -/

section empty

protected def empty : finmap α β :=
⟨0, nodup_keys_zero⟩

instance : has_emptyc (finmap α β) :=
⟨finmap.empty⟩

instance : inhabited (finmap α β) :=
⟨∅⟩

@[simp] theorem empty_val : (∅ : finmap α β).val = 0 :=
rfl

@[simp] theorem not_mem_empty (s : sigma β) : s ∉ (∅ : finmap α β) :=
id

@[simp] theorem ne_empty_of_mem {a : sigma β} {s : finmap α β} (h : a ∈ s) : s ≠ ∅
| e := not_mem_empty a $ e ▸ h

@[simp] theorem empty_subset (s : finmap α β) : ∅ ⊆ s :=
zero_subset _

theorem eq_empty_of_forall_not_mem {s : finmap α β} (H : ∀x, x ∉ s) : s = ∅ :=
eq_of_veq (eq_zero_of_forall_not_mem H)

@[simp] theorem val_eq_zero {s : finmap α β} : s.val = 0 ↔ s = ∅ :=
@val_inj _ _ s ∅

theorem subset_empty {s : finmap α β} : s ⊆ ∅ ↔ s = ∅ :=
subset_zero.trans val_eq_zero

theorem exists_mem_of_ne_empty {s : finmap α β} (h : s ≠ ∅) : ∃ a : sigma β, a ∈ s :=
exists_mem_of_ne_zero (mt val_eq_zero.mp h)

@[simp] lemma coe_empty : ↑(∅ : finmap α β) = (∅ : set (sigma β)) :=
by simp [set.set_eq_def]

end empty

/- singleton -/

/-- `singleton a` is the set `{a}` containing `a` and nothing else. -/
def singleton (s : sigma β) : finmap α β :=
⟨⟦[s]⟧, nodup_keys_singleton s⟩

local prefix `ι`:90 := singleton

@[simp] theorem singleton_val (a : sigma β) : (ι a).val = a :: 0 := rfl

@[simp] theorem mem_singleton {a b : sigma β} : b ∈ ι a ↔ b = a :=
by simp [singleton]

theorem not_mem_singleton {a b : sigma β} : a ∉ ι b ↔ a ≠ b := by simp

theorem mem_singleton_self (a : sigma β) : a ∈ ι a := by simp

theorem singleton_inj {a b : sigma β} : ι a = ι b ↔ a = b :=
⟨λ h, mem_singleton.mp (h ▸ mem_singleton_self _), congr_arg _⟩

@[simp] theorem singleton_ne_empty (a : sigma β) : ι a ≠ ∅ := ne_empty_of_mem (mem_singleton_self _)

@[simp] lemma coe_singleton (a : sigma β) : ↑(ι a) = ({a} : set (sigma β)) :=
by simp [set.set_eq_def]

/- erase -/

section erase
variables [decidable_eq α]

def erase (f : finmap α β) (a : α) : finmap α β :=
⟨kerase a f.nodup_keys, nodup_keys_kerase a f.nodup_keys⟩

@[simp] theorem erase_val (f : finmap α β) (a : α) : (f.erase a).val = kerase a f.nodup_keys :=
rfl

@[simp] theorem mem_erase {s : sigma β} {a : α} {f : finmap α β} :
  s ∈ f.erase a ↔ s.1 ≠ a ∧ s ∈ f :=
mem_kerase f.nodup_keys

theorem not_mem_erase (a : α) (b : β a) (f : finmap α β) : sigma.mk a b ∉ f.erase a :=
by simp

@[simp] theorem erase_empty (a : α) : erase ∅ a = (∅ : finmap α β) :=
rfl

theorem ne_of_mem_erase {s : sigma β} {a : α} {f : finmap α β} : s ∈ f.erase a → s.1 ≠ a :=
by simp {contextual := tt}

theorem erase_subset_erase (a : α) {f g : finmap α β} (h : f ⊆ g) : f.erase a ⊆ g.erase a :=
val_le_iff.mp $ kerase_le_kerase _ (val_le_iff.mpr h) _ _

theorem erase_subset (a : α) {f : finmap α β} : f.erase a ⊆ f :=
kerase_subset a f.nodup_keys

end erase

/- insert -/

section insert
variables [decidable_eq α]

protected def insert (s : sigma β) (f : finmap α β) : finmap α β :=
⟨kinsert s f.nodup_keys, nodup_keys_kinsert s f.nodup_keys⟩

instance : has_insert (sigma β) (finmap α β) :=
⟨finmap.insert⟩

@[simp] theorem insert_val (s : sigma β) (f : finmap α β) :
  (f.insert s).val = kinsert s f.nodup_keys :=
rfl

@[simp] theorem insert_empty (s : sigma β) : insert s (∅ : finmap α β) = {s} :=
rfl

@[simp] theorem mem_insert (s₁ s₂ : sigma β) (f : finmap α β) :
  s₁ ∈ f.insert s₂ ↔ s₁ = s₂ ∨ s₁ ∈ f.erase s₂.1 :=
mem_kinsert f.nodup_keys

end insert

/- lookup -/

section lookup
variables [decidable_eq α]

def lookup (a : α) (f : finmap α β) : option (β a) :=
klookup a f.nodup_keys

theorem lookup_empty (a : α) : lookup a (∅ : finmap α β) = none :=
rfl

end lookup

/- replace -/

section replace
variables [decidable_eq α]

def replace (s : sigma β) (f : finmap α β) : finmap α β :=
⟨kreplace s f.nodup_keys, nodup_keys_kreplace s f.nodup_keys⟩

@[simp] theorem replace_empty (s : sigma β) : replace s ∅ = ∅ :=
rfl

end replace

/- union -/

section union
variables [decidable_eq α]

protected def union (f : finmap α β) (g : finmap α β) : finmap α β :=
⟨kunion f.nodup_keys g.nodup_keys, nodup_keys_kunion f.nodup_keys g.nodup_keys⟩

instance : has_union (finmap α β) :=
⟨finmap.union⟩

end union

/- map -/

section map
variables {α₁ : Type u} {β₁ : α₁ → Type v} {α₂ : Type u} {β₂ : α₂ → Type v} {g : sigma β₁ → sigma β₂}

def map (gi : sigma.fst_injective g) (f : finmap α₁ β₁) : finmap α₂ β₂ :=
⟨f.val.map g, nodup_keys_map gi f.nodup_keys⟩

@[simp] theorem map_empty (gi : sigma.fst_injective g) : map gi ∅ = ∅ :=
rfl

end map

/- map_val -/

section map_val
variables {β₁ β₂ : α → Type v}

def map_val (g : ∀ (a : α), β₁ a → β₂ a) : finmap α β₁ → finmap α β₂ :=
map (sigma.fst_injective_snd g)

@[simp] theorem map_val_empty (g : ∀ (a : α), β₁ a → β₂ a) : map_val g ∅ = ∅ :=
rfl

end map_val

/- keys -/

section keys

def keys (f : finmap α β) : finset α :=
⟨f.val.keys, nodup_keys_iff.mpr f.nodup_keys⟩

@[simp] theorem keys_empty : keys (∅ : finmap α β) = ∅ :=
rfl

end keys

end finmap
