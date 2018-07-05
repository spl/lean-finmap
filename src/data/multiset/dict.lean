import data.list.dict
import data.multiset

namespace multiset
universes u v
variables {α : Type u} {β : α → Type v}

open list

def nodup_keys (s : multiset (sigma β)) : Prop :=
quot.lift_on s nodup_keys (λ _ _, propext ∘ perm_nodup_keys)

theorem nodup_of_nodup_keys {s : multiset (sigma β)} : s.nodup_keys → s.nodup :=
quot.induction_on s $ λ _, nodup_of_nodup_keys

@[simp] theorem nodup_keys_zero : @nodup_keys α β 0 := pairwise.nil _

def keys [decidable_eq α] : multiset (sigma β) → multiset α :=
map sigma.fst

theorem nodup_keys_iff [decidable_eq α] {s : multiset (sigma β)} :
  s.keys.nodup ↔ s.nodup_keys :=
quot.induction_on s $ λ _, list.nodup_keys_iff

def klookup [decidable_eq α] (a : α) (s : multiset (sigma β)) : multiset (β a) :=
quot.lift_on s
  (λ l, (l.klookup_all a : multiset (β a)))
  (λ _ _, quot.sound ∘ perm_klookup_all a)

def kerase [decidable_eq α] (a : α) (s : multiset (sigma β)) : multiset (sigma β) :=
quot.lift_on s
  (λ l, (l.kerase_all a : multiset (sigma β)))
  (λ _ _, quot.sound ∘ perm_kerase_all a)

end multiset
