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

def dict_lookup [decidable_eq α] (a : α) (s : multiset (sigma β)) : multiset (β a) :=
quot.lift_on s (λ l, (l.dict_lookup_all a : multiset (β a)))
               (λ _ _, quot.sound ∘ perm_dict_lookup_all a)

def dict_erase [decidable_eq α] (a : α) (s : multiset (sigma β)) : multiset (sigma β) :=
quot.lift_on s (λ l, (l.dict_erase_all a : multiset (sigma β)))
               (λ _ _, quot.sound ∘ perm_dict_erase_all a)

end multiset
