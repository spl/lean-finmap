import data.list.dict
import data.multiset

namespace multiset
universes u v
variables {α : Type u} {β : α → Type v}

open list

def nodup_keys (s : multiset (sigma β)) : Prop :=
quot.lift_on s nodup_keys (λ l₁ l₂ p, propext $ perm_nodup_keys p)

theorem nodup_of_nodup_keys {s : multiset (sigma β)} : s.nodup_keys → s.nodup :=
quot.induction_on s $ λ l, list.nodup_of_nodup_keys

@[simp] theorem nodup_keys_zero : @nodup_keys α β 0 := pairwise.nil _

def dict_lookups [decidable_eq α] (a : α) (s : multiset (sigma β)) : multiset (β a) :=
quot.lift_on s (λ l, (l.dict_lookups a : multiset (β a)))
               (λ l₁ l₂ p, quot.sound $ perm_dict_lookups a p)

end multiset
