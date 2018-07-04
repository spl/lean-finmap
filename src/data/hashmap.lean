import data.alist
import data.pnat

universes u v

/-- A hash map with an `n`-sized array of association list buckets, a hash
function, and a proof that every bucket is correctly hashed. -/
structure hashmap (α : Type u) [decidable_eq α] (β : α → Type v) :=
/- Number of buckets (positive) -/
(n : ℕ+)
/- Hash function -/
(hash : α → fin n.val)
/- Array of association list buckets -/
(buckets : array n.val (alist α β))
/- Each bucket `i` contains members such that that hash of each member is `i`. -/
(hash_mem : ∀ {i a}, a ∈ (buckets.read i).keys → hash a = i)

/-- Default number of buckets (8) -/
def hashmap.default_n : ℕ+ :=
8

variables {α : Type u} [decidable_eq α] {β : α → Type v}

/-- Construct an empty hashmap with a given number of buckets (or the default)
and a hash function -/
def mk_hashmap (n : ℕ+ := hashmap.default_n) (f : α → fin n.val) : hashmap α β :=
⟨n, f, mk_array n.val ∅, λ _ _ h, by cases h⟩

/-- Create a hash function from a function `f : α → ℕ` using the result modulo
the number of buckets -/
def hashmap.mk_mod_hash (n : ℕ+ := hashmap.default_n) (f : α → ℕ) (a : α) : fin n.val :=
⟨f a % n.val, nat.mod_lt _ n.property⟩

/-- Construct an empty hashmap with a given number of buckets (or the default)
and a modulo hash function -/
def mk_mod_hashmap (n : ℕ+ := hashmap.default_n) (f : α → ℕ) : hashmap α β :=
mk_hashmap n (hashmap.mk_mod_hash n f)
