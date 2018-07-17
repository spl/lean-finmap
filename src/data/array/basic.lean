namespace array
variables {α : Type*} {n : ℕ}

def modify (a : array n α) (i : fin n) (f : α → α) : array n α :=
a.write i $ f $ a.read i

@[simp] theorem modify_id (a : array n α) (i : fin n) : a.modify i id = a :=
array.ext $ λ j, by by_cases h : i = j; simp [h, modify]

/-
theorem read_modify (a : array n α) (i j : fin n) (f : α → α) :
  (a.modify i f).read j = 
-/

end array
