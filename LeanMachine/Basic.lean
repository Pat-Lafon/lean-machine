@[grind]
inductive MyList where
    | nil : MyList
    | cons : Int → MyList → MyList

@[simp, grind]
def myLength (l : MyList) : Nat :=
    match l with
    | MyList.nil => 0
    | MyList.cons _ t => 1 + myLength t

@[simp, grind]
def emp (l : MyList) : Bool :=
    match l with
    | MyList.nil => true
    | MyList.cons _ _ => false

@[simp, grind]
def list_mem (l : MyList) (n : Int) : Bool :=
    match l with
    | MyList.nil => false
    | MyList.cons h t => (h == n) || list_mem t n

@[simp, grind]
def sorted (l : MyList) : Bool :=
    match l with
    | MyList.nil => true
    | MyList.cons _ MyList.nil => true
    | MyList.cons n (MyList.cons n' t) => (n <= n') && sorted (MyList.cons n' t)

@[simp, grind]
def uniq (l : MyList) : Bool :=
    match l with
    | MyList.nil => true
    | MyList.cons n t => uniq t && !list_mem t n

@[simp, grind]
def hd_eq (l : MyList) (x : Int) : Prop :=
    match l with
    | MyList.nil => False
    | MyList.cons h _ => h = x

@[simp, grind]
def tl_eq (l : MyList) (l1 : MyList) : Prop :=
    match l with
    | MyList.nil => False
    | MyList.cons _ t => t = l1

-- Length Theorems
-- Note: asserting that length is in fact a natural number
theorem len_pos : ∀ l, myLength l ≥ 0 := by
    grind

@[grind]
theorem len_0_nil : ∀ l, (myLength l = 0 -> l = MyList.nil) := by
    grind

@[grind]
theorem len_nil_0 : ∀ l, (l = MyList.nil -> myLength l = 0) := by
    grind

theorem len_emp_len_0 : ∀ l n, ((l = MyList.nil ∧ myLength l = n) -> n = 0) := by
    grind

@[grind]
theorem len_positive_is_not_emp : ∀ l n, ((myLength l = n ∧ n > 0) -> l ≠ MyList.nil) := by
    grind

theorem list_len_geq_0 : ∀ l n, myLength l = n → n ≥ 0 := by
grind

@[grind]
theorem list_tl_len_plus_1 : ∀ l l1 n, (tl_eq l l1 → (myLength l1 = n ↔ myLength l = (n + 1))) := by
    grind

-- Maybe redundate predicate theorems
@[grind]
theorem list_emp_no_hd : ∀ l x, (emp l = true → ¬hd_eq l x) := by
    grind

@[grind]
theorem list_emp_no_tl : ∀ l l1, (emp l = true → ¬tl_eq l l1) := by
    grind

/- theorem list_no_emp_exists_tl : ∀ l, ∃ l1, (emp l = false → tl_eq l l1) := by
    intro l
    induction l with
    | nil => grind
    | cons h t ih => grind -/

/- theorem list_no_emp_exists_hd : ∀ l, ∃ x, (emp l = false → hd_eq l x) := by
    sorry -/

@[grind]
theorem list_hd_no_emp : ∀ l x, (hd_eq l x → emp l = false) := by
    grind

@[grind]
theorem list_tl_no_emp : ∀ l l1, (tl_eq l l1 → emp l = false) := by
    grind

theorem list_hd_leq : ∀ l x y, ((x ≤ y ∧ hd_eq l y) → (∀ u, (hd_eq l u → x ≤ u))) := by
    grind


-- Membership Theorems

@[grind]
theorem list_hd_is_mem : ∀ l u, (hd_eq l u → list_mem l u = true) := by
    grind

@[grind]
theorem list_emp_no_mem : ∀ l u, (emp l = true → list_mem l u = false) := by
    grind

@[grind]
theorem list_tl_mem : ∀ l l1 u, ((tl_eq l l1 ∧ list_mem l1 u = true) → list_mem l u = true) := by
    grind

@[grind]
theorem list_cons_mem : ∀ l l1 u, ((tl_eq l l1 ∧ list_mem l u = true) → (list_mem l1 u = true ∨ hd_eq l u)) := by
    grind

-- Sorted Theorems

@[grind]
theorem list_emp_sorted : ∀ l, (emp l = true → sorted l = true) := by
    grind

@[grind]
theorem list_zero_sorted : ∀ l, (myLength l = 0 → MyList.nil = l) := by
    grind

@[grind]
theorem list_zero_sorted_2 : ∀ l, (MyList.nil = l → myLength l = 0 ) := by
    grind

@[grind]
theorem list_single_sorted : ∀ l, (myLength l = 1 → sorted l = true) := by
    grind

@[grind]
theorem list_tl_sorted : ∀ l l1, ((tl_eq l l1 ∧ sorted l = true) → sorted l1 = true) := by
    grind

@[grind]
theorem list_hd_sorted : ∀ l l1 x y, ((tl_eq l l1 ∧ sorted l = true) → (emp l1 = true ∨ ((hd_eq l1 y ∧ hd_eq l x) → x ≤ y))) := by
    grind

@[grind]
theorem list_sorted_hd : ∀ l l1 x y, ((tl_eq l l1 ∧ (sorted l1 = true ∧ (hd_eq l y ∧ (hd_eq l1 x ∧ y ≤ x)))) → sorted l = true) := by
    grind

-- Uniqueness Theorems

@[grind]
theorem list_emp_unique : ∀ l, emp l = true → uniq l = true := by
    grind

@[grind]
theorem list_tl_unique : ∀ l l1, (tl_eq l l1 ∧ uniq l = true) → uniq l1 = true := by
    grind

@[grind]
theorem list_hd_unique : ∀ l l1 x, (tl_eq l l1 ∧ (uniq l = true ∧ hd_eq l x)) → list_mem l1 x = false := by
    grind

@[grind]
theorem list_hd_tl_unique : ∀ l l1 x, (tl_eq l l1 ∧ (uniq l1 = true ∧ (hd_eq l x ∧ list_mem l1 x = false))) → uniq l = true := by
    grind

/- theorem list_unique_hd_tl : ∀ l, ∃ l1 x, ((uniq l = true ∧ emp l = false) → (hd_eq l x ∧ (tl_eq l l1 ∧ list_mem l1 x = false))) := by
    intro l
    induction l with
    | nil => grind
    | cons h t ih => grind -/
