import tactic.basic
import tactic.linarith
import tactic.hint

namespace data

inductive btree (α: Type*)
| leaf (v: α): btree
| intro (lhs rhs: btree): btree

namespace btree
variables {α β: Type*}

def height: btree α → (ℕ → ℕ → ℕ) → ℕ
| (btree.leaf _) := λ _, 0
| (btree.intro lhs rhs) := λ op, op (height lhs op) (height rhs op) + 1

@[simp]
def height_zero (op: ℕ → ℕ → ℕ) (a: α): height (btree.leaf a) op = 0 := rfl

theorem height_min_le_max (b: btree α): height b min ≤ height b max :=
by { induction b, { refl }, { simp [height, b_ih_lhs] } }

def balanced (b: btree α): bool := height b min = height b max

def balanced_def (b: btree α): balanced b ↔ (height b min = height b max) :=
by simp [balanced]

def balanced_def' (b: btree α): balanced b ↔ (height b max = height b min) :=
by rw [balanced_def, eq_comm]

theorem balanced_intro_min {b₀ b₁: btree α}:
  balanced (btree.intro b₀ b₁) → height b₀ min = height b₁ min :=
begin
  unfold balanced height,
  unfold_coes,
  simp [nat.add_comm 1],
  intro h,
  have hb₀ := height_min_le_max b₀,
  have hb₁ := height_min_le_max b₁,
  obtain hm|hm|hm := nat.lt_trichotomy (height b₀ min) (height b₁ min),
  exfalso,
  simp [min_eq_left (le_of_lt hm)] at h,
  linarith [le_of_max_le_right (le_of_eq h.symm)],
  assumption,
  exfalso,
  simp [min_eq_right (le_of_lt hm)] at h,
  linarith [le_of_max_le_left (le_of_eq h.symm)],
end

theorem balanced_intro_max {b₀ b₁: btree α}:
  balanced (btree.intro b₀ b₁) → height b₀ max = height b₁ max :=
begin
  intro p,
  have h := balanced_intro_min p,
  simp [balanced, height, h] at p,
  have h₁ := antisymm (le_of_max_le_right (le_of_eq p.symm)) (height_min_le_max _),
  rw [← h] at p,
  have h₀ := antisymm (le_of_max_le_left (le_of_eq p.symm)) (height_min_le_max _),
  rw [h₀, h₁, h],
end

@[simp]
theorem balanced_leaf (a: α): balanced (btree.leaf a) := by simp[balanced, height]

theorem balanced_intro (b₀ b₁: btree α):
  balanced (btree.intro b₀ b₁) = (balanced b₀ ∧ balanced b₁ ∧  height b₀ min = height b₁ min):=
begin
  apply show ∀ a b : bool, (a → b) → (b → a) → a = b,
  { intros a b,
    cases a;
    cases b;
    simp },
  { intro h,
    have hmin := balanced_intro_min h,
    have hmax := balanced_intro_max h,
    simp [balanced, height] at *,
    split,
    { simp [← hmin, ← hmax] at h, assumption },
    split,
    { simp [hmin, hmax] at h, assumption },
    simp [hmin] },
  simp [balanced, height],
  intros h₀ h₁ hmin,
  rw [← h₀, ← h₁, hmin],
  simp,
end

theorem balanced_of_intro {b₀ b₁: btree α}:
  balanced b₀ → balanced b₁ →  height b₀ min = height b₁ min → balanced (btree.intro b₀ b₁):=
begin intros p q h, rw[balanced_intro], simp[p, q, h] end

def has_element: btree α → α → Prop
| (btree.leaf a) := λ v, a = v
| (btree.intro lhs rhs) := λ v, has_element lhs v ∨ has_element rhs v

instance has_element.decidable (α: Type*) [decidable_eq α] (b: btree α) (v: α): decidable (has_element b v) :=
begin
  induction b,
  unfold has_element,
  apply_instance,
  unfold has_element,
  apply @or.decidable _ _ b_ih_lhs b_ih_rhs,
end

def map (f: α → β): btree α → btree β
| (btree.leaf a) := btree.leaf (f a)
| (btree.intro lhs rhs) := btree.intro (map lhs) (map rhs)

@[simp]
theorem map_height (f: α → β) (b: btree α) (op: ℕ → ℕ → ℕ): height (map f b) op = height b op :=
begin
  induction b,
  { simp [height, map] },
  { simp [height, b_ih_lhs, b_ih_rhs, map] },
end

@[simp]
theorem map_balanced (f: α → β) (b: btree α): balanced (map f b) = balanced b :=
by simp [balanced]

def extend_left' (a: α): ℕ → btree α → btree α
| 0 := λ t, t
| (n+1) := λ t, extend_left' n (btree.intro (map (λ _, a) t) t)

def extend_left (b: btree α) (a: α) (n: ℕ) := extend_left' a n b

theorem extend_left_height (b: btree α) {op: ℕ → ℕ → ℕ} (hop: ∀ a, op a a = a) (v: α) (n: ℕ):
  height (extend_left b v n) op = height b op + n :=
begin
  unfold extend_left,
  induction n generalizing b,
  { simp [extend_left', nat.add_zero] },
  simp [extend_left', height, n_ih, map_height, hop,
    nat.succ_eq_add_one, nat.add_comm 1, nat.add_right_comm _ 1, ← nat.add_assoc _ n_n 1, nat.zero_add]
end

@[simp]
theorem extend_left_max (b: btree α) (v: α) (n: ℕ) : height (extend_left b v n) max  = height b max + n :=
  extend_left_height b max_self v n

@[simp]
theorem extend_left_min (b: btree α) (v: α) (n: ℕ): height (extend_left b v n) min = height b min + n :=
  extend_left_height b min_self v n

@[simp]
theorem extend_left_balanced (b: btree α) (v: α) (n: ℕ): balanced (extend_left b v n) = balanced b :=
begin
  unfold extend_left,
  induction n generalizing b,
  refl,
  simp [extend_left', balanced_intro, n_ih],
end

theorem extend_left_balanced' (b: btree α) (v: α) (n: ℕ): balanced b → balanced (extend_left b v n) :=
by simp

def match_height (b₀ b₁: btree α) (op: ℕ → ℕ → ℕ) (v: α): btree α :=
  extend_left b₀ v (height b₁ op - height b₀ op)

theorem match_height_le {b₀ b₁: btree α}  (op: ℕ → ℕ → ℕ) (h₀: ∀ a, op a a = a) (h₁: height b₀ op ≤ height b₁ op) (v: α):
   height (match_height b₀ b₁ op v) op = height b₁ op :=
begin
  unfold match_height,
  rw [@extend_left_height _ _ op h₀, nat.add_comm, nat.sub_add_cancel h₁],
end

theorem match_height_ge {b₀ b₁: btree α} (op: ℕ → ℕ → ℕ) (h₀: ∀ a, op a a = a) (h₁: height b₁ op ≤ height b₀ op) (v: α):
   height (match_height b₀ b₁ op v) op = height b₀ op :=
begin
  unfold match_height,
  rw [@extend_left_height _ _ op h₀, nat.sub_eq_zero_of_le h₁, nat.add_zero],
end

theorem match_height_max {b₀ b₁: btree α} (op: ℕ → ℕ → ℕ) (h₀: ∀ a, op a a = a) (v: α):
   height (match_height b₀ b₁ op v) op = max (height b₀ op) (height b₁ op) :=
begin
  apply eq.symm,
  cases le_total (height b₀ op) (height b₁ op);
  simp [max_eq_iff, h, match_height_le op h₀ h, match_height_ge op h₀ h]
end

theorem match_height_sound (b₀ b₁: btree α) {op: ℕ → ℕ → ℕ} (h: ∀ a, op a a = a) (v: α):
  height (match_height b₀ b₁ op v) op = height (match_height b₁ b₀ op v) op :=
by cases le_total _ _; rw [@match_height_le _ _ _ op h h_1, @match_height_ge _ _ _ op h h_1]

theorem match_height_balanced {b₀: btree α} (op: ℕ → ℕ → ℕ) (v: α) (b₁: btree α):
  balanced (match_height b₀ b₁ op v) = balanced b₀ :=
by simp [match_height]

def add_with_carry: Π (b₀ b₁ : btree bool) (c: bool), (bool × btree bool)
| (btree.leaf a₀) (btree.leaf a₁) := λ c,
  ite a₀
    (ite a₁
      (ite c (tt, btree.leaf tt) (tt, btree.leaf ff))
      (ite c (tt, btree.leaf ff) (ff, btree.leaf tt)))
    (ite a₁
      (ite c (tt, btree.leaf ff) (ff, btree.leaf tt))
      (ite c (ff, btree.leaf tt) (ff, btree.leaf ff)))
| (btree.intro high₀ low₀) (btree.leaf a₁) := λ c, (ff, btree.intro high₀ low₀) -- garbage value
| (btree.leaf a₀) (btree.intro high₁ low₁) := λ c, (ff, btree.leaf a₀) -- garbage value
| (btree.intro high₀ low₀) (btree.intro high₁ low₁) := λ c,
  match add_with_carry low₀ low₁ c with
  | (c₁, low₂) := match add_with_carry high₀ high₁ c₁ with
  | (c₂, high₂) := (c₂, (btree.intro high₂ low₂)) end end

theorem add_with_carry_height (op: ℕ → ℕ → ℕ) (b₀ b₁: btree bool) (c: bool):
  height (add_with_carry b₀ b₁ c).snd op = height b₀ op :=
begin
  induction b₀ generalizing b₁ c;
  cases b₁,
  { cases b₀;
    cases b₁;
    cases c;
    simp [balanced, add_with_carry, height] },
  { simp [add_with_carry] },
  { simp [add_with_carry] },
  { cases h_rhs: (add_with_carry b₀_rhs b₁_rhs c) with c₁ b₂_rhs,
    cases h_lhs: (add_with_carry b₀_lhs b₁_lhs c₁) with c₂ b₂_lhs,
    specialize b₀_ih_rhs b₁_rhs c,
    specialize b₀_ih_lhs b₁_lhs c₁,
    rw [h_rhs] at b₀_ih_rhs,
    rw [h_lhs] at b₀_ih_lhs,
    unfold prod.snd at b₀_ih_lhs b₀_ih_rhs,  
    simp [add_with_carry, h_rhs, h_lhs, height, b₀_ih_rhs, b₀_ih_lhs] }
end

theorem add_with_carry_balanced (b₀ b₁: btree bool) (c: bool):
  balanced (add_with_carry b₀ b₁ c).snd = balanced b₀ :=
begin
  unfold balanced,
  rw [add_with_carry_height, add_with_carry_height],
end

-- def minimize [decidable_eq α]: btree α → α → btree α
-- | (btree.leaf v) := λ _, (btree.leaf v)
-- | (btree.intro lhs rhs) := λ a,
--   if has_element lhs a
--   then (btree.intro lhs rhs)
--   else minimize rhs a

-- def minimal_height [decidable_eq α]: (btree α) → α → bool
-- | (btree.leaf a) := λ _, tt
-- | (btree.intro lhs _) := λ a, has_element lhs a

-- @[simp]
-- theorem minimal_height_of_minimized  [decidable_eq α] (b: btree α) (a: α):
--   minimal_height (minimize b a) a :=
-- begin
--   induction b,
--   { simp [minimal_height, minimize] },
--   by_cases h: (has_element b_lhs a);
--   simp [minimize, minimal_height, h, b_ih_rhs],
-- end

-- theorem balanced_of_minimized [decidable_eq α] {b: btree α} (a: α) :
--   balanced b → balanced (minimize b a) :=
-- begin
--   induction b,
--   simp [balanced, minimize],
--   by_cases h: (has_element b_lhs a);
--   simp [minimize, minimal_height, h, balanced_intro];
--   intros hl hr h,
--   apply b_ih_rhs hr,
--   exact ⟨hl, hr, h⟩,
-- end
end btree

structure binary_nat :=
mk ::
  (height: ℕ)
  (data: btree bool)
  (proof: data.balanced ∧ height = data.height min)

namespace binary_nat

@[pattern] def leaf: bool → binary_nat
| bit := ⟨ 0, (btree.leaf bit), ⟨ rfl, rfl ⟩ ⟩

@[pattern] def intro: Π (x y: binary_nat), (x.height = y.height) → binary_nat
| ⟨hx, dx, pfbx, pfhx ⟩ ⟨hy, dy, pfby, pfhy ⟩ h :=
  ⟨ hx + 1,
    btree.intro dx dy,
    btree.balanced_of_intro pfbx pfby (by simp only [binary_nat.height] at h; simp [h, ← pfhx, ← pfhy]),
    by unfold btree.height; simp only [binary_nat.height] at h; simp [h, ← pfhx, ← pfhy] ⟩

def intro' (x y: binary_nat): binary_nat :=
  ⟨ max x.height y.height + 1,
    btree.intro (btree.match_height x.data y.data min ff) (btree.match_height y.data x.data min ff),
    begin
      apply btree.balanced_of_intro,
      rw [btree.match_height_balanced],
      apply x.proof.left,
      rw [btree.match_height_balanced],
      apply y.proof.left,
      apply btree.match_height_sound,
      apply min_self,
    end,
    begin
      unfold btree.height,
      rw [add_right_cancel_iff, btree.match_height_sound, min_self, x.proof.right, y.proof.right, btree.match_height_max min],
      apply max_comm,
      apply min_self,
      apply min_self,
    end ⟩

@[simp] theorem leaf_ne_intro (bit: bool) (x y: binary_nat) (h: x.height = y.height):
  leaf bit ≠ intro x y h :=
by rcases x with ⟨_, _, _, _⟩; rcases y with ⟨_, _, _, _⟩; simp [leaf, intro]

@[simp] theorem intro_ne_leaf (x y: binary_nat) (h: x.height = y.height) (bit: bool):
  intro x y h ≠ leaf bit := ne.symm (leaf_ne_intro bit x y h)




-- def iszero: binary_nat → Prop
-- | (leaf v) :=

-- def add (x y: binary_nat): binary_nat :=
-- begin
--   let x' := x.data.match_height y.data max ff,
--   let y' := y.data.match_height x.data max ff,
--   let cz := x'.add_with_carry y' ff,
--   apply ite cz.fst,
--   apply intro',
--   apply leaf tt,
--   fconstructor,
--   apply x.height,
--   apply cz.snd,
--   simp [cz, x', y', x.proof,
--     btree.add_with_carry_balanced, btree.match_height_balanced,
--     btree.add_with_carry_height],



-- end
--   apply intro,
--   rotate,
--   fconstructor,
--   apply x'.height + 1,
--   apply btree.intro,
--   apply btree.match_height (btree.leaf cz.fst) cz.snd max ff ,
--   apply cz.snd,
--   simp only [cz, x', y'],
--   refine ⟨btree.balanced_of_minimized _ _, btree.minimal_height_of_minimized _ _⟩,
--   simp [btree.balanced_intro, btree.match_height_balanced, btree.add_with_carry_balanced, x.proof,
--         btree.match_height, ← btree.balanced_def']
-- end

-- def mul (x y: binary_nat): binary_nat :=
-- | (binary_nat.leaf a) (binary_nat.leaf b) := sorry

end binary_nat

end data