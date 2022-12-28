import lambda_calculus.utlc.basic
import lambda_calculus.utlc.reduction
import lambda_calculus.utlc.properties

namespace utlc

variables {n m k d : ℕ}
variables {f f' g g': utlc}

def substitution : utlc → ℕ → utlc → utlc
| (↓m) := λ n x, if m < n then ↓ m else if m = n then shift x n 0 else ↓ m.pred
| (Λ f) := λ n x, Λ (substitution f (n + 1) x)
| (f · g) := λ n x, (substitution f n x) · (substitution g n x)

theorem index_substitution : substitution (↓n) n f = shift f n 0 := by simp[substitution]

theorem id_substiution : substitution (↓0) 0 f = f := by rw[index_substitution, shift_zero]

theorem substitution_closed_below : f.closed_below n → n ≤ m → f.substitution m g = f :=
begin
  induction f generalizing n m,
  all_goals { simp [closed_below, substitution] },
  { intros _ _ _,
    exfalso,
    linarith },
  { intros p q,
    apply f_ih p,
    linarith },
  { intros p q nm,
    exact ⟨f_ih_f p nm, f_ih_g q nm⟩ }
end

theorem substitution_closed : f.closed → ∀ n, f.substitution n g = f :=
begin
  unfold closed,
  intros _ _,
  exact substitution_closed_below (by assumption) (nat.zero_le _),
end

theorem size_substiution : (f.substitution n g).size = f.size + (f.uses n) * (g.size - 1) :=
begin
  revert n,
  induction f with _ _ fh _ _ fh fh',
  all_goals { intro n, simp [substitution, uses, size] },
  { split_ifs,
    any_goals { linarith },
    any_goals { tauto },
    rw [size_shift, ← nat.add_sub_assoc, nat.add_sub_cancel_left],
    apply size_pos },
  rw [fh],
  ring,
  rw [fh, fh'],
  ring,
end

theorem uses_substitution_lt : m < n → (f.substitution n g).uses m = f.uses m :=
begin
  revert n m,
  induction f with x _ fh _ _ fh fh',
  all_goals { intros n m nm, simp [substitution, uses] },
  { split_ifs,
    any_goals { simp[uses, h_1] },
    any_goals { rw [uses_shift_zero] },
    any_goals { linarith },
    contrapose! h,
    simp at h,
    rw [← h] at nm,
    cases x,
    rwa [nat.pred_zero] at nm,
    rw [nat.pred_succ] at h nm,
    cases lt_trichotomy x.succ n with xn xn,
    assumption,
    cases xn,
    contrapose! h_1,
    rw [xn],
    rw [nat.succ_eq_add_one] at *,
    linarith
  },
  { rw [fh], linarith },
  { rw [fh nm, fh' nm] }
end

theorem uses_substitution_ge : n ≤ m → (f.substitution n g).uses m = f.uses m.succ + (f.uses n) * ((g.shift n 0).uses m) :=
begin
  revert n m,
  induction f with k f fh f f' fh fh',
  all_goals { intros n m nm },
  { simp [substitution],
    cases (nat.lt_trichotomy k n),
    simp [h, uses],
    cases (nat.lt_trichotomy k m),
    simp [show k ≠ m, by linarith, show k ≠ n, by linarith,
      show k ≠ m.succ, by linarith [nat.lt_succ_self m]],
    cases h_1,
    linarith,
    linarith,
    cases h,
    rw [h],
    simp [show (index n).uses n = 1, by simp[uses]],
    unfold uses,
    split_ifs,
    linarith [nat.lt_succ_self m],
    simp,
    simp [uses, show ¬ (k < n), by linarith,
        show (n ≠ k), by linarith,
        show (k ≠ n), by linarith,
        show k.pred = m ↔ k = m.succ, by {
          split,
          all_goals { intro h₁ },
          rw [← h₁, nat.succ_pred_eq_of_pos],
          apply nat.lt_of_le_of_lt (nat.zero_le _) h,
          rw [h₁, nat.pred_succ]
        }],
  },
  { simp [uses, substitution],
    rw [fh, ← nat.succ_add],
    apply show ∀ a b c : ℕ, a = b → c + a = c + b, by { intros _ _ _ h, rw[h] },
    apply show ∀ a b c : ℕ, a = b → c * a = c * b, by { intros _ _ _ h, rw[h] },
    rw [uses_shift_ge', uses_shift_ge',
        show (m + 1 - (n + 1) = (m - n)), by norm_num],
    all_goals { linarith },
  },
  simp [uses, substitution],
  rw [fh nm, fh' nm],
  ring
end

theorem substition_closed_below_le {f : utlc} {n k: ℕ}: f.closed_below n → n ≤ k → ∀ g, f.substitution k g = f :=
begin
  induction f with _ _ fh _ _ fh gh generalizing n k,
  all_goals { simp[closed_below, substitution] },
  { intros p q g r,
    exfalso,
    linarith },
  { intros p _ _,
    apply fh p,
    linarith },
  { intros p q r _,
    rw [fh p r, gh q r],
    exact ⟨rfl, rfl⟩ }
end

theorem substitution_closed_below_helper: f.closed_below n → g.closed_below m → (f.substitution k g).closed_below (max n (m + k)) :=
begin
  simp [uses_closed_below],
  intros p q x nx mkx,
  obtain h|h|h := nat.lt_trichotomy x k,
  { rw [uses_substitution_lt h],
    apply p _ nx },
  { simp [
      uses_substitution_ge (nat.le_refl k),
      uses_shift_ge' (nat.le_refl k),
      nat.succ_eq_add_one,
      h],
    split,
    apply p,
    linarith,
    right,
    apply q,
    linarith },
  { simp [uses_substitution_ge (nat.le_of_lt h),
      nat.succ_eq_add_one],
    split,
    apply p,
    linarith,
    right,
    rw [uses_shift_ge'],
    apply q,
    rw [show m = (m + k) - k, by simp],
    exact tsub_le_tsub_right mkx k,
    exact nat.le_of_lt h,
    simp [nat.le_of_lt h]
  }
end 

theorem substitution_closed_below'': f.closed_below (n+1) → g.closed_below 0 → (f.substitution n g).closed_below n :=
begin
  simp [uses_closed_below],
  intros p q m nm,
  { simp [uses_substitution_ge nm, nat.succ_eq_add_one],
    split,
    rw [p],
    linarith,
    right,
    rw [uses_shift_ge' nm],
    apply q,
    simp[nm] }
end

theorem shift_substitution' : (f.substitution (n + k) g).shift m k = (f.shift m k).substitution (n + m + k) g :=
begin
  induction f with i f hf f f' hf hf' generalizing g n m k,
  all_goals { simp[substitution, shift] },
  { split_ifs,
    simp[shift, substitution, h_1, show i < n + m + k, by linarith],
    simp[shift, substitution, h_1, show i + m < n + m + k, by linarith],
    simp[shift, substitution, h, show i < n + m + k, by linarith],
    exfalso, linarith,
    simp[substitution, h_1, nat.add_right_comm _ m],
    rw [shift_shift_add'],
    exfalso, linarith,
    simp [shift, substitution],
    cases i,
    rw [show n = 0, by linarith[nat.zero_le n],  show k = 0, by linarith[nat.zero_le k]] at h_1,
    contradiction,
    simp [nat.pred_succ],
    simp [nat.succ_eq_add_one] at *,
    have h_1: n + k < i + 1,
    { apply nat.lt_of_le_and_ne h, contrapose! h_1, rw [h_1] },
    simp [show ¬ (i + 1 + m < n + m + k), by linarith],
    simp [show i + 1 + m ≠ n + m + k, by linarith],
    simp [nat.add_right_comm _ 1],
    intro h,
    exfalso,
    linarith,
  },
  { simp [nat.add_assoc _ _ 1, hf] },
  { simp [hf, hf'] },
end

theorem shift_substitution_zero' : (f.substitution n g).shift m 0 = (f.shift m 0).substitution (n + m ) g :=
begin
  have h := @shift_substitution' n m 0 f g,
  simp at h,
  assumption
end

theorem shift_substitution : k ≤ m → (f.substitution k g).shift n m = ((f.shift n (m+1)).substitution k (g.shift n (m - k))) :=
begin
  induction f with f f hf f f' hf hf' generalizing g k n m,
  { simp [substitution, shift ],
    intro km,
    split_ifs,
    any_goals { simp[substitution, shift] },
    any_goals { split_ifs },
    any_goals { simp },
    any_goals { { exfalso, linarith } },
    apply shift_shift_comm' km,
    all_goals { cases f, cases k, contradiction },
    any_goals { { contrapose! h, apply nat.zero_lt_succ } },
    any_goals { { contrapose! h_3, rw [nat.pred_succ], rw [nat.succ_eq_add_one] at h_2, linarith} },
    simp [nat.succ_add, nat.pred_succ],
  },
  { simp [substitution, shift],
    intro km,
    rw [hf],
    norm_num,
    linarith },
  { simp [substitution, shift],
    intro km,
    simp [hf km, hf' km] }
end

theorem substitution_shift: k ≤ n + m → m ≤ k → (f.shift (n + 1) m).substitution k g = f.shift n m :=
begin
  induction f with _ _ fh _ _ fh fh' generalizing n m k g,
  all_goals { intros hkn hkm, simp [shift, substitution] },
  { split_ifs,
    simp [substitution, h, hkn, hkm],
    intro hkf,
    split_ifs,
    exfalso, linarith,
    exfalso, linarith,
    simp [substitution],
    split_ifs,
    exfalso, linarith,
    exfalso, linarith,
    simp [←nat.succ_eq_add_one, nat.add_succ] },
  { apply fh, linarith, linarith },
  { exact ⟨fh hkn hkm, fh' hkn hkm⟩ }
end

theorem substitution_shift_index: (f.shift (n + 1) m).substitution m ↓n = f.shift n m :=
begin
  -- intros p q,
  induction f with _ _ fh _ _ fh gh generalizing m,
  -- all_goals { intro nm },
  { simp [shift],
    split_ifs,
    simp [substitution],
    simp [show ¬ m ≤ f, by linarith],
    have h := le_of_not_lt h,
    simp [substitution,
          show ¬ (f + n + 1 < m), by linarith,
          show ¬ (f + n + 1 = m), by linarith,
          nat.pred_eq_sub_one,
          ←nat.add_assoc] },
  { simp [substitution, shift],
    apply fh },
  { simp [substitution, shift],
    refine ⟨fh, gh⟩ }
end
-- (f.substitution (n + k) g).shift m k = (f.shift m k).substitution (n + m + k) g
-- 
-- theorem substitution_shift_closed_below: f.closed_below (m + 1) → (f.shift n m).substitution (n + m) g = f.substitution m g :=
-- begin
--   have h := @shift_substitution' 0 n m f g,
--   simp at h,
--   rw [← h],


-- end
theorem substitution_shift_index': f.closed_below (k + 1) → f.substitution k ↓1 = f.shift 1 k :=
begin
  induction f with _ f fh f g fh gh generalizing k,
  { simp [closed_below, substitution, shift],
    split_ifs,
    simp,
    simp [h_1],
    ring,
    intro p,
    exfalso,
    have p := nat.le_of_lt_succ p,
    have p := nat.lt_of_le_and_ne p h_1,
    linarith[nat.zero_le f] },
  { simp [closed_below, substitution, shift, ← nat.add_assoc],
    apply fh },
  { simp [closed_below, substitution, shift],
    intros p q,
    exact ⟨fh p, gh q⟩ }
end

theorem substitution_shift_index_zero: (f.shift 1 (n+1)).substitution n ↓0 = f :=
begin
  induction f with _ _ fh _ _ fh gh generalizing n,
  { simp [shift],
    split_ifs,
    simp [substitution],
    intro p,
    simp [nat.eq_of_le_of_lt_succ p h, shift],
    have h := le_of_not_lt h,
    simp [substitution,
      show ¬ (f + 1 < n), by linarith,
      show ¬ (f + 1 = n), by linarith] },
  { simp [substitution, shift],
    apply fh },
  { simp [substitution, shift],
    refine ⟨by apply fh, by apply gh⟩ }
end 
-- theorem substitution_shift':

-- #eval ((index 2).shift 1 0).substitution 3 (index 4)
-- #eval ((index 2).substitution 3 (index 4)).shift 1 0

-- example : ∀ n : ℕ, ¬ n < 0 := by library_search

theorem substitution_substitution: (f.substitution m g).substitution (n + m) g' = (f.substitution (n+m+1) g').substitution m (g.substitution n g') :=
begin
  have lsub : ∀ x y z, substitution x y z = (λ a, substitution a y z) x, by simp,
  induction f with k _ fh _ _ fh fh' generalizing g g' n m,
  all_goals { simp [substitution] },
  { obtain hkm|hkm|hkm := nat.lt_trichotomy k m,
    simp [hkm, show k < n + m + 1, by linarith, substitution],
    by_contra' h,
    linarith,
    simp [hkm, show m < n + m + 1, by linarith, substitution],
    rw [shift_substitution_zero'],
    simp [show ¬ (k < m), by linarith, show k ≠ m, by linarith],
    cases k,
    exfalso, linarith [nat.zero_le m],
    simp[nat.pred_succ],
    simp [nat.succ_eq_add_one] at *,
    split_ifs,
    simp [substitution],
    simp [h],
    simp [show ¬ (k + 1 < m), by linarith, show k + 1 ≠ m, by linarith],
    simp [substitution, h_1],
    rw [substitution_shift],
    simp,
    apply nat.zero_le,
    simp [substitution, h, h_1],
    simp at h,
    simp [show ¬ k < m, by linarith],
    split_ifs,
    exfalso,
    apply h_1,
    simp [h_2],
    simp [h_2] at h,
    assumption,
    refl },
  { simp[nat.add_assoc _ m],
    apply fh },
  { simp[fh, fh'] }
end

theorem substitution_substitution': (f.substitution 0 g).substitution n g' = (f.substitution (n+1) g').substitution 0 (g.substitution n g') :=
begin
  have h := @substitution_substitution n 0 f g g',
  simp at h,
  assumption
end


@[simp]
def β_reduction : utlc → utlc → Prop
| (↓ _) := λ g, false
| (Λ _) := λ g, false
| (f1 · f2) := match f1 with
  | (↓ _) := λ g, false
  | (Λ f1) := λ g, substitution f1 0 f2 = g
  | (_ · _) := λ g, false
  end

instance β_reduction.decidable_rel : decidable_rel β_reduction :=
begin
  intros f _,
  cases f,
  any_goals { simp [β_reduction], apply_instance },
  cases f_f,
  all_goals { simp [β_reduction], apply_instance },
end

theorem lambda_β_reduction:
  β_reduction (Λ f) (Λ f') → β_reduction f f' := by simp

@[simp]
def β_reducible_step := reducible_step_of β_reduction

theorem lambda_β_reducible_step_iff:
  β_reducible_step (Λ f) (Λ f') ↔ β_reducible_step f f' := by simp [reducible_step]

@[simp]
def β_reduced_step : utlc → bool
| (↓ _) := true
| (Λ _) := true
| (f·g) := match f with
  | (↓ _) := true
  | (Λ _) := false
  | (f·g) := true
  end

@[simp]
def β_reduced := λ f, reduced f β_reduced_step

theorem lambda_β_reduced_iff:
  β_reduced f ↔ β_reduced (Λ f) := by simp [reduced]

theorem lambda_of_β_reduced_and_closed: f.β_reduced → f.closed → ∃ g, f = Λ g :=
begin
  induction f with _ f _ f g fh,
  { simp [closed, closed_below] },
  { intros _ _,
    use f,
    refl },
  simp [reduced, closed_below],
  cases f with _ _ f f',
  any_goals { { simp [reduced, closed_below] } },
  intros _ p _ q _,
  specialize fh p q,
  simp at fh,
  contradiction
end

end utlc