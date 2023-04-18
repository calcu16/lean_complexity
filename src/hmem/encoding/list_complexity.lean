import hmem.stack
import hmem.encoding.list
import hmem.split_cost
import complexity.basic

variables {μ: Type*} [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]

namespace hmem
namespace encoding

theorem split_complexity {α: Type*} [complexity.has_encoding (runtime_model μ) α] (l: list α):
  (split μ).has_time_cost (encode l) (5 * l.length + 3) :=
begin
  induction l,
  { apply thunk.time_cost_of_split',
    apply thunk.has_trace.split_cost,
    apply split_has_trace,
    unfold trace.has_call_cost,
    apply list.sum_le_nil',
    unfold split split_trace thunk.current trace.prog_calls trace.branch trace.calls program.calls_on_branch instruction.ifz instruction.const,
    refl,
    apply list.sum_le_nil,
    simp only [list.length, split_trace, mul_zero, add_zero] },
  { apply thunk.time_cost_of_split',
    apply thunk.has_trace.split_cost,
    apply split_has_trace,
    apply list.sum_le_nil',
    unfold split split_trace thunk.current trace.prog_calls trace.branch trace.calls program.calls_on_branch instruction.ifz instruction.const instruction.swap,
    refl,
    apply list.sum_le_cons l_ih list.sum_le_nil,
    unfold split_trace list.length,
    ring }
end

theorem merge_complexity {α: Type*} [complexity.has_encoding (runtime_model μ) α]
  (fcmp: α → α → Prop) [dcmp: decidable_rel fcmp]
  {pcmp: program μ} (hcmp: ∀ (a b: α), pcmp.has_result (encode (a, b)) (encode (dcmp a b)))
  {c: ℕ}
  {as bs: list α}
  (hcost: ∀ a b, a ∈ as → b ∈ bs → pcmp.has_time_cost (encode (a, b)) c):
  (merge pcmp).has_time_cost (encode (as, bs)) ((10 + c) * (as.length + bs.length) + 3) :=
begin
  induction h:(as.length + bs.length) using nat.strong_induction_on with n ih generalizing as bs,
  cases as with a as,
  { apply program.time_cost_mono,
    apply thunk.time_cost_of_split',
    apply thunk.has_trace.split_cost,
    apply merge_has_trace fcmp hcmp,
    apply list.sum_le_nil',
    unfold merge merge_trace thunk.current trace.prog_calls trace.branch trace.calls program.calls_on_branch instruction.ifz instruction.const instruction.move,
    refl,
    apply list.sum_le_nil,
    unfold merge_trace,
    ring_nf,
    apply le_add_left,
    apply le_add_left,
    apply le_refl, },
  cases bs with b bs,
  { apply program.time_cost_mono,
    apply thunk.time_cost_of_split',
    apply thunk.has_trace.split_cost,
    apply merge_has_trace fcmp hcmp,
    apply list.sum_le_nil',
    unfold merge merge_trace thunk.current trace.prog_calls trace.branch trace.calls program.calls_on_branch instruction.ifz instruction.const instruction.move,
    refl,
    apply list.sum_le_nil,
    unfold merge_trace,
    rw [← h],
    unfold list.length,
    ring_nf,
    apply le_add_left,
    linarith },
  by_cases hab:fcmp a b,
  { apply program.time_cost_mono,
    apply thunk.time_cost_of_split',
    apply thunk.has_trace.split_cost,
    apply merge_has_trace fcmp hcmp,
    { simp only [merge_trace, hab, if_true],
      unfold merge merge_trace trace.has_call_cost thunk.current trace.prog_calls trace.branch trace.calls program.calls_on_branch instruction.ifz instruction.const instruction.move instruction.copy,
      apply list.sum_le_cons,
      apply hcost,
      apply list.mem_cons_self,
      apply list.mem_cons_self,
      rw [to_bool_ff (not_not.mpr trivial)],
      apply list.sum_le_nil',
      unfold program.calls_on_branch,
      refl },
    { simp only [merge_trace, hab, if_true],
      apply list.sum_le_cons,
      apply ih _ _ _ rfl,
      simpa only [← h, list.length, ← add_assoc, add_lt_add_iff_right] using nat.lt_succ_self _,
      { intros a b ha hb,
        apply hcost _ _ _ hb,
        apply list.mem_cons_of_mem _ ha },
      apply list.sum_le_nil },
    refl,
    simp only [hab, if_true, ← h, list.length, merge_trace, list.length],
    linarith },
  { apply program.time_cost_mono,
    apply thunk.time_cost_of_split',
    apply thunk.has_trace.split_cost,
    apply merge_has_trace fcmp hcmp,
    { simp only [merge_trace, hab, if_false],
      unfold merge merge_trace trace.has_call_cost thunk.current trace.prog_calls trace.branch trace.calls program.calls_on_branch instruction.ifz instruction.const instruction.move instruction.copy,
      apply list.sum_le_cons,
      apply hcost,
      apply list.mem_cons_self,
      apply list.mem_cons_self,
      rw [to_bool_tt not_false],
      apply list.sum_le_nil',
      unfold program.calls_on_branch,
      refl },
    { simp only [merge_trace, hab, if_false],
      apply list.sum_le_cons,
      apply ih _ _ _ rfl,
      simpa only [← h, list.length, ← add_assoc, add_lt_add_iff_right] using nat.lt_succ_self _,
      { intros a b ha hb,
        apply hcost _ _ ha,
        apply list.mem_cons_of_mem _ hb },
      apply list.sum_le_nil },
    refl,
    simp only [hab, if_false, ← h, list.length, merge_trace, list.length],
    linarith },
end

theorem list.perm_split {α: Type*} : ∀ (l : list α), l ~ l.split.fst ++ l.split.snd
| [] := by simp
| (a::l) :=
begin
  unfold list.split,
  cases h:l.split,
  unfold list.split,
  simp,
  refine (list.perm_split _).trans _,
  simp [h],
  exact list.perm_append_comm,
end

theorem list.perm_split'  {α: Type*} {l l₀ l₁: list α}:
  l.split = (l₀, l₁) → l ~ l₀ ++ l₁ :=
begin
  intro heq,
  have h := list.perm_split l,
  rw [heq] at h,
  apply h,
end

theorem list.length_split {α: Type*} (l: list α):
  l.split.fst.length = (l.length + 1) / 2 ∧ l.split.snd.length = l.length / 2 :=
begin
  induction l,
  { simp [nat.div_eq_zero] },
  cases h:l_tl.split,
  simpa [h, nat.add_assoc, nat.succ_eq_add_one] using and.symm l_ih,
end

theorem list.length_split' {α: Type*} {l l₀ l₁: list α}:
  l.split = (l₀, l₁) → l₀.length = (l.length + 1) / 2 ∧ l₁.length = l.length / 2 :=
begin
  intro heq,
  have h := list.length_split l,
  rw [heq] at h,
  apply h,
end

theorem list.length_split_le' {α: Type*} {l l₀ l₁: list α}:
  l.split = (l₀, l₁) → l₁.length ≤ l₀.length :=
begin
  intro heq,
  simp only [list.length_split' heq],
  apply nat.div_le_div_right,
  apply nat.le_succ,
end

theorem merge_sort_complexity {α: Type*} [complexity.has_encoding (runtime_model μ) α]
  (fcmp: α → α → Prop) [dcmp: decidable_rel fcmp]
  {pcmp: program μ} (hcmp: ∀ (a b: α), pcmp.has_result (encode (a, b)) (encode (dcmp a b)))
  {c: ℕ} {l: list α}
  (hcost: ∀ a b, a ∈ l → b ∈ l → pcmp.has_time_cost (encode (a, b)) c):
  (merge_sort pcmp).has_time_cost (encode l) ((22 + c) * l.length * (nat.clog 2 l.length) + 2) :=
begin
  induction h:l.length using nat.strong_induction_on with n ih generalizing l,
  cases hsplit:l.split with l₀ l₁,
  cases l with a l,
  { rw [← h, list.length, mul_zero, zero_mul, zero_add],
    apply program.time_cost_mono,
    apply thunk.time_cost_of_split',
    apply thunk.has_trace.split_cost,
    apply merge_sort_has_trace fcmp hcmp,
    apply list.sum_le_nil',
    unfold merge_sort merge_sort_trace trace.prog_calls program.calls_on_branch thunk.current instruction.ifz trace.branch,
    refl,
    apply list.sum_le_nil,
    unfold merge_sort_trace,
    linarith },
  cases l with b l,
  { rw [← h, list.length, list.length, zero_add, nat.clog_one_right, mul_zero, zero_add],
    apply program.time_cost_mono,
    apply thunk.time_cost_of_split',
    apply thunk.has_trace.split_cost,
    apply merge_sort_has_trace fcmp hcmp,
    apply list.sum_le_nil',
    unfold merge_sort merge_sort_trace trace.prog_calls program.calls_on_branch thunk.current instruction.ifz trace.branch,
    refl,
    apply list.sum_le_nil,
    unfold merge_sort_trace,
    linarith },
  apply program.time_cost_mono,
  apply thunk.time_cost_of_split',
  apply thunk.has_trace.split_cost,
  apply merge_sort_has_trace fcmp hcmp,
  { simp only [merge_sort_trace, hsplit],
    unfold trace.has_call_cost merge_sort merge_sort_trace trace.prog_calls program.calls_on_branch thunk.current instruction.ifz trace.branch,  
    apply list.sum_le_cons,
    apply split_complexity,
    apply list.sum_le_cons,
    apply merge_complexity fcmp hcmp,
    { intros a b ha hb,
      apply hcost,
      rw [list.perm.mem_iff (list.perm_merge_sort _ _)] at ha hb,
      rw [list.perm.mem_iff (list.perm_split _), hsplit, list.mem_append],
      exact or.inl ha,
      rw [list.perm.mem_iff (list.perm_merge_sort _ _)] at ha hb,
      rw [list.perm.mem_iff (list.perm_split _), hsplit, list.mem_append],
      exact or.inr hb },
    apply list.sum_le_nil },
  { simp only [merge_sort_trace, hsplit],
    apply list.sum_le_cons,
    { apply ih _ _ _ rfl,
      rw [← h],
      apply (list.length_split_lt hsplit).left,
      intros a b ha hb,
      apply hcost,
      rw [list.perm.mem_iff (list.perm_split _), hsplit, list.mem_append],
      exact or.inl ha,
      rw [list.perm.mem_iff (list.perm_split _), hsplit, list.mem_append],
      exact or.inl hb },
    apply list.sum_le_cons,
    { apply ih _ _ _ rfl,
      rw [← h],
      apply (list.length_split_lt hsplit).right,
      intros a b ha hb,
      apply hcost,
      rw [list.perm.mem_iff (list.perm_split _), hsplit, list.mem_append],
      exact or.inr ha,
      rw [list.perm.mem_iff (list.perm_split _), hsplit, list.mem_append],
      exact or.inr hb },
    exact list.sum_le_nil },
  simp only [merge_sort_trace, hsplit],
  ring_nf,
  rw [nat.add_left_comm],
  apply add_le_add,
  { apply nat.mul_le_mul_right,
    rw [← nat.add_assoc,
      list.perm.length_eq (list.perm_merge_sort fcmp _),
      list.perm.length_eq (list.perm_merge_sort fcmp _),
      ← list.length_append, list.perm.length_eq (list.perm_split' hsplit).symm],
    apply nat.le_trans,
    { apply nat.add_le_add_left,
      apply nat.add_le_add_left,
      apply nat.mul_le_mul_right,
      apply nat.clog_mono_right,
      apply list.length_split_le' hsplit },
    rw [← mul_add, ← list.length_append, list.perm.length_eq (list.perm_split' hsplit).symm, add_comm, ← nat.succ_mul, h],
    apply nat.mul_le_mul_right,
    rw [(list.length_split' hsplit).left, h,
      show ∀ n : ℕ, n + 1 = n + 2 - 1,
      begin
          intro _,
          simp [← nat.succ_eq_add_one],
      end,
      nat.succ_eq_add_one,
      ← nat.clog_of_two_le (one_lt_two)],
    rw [← h, list.length, list.length],
    apply nat.succ_le_succ,
    apply nat.succ_le_succ,
    apply nat.zero_le },
    rw [list.perm.length_eq (list.perm_merge_sort fcmp _), list.perm.length_eq (list.perm_merge_sort fcmp _),
      show ∀ n m, (m * l₀.length + (m * l₁.length + n)) = m * (l₀.length + l₁.length) + n,
      by simp only [nat.add_assoc, mul_add, eq_self_iff_true, forall_2_true_iff],
      ← list.length_append, list.perm.length_eq (list.perm_split' hsplit).symm, h],
    ring_nf,
    apply nat.le_trans,
    { apply add_le_add_left,
      apply add_le_add_left,
      apply add_le_add_right,
      apply nat.mul_le_mul_left,
      apply nat.clog_mono_right,
      apply list.length_split_le' hsplit },
    rw [mul_right_comm, mul_right_comm _ l₁.length,
      show ∀ n m, (m * l₀.length + (m * l₁.length + n)) = m * (l₀.length + l₁.length) + n,
      by simp only [nat.add_assoc, mul_add, eq_self_iff_true, forall_2_true_iff],
      ← list.length_append, list.perm.length_eq (list.perm_split' hsplit).symm, h,
      (list.length_split' hsplit).left, h,
      show ∀ n : ℕ, n + 1 = n + 2 - 1,
      begin
          intro _,
          simp [← nat.succ_eq_add_one],
      end,
      show ∀ n: ℕ, n + 2 - 1 = n + 1,
      by simp only [← nat.succ_eq_add_one, ← nat.pred_eq_sub_one, nat.pred_succ, eq_self_iff_true, forall_true_iff]],
    rw [← @nat.add_le_add_iff_right (7 * n)],
    ring_nf,
    rw [← nat.mul_succ, nat.succ_eq_add_one,
      show n + 1 = n + 2 - 1,
      by simp [← nat.succ_eq_add_one],
      ← nat.clog_of_two_le (one_lt_two),
      add_mul, nat.add_assoc],
    apply add_le_add_left,
    rw [← h, list.length, list.length],
    linarith,
    rw [← h, list.length, list.length],
    apply nat.succ_le_succ,
    apply nat.succ_le_succ,
    apply zero_le _,
end

end encoding
end hmem