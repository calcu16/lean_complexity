import lambda_calculus.utlc.basic
import lambda_calculus.utlc.reduction
import lambda_calculus.utlc.eta.basic
import logic.relation

namespace lambda_calculus
namespace utlc
namespace η

lemma normal_form_exists_helper: Π (n: ℕ), ∀ {f:utlc}, f.size ≤ n → ∃ g, f ↠η g ∧ reduced g
| (0) := begin
  intros f p,
  exfalso,
  linarith [size_pos f]
end
| (n+1) := begin
  intros f p,
  apply dite (reduced f),
  { intro q, exact ⟨f, by refl, q⟩ },
  rw [reduced_iff_not_reduction],
  simp,
  intros x fx,
  rcases normal_form_exists_helper n (nat.le_of_lt_succ (lt_of_lt_of_le (reduction_step_size_mono fx) p)) with ⟨y, hxy, hy⟩,
  exact ⟨y, relation.refl_trans_gen.head fx hxy, hy⟩,
end

theorem normal_form_exists (f: utlc): ∃ g, f ↠η g ∧ reduced g := normal_form_exists_helper f.size (le_refl _)

-- def normal_form: utlc → utlc
-- | (↓n) := ↓n
-- | (Λ (↓n)) := (Λ (↓n))
-- | (Λ (Λ f)) := Λ normal_form (Λ f)
-- | (Λ (f·g)) := if f.uses 0 = 0 ∧ g = ↓0
--   then normal_form f
--   else Λ normal_form f · normal_form g
-- | (f·g) := (normal_form f) · (normal_form g)

-- theorem blah (f g: utlc): head_reduced f → f ↠η g → head_reduced g :=
-- begin
--   induction f generalizing g,
--   { simp, intros _ p, rw[p], simp[head_reduced] },
--   { simp,
--     intros p q,
--     revert p,
--     induction q with x g hfx hxg,
--     simp,
--     intro p,
--     specialize q_ih p,
--     cases x,
--     { simp at hxg, contradiction },
--     swap,
--     { simp [dot_step_iff] at hxg,
--       rcases hxg with ⟨_, _, h, _⟩,
--       simp [h, head_reduced] },
--     simp at *,
--     cases x,
--     { simp[lambda_step_iff] at hxg, contradiction },
--     { rw [lambda_step_iff] at hxg,
--       simp at hxg,
--       rcases hxg with ⟨ y, hgy, hxy ⟩,
      

--     }
--   },
--   { simp,
--     intros p q,
--     rcases dot_reduction_cases q with ⟨x, y, hgxy, _, _⟩,
--     rw [hgxy],
--     simp [head_reduced],
--   }
-- end

-- def normal_form_exists (f: utlc): ∃ g, f ↠η g ∧ reduced g :=
-- begin
--   induction f,
--   { use f, simp },
--   { apply dite (head_reduced (Λ f_f)),
--     intro p,
--     cases f_ih with g h,
--     use Λ g,
--     refine ⟨ lambda_reduction_lambda h.left, _⟩,
--     rw [lambda_reduced], 
--     refine ⟨_, h.right⟩,

    

--   },
--   { cases f_ih_f with x hx,
--     cases f_ih_g with y hy,
--     use x·y,
--     split,
--     apply dot_reduction_dot hx.left hy.left,
--     simp,
--     exact ⟨hx.right, hy.right⟩ }
-- end

end η
end utlc
end lambda_calculus