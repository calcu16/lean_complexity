import lambda_calculus.utlc.basic
import lambda_calculus.utlc.reduction
import lambda_calculus.utlc.beta.church_rosser
import lambda_calculus.utlc.beta.basic

namespace lambda_calculus
namespace utlc
namespace β

local notation a `[` b `:=` c  `]` : 70 := has_substitution.substitution a b c

inductive reduction_strategy: Type
| normal: reduction_strategy
| applicative: reduction_strategy
| left: reduction_strategy → reduction_strategy
| right: reduction_strategy → reduction_strategy

def reduction_strategy_next: reduction_strategy → reduction_strategy
| (reduction_strategy.left s) := s
| (reduction_strategy.right s) := s
| s := s

def maybe_head_reduction_step: utlc → utlc
| (↓n) := ↓n
| (Λ f) := Λ f
| (f·g) := match f with
  | (↓n) := ↓n·g
  | (Λ f) := f[0:=g]
  | (f·f') := f·f'·g
  end

theorem maybe_head_reduction_step_is_eq_or_reduction_step (f: utlc):
  f = maybe_head_reduction_step f ∨ f →β (maybe_head_reduction_step f)  :=
begin
  cases f;
  simp[maybe_head_reduction_step],
  cases f_f;
  simp[maybe_head_reduction_step],
  right,
  apply lambda_dot_step_substitution
end

def strategic_head_reduction (head head' left left' right right': utlc): reduction_strategy → utlc
| reduction_strategy.normal := if ¬ head_reduced head then head' else if ¬ reduced left then left'·right else left·right'
| reduction_strategy.applicative := if ¬ reduced left then left'·right else if ¬ reduced right then left·right' else head'
| (reduction_strategy.left _) := left'·right
| (reduction_strategy.right _) := left·right'

theorem strategic_head_reduction_cases (head' left' right': utlc) (head left right: utlc) (s: reduction_strategy):
  strategic_head_reduction head head' left left' right right' s = head'
  ∨ strategic_head_reduction head head' left left' right right' s = left'·right
  ∨ strategic_head_reduction head head' left left' right right' s = left·right' :=
begin
  cases s,
  all_goals { simp[strategic_head_reduction] },
  all_goals { split_ifs },
  any_goals { simp[*] }
end

def strategic_reduction_step: utlc → reduction_strategy → utlc
| (↓n) := λ s, ↓n
| (Λ f) := λ s, Λ strategic_reduction_step f s
| (f·g) := λ s,
  strategic_head_reduction
    (f·g) (maybe_head_reduction_step (f·g))
    f (strategic_reduction_step f (reduction_strategy_next s))
    g (strategic_reduction_step g (reduction_strategy_next s))
    s

def normal_reduction_step: utlc → utlc := λf, strategic_reduction_step f reduction_strategy.normal

def applicative_reduction_step: utlc → utlc := λf, strategic_reduction_step f reduction_strategy.normal

theorem strategic_reduction_step_eq_or_reduction_step (f: utlc): ∀ strategy, f = strategic_reduction_step f strategy ∨ f →β (strategic_reduction_step f strategy) :=
begin
  intro s,
  induction f generalizing s,
  any_goals { simp [strategic_reduction_step] },
  { apply f_ih },
  obtain h|h|h := strategic_head_reduction_cases _ _ _ _ _ _ s,
  all_goals { rw[h] },
  { apply maybe_head_reduction_step_is_eq_or_reduction_step (f_f·f_g) },
  { cases f_ih_f _,
    left,
    simp,
    apply h_1,
    right,
    apply dot_step_dot_left h_1 },
  { cases f_ih_g _,
    left,
    simp,
    apply h_1,
    right,
    apply dot_step_dot_right h_1 },
end

attribute [simp] normal_reduction_step applicative_reduction_step strategic_reduction_step strategic_head_reduction maybe_head_reduction_step reduction_strategy_next

theorem reduction_of_strategic_reduction (f: utlc) (s: reduction_strategy): f ↠β strategic_reduction_step f s :=
begin
  cases strategic_reduction_step_eq_or_reduction_step f s,
  { rw [← h] },
  { exact relation.refl_trans_gen.single h}
end

theorem equiv_of_strategic_reduction (f: utlc) (s: reduction_strategy): f ≡β strategic_reduction_step f s :=
begin
  use strategic_reduction_step f s,
  refine ⟨reduction_of_strategic_reduction _ _, by refl⟩,
end

theorem equiv_of_strategic_reduction' (f: utlc) (s: reduction_strategy): strategic_reduction_step f s ≡β f :=
  equiv_symm (equiv_of_strategic_reduction _ _)

theorem trans_equiv_of_strategic_reduction {f g: utlc} {s: reduction_strategy}: strategic_reduction_step f s ≡β g → f ≡β g :=
  equiv_trans (equiv_of_strategic_reduction _ _)

theorem trans_equiv_of_strategic_reduction' {f g: utlc} {s: reduction_strategy}: f ≡β strategic_reduction_step g s → f ≡β g :=
  λ p, equiv_trans p (equiv_of_strategic_reduction' _ _)

def normal_iteration : ℕ → utlc → utlc
| 0 := λ f, f
| (n+1) := λ f, (normal_iteration n (normal_reduction_step f))

def reduction_of_normal_iterator (n: ℕ) {f : utlc}: f ↠β normal_iteration n f :=
begin
  induction n generalizing f,
  { simp [normal_iteration] },
  { simp [normal_iteration],
    apply trans _ n_ih,
    apply reduction_of_strategic_reduction }
end

theorem trans_equiv_of_normal_iteration (n: ℕ) {f g: utlc}: normal_iteration n f ≡β g → f ≡β g :=
begin
  intro p,
  cases p with x p,
  exact ⟨x, trans (reduction_of_normal_iterator _) p.left, p.right⟩
end

theorem trans_equiv_of_normal_iteration' (n: ℕ) {f g: utlc}: f ≡β normal_iteration n g → f ≡β g :=
  λ p, equiv_symm (trans_equiv_of_normal_iteration _ (equiv_symm p))

def normal_form (f g : utlc) := reduced g ∧ ∃ n, normal_iteration n f = g

end β
end utlc
end lambda_calculus