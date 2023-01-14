import lambda_calculus.distance
import lambda_calculus.utlc.basic
import lambda_calculus.utlc.beta.basic
import lambda_calculus.utlc.beta.distance
import lambda_calculus.utlc.encoding.basic
import lambda_calculus.utlc.encoding.nat

namespace lambda_calculus
namespace complexity

open utlc

lemma ftype_right (α: Type) {β β': Type}: β = β' → (α → β) = (α → β') :=
by { intro p, rw [p] }

lemma fcast: ∀ {α β γ: Type} (f: α → β) (a: α) (h: (β = γ)), (cast h (f a)) = (cast (ftype_right α h) f) a :=
 by { intros α β γ f a h, finish }

 lemma fcast': ∀ {α β γ: Type} (f: α → β) (a: α) (h: (β = γ)) (h': ((α → β) = (α → γ))), (cast h (f a)) = (cast h' f) a :=
 by { intros α β γ f a h, finish }

namespace complexity_le

inductive encodable_function: Type 1
| result: Π {α: Type}, has_encoding α → encodable_function
| application: Π {α: Type}, has_encoding α → encodable_function → encodable_function

@[simp] def unwrap: encodable_function → Type
| (@encodable_function.result α _) := α
| (@encodable_function.application α _ b) := α → unwrap b

def result_type : encodable_function → Type
| (@encodable_function.result α _) := α
| (encodable_function.application _ b) := result_type b

def is_encoded_function (α: Type) :=  { value: encodable_function // unwrap value = α }

class has_encodable_function (α: Type) := (value: is_encoded_function α)

@[simp] theorem unwrap_has_encodable {α: Type} (a: has_encodable_function α): unwrap a.value.1 = α := a.value.2
theorem unwrap_has_encodable' {α: Type} (a: has_encodable_function α): α = unwrap a.value.1 := a.value.2.symm

@[simp] theorem unwrap_is_encoded_function {α: Type} (a: is_encoded_function α): unwrap a.1 = α := a.2

def cast_unwrap {α: Type} [a: has_encodable_function α] (f: α): unwrap a.value.1 :=
  cast (unwrap_has_encodable' a) f

instance encodable_result (α: Type) [f: has_encoding α]:
    has_encodable_function α :=
  ⟨ ⟨ encodable_function.result f, by simp [unwrap] ⟩ ⟩


instance encodable_application (α: Type) [f: has_encoding α] (β: Type) [g: has_encodable_function β]:
    has_encodable_function (α → β) :=
  ⟨ ⟨ encodable_function.application f g.value.1,
    begin
      simp [unwrap],
      apply ftype_right,
      exact g.value.2,
    end ⟩ ⟩

@[simp] def cost_function: encodable_function → Type
| (encodable_function.result _) := ℕ
| (@encodable_function.application α _ b) := α → (cost_function b)

@[simp] def cost_function' (α : Type) [f: has_encodable_function α] := cost_function f.value.1

namespace cost_function
@[simp] def add_constant: Π {α: encodable_function}, cost_function α →  ℕ → cost_function α
| (encodable_function.result _) := λ n m, cast (by simp) ((cast (by simp) n) + m)
| (encodable_function.application _ _) := λ f m b, add_constant (f b) m

@[simp] def add: Π {α: encodable_function}, cost_function α → cost_function α → cost_function α
| (encodable_function.result _) := λ n m, cast (by simp) ((cast (by simp) n) + (cast (by simp) m))
| (encodable_function.application _ _) := λ f g b, add (f b) (g b)

@[simp] def always_le: Π {α: encodable_function}, cost_function α → cost_function α → Prop
| (encodable_function.result _) := λ n m, cast (by simp) n ≤ cast (by simp) m
| (encodable_function.application _ _) := λ f g, ∀ a, always_le (f a) (g a)

@[refl]
theorem always_le_refl {α: Type} [α_en: has_encodable_function α] (c: cost_function' α): always_le c c :=
begin
  unfreezingI {
    cases α_en,
    cases α_en with α' hα,
    induction α' with _ _ β β_en γ_en ih generalizing α c,
    rw [always_le],
    intro a,
    apply ih,
    simp at hα,
  }
end

end cost_function

def witness: Π (a : encodable_function), (unwrap a) → utlc → (cost_function a) → Prop
| (encodable_function.result e) := λ f g n, utlc.β.distance_le n g (@encode _ e f)
| (@encodable_function.application α e b) := λ f g n, ∀ a : α, witness b (f a) (g·(@encode α e a)) (n a)

theorem of_distance_le
  {a: encodable_function} {f f': unwrap a} {g g': utlc} (fc fc': cost_function a) (n: ℕ):
  β.distance_le n g' g → witness a f g fc → f = f' → (fc.add_constant n).always_le fc' →
  witness a f' g' fc' :=
begin
  induction a generalizing f f' g g' fc fc',
  all_goals { simp at * },
  { intros hg hw hf hfc,
    rw [← hf],
    apply distance_le_mono,
    apply distance_le_trans',
    apply hg,
    apply hw,
    refl,
    linarith },
  { intros hg hw hf hfc a,
    apply a_ih,
    apply utlc.β.dot_distance_le_dot_left,
    apply hg,
    apply hw,
    rw [hf],
    apply hfc,
  }
end
end complexity_le

open complexity_le
open complexity_le.cost_function

def complexity_le {α: Type} [a: complexity_le.has_encodable_function α] (f: α) (n: (complexity_le.cost_function' α)): Prop :=
  ∃ g: utlc, g.closed ∧ complexity_le.witness a.value.1 (cast (unwrap_has_encodable' a) f) g n

section -- these use the underlying lambda function definition
open utlc.encoding

theorem value_complexity_le {α: Type} [has_encoding α] (a: α): complexity_le a (0:ℕ) :=
begin
  use encode a,
  refine ⟨ by simp[identity], _ ⟩,
  apply distance_le_refl,
  apply has_β_reduction.step, -- why?
end

theorem partial_complexity_le {α β: Type} [has_encoding α] [complexity_le.has_encodable_function β]
  {f: α → β} {n: α → (complexity_le.cost_function' β)} (h: complexity_le f n)
  (a: α):
  complexity_le (f a) (n a) :=
begin
  rcases h with ⟨lc, hl, h⟩,
  use lc·(encode a),
  simp [closed],
  refine ⟨ hl , _ ⟩,
  specialize h a,
  rw [fcast],
  apply h
end

theorem const_complexity_le {α β: Type} [has_encoding α] [has_encodable_function β]
  {f: β} {nf: complexity_le.cost_function' β}
  {g: α → β} {ng: complexity_le.cost_function' (α → β)}:
  complexity_le f nf → (∀ a, f = g a) → (∀ a, (nf.add_constant 2).always_le (ng a)) →
  complexity_le g ng :=
begin
  intros h hf hn,
  rcases h with ⟨lc, hlc, h⟩,
  use true·lc,
  simp,
  refine ⟨⟨by simp[encoding.true], hlc⟩, _⟩,
  intro a,
  apply of_distance_le,
  apply true_distance_le,
  apply h,
  rw [hf a, fcast'],
  apply hn,
end

theorem compose_complexity_le
  (β: Type) {α γ: Type}
  [α_en: has_encoding α] [β_en: has_encoding β] [γ_en: has_encodable_function γ]
  {f: α → β} {nf: α → ℕ}
  {g: β → γ} (ng: β → cost_function' γ)
  {gf: α → γ} {ngf: α → cost_function' γ}:
  complexity_le (cast (by tauto) f) (cast (by tauto) nf) →
  complexity_le g ng →
  gf = g∘f →
  (∀ a, always_le (((ng (f a)).add_constant (3 + nf a))) (ngf a)) →
  complexity_le gf ngf :=
begin
  intros p q hgf hn,
  rcases p with ⟨lcp, hlcp, hp⟩,
  rcases q with ⟨lcq, hlcq, hq⟩,
  use compose·lcq·lcp,
  simp,
  refine ⟨⟨by simp [compose], hlcq, hlcp⟩, _⟩,
  intro a,
  apply of_distance_le,
  apply distance_le_trans,
  apply compose_distance_le,
  apply utlc.β.dot_distance_le_dot_right,
  apply hp a,
  apply hq,
  rw [hgf],
  simp,
  rw [← fcast', ← fcast'],
  rw [unwrap_is_encoded_function],
  simp,
  apply hn,
end

theorem curry_complexity_le {α β γ: Type} [has_encoding α] [has_encoding β] [hγ: has_encodable_function γ]
  {f: (α × β) → γ} {n: cost_function' ((α × β) → γ)} (h: complexity_le f n)
  {fc: α → β → γ} {nc: cost_function' (α → β → γ)} (hfc: fc = (λ a b, f (a, b))) (hnc: ∀ a b, ((n (a, b)).add_constant 3).always_le (nc a b))
  :
  complexity_le fc nc :=
begin
  rcases h with ⟨lc, hl, h⟩,
  use curry·lc,
  simp,
  refine ⟨closed_below_mono hl (nat.zero_le _), _⟩,
  intros a b,
  rw [hfc],
  specialize h (a, b),
  apply of_distance_le,
  apply curry_distance_le,
  apply h,
  rw [← fcast', ← fcast', ← fcast'],
  apply hγ.value.2.symm,
  rw [unwrap_has_encodable],
  apply hnc,
end

theorem uncurry_complexity_le {α β γ: Type} [has_encoding α] [has_encoding β] [hγ: has_encodable_function γ]
  {f: α → β → γ} {n: cost_function' (α → β → γ)} (h: complexity_le f n)
  {fc: (α × β) → γ} {nc: cost_function' ((α × β) → γ)} (hfc: fc = (λ ab, f ab.fst ab.snd)) (hnc: ∀ a b, (((n a b)).add_constant 3).always_le (nc (a, b))):
  complexity_le fc nc :=
begin
  rw [hfc],
  rcases h with ⟨lc, hl, h⟩,
  use uncurry·lc,
  simp,
  refine ⟨closed_below_mono hl (nat.zero_le _), _⟩,
  intro ab,
  cases ab with a b,
  specialize h a b,
  apply of_distance_le,
  apply uncurry_distance_le,
  apply h,
  rw [← fcast', ← fcast', ← fcast'],
  rw [unwrap_has_encodable],
  rw [unwrap_has_encodable],
  apply hnc,
end

theorem fork_complexity_le {α β γ: Type} [has_encoding α] [has_encoding β] [has_encoding γ]
  {f: α → β} {nf: α → ℕ} (hf: complexity_le f nf)
  {g: α → γ} {ng: α → ℕ} (hg: complexity_le g ng)
  {fg: α → (β × γ)} {nfg: α → ℕ} (hfg: fg = λ a, (f a, g a)) (hn: ∀ a, 3 + (nf a + ng a) ≤ nfg a):
  complexity_le fg nfg :=
begin
  rw [hfg],
  rcases hf with ⟨lcf, hlcf, hf⟩,
  rcases hg with ⟨lcg, hlcg, hg⟩,
  use fork·lcf·lcg,
  simp,
  refine ⟨ ⟨ by simp [fork, pair, tuple],hlcf, hlcg ⟩, _⟩,
  intro a,
  simp,
  apply distance_le_mono,
  apply distance_le_trans',
  apply fork_distance_le,
  simp [encoding.pair, encoding.tuple, encode, has_encoding.value],
  simp,
  apply utlc.β.lambda_distance_le_lambda,
  rw [shift_of_closed, shift_of_closed, shift_of_closed],
  apply distance_le_trans',
  apply utlc.β.dot_distance_le_dot_left,
  apply utlc.β.dot_distance_le_dot_right,
  apply hf,
  rw [shift_of_closed, shift_of_closed],
  apply utlc.β.dot_distance_le_dot_right,
  apply hg,
  any_goals { apply utlc.encoding.is_closed },
  any_goals { apply hlcf },
  any_goals { apply hlcg },
  refl,
  refl,
  apply hn,
end

theorem to_fst_complexity_le {α β: Type} [has_encoding α] [has_encoding β]
  {f: α → β} {n: α → ℕ} (h: complexity_le f n)
  {f': α → (β × α)} {n': α → ℕ} (hf: f' = λ a, (f a, a)) (hn: ∀ a, 2 + n a ≤ n' a):
  complexity_le f' n' :=
begin
  rw [hf],
  rcases h with ⟨lc, hlc, h⟩,
  use to_fst·lc,
  split,
  { simp [to_fst, pair, tuple],
    exact hlc },
  intro a,
  simp,
  apply distance_le_mono,
  apply distance_le_trans',
  apply to_fst_distance_le,
  simp [encoding.pair, encoding.tuple, encode, has_encoding.value],
  simp,
  apply utlc.β.lambda_distance_le_lambda,
  apply utlc.β.dot_distance_le_dot_left,
  apply utlc.β.dot_distance_le_dot_right,
  rw [shift_of_closed hlc,
      shift_of_closed, shift_of_closed],
  apply h a,
  repeat { apply is_closed },
  refl,
  apply hn,
end

theorem to_snd_complexity_le {α β: Type} [has_encoding α] [has_encoding β]
  {f: α → β} {n: α → ℕ} (h: complexity_le f n)
  {f': α → (α × β)} {n': α → ℕ} (hf: f' = λ a, (a, f a)) (hn: ∀ a, 2 + n a ≤ n' a):
  complexity_le f' n' :=
begin
  rw [hf],
  rcases h with ⟨lc, hlc, h⟩,
  use to_snd·lc,
  split,
  { simp [to_snd, pair, tuple],
    exact hlc },
  intro a,
  simp,
  apply distance_le_mono,
  apply distance_le_trans',
  apply to_snd_distance_le,
  simp [encoding.pair, encoding.tuple, encode, has_encoding.value],
  simp,
  apply utlc.β.lambda_distance_le_lambda,
  apply utlc.β.dot_distance_le_dot_right,
  rw [shift_of_closed hlc,
      shift_of_closed, shift_of_closed],
  apply h a,
  repeat { apply is_closed },
  refl,
  apply hn,
end

theorem swap_complexity_le {α β: Type} [has_encoding α] [has_encoding β]:
  complexity_le (@prod.swap α β) (λ ab, (4:ℕ)) :=
begin
  use swap,
  split,
  { simp [swap, pair, tuple], norm_num },
  intro a,
  simp,
  apply swap_distance_le,
end

theorem fst_complexity_le {α β: Type} [has_encoding α] [has_encoding β]:
  complexity_le (@prod.fst α β) (λ ab, (5:ℕ)) :=
begin
  use pipe·true,
  refine ⟨ by simp[pipe, encoding.true], _⟩,
  intro ab,
  apply distance_le_trans',
  apply pipe_distance_le,
  apply fst_distance_le,
  simp,
end

theorem snd_complexity_le {α β: Type} [has_encoding α] [has_encoding β]:
  complexity_le (@prod.snd α β) (λ ab, (5:ℕ)) :=
begin
  use pipe·false,
  refine ⟨ by simp[pipe, encoding.false], _⟩,
  intro ab,
  apply distance_le_trans',
  apply pipe_distance_le,
  apply snd_distance_le,
  simp,
end

namespace iteration_complexity_le
@[simp] def cost_function {α: Type}
  (fz: α) (nz: ℕ)
  (fi: α → α) (ni: α → ℕ): ℕ → ℕ
| 0 := nz + 5
| (n+1) := (ni (fi^[n] fz)) + (cost_function n) + 10

@[simp] def cost_function' {α: Type}
  (fi: α → α) (ni: α → ℕ): α → ℕ → ℕ := λ a, cost_function a 0 fi ni
end iteration_complexity_le

theorem iteration_complexity_le {α : Type} [has_encoding α]
  {fi: α → α} {ni: α → ℕ} (hi: complexity_le fi ni)
  {fiz: ℕ → α → α} (hfiz: fiz = nat.iterate fi)
  {niz : ℕ → α → ℕ} (hiz: ∀ n a, iteration_complexity_le.cost_function' fi ni a n ≤ niz n a):
    complexity_le fiz niz :=
begin
  rw [hfiz],
  rcases hi with ⟨lc, hlc, hi⟩,
  use nat.apply_iterate·lc,
  split,
  simp [nat.apply_iterate, closed],
  exact closed_below_mono hlc (nat.zero_le _),
  intro n,
  intro a,
  apply distance_le_mono _ (hiz n a),
  induction n,
  { simp,
    apply nat.apply_iterate_zero_distance_le },
  { simp,
    apply distance_le_trans',
    apply nat.apply_iterate_succ_distance_le,
    apply distance_le_trans',
    apply utlc.β.dot_distance_le_dot_right,
    apply n_ih,
    specialize hi (fi^[n_n] a),
    simp at hi,
    rw [← function.iterate_succ_apply' fi n_n a] at hi,
    apply hi,
    refl,
    simp,
    ring }
end

theorem iteration_complexity_le' {α : Type} [has_encoding α]
  {fi: α → α} {ni: α → ℕ} (hi: complexity_le fi ni)
  {fiz: α → ℕ → α} (hfiz: fiz = flip (nat.iterate fi))
  {niz : α → ℕ → ℕ} (hiz: ∀ a n, iteration_complexity_le.cost_function' fi ni a n ≤ niz a n):
    complexity_le fiz niz :=
begin
  rw [hfiz],
  rcases hi with ⟨lc, hlc, hi⟩,
  use nat.apply_iterate'·lc,
  split,
  simp [nat.apply_iterate', closed],
  exact closed_below_mono hlc (nat.zero_le _),
  intro a,
  intro n,
  apply distance_le_mono _ (hiz a n),
  induction n,
  { simp,
    apply nat.apply_iterate_zero_distance_le' },
  { simp,
    apply distance_le_trans',
    apply nat.apply_iterate_succ_distance_le',
    apply distance_le_trans',
    apply utlc.β.dot_distance_le_dot_right,
    apply n_ih,
    specialize hi (fi^[n_n] a),
    simp at hi,
    rw [← function.iterate_succ_apply' fi n_n a] at hi,
    apply hi,
    refl,
    simp,
    ring }
end
end -- using utlc.encoding

theorem flip_complexity_le {α β γ: Type} [has_encoding α] [has_encoding β] [has_encoding γ]
  {f: α → β → γ} {n: α → β → ℕ} (h: complexity_le f n)
  {ff: β → α → γ} {fn: β → α → ℕ} (hf: ff = function.swap f) (hn: ∀ b a, n a b + 13 ≤ fn b a):
  complexity_le ff fn :=
begin
  apply curry_complexity_le,
  apply compose_complexity_le (α×β),
  apply swap_complexity_le,
  apply uncurry_complexity_le,
  apply h,
  any_goals { refl },
  simp,
  intros a b,
  rw [show n a b + 3 = (λ ab:(α×β), n ab.fst ab.snd + 3) (a, b), by simp],
  ring_nf,
  intros a,
  simp,
  simp [hf],
  intros a b,
  simp,
  ring_nf,
  apply hn,
end


end complexity
end lambda_calculus