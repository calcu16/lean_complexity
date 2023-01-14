import complexity.basic
import complexity.core
import tactic.linarith


namespace complexity
namespace nat

variables {mα mβ mγ: Type} [has_equiv mβ] [preorder mγ] [has_add mγ]
variables {m: model mα mβ mγ}

instance mul_complexity [has_encoding m ℕ] [has_encoding m (ℕ×ℕ)]
  [cf: has_complexity m
    (curry (compose
      prod.fst
      ((compose
        (uncurry (nat.iterate (fork (uncurry nat.add) prod.snd)))
        (((fork prod.snd (fork (@const ℕ (ℕ×ℕ) 0) prod.fst))))))))]:
  has_complexity m nat.mul :=
begin
  fconstructor,
  fconstructor,
  exact cf.value.cost,
  apply omega_equiv cf.value.proof,
  clear cf,
  ext1 n, ext1 m,
  apply (show ∀ (c: ℕ) (a: ℕ×ℕ) (b: ℕ), a = (b, c) → a.fst = b, by finish) n,
  simp [compose, flip, fork, to_fst, function.uncurry, const, curry, uncurry],
  induction m,
  { simp, },
  simp [function.iterate_succ', nat.mul_succ, m_ih],
end

end nat
end complexity