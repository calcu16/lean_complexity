import lambda_calculus.utlc.basic
import lambda_calculus.utlc.reduction
import lambda_calculus.utlc.beta.basic
import lambda_calculus.utlc.beta.church_rosser
import logic.relation

namespace utlc

infix ` ↠ᵦ `: 50 := relation.refl_trans_gen β_reducible_step
infix ` ≈ᵦ `: 50 := relation.join (relation.refl_trans_gen β_reducible_step)

@[refl]
theorem β_equiv_refl (f : utlc): f ≈ᵦ f :=
  ⟨f, relation.refl_trans_gen.refl, relation.refl_trans_gen.refl⟩

@[symm]
theorem β_equiv_symm {a b: utlc}: a ≈ᵦ b → b ≈ᵦ a :=
begin
  apply relation.symmetric_join
end

@[trans]
theorem β_equiv_trans {a b c : utlc}: a ≈ᵦ b → b ≈ᵦ c → a ≈ᵦ c :=
begin
  apply relation.transitive_join,
  apply relation.refl_trans_gen.trans,
  apply β_church_rosser,
end

theorem β_equiv_lambda {f g : utlc}: f ≈ᵦ g → Λ f ≈ᵦ Λ g :=
begin
  intro p,
  cases p with c p,
  use Λ c,
  exact ⟨β_trans_lambda p.left, β_trans_lambda p.right⟩
end

theorem β_equiv_application {f f' g g': utlc}: f ≈ᵦ f' → g ≈ᵦ g' → f·g ≈ᵦ f'·g' :=
begin
  intros p q,
  cases p with c p,
  cases q with d q,
  use c·d,
  exact ⟨β_trans_application p.left q.left, β_trans_application p.right q.right⟩
end


theorem β_equiv_application_left {f f' g: utlc}: f ≈ᵦ f' → f·g ≈ᵦ f'·g :=
begin
  intro p,
  apply β_equiv_application p,
  refl,
end


theorem β_equiv_application_right {f g g': utlc}: g ≈ᵦ g' → f·g ≈ᵦ f·g' :=
begin
  apply β_equiv_application,
  refl
end

end utlc