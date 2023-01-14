import complexity.basic

def fork {α β γ: Type}: (α → β) → (α → γ) → α → (β × γ) := λ f g a, (f a, g a)

def to_fst {α β: Type}: (α → β) → α → (β × α) := (flip fork) id

def to_snd {α β: Type}: (α → β) → α → (α × β) := fork id

def curry {α β γ: Type} (f: (α × β) → γ):= λ a b, f (a, b)

def uncurry {α β γ: Type} (f: α → β → γ):= λ ab : (α × β), f ab.fst ab.snd

def const {α: Type} (β: Type) (a: α) := λ _:β, a

def compose {α β γ: Type} (f: β → γ) (g: α → β) := λ a, f (g a)

namespace complexity

variables {mα mβ mγ: Type} [has_equiv mβ] [preorder mγ] [has_add mγ]
variables {m: model mα mβ mγ}

instance to_fst_complexity {α β: Type}
  [has_encoding m α] [has_encoding m β] [has_encoding m (β × α)]
  (f: α → β) [has_complexity m f]
  [cf: has_complexity m ((flip fork) id f: α → (β × α))]:
  has_complexity m (to_fst f) := ⟨ ⟨ cf.value.cost, by rw [to_fst]; apply cf.value.proof ⟩ ⟩

instance to_snd_complexity {α β: Type}
  [has_encoding m α] [has_encoding m β] [has_encoding m (α × β)]
  (f: α → β) [has_complexity m f]
  [cf: has_complexity m (fork id f: α → (α × β))]:
  has_complexity m (to_snd f) := ⟨ ⟨ cf.value.cost, by rw [to_snd]; apply cf.value.proof ⟩ ⟩

instance fst_complexity {α β: Type}
  [has_encoding m α] [has_encoding m β] [has_encoding m (α × β)]
  [cf: has_complexity m (uncurry (@const α β))]:
  has_complexity m (@prod.fst α β) :=
begin
  fconstructor,
  fconstructor,
  exact cf.value.cost,
  apply omega_equiv cf.value.proof,
  ext1,
  simp [uncurry, const],
end
  
instance snd_complexity {α β: Type}
  [has_encoding m α] [has_encoding m β] [has_encoding m (α × β)]
  [cf: has_complexity m (uncurry (flip (@const β α)))]:
  has_complexity m (@prod.snd α β) :=
begin
  fconstructor,
  fconstructor,
  exact cf.value.cost,
  apply omega_equiv cf.value.proof,
  ext1,
  simp [flip, uncurry, const],
end
  

end complexity