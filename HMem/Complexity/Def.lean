import HMem.Encoding.Basic
import HMem.Trace.Cost


namespace HMem

variable (next: List (Program → Program)) [Trace.HasTracedProgram (Program.build next)]
variable (pos: List (Program → Program)) [Trace.HasTracedProgram (Program.build pos)]
variable (neg: List (Program → Program)) [Trace.HasTracedProgram (Program.build neg)]

variable (next': List (Program → Program)) [Trace.HasCostedProgram (Program.build next')]
variable (pos': List (Program → Program)) [Trace.HasCostedProgram (Program.build pos')]
variable (neg': List (Program → Program)) [Trace.HasCostedProgram (Program.build neg')]

instance {next: Bool → Program} [Trace.HasTracedProgram (next true)] [Trace.HasTracedProgram (next false)]:
  {b: Bool} → Trace.HasTracedProgram (next b)
| false => inferInstance
| true => inferInstance

instance: Trace.HasTracedProgram (Program.build []) where
  tracedProgram := .exit
  tracedProgramMatches := rfl
instance: Trace.HasCostedProgram (Program.build []) where
  costedProgram := .exit
  costedProgramMatches := rfl

@[simp] def Program.setv (dst: Source) (b: Bool): Program → Program := op (.vop (λ _ ↦ b) dst finZeroElim)
@[simp] def Trace.TracedProgram.setv (dst: Source) (b: Bool): Trace.TracedProgram → Trace.TracedProgram := op (.vop (λ _ ↦ b) dst finZeroElim)
@[simp] def Trace.CostedProgram.setv (dst: Source) (b: Bool): Trace.CostedProgram → Trace.CostedProgram := op (.vop (λ _ ↦ b) dst finZeroElim)
instance: Trace.HasTracedProgram (Program.build (.setv dst b::next)) where
  tracedProgram := .setv dst b (Program.build next).traced
  tracedProgramMatches := congrArg _ (Program.tracedMatches _)
instance: Trace.HasCostedProgram (Program.build (.setv dst b::next')) where
  costedProgram := .setv dst b (Program.build next').costed
  costedProgramMatches := congrArg _ (Program.costedMatches _)

@[simp] def Program.setm (dst: Source) (src: Memory): Program → Program := op (.const dst src)
@[simp] def Trace.TracedProgram.setm (dst: Source) (src: Memory): Trace.TracedProgram → Trace.TracedProgram := op (.const dst src)
@[simp] def Trace.CostedProgram.setm (dst: Source) (src: Memory): Trace.CostedProgram → Trace.CostedProgram := op (.const dst src)
instance: Trace.HasTracedProgram (Program.build (.setm dst src::next)) where
  tracedProgram := .setm dst src (Program.build next).traced
  tracedProgramMatches := congrArg _ (Program.tracedMatches _)
instance: Trace.HasCostedProgram (Program.build (.setm dst src::next')) where
  costedProgram := .setm dst src (Program.build next').costed
  costedProgramMatches := congrArg _ (Program.costedMatches _)

@[simp] def Program.copyv (dst src: Source): Program → Program := op (.vop (λ f ↦ f 0) dst (λ (_: Fin 1) ↦ src))
@[simp] def Trace.TracedProgram.copyv (dst src: Source): TracedProgram → TracedProgram := op (.vop (λ f ↦ f 0) dst (λ (_: Fin 1) ↦ src))
@[simp] def Trace.CostedProgram.copyv (dst src: Source): CostedProgram → CostedProgram := op (.vop (λ f ↦ f 0) dst (λ (_: Fin 1) ↦ src))
instance: Trace.HasTracedProgram (Program.build (.copyv dst src::next)) where
  tracedProgram := .copyv dst src (Program.build next).traced
  tracedProgramMatches := congrArg _ (Program.tracedMatches _)
instance: Trace.HasCostedProgram (Program.build (.copyv dst src::next')) where
  costedProgram := .copyv dst src (Program.build next').costed
  costedProgramMatches := congrArg _ (Program.costedMatches _)

@[simp] def Program.copy (dst src: Source): Program → Program := op (.mop .COPY dst src)
@[simp] def Trace.TracedProgram.copy (dst src: Source): TracedProgram → TracedProgram := op (.mop .COPY dst src)
@[simp] def Trace.CostedProgram.copy (dst src: Source): CostedProgram → CostedProgram := op (.mop .COPY dst src)
instance: Trace.HasTracedProgram (Program.build (.copy dst src::next)) where
  tracedProgram := .copy dst src (Program.build next).traced
  tracedProgramMatches := congrArg _ (Program.tracedMatches _)
instance: Trace.HasCostedProgram (Program.build (.copy dst src::next')) where
  costedProgram := .copy dst src (Program.build next').costed
  costedProgramMatches := congrArg _ (Program.costedMatches _)

@[simp] def Program.move (dst src: Source): Program → Program := op (.mop .MOVE dst src)
@[simp] def Trace.TracedProgram.move (dst src: Source): TracedProgram → TracedProgram := op (.mop .MOVE dst src)
@[simp] def Trace.CostedProgram.move (dst src: Source): CostedProgram → CostedProgram := op (.mop .MOVE dst src)
instance: Trace.HasTracedProgram (Program.build (.move dst src::next)) where
  tracedProgram := .move dst src (Program.build next).traced
  tracedProgramMatches := congrArg _ (Program.tracedMatches _)
instance: Trace.HasCostedProgram (Program.build (.move dst src::next')) where
  costedProgram := .move dst src (Program.build next').costed
  costedProgramMatches := congrArg _ (Program.costedMatches _)

@[simp] def Program.swap (dst src: Source): Program → Program := op (.mop .SWAP dst src)
@[simp] def Trace.TracedProgram.swap (dst src: Source): TracedProgram → TracedProgram := op (.mop .SWAP dst src)
@[simp] def Trace.CostedProgram.swap (dst src: Source): CostedProgram → CostedProgram := op (.mop .SWAP dst src)
instance: Trace.HasTracedProgram (Program.build (.swap dst src::next)) where
  tracedProgram := .swap dst src (Program.build next).traced
  tracedProgramMatches := congrArg _ (Program.tracedMatches _)
instance: Trace.HasCostedProgram (Program.build (.swap dst src::next')) where
  costedProgram := .swap dst src (Program.build next').costed
  costedProgramMatches := congrArg _ (Program.costedMatches _)

@[simp] def Program.ifv (src: Source) (t: List (Program → Program)) (f: Program): Program := branch (.ifTrue (λ f ↦ f 0) (λ (_: Fin 1) ↦ src)) λ | true => build t | false => f
@[simp] def Trace.TracedProgram.ifv (src: Source) (t: TracedProgram) (f: TracedProgram): TracedProgram := branch (.ifTrue (λ f ↦ f 0) (λ (_: Fin 1) ↦ src)) λ | true => t | false => f
@[simp] def Trace.CostedProgram.ifv (src: Source) (t: CostedProgram) (f: CostedProgram): CostedProgram := branch (.ifTrue (λ f ↦ f 0) (λ (_: Fin 1) ↦ src)) λ | true => t | false => f
instance: Trace.HasTracedProgram (Program.build (.ifv src pos::neg)) where
  tracedProgram := .ifv src (Program.build pos).traced (Program.build neg).traced
  tracedProgramMatches := congrArg (Program.branch _) (funext λ
    | true => Program.tracedMatches _
    | false => Program.tracedMatches _)
instance: Trace.HasCostedProgram (Program.build (.ifv src pos'::neg')) where
  costedProgram := .ifv src (Program.build pos').costed (Program.build neg').costed
  costedProgramMatches := congrArg (Program.branch _) (funext λ
    | true => Program.costedMatches _
    | false => Program.costedMatches _)

variable {γ: Type _} [Complexity.Encoding γ Memory] {δ: Type _} [Complexity.Encoding δ Memory] {fs: γ → δ} [Complexity.Computable Encoding.Model fs]
@[simp] def Program.subroutine' (dst src: Source) (fs: γ → δ) [Complexity.Computable Encoding.Model fs]: Program → Program :=
  Program.subroutine dst src (Encoding.getProgram fs)
instance: Trace.HasTracedProgram (Program.build (.subroutine' dst src fs::next)) where
  tracedProgram := .subroutine dst src fs (Program.build next).traced
  tracedProgramMatches := congrArg _ (Program.tracedMatches _)
variable {fs': γ → δ} {cs': outParam (Complexity.CostFunction γ ℕ)} [Complexity Encoding.Model fs' cs']
@[simp] def Program.costedSubroutine (dst src: Source) (fs: γ → δ) (cs: Complexity.CostFunction γ ℕ) [Complexity Encoding.Model fs cs]: Program → Program :=
  Program.subroutine dst src (Encoding.getProgram fs)
instance: Trace.HasCostedProgram (Program.build (.costedSubroutine dst src fs' cs'::next')) where
  costedProgram := .subroutine dst src fs' cs' (Program.build next').costed
  costedProgramMatches := congrArg _ (Program.costedMatches _)

instance: Trace.HasTracedProgram (Program.build (.recurse dst src::next)) where
  tracedProgram := .recurse dst src (Program.build next).traced
  tracedProgramMatches := congrArg _ (Program.tracedMatches _)
instance: Trace.HasCostedProgram (Program.build (.recurse dst src::next')) where
  costedProgram := .recurse dst src (Program.build next').costed
  costedProgramMatches := congrArg _ (Program.costedMatches _)

end HMem
