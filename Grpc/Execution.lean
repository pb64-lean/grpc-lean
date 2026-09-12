module

public section

namespace Grpc.Execution

variable {Command : Type} {Outcome : Command → Type} {α β γ : Type}

/-- Finite control flow whose individual effects are supplied by a driver. -/
inductive Program (Command : Type) (Outcome : Command → Type) (α : Type) where
  | done (value : α)
  | call (command : Command) (next : Outcome command → Program Command Outcome α)

@[expose] def Program.bind (program : Program Command Outcome α)
    (next : α → Program Command Outcome β) : Program Command Outcome β :=
  match program with
  | .done value => next value
  | .call command cont => .call command fun outcome => (cont outcome).bind next

instance : Monad (Program Command Outcome) where
  pure := .done
  bind := Program.bind

/-- One completed command, recording its actual returned outcome. -/
structure Event (Command : Type) (Outcome : Command → Type) where
  command : Command
  outcome : Outcome command

inductive Executes : Program Command Outcome α → List (Event Command Outcome) → α → Prop where
  | done : Executes (.done value) [] value
  | call {command : Command} {next : Outcome command → Program Command Outcome α}
      {outcome : Outcome command} : Executes (next outcome) tail value →
      Executes (.call command next) (⟨command, outcome⟩ :: tail) value

private def Program.interpretFrom [Monad m]
    (invoke : (command : Command) → m (Outcome command))
    (root program : Program Command Outcome α)
    (certify : ∀ value, (∃ trace, Executes program trace value) →
      ∃ trace, Executes root trace value)
    (finish : (value : α) → (∃ trace, Executes root trace value) → β) : m β :=
  match program with
  | .done value => pure (finish value (certify value ⟨[], .done⟩))
  | .call command next => do
      let outcome ← invoke command
      Program.interpretFrom invoke root (next outcome) (fun value evidence => by
        obtain ⟨trace, executed⟩ := evidence
        exact certify value ⟨⟨command, outcome⟩ :: trace, .call executed⟩) finish

/-- Project the certified result in the interpreter's terminal branch, without
adding an effectful continuation around its task. This matters when task
identity carries cooperative cancellation. -/
def Program.interpretWith [Monad m]
    (invoke : (command : Command) → m (Outcome command))
    (program : Program Command Outcome α)
    (finish : (value : α) → (∃ trace, Executes program trace value) → β) : m β :=
  Program.interpretFrom invoke program program (fun _ evidence => evidence) finish

/-- Run this same program with production effects. Certificates use each
returned outcome, and are erased. An effect that never returns yields no
completion certificate; callback correctness and scheduling remain explicit
assumptions of any interpretation of the command trace. -/
def Program.interpret [Monad m]
    (invoke : (command : Command) → m (Outcome command))
    (program : Program Command Outcome α) :
    m { value : α // ∃ trace, Executes program trace value } :=
  program.interpretWith invoke (fun value evidence => ⟨value, evidence⟩)

theorem executes_done_iff :
    Executes (.done value : Program Command Outcome α) trace result ↔
      trace = [] ∧ result = value := by
  constructor
  · intro executed
    cases executed
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .done

theorem executes_call_iff (command : Command)
    (next : Outcome command → Program Command Outcome α) :
    Executes (.call command next) trace value ↔
      ∃ outcome tail, trace = ⟨command, outcome⟩ :: tail ∧
        Executes (next outcome) tail value := by
  constructor
  · intro executed
    cases executed with
    | call continuation => exact ⟨_, _, rfl, continuation⟩
  · rintro ⟨outcome, tail, rfl, continuation⟩
    exact .call continuation

theorem executes_bind_iff (program : Program Command Outcome α)
    (next : α → Program Command Outcome β) :
    Executes (program.bind next) trace result ↔
      ∃ before value after, Executes program before value ∧
        Executes (next value) after result ∧ trace = before ++ after := by
  induction program generalizing trace result with
  | done value =>
      constructor
      · intro executed
        exact ⟨[], value, trace, .done, executed, rfl⟩
      · rintro ⟨before, intermediate, after, first, last, heq⟩
        cases first
        simpa using heq ▸ last
  | call command cont ih =>
      constructor
      · intro executed
        cases executed with
        | call remainder =>
            obtain ⟨before, value, after, first, continuation, rfl⟩ := (ih _).mp remainder
            exact ⟨_ :: before, value, after, .call first, continuation, rfl⟩
      · rintro ⟨before, value, after, first, last, rfl⟩
        cases first with
        | call first =>
            exact .call ((ih _).mpr ⟨_, _, _, first, last, rfl⟩)

/-- A command invocation can occur before the remaining program completes. -/
inductive Invokes : Program Command Outcome α → List (Event Command Outcome) → Command → Prop where
  | here : Invokes (.call command next) [] command
  | step {current : Command} {next : Outcome current → Program Command Outcome α}
      {outcome : Outcome current} : Invokes (next outcome) before command →
      Invokes (.call current next) (⟨current, outcome⟩ :: before) command

@[expose] def Program.ReturnsOnly (post : α → Prop) : Program Command Outcome α → Prop
  | .done value => post value
  | .call _ next => ∀ outcome, (next outcome).ReturnsOnly post

theorem returnsOnly_result {program : Program Command Outcome α}
    {trace : List (Event Command Outcome)} {result : α} {post : α → Prop}
    (checked : program.ReturnsOnly post) (executed : Executes program trace result) :
    post result := by
  induction executed with
  | done => exact checked
  | call _ ih => exact ih (checked _)

@[expose] def Program.CostBound (cost : Command → Nat) :
    Nat → Program Command Outcome α → Prop
  | _, .done _ => True
  | budget, .call command next =>
      cost command ≤ budget ∧ ∀ outcome, (next outcome).CostBound cost (budget - cost command)

theorem costBound_trace {program : Program Command Outcome α}
    {trace : List (Event Command Outcome)} {result : α} {cost : Command → Nat}
    (checked : program.CostBound cost budget) (executed : Executes program trace result) :
    (trace.map fun event => cost event.command).sum ≤ budget := by
  induction executed generalizing budget with
  | done => exact Nat.zero_le _
  | call _ ih =>
      have tail := ih (checked.2 _)
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_of_le_sub' checked.1 tail

@[expose] def Program.TraceChecks
    (post : List (Event Command Outcome) → α → Prop)
    (before : List (Event Command Outcome)) : Program Command Outcome α → Prop
  | .done value => post before value
  | .call command next => ∀ outcome,
      (next outcome).TraceChecks post (before ++ [⟨command, outcome⟩])

theorem traceChecks_call {command : Command} {next : Outcome command → Program Command Outcome α}
    {post : List (Event Command Outcome) → α → Prop} {before : List (Event Command Outcome)}
    (checked : ∀ outcome, (next outcome).TraceChecks post (before ++ [⟨command, outcome⟩])) :
    (Program.call command next).TraceChecks post before := checked

theorem traceChecks_result {program : Program Command Outcome α}
    {trace before : List (Event Command Outcome)} {result : α}
    {post : List (Event Command Outcome) → α → Prop}
    (checked : program.TraceChecks post before)
    (executed : Executes program trace result) : post (before ++ trace) result := by
  induction executed generalizing before with
  | done => simpa only [Program.TraceChecks, List.append_nil] using checked
  | call _ ih => simpa [List.append_assoc] using ih (checked _)

theorem costBound_invokes {program : Program Command Outcome α}
    {before : List (Event Command Outcome)} {command : Command} {cost : Command → Nat}
    (checked : program.CostBound cost budget) (invoked : Invokes program before command) :
    (before.map fun event => cost event.command).sum + cost command ≤ budget := by
  induction invoked generalizing budget with
  | here => simpa using checked.1
  | step _ ih =>
      have tail := ih (checked.2 _)
      simpa [Nat.add_assoc] using Nat.add_le_of_le_sub' checked.1 tail

end Grpc.Execution
