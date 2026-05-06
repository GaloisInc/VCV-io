/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.UAKE.MessageTransmissionProtocol.Defs
import VCVio.CryptoFoundations.UAKE.MessageTransmissionProtocol.Transcript
import VCVio.OracleComp.OracleComp
import VCVio.OracleComp.SimSemantics.QueryImpl
import VCVio.OracleComp.SimSemantics.StateT
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.ProbCompLift
import VCVio.CryptoFoundations.SecExp

/-!
# iCMA Security Game (Sec. 2.1, Definition 6)

iCMA security for `MessageTransmissionProtocol`s, in the style of
`unforgeableExp` (`SignatureAlg.lean`). The challenge has the adversary on
the sender side versus the honest receiver `R(recvk)`; the adversary has
concurrent oracle access to honest sender instances `S(sendk, ·)` on
adversary-chosen messages. A wins iff `R` outputs `some msg` and is *not*
ping-pong (Definition 4 of the paper).

For each oracle session, the adversary picks a message to authenticate, and
plays the *receiver* side; the honest `S` plays the sender. This is the
dual of the iCCA setup.

The full implementation:

* `OSpec` is the three-sub-oracle adversary interface (start session,
  submit at receiver steps, query at sender steps).
* `SessionState` / `GameState` carry per-session bookkeeping and the
  global counter / completed-transcript log. `consumedCount : ℕ` keeps
  `SessionState` at `Type 0` so `StateT` stays compatible with the
  underlying `OracleComp spec`.
* `oracleImpl` advances sessions one step at a time via
  `advanceSenderStepAt` / `advanceReceiverStepAt`, with the dependent
  typing of `sess.remaining` discharged through `consumeStep`.
* `runChallenge` runs the adversary's sender-side challenge strategy
  (`OracleComp (spec + OSpec)`) against the honest receiver (`OracleComp
  spec`, lifted) inside `StateT GameState (OracleComp spec)`, recording
  the timestamped challenge transcript as it goes.
* `Game` returns the win Bool: `recvOut.isSome ∧ ¬ IsPingPong …`.
* `Advantage` is the resulting `boolBiasAdvantage`.

Asymptotic security (advantage negligible in the security parameter) is
not stated here; downstream callers compose this `Advantage` with
`SecurityGame` / `negligible` from `CryptoFoundations.Asymptotics`. -/

namespace Interaction

open Spec OracleSpec OracleComp ENNReal

namespace MessageTransmissionProtocol

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {M SendK RecvK : Type}

namespace iCMA

/-! ## Oracle spec

The adversary's oracle has three sub-oracles: start a fresh `S`-session on
a chosen message, submit a move at a session's current step (only valid
when the step's role is `.receiver` — the role the adversary plays in
oracle sessions), and query the honest sender's move (only valid at
`.sender` steps). The query range is wrapped in `Option` so that
malformed queries can return `none`. -/

abbrev StartSpec (M : Type) : OracleSpec.{0, 0} M := M →ₒ ℕ

def SubmitDomain (steps : List LinearStep) : Type :=
  ℕ × Σ (i : Fin steps.length), (steps.get i).moveType

def SubmitSpec (steps : List LinearStep) :
    OracleSpec.{0, 0} (SubmitDomain steps) :=
  fun _ => Unit

def QueryDomain (steps : List LinearStep) : Type := ℕ × Fin steps.length

def QueryRange (steps : List LinearStep) (input : QueryDomain steps) : Type :=
  Option (steps.get input.2).moveType

def QuerySpec (steps : List LinearStep) :
    OracleSpec.{0, 0} (QueryDomain steps) :=
  QueryRange steps

def OSpec (steps : List LinearStep) (M : Type) :
    OracleSpec ((M ⊕ SubmitDomain steps) ⊕ QueryDomain steps) :=
  StartSpec M + SubmitSpec steps + QuerySpec steps

/-! ## Adversary -/

/-- iCMA adversary: plays the sender-side strategy of the challenge with
S-oracle access. The strategy carries no terminal output (`SenderProgram`'s
`X = Unit`); the win condition reads the receiver's `Option M` output and
the timestamped transcript log instead. -/
structure Adversary (mtp : MessageTransmissionProtocol (OracleComp spec) M SendK RecvK) where
  challengeStrategy : RecvK →
    SenderProgram (OracleComp (spec + OSpec mtp.steps M)) Unit mtp.steps

/-! ## Game state and per-session state

Each open S-session tracks the steps remaining, the honest sender's
continuation strategy at the current point, and a `prefixDone`
continuation that builds the typed full session transcript when the
session ends. -/

/-- Per-session state. Indexed by `mtp` so the typed `remaining` strategy
and `prefixDone` continuation refer to the protocol's step list. We track
how many steps have been *consumed* rather than carrying a `List
LinearStep` field, so the structure stays at `Type 0` and is compatible
with `StateT`. -/
structure SessionState (mtp : MessageTransmissionProtocol (OracleComp spec) M SendK RecvK) :
    Type where
  consumedCount : ℕ
  remaining : SenderProgram (OracleComp spec) Unit (mtp.steps.drop consumedCount)
  prefixDone : TimestampedTranscript (mtp.steps.drop consumedCount) →
               TimestampedTranscript mtp.steps

structure GameState (mtp : MessageTransmissionProtocol (OracleComp spec) M SendK RecvK) :
    Type where
  counter : ℕ
  sessions : List (ℕ × SessionState mtp)
  completedTranscripts : List (TimestampedTranscript mtp.steps)
  nextSid : ℕ

namespace GameState

variable {mtp : MessageTransmissionProtocol (OracleComp spec) M SendK RecvK}

/-- Empty initial state. -/
def empty : GameState mtp where
  counter := 0
  sessions := []
  completedTranscripts := []
  nextSid := 0

end GameState

/-! ## Step-advance machinery for oracle sessions

`consumeStep` is the dependent-type-aware piece that the linear-program
refactor unblocked: given a SessionState plus a proof that
`mtp.steps.drop consumedCount = step :: rest`, it builds a fresh session
advanced by one step, with the just-consumed `(move, timestamp)` pair
folded into `prefixDone` and `consumedCount` bumped.

`finishedTranscript` reads off the completed transcript when a session has
consumed all steps (i.e. `mtp.steps.drop consumedCount = []`). -/

variable {mtp : MessageTransmissionProtocol (OracleComp spec) M SendK RecvK}

/-- If `xs.drop n` cons-decomposes as `step :: rest`, then
`xs.drop (n + 1) = rest`. -/
private theorem drop_succ_of_drop_eq_cons {α : Type*} {xs : List α} {n : ℕ}
    {step : α} {rest : List α} (h : xs.drop n = step :: rest) :
    xs.drop (n + 1) = rest := by
  have : xs.drop (n + 1) = (xs.drop n).drop 1 := by rw [List.drop_drop]
  rw [this, h]; rfl

/-- Advance a session by one step. Given a proof `h_drop` that the head of
`mtp.steps.drop sess.consumedCount` is `step`, plus the move just consumed
at that step, the new sender continuation, and a fresh timestamp, build the
new SessionState: `consumedCount` bumps, `remaining` becomes `newRem`
(transported along the `drop_succ` lemma), and `prefixDone` extends with
`(move, timestamp)`. -/
private def consumeStep (sess : SessionState mtp)
    {step : LinearStep} {rest : List LinearStep}
    (h_drop : mtp.steps.drop sess.consumedCount = step :: rest)
    (move : step.moveType) (timestamp : ℕ)
    (newRem : SenderProgram (OracleComp spec) Unit rest) :
    SessionState mtp :=
  let h_succ : mtp.steps.drop (sess.consumedCount + 1) = rest :=
    drop_succ_of_drop_eq_cons h_drop
  { consumedCount := sess.consumedCount + 1
    remaining := h_succ.symm ▸ newRem
    prefixDone := fun t =>
      sess.prefixDone (h_drop.symm ▸
        (⟨move, timestamp, h_succ ▸ t⟩ : TimestampedTranscript (step :: rest))) }

/-- If a session has consumed all steps, the prefixDone continuation
applied to the empty trailing transcript is the full timestamped
transcript; otherwise the session is still running. -/
private def finishedTranscript (sess : SessionState mtp) :
    Option (TimestampedTranscript mtp.steps) :=
  match h_drop : mtp.steps.drop sess.consumedCount with
  | [] => some (sess.prefixDone (h_drop.symm ▸ (() : TimestampedTranscript [])))
  | _ :: _ => none

/-- Advance a session by one step at a sender position: bind the honest
sender's continuation to extract the move, build the new SessionState, and
report the optional completed transcript. The proofs `h_drop`, `h_speaker`
discharge the dependent typing of `sess.remaining`. -/
private def advanceSenderStepAt
    (sess : SessionState mtp) {step : LinearStep} {rest : List LinearStep}
    (h_drop : mtp.steps.drop sess.consumedCount = step :: rest)
    (h_speaker : step.speaker = .sender)
    (timestamp : ℕ) :
    OracleComp spec
      (step.moveType × SessionState mtp × Option (TimestampedTranscript mtp.steps)) := do
  let h_ty : SenderProgram (OracleComp spec) Unit (mtp.steps.drop sess.consumedCount) =
      OracleComp spec (step.moveType × SenderProgram (OracleComp spec) Unit rest) := by
    rw [h_drop, SenderProgram_cons_sender h_speaker]
  let ⟨move, newRem⟩ ← (cast h_ty sess.remaining)
  let newSess := consumeStep sess h_drop move timestamp newRem
  pure (move, newSess, finishedTranscript newSess)

/-- Advance a session by one step at a receiver position: feed the
adversary's `move` into the honest sender's continuation, build the new
SessionState, and report the optional completed transcript. -/
private def advanceReceiverStepAt
    (sess : SessionState mtp) {step : LinearStep} {rest : List LinearStep}
    (h_drop : mtp.steps.drop sess.consumedCount = step :: rest)
    (h_speaker : step.speaker = .receiver)
    (move : step.moveType) (timestamp : ℕ) :
    OracleComp spec (SessionState mtp × Option (TimestampedTranscript mtp.steps)) := do
  let h_ty : SenderProgram (OracleComp spec) Unit (mtp.steps.drop sess.consumedCount) =
      (step.moveType → OracleComp spec (SenderProgram (OracleComp spec) Unit rest)) := by
    rw [h_drop, SenderProgram_cons_receiver h_speaker]
  let newRem ← (cast h_ty sess.remaining) move
  let newSess := consumeStep sess h_drop move timestamp newRem
  pure (newSess, finishedTranscript newSess)

/-- Splice the result of a single advance back into the game state: bump
the global counter, replace the session by the advanced one if it's still
running, or remove it and append its completed transcript otherwise. -/
private def commitAdvance (sid : ℕ) (newSess : SessionState mtp)
    (doneOpt : Option (TimestampedTranscript mtp.steps)) :
    StateT (GameState mtp) (OracleComp spec) Unit :=
  modify fun st =>
    let counter' := st.counter + 1
    match doneOpt with
    | some t =>
      { st with
        counter := counter'
        sessions := st.sessions.filter fun e => e.1 ≠ sid
        completedTranscripts := t :: st.completedTranscripts }
    | none =>
      { st with
        counter := counter'
        sessions := st.sessions.map fun e => if e.1 = sid then (e.1, newSess) else e }

/-! ## Oracle implementation

* `startSession` builds a fresh `SessionState` carrying the honest sender's
  strategy `mtp.sender sendk m` at `consumedCount = 0` and `prefixDone =
  id` (since `mtp.steps.drop 0 = mtp.steps` definitionally). The session
  id is the previous `nextSid`, which is then bumped.

* `submitMove ⟨sid, ⟨i, move⟩⟩` advances session `sid` at step `i`, but
  only if `i.val = sess.consumedCount` and the step at that position has
  speaker `.receiver`. The advance feeds `move` into the honest sender's
  continuation via `advanceReceiverStepAt`. The new session is committed
  via `commitAdvance` (counter ticks; session list updated; if the move
  consumed the final step, the timestamped transcript moves to
  `completedTranscripts` and the session is removed).

* `queryMove ⟨sid, i⟩` is the dual, valid only at `.sender` positions: it
  binds the honest sender's continuation, returns the produced move, and
  commits the advance. -/
noncomputable def oracleImpl
    (mtp : MessageTransmissionProtocol (OracleComp spec) M SendK RecvK)
    (sendk : SendK) :
    QueryImpl (OSpec mtp.steps M)
              (StateT (GameState mtp) (OracleComp spec)) :=
  fun query =>
    match query with
    | Sum.inl (Sum.inl m) =>
        modifyGet fun st =>
          (st.nextSid,
           { st with
             sessions := (st.nextSid,
               { consumedCount := 0,
                 remaining := mtp.sender sendk m,
                 prefixDone := id }) :: st.sessions,
             nextSid := st.nextSid + 1 })
    | Sum.inl (Sum.inr ⟨sid, ⟨i, move⟩⟩) => do
        let st ← get
        match st.sessions.lookup sid with
        | none => pure ()
        | some sess =>
          if h_idx : i.val = sess.consumedCount then
            have h_lt : sess.consumedCount < mtp.steps.length := h_idx ▸ i.isLt
            let h_drop : mtp.steps.drop sess.consumedCount =
                mtp.steps[sess.consumedCount]'h_lt ::
                  mtp.steps.drop (sess.consumedCount + 1) :=
              List.drop_eq_getElem_cons h_lt
            have h_step_eq :
                mtp.steps[i] = mtp.steps[sess.consumedCount]'h_lt := by
              change mtp.steps[i.val]'i.isLt = mtp.steps[sess.consumedCount]'h_lt
              congr 1
            match h_speaker :
                (mtp.steps[sess.consumedCount]'h_lt).speaker with
            | .receiver =>
              let move' : (mtp.steps[sess.consumedCount]'h_lt).moveType :=
                cast (congrArg LinearStep.moveType h_step_eq) move
              let ⟨newSess, doneOpt⟩ ←
                (advanceReceiverStepAt sess h_drop h_speaker move' st.counter :
                  OracleComp spec _)
              commitAdvance sid newSess doneOpt
            | .sender => pure ()
          else pure ()
    | Sum.inr ⟨sid, i⟩ => do
        let st ← get
        match st.sessions.lookup sid with
        | none => pure none
        | some sess =>
          if h_idx : i.val = sess.consumedCount then
            have h_lt : sess.consumedCount < mtp.steps.length := h_idx ▸ i.isLt
            let h_drop : mtp.steps.drop sess.consumedCount =
                mtp.steps[sess.consumedCount]'h_lt ::
                  mtp.steps.drop (sess.consumedCount + 1) :=
              List.drop_eq_getElem_cons h_lt
            have h_step_eq :
                mtp.steps[i] = mtp.steps[sess.consumedCount]'h_lt := by
              change mtp.steps[i.val]'i.isLt = mtp.steps[sess.consumedCount]'h_lt
              congr 1
            match h_speaker :
                (mtp.steps[sess.consumedCount]'h_lt).speaker with
            | .sender =>
              let ⟨move, newSess, doneOpt⟩ ←
                (advanceSenderStepAt sess h_drop h_speaker st.counter :
                  OracleComp spec _)
              commitAdvance sid newSess doneOpt
              pure (some (cast (congrArg LinearStep.moveType h_step_eq.symm) move))
            | .receiver => pure none
          else pure none

/-! ## Challenge run

`runChallenge` walks the protocol's step list, running the adversary's
sender-side strategy (in `OracleComp (spec + OSpec)`, with OSpec
interpreted via `oracleImpl`) against the honest receiver (in
`OracleComp spec`, lifted to `StateT _ (OracleComp spec)`). At each step it
ticks the global counter, records the move with that timestamp into the
challenge transcript, and recurses on the rest. The final result is the
receiver's terminal output (`Option M` for the honest receiver) paired
with the timestamped challenge transcript. -/

private noncomputable def runChallenge {Y : Type}
    (mtp : MessageTransmissionProtocol (OracleComp spec) M SendK RecvK)
    (sendk : SendK) :
    (steps : List LinearStep) →
    SenderProgram (OracleComp (spec + OSpec mtp.steps M)) Unit steps →
    ReceiverProgram (OracleComp spec) Y steps →
    StateT (GameState mtp) (OracleComp spec) (Y × TimestampedTranscript steps)
  | [], _, recv => pure (recv, ())
  | ⟨X, .sender⟩ :: rest, send, recv => do
      let sendOC : OracleComp (spec + OSpec mtp.steps M)
          (X × SenderProgram (OracleComp (spec + OSpec mtp.steps M)) Unit rest) := send
      let ⟨move, sNext⟩ ←
        simulateQ ((QueryImpl.id' spec).addLift (oracleImpl mtp sendk)) sendOC
      let timestamp ← modifyGet fun st => (st.counter, { st with counter := st.counter + 1 })
      let recvFn : X → OracleComp spec (ReceiverProgram (OracleComp spec) Y rest) := recv
      let rNext ← (recvFn move : OracleComp spec _)
      let ⟨y, restTrans⟩ ← runChallenge mtp sendk rest sNext rNext
      pure (y, ⟨move, timestamp, restTrans⟩)
  | ⟨X, .receiver⟩ :: rest, send, recv => do
      let recvOC : OracleComp spec (X × ReceiverProgram (OracleComp spec) Y rest) := recv
      let ⟨move, rNext⟩ ← (recvOC : OracleComp spec _)
      let timestamp ← modifyGet fun st => (st.counter, { st with counter := st.counter + 1 })
      let sendFn : X → OracleComp (spec + OSpec mtp.steps M)
          (SenderProgram (OracleComp (spec + OSpec mtp.steps M)) Unit rest) := send
      let sNext ←
        simulateQ ((QueryImpl.id' spec).addLift (oracleImpl mtp sendk)) (sendFn move)
      let ⟨y, restTrans⟩ ← runChallenge mtp sendk rest sNext rNext
      pure (y, ⟨move, timestamp, restTrans⟩)

/-! ## Game body

A wins iff the honest receiver accepts (`recvOut.isSome`) **and** the
adversary is not ping-pong (Definition 4 of the paper). The ping-pong
check is a `Prop` over arbitrary move types; we discharge it via classical
decidability so the Game stays usable without imposing `DecidableEq` on
every step's move type. -/

open Classical in
noncomputable def Game
    (mtp : MessageTransmissionProtocol (OracleComp spec) M SendK RecvK)
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : Adversary mtp) : SPMF Bool :=
  runtime.evalDist do
    let ⟨sendk, recvk⟩ ← mtp.setup
    let ⟨⟨recvOut, challTrans⟩, finalState⟩ ←
      (runChallenge mtp sendk mtp.steps
        (adv.challengeStrategy recvk) (mtp.receiver recvk)).run GameState.empty
    pure (recvOut.isSome &&
      !decide (TimestampedTranscript.IsPingPong mtp.steps challTrans
        finalState.completedTranscripts))

/-- The adversary's iCMA win probability — i.e., the probability that the
honest receiver accepts a non-ping-pong challenge. iCMA is a *find* game,
not a distinguishing game, so the advantage is `Pr[Game = true]` directly,
not `boolBiasAdvantage` (which would be `|2·Pr[true] - 1|`, the wrong
shape: an adversary that never wins would then have advantage `1`). This
matches the convention used by `unforgeableAdv.advantage`. -/
noncomputable def Advantage
    (runtime : ProbCompRuntime (OracleComp spec))
    {mtp : MessageTransmissionProtocol (OracleComp spec) M SendK RecvK}
    (adv : Adversary mtp) : ℝ≥0∞ :=
  Pr[= true | Game mtp runtime adv]

end iCMA

end MessageTransmissionProtocol

end Interaction
