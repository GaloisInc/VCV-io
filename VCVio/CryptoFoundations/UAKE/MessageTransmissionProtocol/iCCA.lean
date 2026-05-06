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
import VCVio.OracleComp.Constructions.SampleableType

/-!
# iCCA Security Game (Sec. 2.1, Definition 5)

iCCA security for `MessageTransmissionProtocol`s, in the style of
`IND_CCA_Game` (`AsymmEncAlg/INDCCA.lean`). The challenge has the honest
sender `S(sendk, m_b)` against the adversary on the receiver side; the
adversary has concurrent oracle access to honest receiver instances. A wins
iff `b = b'` and is *not* ping-pong (Definition 4 of the paper).

For each session, the adversary can submit moves at sender-positions and
query R for moves at receiver-positions. Because the protocol's `steps`
list pins down a per-round move type, the oracle's query domain stays at
`Type 0` without needing the heterogeneous `Σ X : Type, X` encoding.

The full per-message-interleaved adversary model is the *intended* one:
* A single global counter ticks on each oracle / challenge message.
* The adversary makes one-step queries via session IDs.
* Multiple oracle sessions can be in flight simultaneously.
* The challenge session is also a stepwise interaction in the same monad.

This file establishes the API surface — oracle spec, adversary structure,
advantage and security predicates — with a placeholder game body. A fully
faithful game body (running the adversary's `OracleComp` against a
session-state-machine `QueryImpl` and recording timestamped transcripts) is
the explicit follow-up step.
-/

namespace Interaction

open Spec OracleSpec OracleComp

namespace MessageTransmissionProtocol

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {M SendK RecvK : Type}

namespace iCCA

/-- Sub-oracle: start a new R-session. Input: nothing. Output: fresh session id. -/
abbrev StartSpec : OracleSpec.{0, 0} Unit := Unit →ₒ ℕ

/-- Domain of the iCCA "submit" oracle: a session ID, a step index, and the
move to submit (whose type depends on the step). -/
def SubmitDomain (steps : List LinearStep) : Type :=
  ℕ × Σ (i : Fin steps.length), (steps.get i).moveType

/-- Range of the submit oracle: always `Option M`, the receiver's terminal
output. Non-last-step submits return `none` (no decision yet); only the
final-step submit can return `some m`. -/
def SubmitSpec (steps : List LinearStep) (M : Type) :
    OracleSpec.{0, 0} (SubmitDomain steps) :=
  fun _ => Option M

/-- Domain of the iCCA "query" oracle: a session ID and a step index. -/
def QueryDomain (steps : List LinearStep) : Type := ℕ × Fin steps.length

/-- Range of the query oracle: `Option (move × Option M)`. The outer
`Option` is `none` for malformed queries (bad sid, wrong step index, or
wrong speaker). The inner `Option M` is the receiver's terminal output —
`none` at non-final steps, `some m` at the final step iff the receiver
accepts. -/
def QuerySpec (steps : List LinearStep) (M : Type) :
    OracleSpec.{0, 0} (QueryDomain steps) :=
  fun input => Option ((steps.get input.2).moveType × Option M)

/-- The iCCA adversary's oracle spec: start + submit + query, summed.
The `+` for `OracleSpec` left-associates, so the index is
`(Unit ⊕ SubmitDomain steps) ⊕ QueryDomain steps`. -/
def OSpec (steps : List LinearStep) (M : Type) :
    OracleSpec ((Unit ⊕ SubmitDomain steps) ⊕ QueryDomain steps) :=
  StartSpec + SubmitSpec steps M + QuerySpec steps M

/-- iCCA adversary against a `MessageTransmissionProtocol` whose underlying
monad is `OracleComp spec`.

* `phase1` produces the challenge plaintext pair `(m₀, m₁)` plus state, given
  the public sender key, with R-oracle access.
* `phase2` is the adversary's role on the receiver side of the challenge
  session, in `OracleComp` over the combined oracle spec. -/
structure Adversary (mtp : MessageTransmissionProtocol (OracleComp spec) M SendK RecvK) where
  State : Type
  phase1 : SendK →
    OracleComp (spec + OSpec mtp.steps M) (M × M × State)
  phase2 : State →
    ReceiverProgram (OracleComp (spec + OSpec mtp.steps M)) Bool mtp.steps

/-! ## Game state and per-session state

Mirrors iCMA's structure but R-side: the adversary plays sender in oracle
sessions (submitting moves), the honest receiver is the "remaining"
strategy. -/

/-- Per-session state for an iCCA oracle session. The `remaining` field is
the honest receiver's continuation. When all steps are consumed
(`mtp.steps.drop consumedCount = []`), `remaining` is the receiver's
terminal `Option M` output. -/
structure SessionState (mtp : MessageTransmissionProtocol (OracleComp spec) M SendK RecvK) :
    Type where
  consumedCount : ℕ
  remaining : ReceiverProgram (OracleComp spec) (Option M) (mtp.steps.drop consumedCount)
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

def empty : GameState mtp where
  counter := 0
  sessions := []
  completedTranscripts := []
  nextSid := 0

end GameState

/-! ## Step-advance machinery

Dual to iCMA's: each oracle session's `remaining` is a `ReceiverProgram`,
and the per-step advance either feeds A's submitted move into the
receiver's continuation (sender steps) or extracts the receiver's produced
move (receiver steps). At the last step, the receiver's terminal
`Option M` is exposed. -/

variable {mtp : MessageTransmissionProtocol (OracleComp spec) M SendK RecvK}

private theorem drop_succ_of_drop_eq_cons {α : Type*} {xs : List α} {n : ℕ}
    {step : α} {rest : List α} (h : xs.drop n = step :: rest) :
    xs.drop (n + 1) = rest := by
  have : xs.drop (n + 1) = (xs.drop n).drop 1 := by rw [List.drop_drop]
  rw [this, h]; rfl

private def consumeStep (sess : SessionState mtp)
    {step : LinearStep} {rest : List LinearStep}
    (h_drop : mtp.steps.drop sess.consumedCount = step :: rest)
    (move : step.moveType) (timestamp : ℕ)
    (newRem : ReceiverProgram (OracleComp spec) (Option M) rest) :
    SessionState mtp :=
  let h_succ : mtp.steps.drop (sess.consumedCount + 1) = rest :=
    drop_succ_of_drop_eq_cons h_drop
  { consumedCount := sess.consumedCount + 1
    remaining := h_succ.symm ▸ newRem
    prefixDone := fun t =>
      sess.prefixDone (h_drop.symm ▸
        (⟨move, timestamp, h_succ ▸ t⟩ : TimestampedTranscript (step :: rest))) }

/-- The completed transcript of a finished session, or none if running. -/
private def finishedTranscript (sess : SessionState mtp) :
    Option (TimestampedTranscript mtp.steps) :=
  match h_drop : mtp.steps.drop sess.consumedCount with
  | [] => some (sess.prefixDone (h_drop.symm ▸ (() : TimestampedTranscript [])))
  | _ :: _ => none

/-- The receiver's terminal `Option M` output, available iff the session
has consumed all steps. -/
private def finishedOutput (sess : SessionState mtp) : Option (Option M) :=
  match h_drop : mtp.steps.drop sess.consumedCount with
  | [] =>
    let h_ty : ReceiverProgram (OracleComp spec) (Option M) (mtp.steps.drop sess.consumedCount) =
        Option M := by rw [h_drop]; rfl
    some (cast h_ty sess.remaining)
  | _ :: _ => none

/-- Advance at a sender step (A submits a move; honest R consumes). -/
private def advanceSenderStepAt
    (sess : SessionState mtp) {step : LinearStep} {rest : List LinearStep}
    (h_drop : mtp.steps.drop sess.consumedCount = step :: rest)
    (h_speaker : step.speaker = .sender)
    (move : step.moveType) (timestamp : ℕ) :
    OracleComp spec (SessionState mtp × Option (TimestampedTranscript mtp.steps)) := do
  let h_ty : ReceiverProgram (OracleComp spec) (Option M) (mtp.steps.drop sess.consumedCount) =
      (step.moveType → OracleComp spec
        (ReceiverProgram (OracleComp spec) (Option M) rest)) := by
    rw [h_drop, ReceiverProgram_cons_sender h_speaker]
  let newRem ← (cast h_ty sess.remaining) move
  let newSess := consumeStep sess h_drop move timestamp newRem
  pure (newSess, finishedTranscript newSess)

/-- Advance at a receiver step (A queries; honest R produces). -/
private def advanceReceiverStepAt
    (sess : SessionState mtp) {step : LinearStep} {rest : List LinearStep}
    (h_drop : mtp.steps.drop sess.consumedCount = step :: rest)
    (h_speaker : step.speaker = .receiver)
    (timestamp : ℕ) :
    OracleComp spec
      (step.moveType × SessionState mtp × Option (TimestampedTranscript mtp.steps)) := do
  let h_ty : ReceiverProgram (OracleComp spec) (Option M) (mtp.steps.drop sess.consumedCount) =
      OracleComp spec
        (step.moveType × ReceiverProgram (OracleComp spec) (Option M) rest) := by
    rw [h_drop, ReceiverProgram_cons_receiver h_speaker]
  let ⟨move, newRem⟩ ← (cast h_ty sess.remaining)
  let newSess := consumeStep sess h_drop move timestamp newRem
  pure (move, newSess, finishedTranscript newSess)

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

* `Start` creates a fresh R-session at `consumedCount = 0` carrying the
  honest receiver's strategy `mtp.receiver recvk`.
* `Submit ⟨sid, ⟨i, move⟩⟩` is valid at `.sender` positions (A is the
  sender in oracle sessions). It feeds A's move into R's continuation.
  At the last step, returns the receiver's `Option M` output.
* `Query ⟨sid, i⟩` is valid at `.receiver` positions: it binds R's
  continuation to extract R's produced move. At the last step, also
  returns R's `Option M` output. -/
noncomputable def oracleImpl
    (mtp : MessageTransmissionProtocol (OracleComp spec) M SendK RecvK)
    (recvk : RecvK) :
    QueryImpl (OSpec mtp.steps M)
              (StateT (GameState mtp) (OracleComp spec)) :=
  fun query =>
    match query with
    | Sum.inl (Sum.inl ()) =>
        modifyGet fun st =>
          (st.nextSid,
           { st with
             sessions := (st.nextSid,
               { consumedCount := 0
                 remaining := mtp.receiver recvk
                 prefixDone := id }) :: st.sessions
             nextSid := st.nextSid + 1 })
    | Sum.inl (Sum.inr ⟨sid, ⟨i, move⟩⟩) => do
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
              let move' : (mtp.steps[sess.consumedCount]'h_lt).moveType :=
                cast (congrArg LinearStep.moveType h_step_eq) move
              let ⟨newSess, doneOpt⟩ ←
                (advanceSenderStepAt sess h_drop h_speaker move' st.counter :
                  OracleComp spec _)
              commitAdvance sid newSess doneOpt
              pure ((finishedOutput newSess).getD none)
            | .receiver => pure none
          else pure none
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
            | .receiver =>
              let ⟨move, newSess, doneOpt⟩ ←
                (advanceReceiverStepAt sess h_drop h_speaker st.counter :
                  OracleComp spec _)
              commitAdvance sid newSess doneOpt
              let move_at_i : (mtp.steps.get i).moveType :=
                cast (congrArg LinearStep.moveType h_step_eq.symm) move
              pure (some (move_at_i, (finishedOutput newSess).getD none))
            | .sender => pure none
          else pure none

/-! ## Challenge run

`runChallenge` walks the protocol's step list, running the honest sender
(in `OracleComp spec`, lifted to `StateT _ (OracleComp spec)`) against the
adversary's receiver-side strategy (in `OracleComp (spec + OSpec)`,
simulated through the combined oracle handler). At each step it ticks the
global counter and records the move with that timestamp into the challenge
transcript. Dual of iCMA's `runChallenge`. -/
private noncomputable def runChallenge {Y : Type}
    (mtp : MessageTransmissionProtocol (OracleComp spec) M SendK RecvK)
    (recvk : RecvK) :
    (steps : List LinearStep) →
    SenderProgram (OracleComp spec) Unit steps →
    ReceiverProgram (OracleComp (spec + OSpec mtp.steps M)) Y steps →
    StateT (GameState mtp) (OracleComp spec) (Y × TimestampedTranscript steps)
  | [], _, recv => pure (recv, ())
  | ⟨X, .sender⟩ :: rest, send, recv => do
      let sendOC : OracleComp spec (X × SenderProgram (OracleComp spec) Unit rest) := send
      let ⟨move, sNext⟩ ← (sendOC : OracleComp spec _)
      let timestamp ← modifyGet fun st => (st.counter, { st with counter := st.counter + 1 })
      let recvFn : X → OracleComp (spec + OSpec mtp.steps M)
          (ReceiverProgram (OracleComp (spec + OSpec mtp.steps M)) Y rest) := recv
      let rNext ←
        simulateQ ((QueryImpl.id' spec).addLift (oracleImpl mtp recvk)) (recvFn move)
      let ⟨y, restTrans⟩ ← runChallenge mtp recvk rest sNext rNext
      pure (y, ⟨move, timestamp, restTrans⟩)
  | ⟨X, .receiver⟩ :: rest, send, recv => do
      let recvOC : OracleComp (spec + OSpec mtp.steps M)
          (X × ReceiverProgram (OracleComp (spec + OSpec mtp.steps M)) Y rest) := recv
      let ⟨move, rNext⟩ ←
        simulateQ ((QueryImpl.id' spec).addLift (oracleImpl mtp recvk)) recvOC
      let timestamp ← modifyGet fun st => (st.counter, { st with counter := st.counter + 1 })
      let sendFn : X → OracleComp spec (SenderProgram (OracleComp spec) Unit rest) := send
      let sNext ← (sendFn move : OracleComp spec _)
      let ⟨y, restTrans⟩ ← runChallenge mtp recvk rest sNext rNext
      pure (y, ⟨move, timestamp, restTrans⟩)

/-! ## Game body

The iCCA Game samples a hidden bit `b`, has the honest sender transmit
`m_b` (with `(m_0, m_1)` chosen by `phase1`) against the adversary's
receiver-side strategy (`phase2`). A wins iff `b = b'` (correct guess) AND
the adversary is not ping-pong (Definition 4). Classical decidability is
used for the `IsPingPong` check so the game stays usable without imposing
`DecidableEq` on every step's move type. -/
open Classical in
noncomputable def Game
    (mtp : MessageTransmissionProtocol (OracleComp spec) M SendK RecvK)
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : Adversary mtp) : SPMF Bool :=
  runtime.evalDist do
    let ⟨sendk, recvk⟩ ← mtp.setup
    -- Phase 1: A produces (m_0, m_1, state) with R-oracle access.
    let phase1Sim : StateT (GameState mtp) (OracleComp spec) (M × M × adv.State) :=
      simulateQ ((QueryImpl.id' spec).addLift (oracleImpl mtp recvk)) (adv.phase1 sendk)
    let ⟨⟨m_0, m_1, advState⟩, phase1State⟩ ← phase1Sim.run GameState.empty
    -- Sample hidden bit and the corresponding plaintext.
    let b ← runtime.liftProbComp ($ᵗ Bool)
    let m_b := if b then m_1 else m_0
    -- Phase 2: honest S(sendk, m_b) vs A's receiver-side strategy.
    let ⟨⟨b', challTrans⟩, finalState⟩ ←
      (runChallenge mtp recvk mtp.steps (mtp.sender sendk m_b) (adv.phase2 advState)).run
        phase1State
    pure (b == b' &&
      !decide (TimestampedTranscript.IsPingPong mtp.steps challTrans
        finalState.completedTranscripts))

/-- Boolean-bias advantage of an iCCA adversary: distinguishing advantage
on the hidden bit `b`, in the canonical `|Pr[true] - Pr[false]|` form
(matches `IND_CCA_Advantage`). -/
noncomputable def Advantage
    (runtime : ProbCompRuntime (OracleComp spec))
    {mtp : MessageTransmissionProtocol (OracleComp spec) M SendK RecvK}
    (adv : Adversary mtp) : ℝ :=
  (Game mtp runtime adv).boolBiasAdvantage

end iCCA

end MessageTransmissionProtocol

end Interaction
