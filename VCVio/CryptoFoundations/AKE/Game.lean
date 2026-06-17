/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.AKE.Interactive.Protocol

open OracleSpec OracleComp Interaction Interaction.TwoParty
open TimestampedTranscript MsgTransmissionProtocol

namespace AKE

abbrev CptStrategy (Ms : List Type) : Type :=
  StrategyOver (SyntaxOver.TwoParty.pairedSpec ProbComp) Participant.counterpart
    (Spec.ofList Ms) (alternatingOwner Ms) (fun _ => Unit)

structure Env (Ms : List Type) where
  clock : ℕ
  sessions : List (TimestampedTranscript Ms)

structure ChallengeResult (Ms : List Type) (Outcome : Type) where
  outcome : Outcome
  transcript : TimestampedTranscript Ms
  oracleSessions : List (TimestampedTranscript Ms)

def stampAt (Ms : List Type) (tr : Spec.Transcript (Spec.ofList Ms)) (clock : ℕ) :
    TimestampedTranscript Ms :=
  ⟨tr, (List.range Ms.length).map (· + clock),
    by simp [List.length_map, List.length_range]⟩

def logSession {Ms : List Type} (tr : Spec.Transcript (Spec.ofList Ms)) :
    StateT (Env Ms) ProbComp (TimestampedTranscript Ms) := do
  let env ← get
  let session := stampAt Ms tr env.clock
  set (⟨env.clock + Ms.length, env.sessions ++ [session]⟩ : Env Ms)
  pure session

def withUnif {ι : Type} {customSpec : OracleSpec ι} {σ : Type}
    (customImpl : QueryImpl customSpec (StateT σ ProbComp)) :
    QueryImpl (unifSpec + customSpec) (StateT σ ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget (StateT σ ProbComp)
    + customImpl

def pingPong {Ms : List Type} [DecidableEq (Spec.Transcript (Spec.ofList Ms))] (challenger : Role)
    (oracleSessions : List (TimestampedTranscript Ms))
    (challengeTr : TimestampedTranscript Ms) : Bool :=
  oracleSessions.any fun T => decide (Matching challenger T challengeTr)

end AKE
