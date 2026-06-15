/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.AKE.Interactive.Protocol

open OracleSpec OracleComp Interaction Interaction.TwoParty TimestampedTranscript MsgTransmissionProtocol

namespace UAKE

variable {K TK UK : Type}

abbrev CptStrategy (proto : MsgTransmissionProtocol ProbComp K TK UK) : Type :=
  StrategyOver (SyntaxOver.TwoParty.pairedSpec ProbComp) Participant.counterpart
    proto.spec proto.owner (fun _ => Unit)

def Toracle (proto : MsgTransmissionProtocol ProbComp K TK UK) :
    OracleSpec (CptStrategy proto) :=
  fun _ => TimestampedTranscript proto.Ms × Option K

structure Env (proto : MsgTransmissionProtocol ProbComp K TK UK) where
  clock : ℕ
  sessions : List (TimestampedTranscript proto.Ms)

def toracleImpl [SampleableType K] {proto : MsgTransmissionProtocol ProbComp K TK UK} (tk : TK) :
    QueryImpl (Toracle proto) (StateT (Env proto) ProbComp) := fun cpt => do
  let key ← ($ᵗ K)
  let ⟨tr, _, _⟩ ←
    (Interaction.TwoParty.run proto.spec proto.owner (proto.sender tk key) cpt : ProbComp _)
  let env ← get
  let ts := (List.range proto.Ms.length).map (· + env.clock)
  let session : TimestampedTranscript proto.Ms :=
    ⟨tr, ts, by simp [ts, List.length_map, List.length_range]⟩
  set (⟨env.clock + proto.Ms.length, env.sessions ++ [session]⟩ : Env proto)
  pure (session, some key)

def fullImpl [SampleableType K] {proto : MsgTransmissionProtocol ProbComp K TK UK} (tk : TK) :
    QueryImpl (unifSpec + Toracle proto) (StateT (Env proto) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget (StateT (Env proto) ProbComp)
    + toracleImpl (proto := proto) tk

structure ChallengeResult (proto : MsgTransmissionProtocol ProbComp K TK UK) where
  K0 : Option K
  transcript : TimestampedTranscript proto.Ms
  oracleSessions : List (TimestampedTranscript proto.Ms)

structure Adversary (proto : MsgTransmissionProtocol ProbComp K TK UK) where
  State : Type
  challenge : UK → OracleComp (unifSpec + Toracle proto)
    (SenderStrategy ProbComp proto.Ms × State)
  post : State → Option K → OracleComp (unifSpec + Toracle proto)
    (Bool × Option (TimestampedTranscript proto.Ms))

variable {proto : MsgTransmissionProtocol ProbComp K TK UK}
  [DecidableEq (Spec.Transcript (Spec.ofList proto.Ms))]

def isPingPong (cr : ChallengeResult proto) : Bool :=
  cr.oracleSessions.any fun T => decide (Matching Role.receiver T cr.transcript)

def isFullPingPong (cr : ChallengeResult proto) :
    Option (TimestampedTranscript proto.Ms) → Bool
  | none => false
  | some T => decide (Matching Role.receiver T cr.transcript)

def challengeSession [SampleableType K] (A : Adversary proto) (uk : UK) (tk : TK) :
    ProbComp (ChallengeResult proto × (A.State × Env proto × TK)) := do
  let ((focalStrat, st), env) ← (simulateQ (fullImpl tk) (A.challenge uk)).run ⟨0, []⟩
  let ⟨tr, _, K0⟩ ← Interaction.TwoParty.run proto.spec proto.owner focalStrat (proto.receiver uk)
  let ts := (List.range proto.Ms.length).map (· + env.clock)
  let challengeTr : TimestampedTranscript proto.Ms :=
    ⟨tr, ts, by simp [ts, List.length_map, List.length_range]⟩
  pure (⟨K0, challengeTr, env.sessions⟩,
    (st, { env with clock := env.clock + proto.Ms.length }, tk))

def finalize [SampleableType K] (A : Adversary proto) (st : A.State × Env proto × TK)
    (cr : ChallengeResult proto) (b : Bool) (K1 : Option K) : ProbComp Bool := do
  let (aSt, env, tk) := st
  let Kb := if b then K1 else cr.K0
  let ((b', revealed), _) ← (simulateQ (fullImpl tk) (A.post aSt Kb)).run env
  if isFullPingPong cr revealed then $ᵗ Bool else pure (b' == b)

def Exp [SampleableType K] (A : Adversary proto) : ProbComp Bool := do
  let (tk, uk) ← proto.setup
  let b ← $ᵗ Bool
  let (cr, st) ← challengeSession A uk tk
  if cr.K0.isNone then
    let K1 := none
    finalize A st cr b K1
  else if !isPingPong cr then
    return true
  else
    let K1 ← some <$> ($ᵗ K)
    finalize A st cr b K1

noncomputable def advantage [SampleableType K] (A : Adversary proto) : ℝ :=
  |(Pr[= true | Exp A]).toReal - 1 / 2|

end UAKE
