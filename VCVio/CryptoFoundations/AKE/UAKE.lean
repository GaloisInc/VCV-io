/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.AKE.Game

open OracleSpec OracleComp Interaction Interaction.TwoParty
open TimestampedTranscript MsgTransmissionProtocol AKE

namespace UAKE

variable {K TK UK : Type}

def Toracle (proto : MsgTransmissionProtocol ProbComp K TK UK) :
    OracleSpec (CptStrategy proto) :=
  fun _ => TimestampedTranscript proto.Ms × Option K

def toracleImpl [SampleableType K] {proto : MsgTransmissionProtocol ProbComp K TK UK} (tk : TK) :
    QueryImpl (Toracle proto) (StateT (Env proto) ProbComp) := fun cpt => do
  let key ← ($ᵗ K)
  let ⟨tr, _, _⟩ ←
    (Interaction.TwoParty.run proto.spec proto.owner (proto.sender tk key) cpt : ProbComp _)
  let session ← logSession tr
  pure (session, some key)

def oracleImpl [SampleableType K] {proto : MsgTransmissionProtocol ProbComp K TK UK} (tk : TK) :
    QueryImpl (unifSpec + Toracle proto) (StateT (Env proto) ProbComp) :=
  withUnif (toracleImpl (proto := proto) tk)

structure Adversary (proto : MsgTransmissionProtocol ProbComp K TK UK) where
  State : Type
  challenge : UK → OracleComp (unifSpec + Toracle proto)
    (SenderStrategy ProbComp proto.Ms × State)
  post : State → Option K → OracleComp (unifSpec + Toracle proto)
    (Bool × Option (TimestampedTranscript proto.Ms))

variable {proto : MsgTransmissionProtocol ProbComp K TK UK}
  [DecidableEq (Spec.Transcript (Spec.ofList proto.Ms))]

def isPingPong (cr : ChallengeResult proto (Option K)) : Bool :=
  pingPong Role.receiver cr.oracleSessions cr.transcript

def isFullPingPong (cr : ChallengeResult proto (Option K)) :
    Option (TimestampedTranscript proto.Ms) → Bool
  | none => false
  | some T => decide (Matching Role.receiver T cr.transcript)

def challengeSession [SampleableType K] (A : Adversary proto) (uk : UK) (tk : TK) :
    ProbComp (ChallengeResult proto (Option K) × (A.State × Env proto × TK)) := do
  let ((focalStrat, st), env) ← (simulateQ (oracleImpl tk) (A.challenge uk)).run ⟨0, []⟩
  let ⟨tr, _, K0⟩ ← Interaction.TwoParty.run proto.spec proto.owner focalStrat (proto.receiver uk)
  let challengeTr := stampAt proto tr env.clock
  pure (⟨K0, challengeTr, env.sessions⟩,
    (st, { env with clock := env.clock + proto.Ms.length }, tk))

def finalize [SampleableType K] (A : Adversary proto) (st : A.State × Env proto × TK)
    (cr : ChallengeResult proto (Option K)) (b : Bool) (K1 : Option K) : ProbComp Bool := do
  let (aSt, env, tk) := st
  let Kb := if b then K1 else cr.outcome
  let ((b', revealed), _) ← (simulateQ (oracleImpl tk) (A.post aSt Kb)).run env
  if isFullPingPong cr revealed then $ᵗ Bool else pure (b' == b)

def Exp [SampleableType K] (A : Adversary proto) : ProbComp Bool := do
  let (tk, uk) ← proto.setup
  let b ← $ᵗ Bool
  let (cr, st) ← challengeSession A uk tk
  if cr.outcome.isNone then
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
