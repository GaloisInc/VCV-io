/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.SimulateQ

open OracleSpec OracleComp

namespace AKE

inductive InitResult (State W : Type)
  | speakFirst (state : State) (msg : W) : InitResult State W
  | waitForMsg (state : State) : InitResult State W

namespace InitResult

@[simp] def state {State W : Type} : InitResult State W → State
  | .speakFirst st _ => st
  | .waitForMsg st => st

@[simp] def opening {State W : Type} : InitResult State W → Option W
  | .speakFirst _ msg => some msg
  | .waitForMsg _ => none

end InitResult

inductive StepResult (State W : Type)
  | acceptAndSend (state : State) (msg : W) (done : Bool) : StepResult State W
  | complete (state : State) : StepResult State W
  | reject : StepResult State W

variable {Msg SendK RecvK W : Type}

structure Party (In W Out : Type) where
  State : Type
  init : In → ProbComp (InitResult State W)
  step : State → W → ProbComp (StepResult State W)
  output : State → ProbComp (Option Out)

namespace Party

def RecoveryDeterministic {In W Out : Type} (P : Party In W Out) : Prop :=
  ∀ st : P.State, ∃ m, P.output st = pure m

def OutputsAtCompletion {In W Out : Type} (P : Party In W Out) : Prop :=
  (∀ i r, r ∈ support (P.init i) → ∀ m ∈ support (P.output r.state), m = none) ∧
    (∀ st w st' w' b, StepResult.acceptAndSend st' w' b ∈ support (P.step st w) →
      ∀ m ∈ support (P.output st'), m = none)

end Party

structure Transcript (W : Type) where
  entries : List (W × ℕ)

namespace Transcript

def relabel {A B : Type} (f : A → B) (t : Transcript A) : Transcript B :=
  ⟨t.entries.map fun p => (f p.1, p.2)⟩

def merge {A : Type} (t1 t2 : Transcript A) : Transcript A :=
  ⟨(t1.entries ++ t2.entries).mergeSort fun p q => decide (p.2 ≤ q.2)⟩

def combine {A B : Type} (ta : Transcript A) (tb : Transcript B) :
    Transcript (A ⊕ B) :=
  (ta.relabel Sum.inl).merge (tb.relabel Sum.inr)

def prefixWith {A B : Type} (a : A) (t : ℕ) (tb : Transcript B) :
    Transcript (A ⊕ B) :=
  ⟨(Sum.inl a, t) :: tb.entries.map fun p => (Sum.inr p.1, p.2)⟩

end Transcript

structure Session (σ W : Type) where
  state : σ
  transcript : Transcript W

def interleave : Bool → List (ℕ × ℕ) → List ℕ
  | _, [] => []
  | ab, (a, b) :: rest => (if ab then [a, b] else [b, a]) ++ interleave (!ab) rest

def Matching (oracleLeadsFirst : Bool) (T Tstar : Transcript W) : Prop :=
  T.entries.map Prod.fst = Tstar.entries.map Prod.fst ∧
    List.IsChain (· < ·)
      (interleave oracleLeadsFirst ((T.entries.map Prod.snd).zip (Tstar.entries.map Prod.snd)))

instance [DecidableEq W] (b : Bool) (T Tstar : Transcript W) :
    Decidable (Matching b T Tstar) := by
  unfold Matching
  infer_instance

def pingPong [DecidableEq W] (oracleLeadsFirst : Bool)
    (oracleTrs : List (Transcript W)) (challengeTr : Transcript W) : Bool :=
  oracleTrs.any fun T => decide (Matching oracleLeadsFirst T challengeTr)

def recordOne (tr : Transcript W) (w : W) (clock : ℕ) : Transcript W × ℕ :=
  (⟨tr.entries ++ [(w, clock)]⟩, clock + 1)

def recordOpt (tr : Transcript W) : Option W → ℕ → Transcript W × ℕ
  | none, clock => (tr, clock)
  | some w, clock => recordOne tr w clock

def withUnif {ι : Type} {customSpec : OracleSpec ι} {σ : Type}
    (customImpl : QueryImpl customSpec (StateT σ ProbComp)) :
    QueryImpl (unifSpec + customSpec) (StateT σ ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget (StateT σ ProbComp)
    + customImpl

def runHonestLoop {InP OutP InQ OutQ : Type}
    (P : Party InP W OutP) (Q : Party InQ W OutQ) :
    ℕ → P.State → Q.State → W → Bool → ProbComp (P.State × Q.State)
  | 0, pState, qState, _, _ => pure (pState, qState)
  | fuel + 1, pState, qState, w, true => do
      match ← Q.step qState w with
      | .acceptAndSend qState' w' _ => runHonestLoop P Q fuel pState qState' w' false
      | .complete qState' => pure (pState, qState')
      | .reject => pure (pState, qState)
  | fuel + 1, pState, qState, w, false => do
      match ← P.step pState w with
      | .acceptAndSend pState' w' _ => runHonestLoop P Q fuel pState' qState w' true
      | .complete pState' => pure (pState', qState)
      | .reject => pure (pState, qState)

def runHonest {InP OutP InQ OutQ : Type}
    (P : Party InP W OutP) (Q : Party InQ W OutQ) (inP : InP) (inQ : InQ) (fuel : ℕ) :
    ProbComp (Option OutP × Option OutQ) := do
  let pInit ← P.init inP
  let qInit ← Q.init inQ
  let (pState', qState') ← match pInit.opening, qInit.opening with
    | some w, _ => runHonestLoop P Q fuel pInit.state qInit.state w true
    | none, some w => runHonestLoop P Q fuel pInit.state qInit.state w false
    | none, none => pure (pInit.state, qInit.state)
  let pOut ← P.output pState'
  let qOut ← Q.output qState'
  pure (pOut, qOut)

namespace MTP

structure Scheme (Msg SendK RecvK W : Type) where
  rounds : ℕ
  setup : ProbComp (SendK × RecvK)
  sender : Party (SendK × Msg) W Unit
  receiver : Party RecvK W (Option Msg)

def CorrectExp [DecidableEq Msg] (proto : Scheme Msg SendK RecvK W) (m : Msg) : ProbComp Bool := do
  let (sendk, recvk) ← proto.setup
  let (_, rOut) ← runHonest proto.sender proto.receiver (sendk, m) recvk (proto.rounds + 1)
  return decide (rOut.join = some m)

def PerfectlyCorrect [DecidableEq Msg] (proto : Scheme Msg SendK RecvK W) : Prop :=
  ∀ m : Msg, Pr[= true | CorrectExp proto m] = 1

end MTP

end AKE
