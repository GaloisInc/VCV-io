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

variable {Msg SendK RecvK W : Type}

structure Party (In W Out : Type) where
  State : Type
  init : In → ProbComp (State × Option W)
  step : State → W → ProbComp (State × ((W × Bool) ⊕ Unit))
  output : State → ProbComp (Option Out)

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

theorem Matching_prefixWith {A B : Type} (ab : Bool)
    (a a' : A) (t t' : ℕ) (Tb Tb' : Transcript B) :
    Matching ab (Transcript.prefixWith a t Tb) (Transcript.prefixWith a' t' Tb') ↔
      (a = a' ∧ Matching (!ab) Tb Tb' ∧
        List.IsChain (· < ·)
          ((if ab then [t, t'] else [t', t]) ++
            interleave (!ab) ((Tb.entries.map Prod.snd).zip (Tb'.entries.map Prod.snd)))) := by
  have hmap : ∀ (l l' : List (B × ℕ)),
      (l.map fun p => (Sum.inr p.1 : A ⊕ B)) = (l'.map fun p => (Sum.inr p.1 : A ⊕ B)) ↔
        l.map Prod.fst = l'.map Prod.fst := fun l l' => by
    rw [show (fun p : B × ℕ => (Sum.inr p.1 : A ⊕ B)) = Sum.inr ∘ Prod.fst from rfl,
      ← List.map_map, ← List.map_map]
    exact (List.map_injective_iff.mpr Sum.inr_injective).eq_iff
  simp only [Matching, Transcript.prefixWith, List.map_cons, List.map_map, Function.comp_def,
    List.zip_cons_cons, interleave, Sum.inl.injEq, List.cons.injEq, hmap]
  constructor
  · rintro ⟨⟨ha, hm⟩, hc⟩
    exact ⟨ha, ⟨hm, hc.sublist (List.sublist_append_right _ _)⟩, hc⟩
  · rintro ⟨ha, ⟨hm, -⟩, hc⟩
    exact ⟨⟨ha, hm⟩, hc⟩

theorem Matching_prefixWith_intro {A B : Type} (a : A) (t t' : ℕ)
    (Tb Tb' : Transcript B) (hb : Matching true Tb Tb')
    (hc : List.IsChain (· < ·)
      ([t', t] ++ interleave true ((Tb.entries.map Prod.snd).zip (Tb'.entries.map Prod.snd)))) :
    Matching false (Transcript.prefixWith a t Tb) (Transcript.prefixWith a t' Tb') :=
  (Matching_prefixWith false a a t t' Tb Tb').mpr ⟨rfl, hb, by simpa using hc⟩

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
      let (qState', react) ← Q.step qState w
      match react with
      | .inl (w', _) => runHonestLoop P Q fuel pState qState' w' false
      | .inr () => pure (pState, qState')
  | fuel + 1, pState, qState, w, false => do
      let (pState', react) ← P.step pState w
      match react with
      | .inl (w', _) => runHonestLoop P Q fuel pState' qState w' true
      | .inr () => pure (pState', qState)

def runHonest {InP OutP InQ OutQ : Type}
    (P : Party InP W OutP) (Q : Party InQ W OutQ) (inP : InP) (inQ : InQ) (fuel : ℕ) :
    ProbComp (Option OutP × Option OutQ) := do
  let (pState, pOpen) ← P.init inP
  let (qState, qOpen) ← Q.init inQ
  let (pState', qState') ← match pOpen, qOpen with
    | some w, _ => runHonestLoop P Q fuel pState qState w true
    | none, some w => runHonestLoop P Q fuel pState qState w false
    | none, none => pure (pState, qState)
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

def RecoveryDeterministic (proto : Scheme Msg SendK RecvK W) : Prop :=
  ∀ st : proto.receiver.State, ∃ m, proto.receiver.output st = pure m

end MTP

end AKE
