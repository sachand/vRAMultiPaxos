--------------------------- MODULE vRAMultiPaxos_StateReduction------------------------
(***************************************************************************)
(* Specification and Safety proof of vRA Multi-Paxos w/o state reduction   *)
(***************************************************************************)

EXTENDS Integers, TLAPS, TLC, FiniteSets, Sequences

CONSTANTS Acceptors, Values, Quorums, Proposers, Replicas, Clients

ASSUME QuorumAssumption == 
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
          /\ UNION {q : q \in Quorums} = Acceptors

ASSUME SystemAssumptions ==
    /\ IsFiniteSet(Acceptors)
    /\ IsFiniteSet(Proposers)
    /\ IsFiniteSet(Clients)
    /\ IsFiniteSet(Replicas)
    /\ Proposers \subseteq Nat
    /\ Proposers # {}
    /\ Acceptors # {}
    /\ Replicas # {}

Ballots == [num : Nat, id : Proposers]
Slots == Nat
InvalidSlot == CHOOSE s : s \notin Slots

VARIABLES msgs,
          pBal,
          pState,
          aVoted,
          aBal

vars == <<msgs, pBal, pState, aVoted, aBal>>

Send(m) == msgs' = msgs \cup {m}
Sends(m) == msgs' = msgs \cup m

Init ==
    /\ msgs = {}
    /\ pBal = [p \in Proposers |-> [num |-> 0, id |-> p]]
    /\ pState = [p \in Proposers |-> 1]
    /\ aVoted = [a \in Acceptors |-> {}]
    /\ aBal = [a \in Acceptors |-> [num |-> -1, id |-> -1]]

GreaterBallot(b1, b2) ==
    \/ b1.num > b2.num
    \/ /\ b1.num = b2.num
       /\ b1.id > b2.id

GreaterOrEqualBallot(b1, b2) ==
  \/ GreaterBallot(b1, b2)
  \/ b1 = b2

PartialBmax(T) ==
    {t \in T : \A t1 \in T : t1.slot = t.slot => GreaterOrEqualBallot(t.bal, t1.bal)}

Bmax(T) ==
    {[slot |-> t.slot, val |-> t.val] : t \in PartialBmax(T)}

MaximumBallot(S) ==
    IF (S = {}) THEN [num |-> -1, id |-> -1]
                ELSE CHOOSE m \in S : \A n \in S \ {m} : GreaterBallot(m, n)

(***************************************************************************)
(* MaxVotedBallotInSlot(voted, s) picks the highest ballot in voted for    *)
(* slot s.                                                                 *)
(***************************************************************************)
MaxVotedBallotInSlot(D, s) ==
  MaximumBallot({d.bal : d \in {d \in D : d.slot = s}})

(***************************************************************************)
(* Phase 1a: Executed by proposer p, it broadcasts current ballot pBal[p]  *)
(* to Acceptors. This is line 26 in Figure 3 of 'Moderately Complex Paxos  *)
(* Made Simple: High Level Specification of Distributed Algorithms'        *)
(***************************************************************************)
Phase1a(p) ==
    /\ pState[p] \in {1}
    /\ pState' = [pState EXCEPT ![p] = 2]
    /\ Send([type  |-> "1a",
             bal   |-> pBal[p],
             from  |-> p,
             to    |-> Acceptors])
    /\ UNCHANGED <<pBal, aVoted, aBal>>

(***************************************************************************)
(* Phase 1b: If an acceptor receives a 1a message with ballot b greater    *)
(* than that of any 1a message to which it has already responded, then it  *)
(* responds to the request with a promise not to accept any more proposals *)
(* for ballots numbered less than b; otherwise it sends a preempt to the   *)
(* proposer telling the greater ballot.                                    *)
(* In case of a 1b reply, the acceptor writes a set in S \times B \times V *)
(* This set reveals all the proposals(2a messages) the acceptor has seen,  *)
(* if any. This is lines 43-48 in Figure 3 of 'Moderately Complex Paxos    *)
(* Made Simple: High Level Specification of Distributed Algorithms'        *)
(***************************************************************************)
Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ a \in m.to
    /\ \A aa \in Acceptors \ {a} : aBal[aa] = aBal[aa]'
    /\ GreaterBallot(m.bal, aBal[a])
    /\ aBal[a]' = m.bal
    /\ Send([type   |-> "1b",
             voted  |-> PartialBmax(aVoted[a]),
             bal    |-> m.bal,
             to     |-> m.from,
             from   |-> a])
    /\ UNCHANGED <<pBal, pState, aVoted>>

(***************************************************************************)
(* Phase 2a1: If the proposer receives a response to its 1b message (for   *)
(* pBal[p]) from a quorum of acceptors, then it sends a 2a message to all  *)
(* acceptors for a proposal in pBal[p]. Per slot received in the replies,  *)
(* the proposer finds out the value most recently (i.e., highest ballot)   *)
(* voted by the acceptors in the received set. Thus a mapping in S -> V    *)
(* is created. This mapping along with the ballot that passed Phase 1a is  *)
(* broadcasted to Acceptors. This is lines 27-29 in Figure 3 of            *)
(* 'Moderately Complex Paxos Made Simple: High Level Specification of      *)
(* Distributed Algorithms'. Note that instead of majority, i.e., greater   *)
(* than half, this specfication uses quorum, which is a more general       *)
(* concept.                                                                *)
(***************************************************************************)
Phase2a1(p) ==
  \E Q \in Quorums : \E S \in SUBSET
    {m \in msgs : (m.type = "1b") /\ (m.bal = pBal[p]) /\ (m.to = p)} :
      /\ \A a \in Q : \E m \in S : m.from = a
      /\ Sends({[type |-> "2a",
                 bal |-> pBal[p],
                 slot |-> t.slot,
                 val |-> t.val,
                 from |-> p,
                 to |-> Acceptors] : t \in Bmax(UNION {m.voted : m \in S})})
      /\ pState[p] \in {2}
      /\ pState' = [pState EXCEPT ![p] = 3]
      /\ UNCHANGED <<pBal, aVoted, aBal>>

(***************************************************************************)
(* Phase 2a11: If the proposer receives a propose message from a replica,  *)
(* for which it has not already sent a 2a message at pBal[p], it sends a   *)
(* 2a message to all Acceptors. This is lines 31-32 in Figure 3 of         *)
(* 'Moderately Complex Paxos Made Simple: High Level Specification of      *)
(* Distributed Algorithms'. Note that instead of majority, i.e., greater   *)
(* than half, this specfication uses quorum, which is a more general       *)
(* concept.                                                                *)
(***************************************************************************)
Phase2a11(p) ==
  \E m \in msgs :
    /\ m.type = "propose"
    /\ p \in m.to
    /\ ~ \E mm \in msgs :
        /\ mm.type = "2a"
        /\ mm.bal = pBal[p]
        /\ mm.slot = m.slot
    /\ Send([type  |-> "2a",
             bal   |-> pBal[p],
             slot  |-> m.slot,
             val   |-> m.val,
             from  |-> p,
             to    |-> Acceptors])
    /\ pState[p] \in {3}
    /\ UNCHANGED <<pBal, pState, aVoted, aBal>>

(***************************************************************************)
(* Phase 2a12: If the proposer receives a set of 2b replies from a quorum  *)
(* of acceptors for the same slot s, and value v, at pBal[p], it sends a   *)
(* decision message to replicas, informing them that value v, has been     *)
(* decided on slot s. This is lines 33-35 in Figure 3 of 'Moderately       *)
(* Complex Paxos Made Simple: High Level Specification of Distributed      *)
(* Algorithms'. Note that instead of majority, i.e., greater than half,    *)
(* this specfication uses quorum, which is a more general concept.         *)
(***************************************************************************)
Phase2a12(p) ==
  \E m \in msgs :
    /\ m.type = "2b"
    /\ m.bal = pBal[p]
    /\ m.to = p
    /\ \E Q \in Quorums : \E S \in SUBSET
        {mm \in msgs : (mm.type = "2b") /\ (mm.bal = pBal[p])
            /\ (mm.slot = m.slot) /\ (mm.val = m.val) /\ (mm.to = p)} :
        /\ \A a \in Q : \E mm \in S : mm.from = a
        /\ Send([type  |-> "decision",
                 slot  |-> m.slot,
                 val   |-> m.val,
                 from  |-> p,
                 to    |-> Replicas])
    /\ pState[p] \in {3}
    /\ UNCHANGED <<pBal, pState, aVoted, aBal>>

(***************************************************************************)
(* Phase 2a13: If the proposer receives a preempt message from an acceptor *)
(* it updates its own ballot and starts over. This is lines 36-38 in       *)
(* Figure 3 of 'Moderately Complex Paxos Made Simple: High Level           *)
(* Specification of Distributed Algorithms'.                               *)
(***************************************************************************)
Phase2a13(p) ==
  \E m \in msgs :
    /\ m.type = "preempt"
    /\ GreaterBallot(m.bal, pBal[p])
    /\ pBal' = [pBal EXCEPT ![p] = [num |-> m.bal.num + 1, id |-> p]]
    /\ pState[p] \in {2, 3}
    /\ pState' = [pState EXCEPT ![p] = 1]
    /\ UNCHANGED <<msgs, aVoted, aBal>>

(***************************************************************************)
(* Phase 2b: If an acceptor receives a 2a message for a ballot which is    *)
(* the highest that it has seen, it votes for it otherwise it replies with *)
(* a preempt message. This is lines 49-53 in Figure 3 of 'Moderately       *)
(* Complex Paxos Made Simple: High Level Specification of Distributed      *)
(* Algorithms'.                                                            *)
(***************************************************************************)
Phase2b(a) == 
  \E m \in msgs :
    /\ m.type = "2a"
    /\ a \in m.to
    /\ \A aa \in Acceptors \ {a} : aVoted'[aa] = aVoted[aa]
    /\ GreaterOrEqualBallot(m.bal, aBal[a])
    /\ aVoted'[a] = aVoted[a] \cup {[bal |-> m.bal, val |-> m.val, slot |-> m.slot]}
    /\ Send([type    |-> "2b",
             slot    |-> m.slot,
             val     |-> m.val,
             bal     |-> m.bal,
             from    |-> a,
             to      |-> m.from])
    /\ UNCHANGED <<pBal, pState, aBal>>

PhasePr(a) ==
  \E m \in msgs:
    /\ m.from \in Proposers
    /\ m.type \in {"1a", "2a"}
    /\ \E m2 \in msgs:
         /\ m2.from = a
         /\ m2.type \in {"1b", "2b"}
         /\ GreaterBallot(m2.bal, m.bal)
    /\ Send([type    |-> "preempt",
             bal     |-> m.bal,
             from    |-> a,
             to      |-> m.from])
    /\ UNCHANGED <<pBal, pState, aBal, aVoted>>

Next == \/ \E p \in Proposers : Phase1a(p) \/ Phase2a1(p) \/ Phase2a11(p) \/ Phase2a12(p) \/ Phase2a13(p)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)  \/ PhasePr(a)

Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
(***************************************************************************)
(* The consistency condition that a consensus algorithm must satisfy is    *)
(* the invariance of the following state predicate Consistency.            *)
(***************************************************************************)
VotedForIn(a, v, b, s) ==
  \E d \in aVoted[a] :
    /\ d.bal = b
    /\ d.val = v
    /\ d.slot = s

Chosen(v, s) ==
    \E m \in msgs :
        /\ m.type = "decision"
        /\ m.slot = s
        /\ m.val = v

Proposed(v, s) ==
  \E m \in msgs :
    /\ m.type = "propose"
    /\ m.from \in Replicas
    /\ m.val = v
    /\ m.slot = s

Consistency == \A v1, v2 \in Values, s \in Slots : Chosen(v1, s) /\ Chosen(v2, s) => (v1 = v2)
DecideProposed == \A v \in Values, s \in Slots : Chosen(v, s) => Proposed(v, s)
-----------------------------------------------------------------------------
(***************************************************************************)
(* This section of the spec defines the invariant Inv.                     *)
(***************************************************************************)
ValidMessage1a(m) ==
  /\ m.bal \in Ballots
  /\ m.from \in Proposers
  /\ m.to \subseteq Acceptors

ValidMessage1b(m) ==
  /\ m.bal \in Ballots
  /\ m.voted \subseteq [bal : Ballots, slot : Slots, val : Values]
  /\ m.from \in Acceptors
  /\ m.to \in Proposers

ValidMessage2a(m) ==
  /\ m.bal \in Ballots
  /\ m.slot \in Slots
  /\ m.val \in Values
  /\ m.from \in Proposers
  /\ m.to \subseteq Acceptors

ValidMessage2b(m) ==
  /\ m.bal \in Ballots
  /\ m.slot \in Slots
  /\ m.val \in Values
  /\ m.from \in Acceptors
  /\ m.to \in Proposers

ValidMessagedecision(m) ==
  /\ m.slot \in Slots
  /\ m.val \in Values
  /\ m.from \in Proposers
  /\ m.to \subseteq Replicas

ValidMessagepropose(m) ==
  /\ m.slot \in Slots
  /\ m.val \in Values
  /\ m.from \in Replicas
  /\ m.to \subseteq Proposers

ValidMessagepreempt(m) ==
  /\ m.bal \in Ballots
  /\ m.from \in Acceptors
  /\ m.to \in Proposers

ValidMessages(M) ==
  \A m \in M :
    /\ m.type \in {"1a", "1b", "2a", "2b", "decision", "propose", "preempt"}
    /\ m.type = "1a" => ValidMessage1a(m)
    /\ m.type = "1b" => ValidMessage1b(m)
    /\ m.type = "2a" => ValidMessage2a(m)
    /\ m.type = "2b" => ValidMessage2b(m)
    /\ m.type = "decision" => ValidMessagedecision(m)
    /\ m.type = "propose"  => ValidMessagepropose(m)
    /\ m.type = "preempt"  => ValidMessagepreempt(m)

TypeOK == /\ ValidMessages(msgs)
          /\ pBal \in [Proposers -> Ballots]
          /\ pState \in [Proposers -> {1, 2, 3}]
          /\ \A a \in Acceptors : /\ aVoted[a] \subseteq [bal : Ballots, slot : Slots, val : Values]
                                  /\ aBal[a] \in Ballots \cup {[num |-> -1, id |-> -1]}

(***************************************************************************)
(* WontVoteIn(a, b, s) is a predicate that implies that a has not voted    *)
(* and never will vote in ballot b wrt slot s.                             *)
(***************************************************************************)                                       
WontVoteIn(a, b, s) == /\ \A v \in Values : ~ VotedForIn(a, v, b, s)
                       /\ GreaterBallot(aBal[a], b)

(***************************************************************************)
(* The predicate SafeAt(v, b, s) implies that no value other than perhaps  *)
(* v has been or ever will be chosen in any ballot numbered less than b    *)
(* for slot s.                                                             *)
(***************************************************************************)                   
SafeAt(v, b, s) == 
  \A c \in Ballots : GreaterBallot(b, c) =>
    (\E Q \in Quorums : 
      \A a \in Q : VotedForIn(a, v, c, s) \/ WontVoteIn(a, c, s))

(***************************************************************************)
(* Maximum(S) picks the largest element in the set S.                      *)
(***************************************************************************)
Maximum(B) ==
  CHOOSE b \in B : \A b2 \in B : b >= b2

AXIOM MaxInSet ==
  \A S \in (SUBSET Nat) \ {}: Maximum(S) \in S

AXIOM MaxBalInSet ==
  \A S \in SUBSET Ballots : S # {} => MaximumBallot(S) \in S

LEMMA MaxOnNat ==
  \A S \in SUBSET Nat :
  ~ \E s \in S : Maximum(S) < s
  BY DEF Maximum

LEMMA MaxOnBal ==
  \A S \in SUBSET Ballots :
    ~ \E s \in S : GreaterBallot(s, MaximumBallot(S))
  BY SystemAssumptions DEF MaximumBallot, GreaterBallot, Ballots


LEMMA EqualBallots ==
  \A b1, b2 \in Ballots \cup {[num |-> -1, id |-> -1]}:
    (b1.num = b2.num /\ b1.id = b2.id) <=> b1 = b2
  BY DEF Ballots

LEMMA GBTotal ==
  \A b1, b2 \in Ballots \cup {[num |-> -1, id |-> -1]}:
    \/ b1 = b2
    \/ GreaterBallot(b1, b2)
    \/ GreaterBallot(b2, b1)
  <1> SUFFICES ASSUME NEW b1 \in Ballots \cup {[num |-> -1, id |-> -1]}, NEW b2 \in Ballots \cup {[num |-> -1, id |-> -1]},
                      b1 # b2
               PROVE  \/ GreaterBallot(b1, b2)
                      \/ GreaterBallot(b2, b1)
    OBVIOUS
    <1>1. PICK x1 \in Nat \cup {-1}, y1 \in Proposers \cup {-1}: x1 = b1.num /\ y1 = b1.id
      BY SystemAssumptions DEF Ballots
    <1>2. PICK x2 \in Nat \cup {-1}, y2 \in Proposers \cup {-1}: x2 = b2.num /\ y2 = b2.id
      BY SystemAssumptions DEF Ballots
    <1>3. x1 # x2 \/ y1 # y2 
      BY <1>1, <1>2, EqualBallots
    <1>4. CASE x1 # x2
      BY <1>1, <1>2, <1>4 DEF GreaterBallot, Ballots
    <1>5. CASE (x1 = x2) /\ y1 # y2
      BY <1>1, <1>2, <1>5, SystemAssumptions DEF GreaterBallot, Ballots
  <1> QED
    BY <1>3, <1>4, <1>5

LEMMA GBTransitive ==
  \A a, b, c \in Ballots \cup {[num |-> -1, id |-> -1]} :
    GreaterOrEqualBallot(a, b) /\ GreaterBallot(b, c) => GreaterBallot(a, c)
BY SystemAssumptions DEF GreaterBallot, Ballots, GreaterOrEqualBallot

LEMMA GBTransitive2 ==
  \A a, b, c \in Ballots \cup {[num |-> -1, id |-> -1]} :
    GreaterBallot(a, b) /\ GreaterOrEqualBallot(b, c) => GreaterBallot(a, c)
BY SystemAssumptions DEF GreaterBallot, Ballots, GreaterOrEqualBallot

LEMMA GBTransitive3 ==
  \A a, b, c \in Ballots \cup {[num |-> -1, id |-> -1]} :
    GreaterBallot(a, b) /\ GreaterBallot(b, c) => GreaterBallot(a, c)
BY SystemAssumptions DEF GreaterBallot, Ballots

LEMMA GEBTransitive ==
  \A a, b, c \in Ballots \cup {[num |-> -1, id |-> -1]} :
    GreaterOrEqualBallot(a, b) /\ GreaterOrEqualBallot(b, c) => GreaterOrEqualBallot(a, c)
BY SystemAssumptions DEF GreaterBallot, Ballots, GreaterOrEqualBallot
LEMMA MaxOnBalN ==  
  \A S \in SUBSET Ballots :
    \A s \in S : s = MaximumBallot(S) \/ GreaterBallot(MaximumBallot(S), s)
  BY SystemAssumptions, MaxOnBal, GBTotal, GBTransitive

LEMMA MaxOnNatS ==
  \A S1, S2 \in (SUBSET Nat) \ {}: S1 \subseteq S2 =>
    Maximum(S1) =< Maximum(S2)
  BY MaxOnNat, MaxInSet

LEMMA MaxOnBalS ==
  \A S1, S2 \in SUBSET Ballots: S1 \subseteq S2 =>
    GreaterOrEqualBallot(MaximumBallot(S2), MaximumBallot(S1))
  BY MaxOnBal, MaxBalInSet DEF GreaterOrEqualBallot

LEMMA GBNotCommutative ==
  \A a, b \in Ballots \cup {[num |-> -1, id |-> -1]} : GreaterBallot(a, b) => ~GreaterBallot(b, a)
  <1> SUFFICES ASSUME NEW a \in Ballots \cup {[num |-> -1, id |-> -1]}, NEW b \in Ballots \cup {[num |-> -1, id |-> -1]},
                      GreaterBallot(a, b)
               PROVE  ~GreaterBallot(b, a)
    OBVIOUS
  <1>2. CASE a.num > b.num
    BY <1>2, SystemAssumptions DEF GreaterBallot, Ballots
  <1>3. CASE /\ a.num = b.num
             /\ a.id > b.id
    BY <1>3, SystemAssumptions DEF GreaterBallot, Ballots
  <1>4. QED
    BY <1>2, <1>3 DEF GreaterBallot

LEMMA GEBNotCommutative ==
  \A a, b \in Ballots \cup {[num |-> -1, id |-> -1]} : GreaterOrEqualBallot(a, b) <=> ~GreaterBallot(b, a)
  <1> SUFFICES ASSUME NEW a \in Ballots \cup {[num |-> -1, id |-> -1]}, NEW b \in Ballots \cup {[num |-> -1, id |-> -1]}
               PROVE  GreaterOrEqualBallot(a, b) <=> ~GreaterBallot(b, a)
    OBVIOUS
    <1>1. GreaterOrEqualBallot(a, b) => ~GreaterBallot(b, a)
       BY GBNotCommutative DEF GreaterOrEqualBallot
    <1>2. ~GreaterBallot(b, a) => GreaterOrEqualBallot(a, b)
       BY GBTotal DEF GreaterOrEqualBallot
  <1> QED BY <1>1, <1>2

LEMMA MVBISType ==
\A S \in SUBSET [bal : Ballots, slot : Slots, val : Values], 
   s \in Slots: MaxVotedBallotInSlot(S, s) \in Ballots \cup {[num |-> -1, id |-> -1]}
BY DEF MaxVotedBallotInSlot, MaximumBallot

LEMMA MVBISSubsets ==
\A S1, S2 \in SUBSET [bal : Ballots, slot : Slots, val : Values]:
    S1 \subseteq S2
    =>
    \A s \in Slots: GreaterOrEqualBallot(MaxVotedBallotInSlot(S2, s), MaxVotedBallotInSlot(S1, s))
  <1> SUFFICES ASSUME NEW S1 \in SUBSET [bal : Ballots, slot : Slots, val : Values],
                      NEW S2 \in SUBSET [bal : Ballots, slot : Slots, val : Values],
                      S1 \subseteq S2,
                      NEW s \in Slots
               PROVE  GreaterOrEqualBallot(MaxVotedBallotInSlot(S2, s), MaxVotedBallotInSlot(S1, s))
    OBVIOUS
  <1>3. {d.bal : d \in {d \in S1 : d.slot = s}} \subseteq {d.bal : d \in {d \in S2 : d.slot = s}}
    OBVIOUS
  <1>1. CASE ~ \E d \in S1 : d.slot = s
    <2>1. MaxVotedBallotInSlot(S1, s) = [num |-> -1, id |-> -1]
      BY <1>1 DEF MaxVotedBallotInSlot, MaximumBallot
    <2> QED BY <2>1, MVBISType DEF Ballots, GreaterOrEqualBallot, GreaterBallot
  <1>2. CASE \E d \in S1 : d.slot = s
    <2>1. CASE ~ \E d \in S2 \ S1 : d.slot = s
      <3>1. MaxVotedBallotInSlot(S1, s) = MaxVotedBallotInSlot(S2, s)
        BY <2>1, <1>2 DEF MaxVotedBallotInSlot, GreaterOrEqualBallot, GreaterBallot
      <3> QED BY <3>1, MVBISType DEF Ballots, GreaterOrEqualBallot, GreaterBallot
    <2>2. CASE \E d \in S2 \ S1 : d.slot = s
      BY <2>2, <1>2, MVBISType, MaxOnBalS, <1>3 DEF Ballots, MaxVotedBallotInSlot\*, GreaterOrEqualBallot, GreaterBallot, MaximumBallot
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>1, <1>2

LEMMA MVBISNoSlot ==
\A S \in SUBSET [bal : Ballots, slot : Slots, val : Values], s \in Slots:
  (~ \E d \in S : d.slot = s) <=> (MaxVotedBallotInSlot(S, s) = [num |-> -1, id |-> -1]) 
  <1> SUFFICES ASSUME NEW S \in SUBSET [bal : Ballots, slot : Slots, val : Values], NEW s \in Slots
               PROVE  (~ \E d \in S : d.slot = s) <=> (MaxVotedBallotInSlot(S, s) = [num |-> -1, id |-> -1])
    OBVIOUS
  <1>1. (~ \E d \in S : d.slot = s) => (MaxVotedBallotInSlot(S, s) = [num |-> -1, id |-> -1])
    BY DEF MaxVotedBallotInSlot, Ballots, MaximumBallot
  <1>2. (MaxVotedBallotInSlot(S, s) = [num |-> -1, id |-> -1]) => (~ \E d \in S : d.slot = s)
    <2>1. CASE {d.bal : d \in {d \in S : d.slot = s}} = {}
      BY <2>1 DEF MaxVotedBallotInSlot, Ballots, MaximumBallot
    <2>2. CASE {d.bal : d \in {d \in S : d.slot = s}} # {}
      BY <2>2 DEF MaxVotedBallotInSlot, Ballots, MaximumBallot
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>1, <1>2

LEMMA MVBISExists ==
\A S \in SUBSET [bal : Ballots, slot : Slots, val : Values],
    s \in Slots:
    (MaxVotedBallotInSlot(S, s) \in Ballots)
     =>
     \E d \in S : d.slot = s /\ d.bal = MaxVotedBallotInSlot(S, s)
  <1> SUFFICES ASSUME NEW S \in SUBSET [bal : Ballots, slot : Slots, val : Values],
                      NEW s \in Slots,
                      MaxVotedBallotInSlot(S, s) \in Ballots
               PROVE  \E d \in S : d.slot = s /\ d.bal = MaxVotedBallotInSlot(S, s)
    OBVIOUS
    <1>1. \E d \in S : d.slot = s
      BY DEF MaxVotedBallotInSlot, Ballots, MaximumBallot
    <1> DEFINE Ss == {d \in S : d.slot = s}
    <1> DEFINE Bs == {d.bal : d \in Ss}
    <1>3. Bs \subseteq Ballots OBVIOUS
  <1> QED
    BY <1>1, <1>3, MaxInSet
  
LEMMA MVBISNoMore ==
\A S \in SUBSET [bal : Ballots, slot : Slots, val : Values], 
   s \in Slots:
     ~\E d \in S : d.slot = s /\ GreaterBallot(d.bal, MaxVotedBallotInSlot(S, s))
  <1> SUFFICES ASSUME NEW S \in SUBSET [bal : Ballots, slot : Slots, val : Values],
                      NEW s \in Slots
               PROVE  ~\E d \in S : d.slot = s /\ GreaterBallot(d.bal, MaxVotedBallotInSlot(S, s))
    OBVIOUS
    <1>1. CASE ~\E d \in S : d.slot = s
      BY <1>1
    <1>2. CASE \E d \in S : d.slot = s
        <2> DEFINE Ss == {d \in S : d.slot = s}
        <2> DEFINE Bs == {d.bal : d \in Ss}
        <2>3. Bs \subseteq Ballots OBVIOUS
        <2>1. ~ \E bbb \in Bs : GreaterBallot(bbb, MaxVotedBallotInSlot(S, s))
          BY <1>2, MaxOnBal, <2>3 DEF MaxVotedBallotInSlot, Ballots, Slots
        <2>2. ~ \E dd \in S : (dd.slot = s /\ GreaterBallot(dd.bal, MaxVotedBallotInSlot(S, s)))
          BY <2>1
        <2> QED BY <2>2
  <1> QED
    BY <1>1, <1>2

LEMMA MVBISUnion ==
\A S \in SUBSET [bal : Ballots, slot : Slots, val : Values], s \in Slots, b \in Ballots, v \in Values:
  \/ MaxVotedBallotInSlot(S \cup {[bal |-> b, val |-> v, slot |-> s]}, s) = MaxVotedBallotInSlot(S, s)
  \/ MaxVotedBallotInSlot(S \cup {[bal |-> b, val |-> v, slot |-> s]}, s) = b
  <1> SUFFICES ASSUME NEW S \in SUBSET [bal : Ballots, slot : Slots, val : Values], NEW s \in Slots, NEW b \in Ballots, NEW v \in Values
               PROVE  \/ MaxVotedBallotInSlot(S \cup {[bal |-> b, val |-> v, slot |-> s]}, s) = MaxVotedBallotInSlot(S, s)
                      \/ MaxVotedBallotInSlot(S \cup {[bal |-> b, val |-> v, slot |-> s]}, s) = b
    OBVIOUS
    <1>0. DEFINE S2 == S \cup {[bal |-> b, val |-> v, slot |-> s]}
    <1>10. DEFINE Bals == {d.bal : d \in {d \in S: d.slot = s}}
    <1>11. DEFINE Bals2 == Bals \cup {b}
    <1> HIDE DEF S2, Bals, Bals2
    <1>1. CASE ~\E d \in S : d.slot = s
      <2>1. {d \in S2 : d.slot = s} = {[bal |-> b, val |-> v, slot |-> s]}
        BY <1>1 DEF S2
      <2>2. {d.bal : d \in {d \in S2 : d.slot = s}} = {b}
        BY <2>1
      <2>3. MaxVotedBallotInSlot(S2, s) = b
        BY <2>2 DEF MaxVotedBallotInSlot, MaximumBallot
      <2> QED BY <2>3 DEF S2
    <1>2. CASE \E d \in S : d.slot = s
      <2>1. PICK dd \in S : (MaxVotedBallotInSlot(S, s) = dd.bal) /\ dd.slot = s
        BY <1>2, MVBISNoSlot, MVBISType, MVBISExists
      <2>2. dd.bal \in {d.bal : d \in {d \in S: d.slot = s}}
        BY <2>1
      <2>31. dd.bal # [num |-> -1, id |-> -1]
        BY <2>1, <1>2 DEF MaxVotedBallotInSlot, MaximumBallot, Ballots
      <2>32. \A s2 \in {d.bal : d \in {d \in S: d.slot = s}} : ~GreaterBallot(s2, MaximumBallot({d.bal : d \in {d \in S: d.slot = s}}))
        BY MaxOnBal DEF MaxVotedBallotInSlot
      <2>33. \A s2 \in {d.bal : d \in {d \in S: d.slot = s}} : ~GreaterBallot(s2, dd.bal)
        BY <2>32, <2>1, <2>2 DEF MaxVotedBallotInSlot
      <2>34. \A s2 \in {d.bal : d \in {d \in S: d.slot = s}} : GreaterOrEqualBallot(dd.bal, s2)
        BY <2>33, GEBNotCommutative
      <2>3. \A b2 \in {d.bal : d \in {d \in S: d.slot = s}} \ {dd.bal} : GreaterBallot(dd.bal, b2)
        BY <2>2, <2>34 DEF GreaterOrEqualBallot
      <2>40. Bals2 # {}
        BY <1>2 DEF S2, Bals2
      <2>41. dd.bal \in Bals2
        BY <2>2 DEF Bals2, S2, Bals
      <2>42. MaxVotedBallotInSlot(S2, s) = MaximumBallot(Bals2)
        BY <1>2 DEF S2, MaxVotedBallotInSlot, Bals2, Bals
      <2>4. CASE GreaterBallot(b, dd.bal)
        <3>1. \A b2 \in Bals \ {dd.bal} : GreaterBallot(b, b2)
          BY <2>1, <2>4, <2>3, GBTransitive3 DEF S2, Bals, GreaterOrEqualBallot
        <3>21. \A b2 \in Bals2 \ {b} : GreaterBallot(b, b2)
          BY <3>1, <2>4, <2>2 DEF Bals2
        <3>3. MaximumBallot(Bals2) = b
          BY <2>40, <3>21 DEF MaximumBallot, Bals2
        <3> QED BY <2>42, <3>3, <2>1 DEF S2
      <2>5. CASE GreaterOrEqualBallot(dd.bal, b) 
        <3>1. \A b2 \in Bals2 \ {dd.bal} : GreaterBallot(dd.bal, b2)
          BY <2>5, <2>3 DEF S2, Bals2, GreaterOrEqualBallot, Bals
        <3>3. MaximumBallot(Bals2) = dd.bal
          BY <2>40, <2>41, <3>1 DEF MaximumBallot
        <3> QED BY <2>42, <3>3, <2>1 DEF S2
      <2> QED BY <2>4, <2>5, <2>1, GBTotal DEF GreaterOrEqualBallot
  <1> QED BY <1>1, <1>2

LEMMA MBType ==
  \A S \in SUBSET Ballots :
    S # {} => MaximumBallot(S) \in Ballots
  <1> SUFFICES ASSUME NEW S \in SUBSET Ballots,
                      S # {}
               PROVE  MaximumBallot(S) \in Ballots
    OBVIOUS
  <1> DEFINE s == CHOOSE s \in S : TRUE
  <1>1. S = {s} => MaximumBallot(S) \in Ballots
    BY DEF MaximumBallot, GreaterBallot, Ballots
  <1>2. MaximumBallot(S \ {s}) \in Ballots => MaximumBallot(S) \in Ballots
    BY DEF MaximumBallot, GreaterBallot, Ballots
  <1> QED
    BY <1>1, <1>2

LEMMA QuorumNonEmpty == \A Q \in Quorums : Q # {}
BY QuorumAssumption

AXIOM PBmaxVotes ==
  \A S \in SUBSET [bal : Ballots, val : Values, slot : Slots] :
    {vote.slot : vote \in S} = {vote.slot : vote \in PartialBmax(S)}

AXIOM PBmaxSingular ==
  \A S \in SUBSET [bal : Ballots, val : Values, slot : Slots]:
    \A e1, e2 \in PartialBmax(S): e1.slot = e2.slot => e1 = e2
AXIOM BmaxVotes ==
  \A S \in SUBSET [bal : Ballots, val : Values, slot : Slots] :
    {vote.slot : vote \in S} = {vote.slot : vote \in Bmax(S)}
(*  <1> SUFFICES ASSUME NEW S \in SUBSET [bal : Ballots, val : Values, slot : Slots]
               PROVE  {vote.slot : vote \in S} = {vote.slot : vote \in Bmax(S)}
    OBVIOUS
    <1>1. {vote.slot : vote \in Bmax(S)} = {vote.slot : vote \in PartialBmax(S)}
      BY DEF Bmax
    <1>2. {vote.slot : vote \in PartialBmax(S)} \subseteq {vote.slot : vote \in S}
      BY DEF PartialBmax, GreaterOrEqualBallot, GreaterBallot
    <1>3. {vote.slot : vote \in S} \subseteq {vote.slot : vote \in PartialBmax(S)}
      <2> SUFFICES ASSUME NEW s \in S,
                          s.slot \notin {vote.slot : vote \in PartialBmax(S)}
                   PROVE  FALSE
        OBVIOUS
        <2>1. \E s2 \in PartialBmax(S): s2.slot = s.slot
          <3>0. DEFINE smax == CHOOSE ss \in S : ss. slot = s.slot /\ \A sss \in S : GreaterOrEqualBallot(ss, sss)
          <3>1. CASE ~ \E ss \in S \ {s} : s.slot = ss.slot
            BY <3>1 DEF PartialBmax, GreaterOrEqualBallot, GreaterBallot
          <3>2. CASE \E ss \in S \ {s} : s.slot = ss.slot
            BY <3>2, smax \in PartialBmax(S) DEF PartialBmax, GreaterOrEqualBallot, GreaterBallot
          <3> QED BY <3>1, <3>2
      <2> QED
      BY DEF PartialBmax, GreaterOrEqualBallot, GreaterBallot
  <1> QED*)

LEMMA MVBISPbmax ==
\A S \in SUBSET [bal : Ballots, slot : Slots, val : Values], s \in Slots:
  MaxVotedBallotInSlot(S, s) = MaxVotedBallotInSlot(PartialBmax(S), s)
  <1> SUFFICES ASSUME NEW S \in SUBSET [bal : Ballots, slot : Slots, val : Values], NEW s \in Slots
               PROVE  MaxVotedBallotInSlot(S, s) = MaxVotedBallotInSlot(PartialBmax(S), s)
    OBVIOUS
    <1>1. CASE ~\E e \in S: e.slot = s
      BY <1>1 DEF PartialBmax, MaxVotedBallotInSlot, MaximumBallot
    <1>2. CASE \E e \in S: e.slot = s
      <2>1. s \in {vote.slot : vote \in S} BY <1>2
      <2>2. s \in {vote.slot : vote \in PartialBmax(S)} BY <2>1, PBmaxVotes
      <2>3. PICK e2 \in PartialBmax(S): e2.slot = s BY <2>2 DEF PartialBmax
      <2>4. \A e \in S: e.slot = s => GreaterOrEqualBallot(e2.bal, e.bal) BY <2>3 DEF PartialBmax
      <2>5. e2 \in S BY <2>3 DEF PartialBmax
      <2>42. \A e \in S: e.slot = s => ~GreaterBallot(e.bal, e2.bal)
        BY <2>3, <2>4, <2>5, GEBNotCommutative
      <2>6. \A e \in S: e.slot = s => ~GreaterBallot(e.bal, MaxVotedBallotInSlot(S, s))
        BY MVBISNoMore
      <2>7. \A e \in S: e.slot = s => GreaterOrEqualBallot(MaxVotedBallotInSlot(S, s), e.bal)
        BY <2>6, MVBISType, GBTotal DEF GreaterOrEqualBallot
      <2>8. e2.bal = MaxVotedBallotInSlot(S, s)
        <3> SUFFICES ASSUME e2.bal # MaxVotedBallotInSlot(S, s)
                     PROVE  FALSE
            OBVIOUS
        <3>1. CASE GreaterBallot(e2.bal, MaxVotedBallotInSlot(S, s))
          BY <3>1, <2>5, <2>3, <2>6
        <3>2. CASE GreaterBallot(MaxVotedBallotInSlot(S, s), e2.bal)
          <4>1. PICK e3 \in S: e3.slot = s /\ e3.bal = MaxVotedBallotInSlot(S, s)
            BY <1>2, MVBISNoSlot, MVBISType, MVBISExists
          <4> QED BY <4>1, <2>42, <3>2, <2>3, <2>5
        <3> QED BY <3>1, <3>2, <2>5, MVBISType, GBTotal
      <2>10. {d \in PartialBmax(S) : d.slot = s} = {e2} BY <2>3, PBmaxSingular
      <2>11. MaxVotedBallotInSlot(PartialBmax(S), s) = CHOOSE m \in {d.bal: d \in {e2}}: \A n \in {d.bal : d \in {e2}} \ {m} : GreaterBallot(m, n)
        BY <1>2, <2>10 DEF MaxVotedBallotInSlot, MaximumBallot
      <2>12. MaxVotedBallotInSlot(PartialBmax(S), s) = CHOOSE m \in {e2.bal}: \A n \in {e2.bal} \ {m} : GreaterBallot(m, n)
        BY <2>11
      <2>13. MaxVotedBallotInSlot(PartialBmax(S), s) = CHOOSE m \in {e2.bal}: TRUE
        BY <2>12
      <2>9. e2.bal = MaxVotedBallotInSlot(PartialBmax(S), s)
        BY <2>13
      <2> QED BY <2>8, <2>9
  <1> QED BY <1>1, <1>2
MsgInv ==
  \A m \in msgs : 
    /\ (m.type = "1b") =>
        /\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                              /\ \E mm \in msgs :
                                   /\ m.from \in mm.to
                                   /\ mm.type = "2a"
                                   /\ mm.bal = r.bal
                                   /\ mm.slot = r.slot
                                   /\ mm.val = r.val
        /\ \A v \in Values, s \in Slots, b \in Ballots :
              GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
        /\ \A s \in Slots, v \in Values, c \in Ballots :
            (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                ~ VotedForIn(m.from, v, c, s)
        /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
        /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                            (\A v \in Values, c \in Ballots :
                              GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s))
    /\ (m.type = "2a") => 
        /\ SafeAt(m.val, m.bal, m.slot)
        /\ Proposed(m.val, m.slot)
        /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val
    /\ (m.type = "2b") => VotedForIn(m.from, m.val, m.bal, m.slot)
    /\ (m.type = "decision") =>
        \E Q \in Quorums, b \in Ballots : \A a \in Q : VotedForIn(a, m.val, b, m.slot)

AccInv ==
  \A a \in Acceptors :
    /\ \A vote \in aVoted[a] :
         /\ \E m \in msgs :
              /\ a \in m.to
              /\ m.type = "2a"
              /\ m.bal = vote.bal
              /\ m.slot = vote.slot
              /\ m.val = vote.val
         /\ \E m \in msgs:
              /\ m.from = a
              /\ m.type = "2b"
              /\ m.bal = vote.bal
              /\ m.slot = vote.slot
              /\ m.val = vote.val
    /\ \A c \in Ballots, s \in Slots, v \in Values :
        GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a], s)) => ~ VotedForIn(a, v, c, s)

PropInv ==
  \A p \in Proposers :
    /\ pState[p] = 1 => ~ \E m \in msgs :
                            /\ m.bal = pBal[p]
                            /\ m.type \in {"1a", "2a"}
    /\ pState[p] = 2 => /\ \E m \in msgs : m.type = "1a" /\ m.bal = pBal[p] /\ m.to = Acceptors
                        /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = pBal[p]
    /\ pState[p] = 3 => /\ \E Q \in Quorums : \A a \in Q : \E m \in msgs :
                            /\ m.type = "1b"
                            /\ m.from = a
                            /\ m.to = p
                            /\ m.bal = pBal[p]
                        /\ \A c \in Ballots, s \in Slots :
                            /\ GreaterBallot(pBal[p], c)
                            /\ ~ \E m \in msgs :
                              /\ m.type = "2a"
                              /\ m.bal = pBal[p]
                              /\ m.slot = s
                            =>
                            \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s)
    /\ ~ \E m \in msgs :  /\ m.type \in {"1a", "2a"}
                          /\ GreaterBallot(m.bal, pBal[p])
                          /\ m.bal.id = p
    /\ pBal[p].id = p

(***************************************************************************)
(* Inv is the complete inductive invariant.                                *)
(***************************************************************************)
Inv == TypeOK /\ MsgInv /\ AccInv /\ PropInv

(***************************************************************************)
(* Simple Continuity Lemmas                                                *)
(***************************************************************************)
LEMMA Phase1aVotedForInv ==
  \A p \in Proposers : TypeOK /\ Phase1a(p) =>
                            \A aa \in Acceptors, bb \in Ballots, vv \in Values, ss \in Slots :
                              VotedForIn(aa, vv, bb, ss) <=> VotedForIn(aa, vv, bb, ss)'
BY DEF VotedForIn, TypeOK, Phase1a, Send

LEMMA Phase1aWontVoteIn ==
  \A p \in Proposers : TypeOK /\ Phase1a(p) =>
                            \A aa \in Acceptors, bb \in Ballots, ss \in Slots :
                              WontVoteIn(aa, bb, ss) => WontVoteIn(aa, bb, ss)'
BY Phase1aVotedForInv DEF WontVoteIn, TypeOK, Phase1a, Send, GreaterBallot

LEMMA Phase1bVotedForInv ==
  \A a \in Acceptors : TypeOK /\ Phase1b(a) =>
                            \A aa \in Acceptors, bb \in Ballots, vv \in Values, ss \in Slots :
                              VotedForIn(aa, vv, bb, ss)' <=> VotedForIn(aa, vv, bb, ss)
BY DEF VotedForIn, TypeOK, Phase1b, Send

LEMMA Phase1bWontVoteIn ==
  \A a \in Acceptors : TypeOK /\ Phase1b(a) =>
                            \A aa \in Acceptors, bb \in Ballots, vv \in Values, ss \in Slots :
                              WontVoteIn(aa, bb, ss) => WontVoteIn(aa, bb, ss)'
  <1> SUFFICES ASSUME NEW a \in Acceptors,
                      TypeOK /\ Phase1b(a),
                      NEW aa \in Acceptors, NEW bb \in Ballots, NEW vv \in Values, NEW ss \in Slots,
                      WontVoteIn(aa, bb, ss)
               PROVE  WontVoteIn(aa, bb, ss)'
    OBVIOUS
  <1>1. CASE aa # a
    BY <1>1, Phase1bVotedForInv DEF WontVoteIn, TypeOK, Phase1b, Send, ValidMessages, ValidMessage1a
  <1>2. CASE aa = a
    <2>1. \A v \in Values : ~VotedForIn(aa, v, bb, ss)'
    BY <1>2, Phase1bVotedForInv, GBTransitive3, GreaterBallot(aBal'[a], aBal[a])
    DEF WontVoteIn, TypeOK, Phase1b, Send, ValidMessages, ValidMessage1a
    <2>2. GreaterBallot(aBal[a], bb)'
    BY <1>2, Phase1bVotedForInv, GBTransitive3, GreaterBallot(aBal'[a], aBal[a])
    DEF WontVoteIn, TypeOK, Phase1b, Send, ValidMessages, ValidMessage1a
    <2> QED BY <2>1, <2>2, <1>2 DEF WontVoteIn
  <1> QED
    BY <1>1, <1>2


LEMMA Phase2a1VotedForInv ==
  \A p \in Proposers : TypeOK /\ Phase2a1(p) =>
                            \A aa \in Acceptors, bb \in Ballots, vv \in Values, ss \in Slots :
                              VotedForIn(aa, vv, bb, ss) <=> VotedForIn(aa, vv, bb, ss)'
BY DEF VotedForIn, TypeOK, Phase2a1, Sends

LEMMA Phase2a1WontVoteIn ==
  \A p \in Proposers : TypeOK /\ Phase2a1(p) =>
                            \A aa \in Acceptors, bb \in Ballots, ss \in Slots :
                              WontVoteIn(aa, bb, ss) => WontVoteIn(aa, bb, ss)'
BY Phase2a1VotedForInv DEF WontVoteIn, TypeOK, Phase2a1, Sends, GreaterBallot, Bmax, PartialBmax

LEMMA Phase2a11VotedForInv ==
  \A p \in Proposers : TypeOK /\ Phase2a11(p) =>
                            \A aa \in Acceptors, bb \in Ballots, vv \in Values, ss \in Slots :
                              VotedForIn(aa, vv, bb, ss) <=> VotedForIn(aa, vv, bb, ss)'
BY DEF VotedForIn, TypeOK, Phase2a11, Send

LEMMA Phase2a11WontVoteIn ==
  \A p \in Proposers : TypeOK /\ Phase2a11(p) =>
                            \A aa \in Acceptors, bb \in Ballots, ss \in Slots :
                              WontVoteIn(aa, bb, ss) => WontVoteIn(aa, bb, ss)'
BY Phase2a11VotedForInv DEF WontVoteIn, TypeOK, Phase2a11, Send, GreaterBallot, Bmax, PartialBmax

LEMMA Phase2a12VotedForInv ==
  \A p \in Proposers : TypeOK /\ Phase2a12(p) =>
                            \A aa \in Acceptors, bb \in Ballots, vv \in Values, ss \in Slots :
                              VotedForIn(aa, vv, bb, ss) <=> VotedForIn(aa, vv, bb, ss)'
BY DEF VotedForIn, TypeOK, Phase2a12, Send

LEMMA Phase2a12WontVoteIn ==
  \A p \in Proposers : TypeOK /\ Phase2a12(p) =>
                            \A aa \in Acceptors, bb \in Ballots, ss \in Slots :
                              WontVoteIn(aa, bb, ss) => WontVoteIn(aa, bb, ss)'
BY Phase2a12VotedForInv DEF WontVoteIn, TypeOK, Phase2a12, Send, GreaterBallot, Bmax, PartialBmax

LEMMA Phase2a13VotedForInv ==
  \A p \in Proposers : TypeOK /\ Phase2a13(p) =>
                            \A aa \in Acceptors, bb \in Ballots, vv \in Values, ss \in Slots :
                              VotedForIn(aa, vv, bb, ss) <=> VotedForIn(aa, vv, bb, ss)'
BY DEF VotedForIn, TypeOK, Phase2a13, Send

LEMMA Phase2a13WontVoteIn ==
  \A p \in Proposers : TypeOK /\ Phase2a13(p) =>
                            \A aa \in Acceptors, bb \in Ballots, ss \in Slots :
                              WontVoteIn(aa, bb, ss) => WontVoteIn(aa, bb, ss)'
BY Phase2a13VotedForInv DEF WontVoteIn, TypeOK, Phase2a13, Send, GreaterBallot, Bmax, PartialBmax

LEMMA Phase2bVotedForInv ==
  \A a \in Acceptors : TypeOK /\ Phase2b(a) =>
                            \A aa \in Acceptors, bb \in Ballots, vv \in Values, ss \in Slots :
                              VotedForIn(aa, vv, bb, ss) => VotedForIn(aa, vv, bb, ss)'
BY DEF VotedForIn, TypeOK, Phase2b, Send

LEMMA Phase2bWontVoteIn ==
  \A a \in Acceptors : TypeOK /\ Phase2b(a) =>
                            \A aa \in Acceptors, bb \in Ballots, ss \in Slots :
                              WontVoteIn(aa, bb, ss) => WontVoteIn(aa, bb, ss)'
  <1> SUFFICES ASSUME NEW a \in Acceptors,
                      TypeOK /\ Phase2b(a),
                      NEW aa \in Acceptors, NEW bb \in Ballots, NEW ss \in Slots,
                      \A v \in Values : ~ VotedForIn(aa, v, bb, ss),
                      GreaterBallot(aBal[aa], bb)
               PROVE  WontVoteIn(aa, bb, ss)'
    BY DEF WontVoteIn
  <1>10. aBal[aa]' \in Ballots \cup {[num |-> -1, id |-> -1]}
    BY DEF Phase2b, TypeOK, ValidMessages, ValidMessage2a
  <1>11. GreaterOrEqualBallot(aBal'[aa], aBal[aa])
    BY DEF Phase2b, GreaterOrEqualBallot
  <1>2. (GreaterBallot(aBal[aa], bb))'
    BY <1>11, <1>10, GBTransitive DEF TypeOK, Phase2b
  <1>12. bb # aBal[aa]'
    BY <1>2 DEF GreaterBallot, Ballots
  <1>1. (\A v \in Values : ~ VotedForIn(aa, v, bb, ss))'
    <2>0. PICK m \in msgs: Phase2b(a)!(m) BY DEF Phase2b
    <2>1. CASE aa = a
      <3>1. GreaterBallot(m.bal, bb)
      BY <2>0, <2>1, <1>12, GBTransitive DEF TypeOK, ValidMessages, ValidMessage2a
      <3>2. m.bal # bb BY <3>1 DEF GreaterBallot
      <3> QED BY <2>0, <3>2, <2>1 DEF TypeOK, VotedForIn
    <2>2. CASE aa # a
      BY Phase2bVotedForInv, <2>2 DEF TypeOK, Phase2b, Send, VotedForIn
    <2> QED BY <2>1, <2>2
  <1>3. QED
    BY <1>1, <1>2 DEF WontVoteIn

LEMMA PhasePrVotedForInv ==
  \A a \in Acceptors : TypeOK /\ PhasePr(a) =>
                            \A aa \in Acceptors, bb \in Ballots, vv \in Values, ss \in Slots :
                              VotedForIn(aa, vv, bb, ss) <=> VotedForIn(aa, vv, bb, ss)'
BY DEF VotedForIn, TypeOK, PhasePr, Send

LEMMA PhasePrWontVoteIn ==
  \A a \in Acceptors : TypeOK /\ PhasePr(a) =>
                            \A aa \in Acceptors, bb \in Ballots, vv \in Values, ss \in Slots :
                              WontVoteIn(aa, bb, ss) <=> WontVoteIn(aa, bb, ss)'
BY DEF WontVoteIn, VotedForIn, TypeOK, PhasePr, Send
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following lemma shows that (the invariant implies that) the         *)
(* predicate SafeAt(v, b,s) is stable, meaning that once it becomes true,  *)
(* it remains true throughout the rest of the excecution.                  *)
(***************************************************************************)
LEMMA SafeAtStable == Inv /\ Next /\ TypeOK' => 
                          \A v \in Values, b \in Ballots, s \in Slots:
                                  SafeAt(v, b, s) => SafeAt(v, b, s)'
  <1> SUFFICES ASSUME Inv,
                      TypeOK',
                      Next
               PROVE  \A v \in Values, b \in Ballots, s \in Slots:
                              SafeAt(v, b, s) => SafeAt(v, b, s)'
    OBVIOUS
  <1>1. ASSUME NEW p \in Proposers,
               Phase1a(p)
        PROVE  \A v \in Values, b \in Ballots, s \in Slots:
                       SafeAt(v, b, s) => SafeAt(v, b, s)'
      BY Phase1aVotedForInv, Phase1aWontVoteIn, QuorumAssumption, <1>1 DEF SafeAt, Inv, GreaterBallot, Ballots
  <1>2. ASSUME NEW p \in Proposers,
               Phase2a1(p)
        PROVE  \A v \in Values, b \in Ballots, s \in Slots:
                       SafeAt(v, b, s) => SafeAt(v, b, s)'
      BY Phase2a1VotedForInv, Phase2a1WontVoteIn, QuorumAssumption, <1>2 DEF SafeAt, Inv, GreaterBallot, Ballots
  <1>3. ASSUME NEW p \in Proposers,
               Phase2a11(p)
        PROVE  \A v \in Values, b \in Ballots, s \in Slots:
                       SafeAt(v, b, s) => SafeAt(v, b, s)'
      BY Phase2a11VotedForInv, Phase2a11WontVoteIn, QuorumAssumption, <1>3 DEF SafeAt, Inv, GreaterBallot, Ballots
  <1>4. ASSUME NEW p \in Proposers,
               Phase2a12(p)
        PROVE  \A v \in Values, b \in Ballots, s \in Slots:
                       SafeAt(v, b, s) => SafeAt(v, b, s)'
      BY Phase2a12VotedForInv, Phase2a12WontVoteIn, QuorumAssumption, <1>4 DEF SafeAt, Inv, GreaterBallot, Ballots
  <1>5. ASSUME NEW p \in Proposers,
               Phase2a13(p)
        PROVE  \A v \in Values, b \in Ballots, s \in Slots:
                       SafeAt(v, b, s) => SafeAt(v, b, s)'
      BY Phase2a13VotedForInv, Phase2a13WontVoteIn, QuorumAssumption, <1>5 DEF SafeAt, Inv, GreaterBallot, Ballots
  <1>6. ASSUME NEW a \in Acceptors,
               Phase1b(a)
        PROVE  \A v \in Values, b \in Ballots, s \in Slots:
                       SafeAt(v, b, s) => SafeAt(v, b, s)'
      BY Phase1bVotedForInv, Phase1bWontVoteIn, QuorumAssumption, <1>6 DEF SafeAt, Inv, GreaterBallot, Ballots
  <1>7. ASSUME NEW a \in Acceptors,
               Phase2b(a)
        PROVE  \A v \in Values, b \in Ballots, s \in Slots:
                       SafeAt(v, b, s) => SafeAt(v, b, s)'
      BY Phase2bVotedForInv, Phase2bWontVoteIn, QuorumAssumption, <1>7 DEF SafeAt, Inv
  <1>8. ASSUME NEW a \in Acceptors,
               PhasePr(a)
        PROVE  \A v \in Values, b \in Ballots, s \in Slots:
                       SafeAt(v, b, s) => SafeAt(v, b, s)'
      BY PhasePrVotedForInv, PhasePrWontVoteIn, QuorumAssumption, <1>8 DEF SafeAt, Inv
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8 DEF Next
------------------------------------------------------------------------

LEMMA VotedOnce == 
        MsgInv /\ AccInv => \A a1, a2 \in Acceptors, b \in Ballots, v1, v2 \in Values, s \in Slots :
                       VotedForIn(a1, v1, b, s) /\ VotedForIn(a2, v2, b, s) => (v1 = v2)
BY DEF MsgInv, VotedForIn, AccInv

LEMMA VotedInv == 
  Inv => 
    \A a \in Acceptors, v \in Values, b \in Ballots, s \in Slots :
        VotedForIn(a, v, b, s) => SafeAt(v, b, s)
BY DEF VotedForIn, MsgInv, AccInv, Inv

LEMMA VotedUnion ==
  Inv => \A m1, m2 \in msgs: 
    /\ m1.type = "1b"
    /\ m2.type = "1b"
    => \A d1 \in m1.voted, d2 \in m2.voted :
        /\ d1.bal = d2.bal
        /\ d1.slot = d2.slot
        => d1.val = d2.val
  <1> SUFFICES ASSUME MsgInv /\ TypeOK /\ AccInv,
                      NEW m1 \in msgs, NEW m2 \in msgs,
                      /\ m1.type = "1b"
                      /\ m2.type = "1b",
                      NEW d1 \in m1.voted, NEW d2 \in m2.voted,
                      d1.bal = d2.bal, d1.slot = d2.slot
               PROVE  d1.val = d2.val
    BY DEF Inv
    <1>1. VotedForIn(m1.from, d1.val, d1.bal, d1.slot)
      BY DEF MsgInv
    <1>2. VotedForIn(m2.from, d2.val, d2.bal, d2.slot)
      BY DEF MsgInv
  <1> QED BY <1>1, <1>2, VotedOnce DEF TypeOK, Inv, ValidMessages, ValidMessage1b

THEOREM Invariant == Spec => []Inv
<1> USE DEF Ballots, Slots
<1>1. Init => Inv
  <2> SUFFICES ASSUME Init
               PROVE  Inv
    OBVIOUS
  <2>1. TypeOK
    BY DEF Init, Inv, TypeOK, AccInv, MsgInv, VotedForIn, PropInv, ValidMessages, VotedForIn
  <2>2. MsgInv
    BY DEF Init, Inv, TypeOK, AccInv, MsgInv, VotedForIn, PropInv, ValidMessages, VotedForIn
  <2>3. AccInv
    BY DEF Init, Inv, TypeOK, AccInv, MsgInv, VotedForIn, PropInv, ValidMessages, VotedForIn,
    MaxVotedBallotInSlot, MaximumBallot, GreaterOrEqualBallot
  <2>4. PropInv
    BY DEF Init, Inv, TypeOK, AccInv, MsgInv, VotedForIn, PropInv, ValidMessages, VotedForIn
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4 DEF Inv
  
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    BY DEF Inv
  <2>1. ASSUME NEW p \in Proposers,
               Phase1a(p)
        PROVE  Inv'
    <3>1. TypeOK'
      <4>1. ValidMessages(msgs)'
        BY <2>1 DEF Phase1a, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      ValidMessagepreempt
      <4>2. (pBal \in [Proposers -> Ballots])'
        BY <2>1 DEF Phase1a, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose
      <4>3. (pState \in [Proposers -> {1, 2, 3}])'
        BY <2>1 DEF Phase1a, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose
      <4>4. (\A a \in Acceptors : /\ aVoted[a] \subseteq [bal : Ballots, slot : Slots, val : Values]
                                  /\ aBal[a] \in Ballots \cup {[num |-> -1, id |-> -1]})'
        BY <2>1 DEF Phase1a, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose
      <4>5. QED
        BY <4>1, <4>2, <4>3, <4>4 DEF TypeOK
      
    <3>2. MsgInv'
      <4> SUFFICES ASSUME NEW m \in msgs'
                   PROVE  (/\ (m.type = "1b") =>
                               /\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                     /\ \E mm \in msgs :
                                                          /\ m.from \in mm.to
                                                          /\ mm.type = "2a"
                                                          /\ mm.bal = r.bal
                                                          /\ mm.slot = r.slot
                                                          /\ mm.val = r.val
                               /\ \A v \in Values, s \in Slots, b \in Ballots :
                                     GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                       => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                               /\ \A s \in Slots, v \in Values, c \in Ballots :
                                   (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                       ~ VotedForIn(m.from, v, c, s)
                               /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                               /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                   (\A v \in Values, c \in Ballots :
                                                     GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s))
                           /\ (m.type = "2a") => 
                               /\ SafeAt(m.val, m.bal, m.slot)
                               /\ Proposed(m.val, m.slot)
                               /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val
                           /\ (m.type = "2b") => VotedForIn(m.from, m.val, m.bal, m.slot)
                           /\ (m.type = "decision") =>
                               \E Q \in Quorums, b \in Ballots : \A a \in Q : VotedForIn(a, m.val, b, m.slot))'
        BY DEF MsgInv
      <4>1. ((m.type = "1b") =>
              /\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                    /\ \E mm \in msgs :
                                         /\ m.from \in mm.to
                                         /\ mm.type = "2a"
                                         /\ mm.bal = r.bal
                                         /\ mm.slot = r.slot
                                         /\ mm.val = r.val
              /\ \A v \in Values, s \in Slots, b \in Ballots :
                    GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                      => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
              /\ \A s \in Slots, v \in Values, c \in Ballots :
                  (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                      ~ VotedForIn(m.from, v, c, s)
              /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
              /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                  (\A v \in Values, c \in Ballots :
                                    GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
        <5> SUFFICES ASSUME (m.type = "1b")'
                     PROVE  (/\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                   /\ \E mm \in msgs :
                                                        /\ m.from \in mm.to
                                                        /\ mm.type = "2a"
                                                        /\ mm.bal = r.bal
                                                        /\ mm.slot = r.slot
                                                        /\ mm.val = r.val
                             /\ \A v \in Values, s \in Slots, b \in Ballots :
                                   GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                     => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                             /\ \A s \in Slots, v \in Values, c \in Ballots :
                                 (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                     ~ VotedForIn(m.from, v, c, s)
                             /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                             /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                 (\A v \in Values, c \in Ballots :
                                                   GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
          OBVIOUS
        <5>1. (\A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                  /\ \E mm \in msgs :
                                       /\ m.from \in mm.to
                                       /\ mm.type = "2a"
                                       /\ mm.bal = r.bal
                                       /\ mm.slot = r.slot
                                       /\ mm.val = r.val)'
          BY <2>1 DEF VotedForIn, MsgInv, Phase1a, Inv, Send, VotedForIn, VotedForIn, WontVoteIn
        <5>2. (\A v \in Values, s \in Slots, b \in Ballots :
                  GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                    => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)'
          <6> SUFFICES ASSUME NEW v \in Values', NEW s \in Slots', NEW b \in Ballots',
                              (GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s))'
                       PROVE  (\E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)'
            OBVIOUS
            <6>1. GreaterBallot(m.bal, b)
              BY DEF GreaterBallot
            <6>2. VotedForIn(m.from, v, b, s)
              BY <2>1 DEF VotedForIn, Phase1a
            <6>3. \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
              BY <6>1, <6>2, <2>1 DEF Inv, MsgInv, Phase1a, Send
          <6> QED
            BY <6>3, <2>1 DEF Phase1a, Send
          
        <5>3. (\A s \in Slots, v \in Values, c \in Ballots :
                (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                    ~ VotedForIn(m.from, v, c, s))'
          <6> SUFFICES ASSUME NEW s \in Slots', NEW v \in Values', NEW c \in Ballots',
                              (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s)))'
                       PROVE  (~ VotedForIn(m.from, v, c, s))'
            OBVIOUS
            <6>1. GreaterBallot(m.bal, c)
              BY DEF GreaterBallot
            <6>2. GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))
              BY DEF GreaterBallot
            <6>3. ~ VotedForIn(m.from, v, c, s)
              BY <6>1, <6>2, <2>1 DEF Inv, MsgInv, Phase1a, Send
          <6> QED
            BY <6>3, <2>1 DEF VotedForIn, Phase1a, Send
          
        <5>4. GreaterOrEqualBallot(aBal[m.from], m.bal)'
          BY <2>1 DEF VotedForIn, MsgInv, Phase1a, Inv, Send, VotedForIn
        <5>5. (\A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                (\A v \in Values, c \in Ballots :
                                  GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
          BY <2>1 DEF VotedForIn, MsgInv, Phase1a, Inv, Send, VotedForIn
        <5>6. QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5
        
      <4>2. ((m.type = "2a") => 
              /\ SafeAt(m.val, m.bal, m.slot)
              /\ Proposed(m.val, m.slot)
              /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
        <5> SUFFICES ASSUME (m.type = "2a")'
                     PROVE  (/\ SafeAt(m.val, m.bal, m.slot)
                             /\ Proposed(m.val, m.slot)
                             /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
          OBVIOUS
        <5>1. SafeAt(m.val, m.bal, m.slot)'
          BY <2>1, QuorumAssumption, SystemAssumptions
          DEF VotedForIn, MsgInv, Phase1a, Inv, Send, SafeAt, Proposed, VotedForIn, WontVoteIn, GreaterBallot
        <5>2. Proposed(m.val, m.slot)'
          BY <2>1, QuorumAssumption, SystemAssumptions, m \in msgs, msgs \subseteq msgs'
          DEF MsgInv, Phase1a, Inv, Send, Proposed
        <5>3. (\A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
          BY <2>1, QuorumAssumption, SystemAssumptions
          DEF VotedForIn, MsgInv, Phase1a, Inv, Send, SafeAt, Proposed, VotedForIn, WontVoteIn, GreaterBallot
        <5>4. QED
          BY <5>1, <5>2, <5>3
      <4>3. ((m.type = "2b") => VotedForIn(m.from, m.val, m.bal, m.slot))'
        BY <2>1 DEF VotedForIn, MsgInv, Inv, Send, Phase1a, TypeOK, ValidMessages, ValidMessage2b
      <4>4. ((m.type = "decision") =>
              \E Q \in Quorums, b \in Ballots : \A a \in Q : VotedForIn(a, m.val, b, m.slot))'
        BY <2>1, QuorumAssumption, SystemAssumptions DEF VotedForIn, MsgInv, Phase1a, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot
      <4>5. QED
        BY <4>1, <4>2, <4>3, <4>4
      
    <3>3. AccInv'
      <4> SUFFICES ASSUME NEW a \in Acceptors'
                   PROVE  (/\ \A vote \in aVoted[a] :
                                /\ \E m \in msgs :
                                     /\ a \in m.to
                                     /\ m.type = "2a"
                                     /\ m.bal = vote.bal
                                     /\ m.slot = vote.slot
                                     /\ m.val = vote.val
                                /\ \E m \in msgs:
                                     /\ m.from = a
                                     /\ m.type = "2b"
                                     /\ m.bal = vote.bal
                                     /\ m.slot = vote.slot
                                     /\ m.val = vote.val
                           /\ \A c \in Ballots, s \in Slots, v \in Values :
                               GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a], s)) => ~ VotedForIn(a, v, c, s))'
        BY DEF AccInv
      <4>1. (\A vote \in aVoted[a] :
               /\ \E m \in msgs :
                    /\ a \in m.to
                    /\ m.type = "2a"
                    /\ m.bal = vote.bal
                    /\ m.slot = vote.slot
                    /\ m.val = vote.val
               /\ \E m \in msgs:
                    /\ m.from = a
                    /\ m.type = "2b"
                    /\ m.bal = vote.bal
                    /\ m.slot = vote.slot
                    /\ m.val = vote.val)'
        BY <2>1 DEF AccInv, Phase1a, Inv, Send, MaxVotedBallotInSlot, MaximumBallot, GreaterBallot, VotedForIn
      <4>2. (\A c \in Ballots, s \in Slots, v \in Values :
              GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a], s)) => ~ VotedForIn(a, v, c, s))'
        <5> SUFFICES ASSUME NEW c \in Ballots', NEW s \in Slots', NEW v \in Values',
                            GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a], s))'
                     PROVE  (~ VotedForIn(a, v, c, s))'
          OBVIOUS
          <5>1. GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a], s))
            BY <2>1 DEF Phase1a, Send
          <5>2. (~ VotedForIn(a, v, c, s))
            BY <2>1, <5>1 DEF Inv, AccInv, Phase1a, Send
        <5> QED
          BY <5>2, <2>1 DEF VotedForIn, Phase1a
      <4>4. QED
        BY <4>1, <4>2

    <3>4. PropInv'
      <4> SUFFICES ASSUME NEW p_1 \in Proposers'
                   PROVE  (/\ pState[p_1] = 1 => ~ \E m \in msgs :
                                                     /\ m.bal = pBal[p_1]
                                                   /\ m.type \in {"1a", "2a"}
                           /\ pState[p_1] = 2 => /\ \E m \in msgs : m.type = "1a" /\ m.bal = pBal[p_1] /\ m.to = Acceptors
                                                 /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = pBal[p_1]
                           /\ pState[p_1] = 3 => /\ \E Q \in Quorums : \A a \in Q : \E m \in msgs :
                                                     /\ m.type = "1b"
                                                   /\ m.from = a
                                                   /\ m.to = p_1
                                                   /\ m.bal = pBal[p_1]
                                                 /\ \A c \in Ballots, s \in Slots :
                                                   /\ GreaterBallot(pBal[p_1], c)
                                                   (*/\ \E m \in msgs :
                                                     /\ m.type = "2a"
                                                     /\ m.bal = pBal[p_1]*)
                                                   /\ ~ \E m \in msgs :
                                                     /\ m.type = "2a"
                                                     /\ m.bal = pBal[p_1]
                                                     /\ m.slot = s
                                                   =>
                                                   \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s)
                           /\ ~ \E m \in msgs :  /\ m.type \in {"1a", "2a"}
                                                 /\ GreaterBallot(m.bal, pBal[p_1])
                                                 /\ m.bal.id = p_1
                           /\ pBal[p_1].id = p_1)'
        BY DEF PropInv
      <4>1. (pState[p_1] = 1 => ~ \E m \in msgs :
                                    /\ m.bal = pBal[p_1]
                                  /\ m.type \in {"1a", "2a"})'
        BY <2>1, <3>1 DEF Phase1a, Send, Inv, PropInv, TypeOK
      <4>2. (pState[p_1] = 2 => /\ \E m \in msgs : m.type = "1a" /\ m.bal = pBal[p_1] /\ m.to = Acceptors
                                /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = pBal[p_1])'
        <5> SUFFICES ASSUME (pState[p_1] = 2)'
                     PROVE  (/\ \E m \in msgs : m.type = "1a" /\ m.bal = pBal[p_1] /\ m.to = Acceptors
                             /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = pBal[p_1])'
          OBVIOUS
        <5>1. (\E m \in msgs : m.type = "1a" /\ m.bal = pBal[p_1] /\ m.to = Acceptors)'
          <6>0. ~ \E m \in msgs : m.type = "1a" /\ m.bal = pBal[p]
            BY <2>1, SystemAssumptions DEF Phase1a, Sends, Inv, PropInv, TypeOK
          <6>2. \A m \in msgs' \msgs : m.type = "1a" /\ m.bal = pBal[p] /\ m.to = Acceptors
            BY <2>1 DEF Phase1a, Send, Inv, TypeOK
          <6>1. \E m \in msgs' : m \notin msgs
            BY <6>0, <2>1, <6>2 DEF Phase1a, Send, Inv, TypeOK\*, ValidMessages, ValidMessage1a, ValidMessage2a
          <6> QED BY <6>1, <6>2, <2>1 DEF PropInv, Inv, TypeOK, Phase1a, Send
          
        <5>2. (~ \E m \in msgs : m.type = "2a" /\ m.bal = pBal[p_1])'
          BY <2>1, \A m \in msgs' \msgs : m.type # "2a", <3>1 DEF Phase1a, Send, Inv, PropInv, TypeOK
        <5>3. QED
          BY <5>1, <5>2

      <4>3. (pState[p_1] = 3 => /\ \E Q \in Quorums : \A a \in Q : \E m \in msgs :
                                    /\ m.type = "1b"
                                  /\ m.from = a
                                  /\ m.to = p_1
                                  /\ m.bal = pBal[p_1]
                                /\ \A c \in Ballots, s \in Slots :
                                  /\ GreaterBallot(pBal[p_1], c)
                                  (*/\ \E m \in msgs :
                                    /\ m.type = "2a"
                                    /\ m.bal = pBal[p_1]*)
                                  /\ ~ \E m \in msgs :
                                    /\ m.type = "2a"
                                    /\ m.bal = pBal[p_1]
                                    /\ m.slot = s
                                  =>
                                  \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s))'
        <5> SUFFICES ASSUME (pState[p_1] = 3)'
                     PROVE  (/\ \E Q \in Quorums : \A a \in Q : \E m \in msgs :
                                 /\ m.type = "1b"
                               /\ m.from = a
                               /\ m.to = p_1
                               /\ m.bal = pBal[p_1]
                             /\ \A c \in Ballots, s \in Slots :
                               /\ GreaterBallot(pBal[p_1], c)
                               (*/\ \E m \in msgs :
                                 /\ m.type = "2a"
                                 /\ m.bal = pBal[p_1]*)
                               /\ ~ \E m \in msgs :
                                 /\ m.type = "2a"
                                 /\ m.bal = pBal[p_1]
                                 /\ m.slot = s
                               =>
                               \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s))'
          OBVIOUS
        <5>1. ( \E Q \in Quorums : \A a \in Q : \E m \in msgs :
                 /\ m.type = "1b"
               /\ m.from = a
               /\ m.to = p_1
               /\ m.bal = pBal[p_1])'
          BY <2>1, <3>1 DEF Phase1a, Send, Inv, PropInv, TypeOK
        <5>2. ( \A c \in Ballots, s \in Slots :
               /\ GreaterBallot(pBal[p_1], c)
               (*/\ \E m \in msgs :
                 /\ m.type = "2a"
                 /\ m.bal = pBal[p_1]*)
               /\ ~ \E m \in msgs :
                 /\ m.type = "2a"
                 /\ m.bal = pBal[p_1]
                 /\ m.slot = s
               =>
               \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s))'
          <6> SUFFICES ASSUME NEW c \in Ballots', NEW s \in Slots',
                              (/\ GreaterBallot(pBal[p_1], c)
                               (*/\ \E m \in msgs :
                                 /\ m.type = "2a"
                                 /\ m.bal = pBal[p_1]*)
                               /\ ~ \E m \in msgs :
                                 /\ m.type = "2a"
                                 /\ m.bal = pBal[p_1]
                                 /\ m.slot = s)'
                       PROVE  (\E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s))'
            OBVIOUS
            <6>1. \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s)
              BY <2>1, <3>1, p # p_1, QuorumAssumption DEF Inv, PropInv, Phase1a, Send, TypeOK
          <6> QED
            BY <2>1, <3>1, Phase1aWontVoteIn, Phase1aVotedForInv, <6>1, QuorumAssumption DEF Inv
          
        <5>3. QED
          BY <5>1, <5>2
        
      <4>4. (~ \E m \in msgs :  /\ m.type \in {"1a", "2a"}
                                /\ GreaterBallot(m.bal, pBal[p_1])
                                /\ m.bal.id = p_1)'
        <5>1. \A m \in msgs' \msgs : m.bal.id = p
          BY <2>1 DEF Phase1a, Send, Inv, PropInv, GreaterBallot
        <5>2. ~ (GreaterBallot(pBal[p], pBal[p]))
          BY DEF GreaterBallot
        <5>3. \A m \in msgs' \msgs : ~( /\ GreaterBallot(m.bal, pBal[p])
                                        /\ m.bal.id = p)
          BY <2>1, <5>1, <5>2 DEF Phase1a, Send, Inv, PropInv, GreaterBallot
        <5> QED BY <5>3, <2>1 DEF Phase1a, Send, Inv, PropInv

      <4>5. (pBal[p_1].id = p_1)'
        BY <2>1, <3>1 DEF Phase1a, Send, Inv, PropInv, TypeOK
      <4>6. QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5
      
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Inv

  <2>2. ASSUME NEW p \in Proposers,
               Phase2a1(p)
        PROVE  Inv'
    <3>0. PICK Q \in Quorums, S \in SUBSET {m_1 \in msgs : m_1.type = "1b" /\ m_1.bal = pBal[p] /\ m_1.to = p} :
            /\ \A a \in Q : \E m_1 \in S : m_1.from = a
            /\ Sends({[type |-> "2a",
                       bal |-> pBal[p],
                       slot |-> t.slot,
                       val |-> t.val,
                       from |-> p,
                       to |-> Acceptors] : t \in Bmax(UNION {m_1.voted : m_1 \in S})})
            /\ pState[p] \in {2}
            /\ pState' = [pState EXCEPT ![p] = 3]
            /\ UNCHANGED <<pBal, aVoted, aBal>>
      BY <2>2 DEF Phase2a1

    <3>1. TypeOK'
      <4>1. (ValidMessages(msgs))'
        <5> SUFFICES ASSUME NEW m \in msgs'
                     PROVE  (/\ m.type \in {"1a", "1b", "2a", "2b", "decision", "propose", "preempt"}
                             /\ m.type = "1a" => ValidMessage1a(m)
                             /\ m.type = "1b" => ValidMessage1b(m)
                             /\ m.type = "2a" => ValidMessage2a(m)
                             /\ m.type = "2b" => ValidMessage2b(m)
                             /\ m.type = "decision" => ValidMessagedecision(m)
                             /\ m.type = "preempt"  => ValidMessagepreempt(m)
                             /\ m.type = "propose"  => ValidMessagepropose(m))'
          BY DEF ValidMessages
        <5>1. (m.type \in {"1a", "1b", "2a", "2b", "decision", "propose", "preempt"})'
          BY <2>2 DEF Phase2a1, TypeOK, Sends, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      Bmax, PartialBmax, GreaterBallot
        <5>2. (m.type = "1a" => ValidMessage1a(m))'
          BY <2>2 DEF Phase2a1, TypeOK, Sends, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      Bmax, PartialBmax, GreaterBallot
        <5>3. (m.type = "1b" => ValidMessage1b(m))'
          BY <2>2 DEF Phase2a1, TypeOK, Sends, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      Bmax, PartialBmax, GreaterBallot
        <5>4. (m.type = "2a" => ValidMessage2a(m))'
          <6> SUFFICES ASSUME (m.type = "2a")'
                       PROVE  ValidMessage2a(m)'
            OBVIOUS
          <6>1. (m.bal \in Ballots)'
            BY <2>2 DEF Phase2a1, TypeOK, Sends, Inv, ValidMessages, ValidMessage1b,
                        ValidMessage2a, Bmax, PartialBmax, GreaterBallot
          <6>21. \A t \in Bmax(UNION {m_1.voted : m_1 \in S}) : t.slot \in Slots /\ t.val \in Values
            BY <3>0 DEF Bmax, PartialBmax, GreaterBallot, Inv, TypeOK, ValidMessages, ValidMessage1b
          <6>2. (m.slot \in Slots)'
            BY <3>0, <6>21 DEF Sends, TypeOK, Inv, ValidMessages, ValidMessage2a
          <6>3. (m.val \in Values)'
            BY <3>0, <6>21 DEF Sends, TypeOK, Inv, ValidMessages, ValidMessage2a
          <6>4. (m.from \in Proposers)'
            BY <2>2 DEF Phase2a1, TypeOK, Sends, Inv, ValidMessages, ValidMessage1b,
                        ValidMessage2a, Bmax, PartialBmax, GreaterBallot
          <6>5. (m.to \subseteq Acceptors)'
            BY <2>2 DEF Phase2a1, TypeOK, Sends, Inv, ValidMessages, ValidMessage1b,
                        ValidMessage2a, Bmax, PartialBmax, GreaterBallot
          <6>6. QED
            BY <6>1, <6>2, <6>3, <6>4, <6>5 DEF ValidMessage2a
          
        <5>5. (m.type = "2b" => ValidMessage2b(m))'
          BY <2>2 DEF Phase2a1, TypeOK, Sends, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      Bmax, PartialBmax, GreaterBallot
        <5>6. (m.type = "decision" => ValidMessagedecision(m))'
          BY <2>2 DEF Phase2a1, TypeOK, Sends, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      Bmax, PartialBmax, GreaterBallot
        <5>7. (m.type = "propose"  => ValidMessagepropose(m))'
          BY <2>2 DEF Phase2a1, TypeOK, Sends, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      Bmax, PartialBmax, GreaterBallot
        <5>9. (m.type = "preempt"  => ValidMessagepreempt(m))'
          BY <2>2 DEF Phase2a1, TypeOK, Sends, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      Bmax, PartialBmax, GreaterBallot, ValidMessagepreempt
        <5>8. QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>9
      <4>5. QED
        BY <4>1, <2>2 DEF Phase2a1, TypeOK, Sends, Inv
      
    <3>2. MsgInv'
      <4> SUFFICES ASSUME NEW m \in msgs'
                   PROVE  (/\ (m.type = "1b") =>
                               /\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                     /\ \E mm \in msgs :
                                                       /\ m.from \in mm.to
                                                       /\ mm.type = "2a"
                                                       /\ mm.bal = r.bal
                                                       /\ mm.slot = r.slot
                                                       /\ mm.val = r.val  
                               /\ \A v \in Values, s \in Slots, b \in Ballots :
                                    GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                    => (\E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)
                               /\ \A s \in Slots, v \in Values, c \in Ballots :
                                   (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                       ~ VotedForIn(m.from, v, c, s)
                               /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                               /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                   (\A v \in Values, c \in Ballots :
                                                     GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s))
                           /\ (m.type = "2a") => 
                               /\ SafeAt(m.val, m.bal, m.slot)
                               /\ Proposed(m.val, m.slot)
                               /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val
                           /\ m.type = "2b" => VotedForIn(m.from, m.val, m.bal, m.slot)
                           /\ (m.type = "decision") =>
                               \E Q_1 \in Quorums, b \in Ballots : \A a \in Q_1 : VotedForIn(a, m.val, b, m.slot))'
        BY DEF MsgInv
      <4>1. ((m.type = "1b") =>
                               /\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                     /\ \E mm \in msgs :
                                                       /\ m.from \in mm.to
                                                       /\ mm.type = "2a"
                                                       /\ mm.bal = r.bal
                                                       /\ mm.slot = r.slot
                                                       /\ mm.val = r.val  
                               /\ \A v \in Values, s \in Slots, b \in Ballots :
                                    GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                    => (\E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)
                               /\ \A s \in Slots, v \in Values, c \in Ballots :
                                   (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                       ~ VotedForIn(m.from, v, c, s)
                               /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                               /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                   (\A v \in Values, c \in Ballots :
                                                     GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
        <5> SUFFICES ASSUME (m.type = "1b")'
                     PROVE  (/\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                   /\ \E mm \in msgs :
                                                     /\ m.from \in mm.to
                                                     /\ mm.type = "2a"
                                                     /\ mm.bal = r.bal
                                                     /\ mm.slot = r.slot
                                                     /\ mm.val = r.val  
                             /\ \A v \in Values, s \in Slots, b \in Ballots :
                                  GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                  => (\E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)
                             /\ \A s \in Slots, v \in Values, c \in Ballots :
                                 (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                     ~ VotedForIn(m.from, v, c, s)
                             /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                             /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                 (\A v \in Values, c \in Ballots :
                                                   GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
          OBVIOUS
        <5>1. (\A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                  /\ \E mm \in msgs :
                                    /\ m.from \in mm.to
                                    /\ mm.type = "2a"
                                    /\ mm.bal = r.bal
                                    /\ mm.slot = r.slot
                                    /\ mm.val = r.val)'
          BY <2>2 DEF VotedForIn, MsgInv, Phase2a1, Inv, Sends, VotedForIn, WontVoteIn, GreaterBallot, Bmax, PartialBmax
        <5>2. (\A v \in Values, s \in Slots, b \in Ballots :
                 GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                 => (\E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s))'
          <6> SUFFICES ASSUME NEW v \in Values', NEW s \in Slots', NEW b \in Ballots',
                              (GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s))'
                       PROVE  (\E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)'
            OBVIOUS
            <6>1. GreaterBallot(m.bal, b)
              BY DEF GreaterBallot
            <6>2. VotedForIn(m.from, v, b, s)
              BY <2>2 DEF VotedForIn, Phase2a1
            <6>3. \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
              BY <6>1, <6>2, <2>2 DEF Inv, MsgInv, Phase2a1, Sends, Bmax, PartialBmax
          <6> QED
            BY <6>3, <2>2 DEF Phase2a1, Sends
          
        <5>3. (\A s \in Slots, v \in Values, c \in Ballots :
                (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                    ~ VotedForIn(m.from, v, c, s))'
          <6> SUFFICES ASSUME NEW s \in Slots', NEW v \in Values', NEW c \in Ballots',
                              (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s)))'
                       PROVE  (~ VotedForIn(m.from, v, c, s))'
            OBVIOUS
            <6>1. GreaterBallot(m.bal, c)
              BY DEF GreaterBallot
            <6>2. GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))
              BY DEF GreaterBallot
            <6>3. ~ VotedForIn(m.from, v, c, s)
              BY <6>1, <6>2, <2>2 DEF Inv, MsgInv, Phase2a1, Sends, Bmax, PartialBmax
          <6> QED
            BY <6>3, <2>2 DEF VotedForIn, Phase2a1, Sends

        <5>4. GreaterOrEqualBallot(aBal[m.from], m.bal)'
          BY <2>2 DEF VotedForIn, MsgInv, Phase2a1, Inv, Sends, VotedForIn, WontVoteIn, GreaterBallot, Bmax, PartialBmax
        <5>5. (\A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                (\A v \in Values, c \in Ballots :
                                  GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
          BY <2>2 DEF VotedForIn, MsgInv, Phase2a1, Inv, Sends, VotedForIn, WontVoteIn, GreaterBallot, Bmax, PartialBmax
        <5>6. QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5
        
      <4>2. ((m.type = "2a") => 
              /\ SafeAt(m.val, m.bal, m.slot)
              /\ Proposed(m.val, m.slot)
              /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
        <5> SUFFICES ASSUME (m.type = "2a")'
                     PROVE  (/\ SafeAt(m.val, m.bal, m.slot)
                             /\ Proposed(m.val, m.slot)
                             /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
          OBVIOUS
        <5>1. SafeAt(m.val, m.bal, m.slot)'
          <6> DEFINE VS == UNION {m_1.voted : m_1 \in S}
          <6> DEFINE b == pBal[p]
          <6>1. \A d \in PartialBmax(VS) : SafeAt(d.val, b, d.slot)
            <8> SUFFICES ASSUME NEW d \in PartialBmax(VS),
                                NEW c \in Ballots,
                                GreaterBallot(b, c)
                         PROVE  \E Q_1 \in Quorums : 
                                  \A a \in Q_1 : VotedForIn(a, d.val, c, d.slot) \/ WontVoteIn(a, c, d.slot)
              BY DEF SafeAt
            <8> DEFINE max == MaxVotedBallotInSlot(VS, d.slot)
            <8> USE DEF PartialBmax
            <8>5. d.slot \in Slots
              BY DEF PartialBmax, TypeOK, Inv, ValidMessages, ValidMessage1b
            <8>32. VS \in SUBSET [bal : Ballots, slot : Slots, val : Values]
              BY <3>1 DEF TypeOK, Inv, ValidMessages, ValidMessage1b
            <8>6. max \in Ballots \cup {[num |-> -1, id |-> -1]}
              BY MVBISType, <8>5, <8>32 DEF TypeOK
            <8>9. d \in VS
              OBVIOUS
            <8>8. max # [num |-> -1, id |-> -1]
              BY <8>9, MVBISNoSlot, <8>32 DEF TypeOK
            <8>10. max \in Ballots
              BY <8>6, <8>8
            <8>4. \A a \in Q : GreaterOrEqualBallot(aBal[a], b)
              BY <3>0 DEF MsgInv, Inv, TypeOK, AccInv
            <8>44. \A a \in Q : GreaterBallot(aBal[a], c)
              BY <8>4, GBTransitive, QuorumAssumption DEF Inv, TypeOK
            <8>7. \A mm \in S : mm.voted \subseteq VS
              OBVIOUS
            <8>0. \A mm \in S : GreaterOrEqualBallot(max, MaxVotedBallotInSlot(mm.voted, d.slot))
              BY MVBISSubsets, <8>7, <8>32 DEF PartialBmax
            <8>31. \A dd \in VS : dd.slot = d.slot => GreaterOrEqualBallot(d.bal, dd.bal)
              BY DEF PartialBmax, TypeOK, Inv, ValidMessages, ValidMessage1b
            <8>30. \A dd \in VS : ~(dd.slot = d.slot /\ ~GreaterOrEqualBallot(d.bal, dd.bal))
              BY <8>31
            <8>33. ~ \E dd \in VS : (dd.slot = d.slot /\ GreaterBallot(dd.bal, d.bal))
              BY <8>30, <8>32, GBTotal, GBNotCommutative DEF GreaterOrEqualBallot
            <8>35. d.bal \in Ballots
              BY DEF TypeOK, ValidMessages, PartialBmax, ValidMessage1b, Inv

            <8>11. max = d.bal
              <9> SUFFICES ASSUME max # d.bal
                           PROVE  FALSE
                OBVIOUS
              <9>1. CASE GreaterBallot(max, d.bal)
                <10>1. \E d1 \in VS : d1.slot = d.slot /\ d1.bal = max
                  BY <8>32, MVBISExists, <8>10
                <10> QED BY <10>1, <8>33, <9>1 DEF GreaterBallot
              <9>2. CASE GreaterBallot(d.bal, max)
                BY MVBISNoMore, <9>2, <8>32 DEF PartialBmax
              <9> QED BY <9>1, <9>2, <8>10, <8>35, GBNotCommutative, GBTotal
            
            <8>1. CASE GreaterBallot(c, max)
              <9>2. \A mm \in S, bb \in Ballots, v \in Values :
                               /\ GreaterBallot(bb, MaxVotedBallotInSlot(mm.voted, d.slot))
                               /\ GreaterBallot(b, bb)
                               => ~VotedForIn(mm.from, v, bb, d.slot)
                BY <8>5 DEF MsgInv, TypeOK, ValidMessages, ValidMessage1b, Inv\*, Messages
              <9> HIDE DEF max, VS
              <9>3. \A mm \in S : GreaterBallot(c, MaxVotedBallotInSlot(mm.voted, d.slot))
                <10> SUFFICES ASSUME NEW mm \in S
                              PROVE  GreaterBallot(c, MaxVotedBallotInSlot(mm.voted, d.slot))
                  OBVIOUS
                <10>1. CASE max = MaxVotedBallotInSlot(mm.voted, d.slot)
                  BY <8>1, GBTransitive, <10>1, <8>10, MVBISType, <8>7, <8>32
                <10>2. CASE GreaterBallot(max, MaxVotedBallotInSlot(mm.voted, d.slot))
                  BY <8>1, GBTransitive, <10>2, <8>10, MVBISType, <8>7, <8>32 DEF GreaterOrEqualBallot
                <10> QED BY <8>0, <10>1, <10>2 DEF GreaterOrEqualBallot
              <9>1. \A mm \in S : \A v \in Values : ~VotedForIn(mm.from, v, c, d.slot)
                BY <8>1, <9>3, <9>2
              <9>4. \A a \in Q : \A v \in Values : ~VotedForIn(a, v, c, d.slot)
                BY <3>0, <9>1
              <9> QED BY <8>1, <8>4, <9>4, <8>44 DEF WontVoteIn, Inv, MsgInv
            <8>2. CASE c = max
                <9>0. \E Q1 \in Quorums : \E a \in Q1, mm \in S :
                        /\ mm.from = a
                        /\ \E dd \in mm.voted : /\ dd.bal = d.bal
                                                /\ dd.val = d.val
                                                /\ dd.slot = d.slot
                  BY <3>0, QuorumAssumption DEF MaxVotedBallotInSlot, TypeOK, ValidMessages, ValidMessage1b, Inv\*, Messages
                <9>1. \E Q1 \in Quorums : \E a \in Q1 : VotedForIn(a, d.val, c, d.slot)
                  BY <8>2, <9>0, <8>11 DEF MsgInv, TypeOK, ValidMessages, ValidMessage1b, Inv\*, Messages
                <9>10. PICK Q2 \in Quorums : \E a \in Q2 : VotedForIn(a, d.val, c, d.slot)
                  BY <9>1
                <9>2. CASE \E a \in Acceptors : VotedForIn(a, d.val, c, d.slot)
                    <10>2. \A q \in Q, w \in Values : VotedForIn(q, w, c, d.slot) => w = d.val
                      BY <9>2, <9>1, VotedOnce, QuorumAssumption, <8>5, <8>32 DEF Inv
                    <10>3. \A q \in Q : GreaterBallot(aBal[q], c)
                      BY <8>44
                    <10>. QED
                      BY <8>4, <8>2, <10>2, <10>3 DEF WontVoteIn, VotedForIn
                <9>3. CASE (~\E a \in Acceptors : VotedForIn(a, d.val, c, d.slot))
                  <10> SUFFICES ASSUME ~( \E Q_1 \in Quorums :
                                            \A a \in Q_1 :
                                                VotedForIn(a, d.val, c, d.slot) \/ WontVoteIn(a, c, d.slot))
                                PROVE  FALSE
                    BY <8>2 DEF SafeAt
                    <10>1. \A a \in Q : GreaterOrEqualBallot(aBal[a], pBal[p])
                      BY <3>0 DEF Inv, MsgInv
                    <10>2. \A a \in Q : GreaterBallot(aBal[a], c)
                      BY <10>1, GBTransitive, QuorumAssumption DEF Inv, TypeOK
                    <10>3. \E a \in Q : \E vv \in Values : VotedForIn(a, vv, c, d.slot)
                      BY <10>2, QuorumAssumption DEF WontVoteIn
                    <10>10. PICK a \in Q, vv \in Values : VotedForIn(a, vv, c, d.slot)
                      BY <10>3
                    <10>11. \E mm1 \in msgs :
                              /\ mm1.type = "2a"
                              /\ mm1.bal = c
                              /\ mm1.slot = d.slot
                              /\ mm1.val = d.val
                      BY <8>2, <8>11 DEF Inv, MsgInv
                    <10>12. \E mm2 \in msgs :
                              /\ mm2.type = "2a"
                              /\ mm2.bal = c
                              /\ mm2.slot = d.slot
                              /\ mm2.val = vv
                      BY <10>10, QuorumAssumption DEF VotedForIn, Inv, AccInv
                    <10>4. vv = d.val
                      BY <10>11, <10>12 DEF Inv, MsgInv
                    <10> QED BY <10>10, <9>3, QuorumAssumption, <10>4, FALSE
                <9> QED BY <9>2, <9>3
            <8>3. CASE GreaterBallot(max, c)
              BY <8>3, <8>11 DEF SafeAt, MsgInv, TypeOK, MaxVotedBallotInSlot, VotedForIn, WontVoteIn, Inv
            <8> QED BY <8>1, <8>2, <8>3, <8>10, GBTotal
          <6>2. PartialBmax(VS) \subseteq [bal : Ballots , val : Values, slot : Slots]
            BY DEF PartialBmax, Inv, TypeOK, ValidMessages, ValidMessage1b
          <6>41. \A d \in Bmax(VS) : SafeAt(d.val, pBal[p], d.slot)
            BY <6>1, <6>2 DEF Bmax
          <6>3. CASE m \in msgs
            <7>1. SafeAt(m.val, m.bal, m.slot)
              BY <6>3 DEF Inv, MsgInv
            <7> QED
            BY <6>3, <7>1, SafeAtStable, <3>1, <2>2 DEF Inv, Next, TypeOK, ValidMessages, ValidMessage2a
          <6>4. CASE m \in msgs' \ msgs
            <7>1. SafeAt(m.val, m.bal, m.slot)
              BY <6>4, <6>41, <3>0 DEF Sends
            <7> QED 
            BY <7>1, <6>4, <3>1, <2>2, SafeAtStable DEF Inv, Next, TypeOK, ValidMessages, ValidMessage2a
          <6> QED BY <6>3, <6>4
          
        <5>21. ~(\E m_1 \in msgs : m_1.type = "2a" /\ m_1.bal = pBal[p])
          BY <3>0 DEF Inv, PropInv
        <5>22. \A mm \in msgs' \ msgs : mm.bal = pBal[p]
          BY <3>0 DEF Sends  
        <5>23. PartialBmax(UNION {m_1.voted : m_1 \in S}) \subseteq [bal : Ballots, slot : Slots, val : Values]
          BY DEF TypeOK, Inv, ValidMessages,ValidMessage1b, PartialBmax
        <5>24. \A r1, r2 \in PartialBmax(UNION {m_1.voted : m_1 \in S}) : r1.slot = r2.slot => r1.bal = r2.bal
          <6> SUFFICES ASSUME NEW r1 \in PartialBmax(UNION {m_1.voted : m_1 \in S}), NEW r2 \in PartialBmax(UNION {m_1.voted : m_1 \in S}),
                              r1.slot = r2.slot,
                              r1.bal # r2.bal
                       PROVE  FALSE
            OBVIOUS
            <6>1. GreaterBallot(r1.bal, r2.bal) \/ GreaterBallot(r2.bal, r1.bal)
              BY <5>23, GBTotal
            <6>2. CASE GreaterBallot(r1.bal, r2.bal)
              BY <6>2, GBNotCommutative, <5>23 DEF PartialBmax, GreaterOrEqualBallot
            <6>3. CASE ~ GreaterBallot(r1.bal, r2.bal) /\ GreaterBallot(r2.bal, r1.bal)
              BY <6>3 DEF PartialBmax, GreaterOrEqualBallot
          <6> QED
            BY <6>1, <6>2, <6>3
        <5>25. PartialBmax(UNION {m_1.voted : m_1 \in S}) \subseteq UNION {m_1.voted : m_1 \in S}
          BY DEF PartialBmax
        <5>26. \A r1, r2 \in PartialBmax(UNION {m_1.voted : m_1 \in S}) :
                r1.bal = r2.bal /\ r1.slot = r2.slot => r1.val = r2.val
          BY <5>24, VotedUnion, <5>25 DEF Inv, TypeOK, ValidMessages, ValidMessage1b
        <5>27. \A t1, t2 \in Bmax(UNION {m_1.voted : m_1 \in S}) : t1.slot = t2.slot => t1.val = t2.val
          BY <5>23, <5>24, <5>26 DEF Bmax
        <5>2. (\A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
          <6>1. CASE m \in msgs
            BY <5>21, <5>22, <6>1 DEF Inv, MsgInv
          <6>2. CASE m \in msgs' \ msgs
            BY <5>21, <5>22, <6>2, <3>0, <5>27 DEF Sends, Inv, TypeOK, ValidMessages, ValidMessage1b
          <6> QED BY <6>1, <6>2
        <5>41. \A e \in Bmax(UNION {m_1.voted : m_1 \in S}) : \E m_1 \in msgs : m_1.type = "1b" /\ \E d \in m_1.voted: d.val = e.val /\ d.slot = e.slot
          BY <5>25 DEF Bmax
        <5>42. m \in msgs' \ msgs => \E t \in Bmax(UNION {m_1.voted : m_1 \in S}) : t.slot = m.slot /\ t.val = m.val
          BY <3>0 DEF Sends
        <5>43. m \in msgs' \ msgs => \E m1 \in msgs : m1.type = "1b" /\ \E d \in m1.voted : (d.val = m.val /\ d.slot = m.slot)
          BY <5>41, <5>42
        <5>44. m \in msgs' \ msgs => \E m1 \in msgs : m1.type = "2a" /\ m1.val = m.val /\ m1.slot = m.slot
          BY <5>43 DEF Inv, MsgInv
        <5>45. m \in msgs' \ msgs => Proposed(m.val, m.slot)
          BY <5>44 DEF Inv, MsgInv
        <5>4. (Proposed(m.val, m.slot))'
          <6>1. CASE m \in msgs
            BY <3>0, <6>1 DEF Inv, Sends, MsgInv, Proposed
          <6>2. CASE m \in msgs' \ msgs
            BY <3>0, <6>2, <5>45 DEF Sends, Inv, Proposed
          <6> QED BY <6>1, <6>2
        <5>3. QED
          BY <5>1, <5>2, <5>4

      <4>3. ((m.type = "decision") =>
              \E Q_1 \in Quorums, b \in Ballots : \A a \in Q_1 : VotedForIn(a, m.val, b, m.slot))'
        BY <2>2 DEF MsgInv, Phase2a1, Inv, Sends, SafeAt, VotedForIn, WontVoteIn, GreaterBallot, Bmax, PartialBmax
      <4>5. (m.type = "2b" => VotedForIn(m.from, m.val, m.bal, m.slot))'
        BY <2>2 DEF MsgInv, Phase2a1, Inv, Sends, SafeAt, VotedForIn, WontVoteIn, GreaterBallot, Bmax, PartialBmax
      <4>4. QED
        BY <4>1, <4>2, <4>3, <4>5

    <3>3. AccInv'
        BY <2>2, Phase2a1VotedForInv, <3>0 DEF AccInv, Inv, Sends, Bmax, PartialBmax,  TypeOK

    <3>4. PropInv'
      <4> SUFFICES ASSUME NEW p_1 \in Proposers'
                   PROVE  (/\ pState[p_1] = 1 => ~ \E m \in msgs :
                                                     /\ m.bal = pBal[p_1]
                                                   /\ m.type \in {"1a", "2a"}
                           /\ pState[p_1] = 2 => /\ \E m \in msgs : m.type = "1a" /\ m.bal = pBal[p_1] /\ m.to = Acceptors
                                                 /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = pBal[p_1]
                           /\ pState[p_1] = 3 => /\ \E Q_1 \in Quorums : \A a \in Q_1 : \E m \in msgs :
                                                     /\ m.type = "1b"
                                                   /\ m.from = a
                                                   /\ m.to = p_1
                                                   /\ m.bal = pBal[p_1]
                                                 /\ \A c \in Ballots, s \in Slots :
                                                   /\ GreaterBallot(pBal[p_1], c)
                                                   (*/\ \E m \in msgs :
                                                     /\ m.type = "2a"
                                                     /\ m.bal = pBal[p_1]*)
                                                   /\ ~ \E m \in msgs :
                                                     /\ m.type = "2a"
                                                     /\ m.bal = pBal[p_1]
                                                     /\ m.slot = s
                                                   =>
                                                   \E Q_1 \in Quorums : \A a \in Q_1 : WontVoteIn(a, c, s)
                           /\ ~ \E m \in msgs :  /\ m.type \in {"1a", "2a"}
                                                 /\ GreaterBallot(m.bal, pBal[p_1])
                                                 /\ m.bal.id = p_1
                           /\ pBal[p_1].id = p_1)'
        BY DEF PropInv
      <4>5. (pBal[p_1].id = p_1)'
        BY <2>2 DEF PropInv, Phase2a1, Inv, Sends, Bmax, PartialBmax, GreaterOrEqualBallot
      <4>1. (pState[p_1] = 1 => ~ \E m \in msgs :
                                    /\ m.bal = pBal[p_1]
                                    /\ m.type \in {"1a", "2a"})'
        BY <3>0 DEF PropInv, Inv, Sends, Bmax, PartialBmax, GreaterOrEqualBallot, TypeOK, ValidMessages, ValidMessage1a, ValidMessage2a
      <4>2. (pState[p_1] = 2 => /\ \E m \in msgs : m.type = "1a" /\ m.bal = pBal[p_1] /\ m.to = Acceptors
                                /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = pBal[p_1])'
        BY <3>0 DEF PropInv, Inv, Sends, Bmax, PartialBmax, GreaterOrEqualBallot, TypeOK, ValidMessages, ValidMessage1a, ValidMessage2a
      <4>3. (pState[p_1] = 3 => /\ \E Q_1 \in Quorums : \A a \in Q_1 : \E m \in msgs :
                                    /\ m.type = "1b"
                                  /\ m.from = a
                                  /\ m.to = p_1
                                  /\ m.bal = pBal[p_1]
                                /\ \A c \in Ballots, s \in Slots :
                                  /\ GreaterBallot(pBal[p_1], c)
                                  /\ ~ \E m \in msgs :
                                    /\ m.type = "2a"
                                    /\ m.bal = pBal[p_1]
                                    /\ m.slot = s
                                  =>
                                  \E Q_1 \in Quorums : \A a \in Q_1 : WontVoteIn(a, c, s))'
        <5> SUFFICES ASSUME (pState[p_1] = 3)'
                     PROVE  (/\ \E Q_1 \in Quorums : \A a \in Q_1 : \E m \in msgs :
                                 /\ m.type = "1b"
                               /\ m.from = a
                               /\ m.to = p_1
                               /\ m.bal = pBal[p_1]
                             /\ \A c \in Ballots, s \in Slots :
                               /\ GreaterBallot(pBal[p_1], c)
                               /\ ~ \E m \in msgs :
                                 /\ m.type = "2a"
                                 /\ m.bal = pBal[p_1]
                                 /\ m.slot = s
                               =>
                               \E Q_1 \in Quorums : \A a \in Q_1 : WontVoteIn(a, c, s))'
          OBVIOUS
        <5>1. ( \E Q_1 \in Quorums : \A a \in Q_1 : \E m \in msgs :
                 /\ m.type = "1b"
               /\ m.from = a
               /\ m.to = p_1
               /\ m.bal = pBal[p_1])'
          BY <3>0 DEF PropInv, Inv, Sends, Bmax, PartialBmax, GreaterOrEqualBallot, TypeOK, ValidMessages, ValidMessage1b, ValidMessage2a
        <5>2. ( \A c \in Ballots, s \in Slots :
               /\ GreaterBallot(pBal[p_1], c)
               /\ ~ \E m \in msgs :
                 /\ m.type = "2a"
                 /\ m.bal = pBal[p_1]
                 /\ m.slot = s
               =>
               \E Q_1 \in Quorums : \A a \in Q_1 : WontVoteIn(a, c, s))'
          <6> SUFFICES ASSUME NEW c \in Ballots', NEW s \in Slots',
                              (/\ GreaterBallot(pBal[p_1], c)
                               /\ ~ \E m \in msgs :
                                 /\ m.type = "2a"
                                 /\ m.bal = pBal[p_1]
                                 /\ m.slot = s)'
                       PROVE  (\E Q_1 \in Quorums : \A a \in Q_1 : WontVoteIn(a, c, s))'
            OBVIOUS
          <6>1. CASE p_1 = p
            <7>11. \A mm \in msgs' \ msgs : mm.slot # s
              BY <3>0, <6>1 DEF Bmax, PartialBmax, Sends, GreaterOrEqualBallot, GreaterBallot
            <7>13. UNION {m_1.voted : m_1 \in S} \subseteq [bal : Ballots, slot : Slots, val : Values]
              BY DEF TypeOK, ValidMessages, ValidMessage1b, Inv
            <7>12. Bmax(UNION {m_1.voted : m_1 \in S}) \subseteq [slot : Slots, val : Values]
              BY DEF Bmax, TypeOK, ValidMessages, ValidMessage1b, Inv, PartialBmax
            <7>14. {vote.slot : vote \in UNION {m_1.voted : m_1 \in S}} = {vote.slot : vote \in Bmax(UNION {m_1.voted : m_1 \in S})}
              BY BmaxVotes, <7>13
            <7>15. (\E vote \in Bmax(UNION {m_1.voted : m_1 \in S}) : vote.slot = s) => (\E vote \in UNION {m_1.voted : m_1 \in S} : vote.slot = s)
              <8> SUFFICES ASSUME NEW vote_1 \in Bmax(UNION {m_1.voted : m_1 \in S}),
                                  vote_1.slot = s,
                                  ~ \E vote \in UNION {m_1.voted : m_1 \in S} : vote.slot = s
                           PROVE  FALSE
                OBVIOUS
                <8>1. s \in {vote.slot : vote \in Bmax(UNION {m_1.voted : m_1 \in S})}
                  OBVIOUS
                <8>2. s \in {vote.slot : vote \in UNION {m_1.voted : m_1 \in S}}
                  BY <8>1, <7>14
                <8>3. \E vote \in UNION {m_1.voted : m_1 \in S} : vote.slot = s
                  BY <8>2
              <8> QED
                BY <8>3
            <7>16. (\E vote \in UNION {m_1.voted : m_1 \in S} : vote.slot = s) => (\E vote \in Bmax(UNION {m_1.voted : m_1 \in S}) : vote.slot = s)
              <8> SUFFICES ASSUME NEW vote_1 \in UNION {m_1.voted : m_1 \in S},
                                  vote_1.slot = s,
                                  ~ \E vote \in Bmax(UNION {m_1.voted : m_1 \in S}) : vote.slot = s
                           PROVE  FALSE
                OBVIOUS
                <8>1. s \in {vote.slot : vote \in UNION {m_1.voted : m_1 \in S}}
                  OBVIOUS
                <8>2. s \in {vote.slot : vote \in Bmax(UNION {m_1.voted : m_1 \in S})}
                  BY <8>1, <7>14
                <8>3. \E vote \in Bmax(UNION {m_1.voted : m_1 \in S}) : vote.slot = s
                  BY <8>2
              <8> QED
                BY <8>3
            <7>17. (\E vote \in Bmax(UNION {m_1.voted : m_1 \in S}) : vote.slot = s) <=> (\E vote \in UNION {m_1.voted : m_1 \in S} : vote.slot = s)
              BY <7>15, <7>16
            <7>18. PartialBmax(UNION {m_1.voted : m_1 \in S}) \subseteq UNION {m_1.voted : m_1 \in S}
              BY DEF PartialBmax
            <7>19. \A vote \in Bmax(UNION {m_1.voted : m_1 \in S}) : vote.slot # s
              <8> SUFFICES ASSUME NEW vote \in Bmax(UNION {m_1.voted : m_1 \in S}),
                                  vote.slot = s
                           PROVE  FALSE
                OBVIOUS
                <8>0. msgs' \ msgs = 
                        {[type |-> "2a", bal |-> pBal[p], slot |-> t.slot,
                            val |-> t.val, from |-> p, to |-> Acceptors] :
                            t \in Bmax(UNION {m_1.voted : m_1 \in S})}
                  BY <3>0, <6>1 DEF Sends, Inv, PropInv
                <8>1. \E m \in msgs' \ msgs : m.slot = vote.slot
                  BY <3>1, <8>0 DEF Inv, TypeOK, ValidMessages, ValidMessage2a
              <8> QED
                BY <8>1, <7>11
              
            <7>1. ~ \E vote \in UNION {m_1.voted : m_1 \in S} : vote.slot = s
              BY <7>11, <7>17, <7>19, <6>1, <3>1, <3>0
            <7>2. \A q \in Q : WontVoteIn(q, c, s)'
              <8> SUFFICES ASSUME NEW q \in Q
                           PROVE  WontVoteIn(q, c, s)'
                OBVIOUS
              <8>11.  \A m \in S, ss \in Slots :
                           ~(\E vote \in m.voted : vote.slot = ss)
                           => (\A v \in Values,
                                  cc \in Ballots :
                                  GreaterBallot(m.bal, cc)
                                  => ~VotedForIn(m.from, v, cc, ss))
                BY QuorumAssumption DEF Inv, MsgInv, TypeOK, ValidMessages, ValidMessage1b
              <8>12. (\A m \in S, v \in Values,
                                  cc \in Ballots :
                                  GreaterBallot(m.bal, cc)
                                  => ~VotedForIn(m.from, v, cc, s))
                BY <8>11, <7>1
              <8>13. \A m \in S , v \in Values: ~VotedForIn(m.from, v, c, s)
                BY <8>12, <6>1, \A m \in S : m.bal = pBal[p], <3>0 DEF Inv, TypeOK
              <8>1. (\A v \in Values : ~ VotedForIn(q, v, c, s))'
                BY <8>13, QuorumAssumption, <3>0, Phase2a1VotedForInv, <2>2 DEF Inv\*, TypeOK, ValidMessages, ValidMessage1b           
              <8>21. \A m \in msgs' \ msgs :
                        /\ m.type = "2a"
                        /\ m.bal = pBal[p]
                        /\ m.to = Acceptors
                BY <3>0 DEF Sends
              <8>22. GreaterOrEqualBallot(aBal[q], pBal[p])
                BY <6>1, <3>0 DEF Inv, MsgInv, TypeOK, ValidMessages, ValidMessage1b
              <8>26. GreaterBallot(pBal[p], c)
                BY <3>0, <6>1 DEF GreaterBallot
              <8>23. aBal[q] \in Ballots \cup {[num |-> -1, id |-> -1]}
                BY QuorumAssumption DEF Inv, TypeOK
              <8>24. pBal[p] \in Ballots
                BY DEF Inv, TypeOK
              <8>25. GreaterOrEqualBallot(aBal[q], pBal[p])'
                BY <3>0, <8>22
              <8>2. (GreaterBallot(aBal[q], c))
                BY <6>1, <8>22, <8>26, <8>23, <8>24, GBTransitive
              <8>3. QED
                BY <8>1, <8>2, <3>0 DEF WontVoteIn
              
            <7> QED BY <7>2
          <6>2. CASE p_1 # p
            BY <6>2, Phase2a1WontVoteIn, QuorumAssumption, <3>0, <3>1, <4>5, ~\E m \in msgs' \ msgs : m.bal = pBal[p_1],
            <2>2, \E Q_1 \in Quorums : \A a \in Q_1 : WontVoteIn(a, c, s)
            DEF PropInv, Sends, Inv, TypeOK, ValidMessages, ValidMessage1b, MsgInv
          <6> QED BY <6>1, <6>2
        <5>3. QED
          BY <5>1, <5>2
        
      <4>4. (~ \E m \in msgs :  /\ m.type \in {"1a", "2a"}
                                /\ GreaterBallot(m.bal, pBal[p_1])
                                /\ m.bal.id = p_1)'
        BY <2>2 DEF PropInv, Phase2a1, Inv, Sends, Bmax, PartialBmax, GreaterOrEqualBallot
      <4>6. QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5
      
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Inv

  <2>3. ASSUME NEW p \in Proposers,
               Phase2a11(p)
        PROVE  Inv'
    <3>0. PICK ms \in msgs : Phase2a11(p)!(ms)
      BY <2>3 DEF Phase2a11
    <3>1. TypeOK'
      <4>1. (ValidMessages(msgs))'
        <5> SUFFICES ASSUME NEW m \in msgs'
                     PROVE  (/\ m.type \in {"1a", "1b", "2a", "2b", "decision", "propose", "preempt"}
                             /\ m.type = "1a" => ValidMessage1a(m)
                             /\ m.type = "1b" => ValidMessage1b(m)
                             /\ m.type = "2a" => ValidMessage2a(m)
                             /\ m.type = "2b" => ValidMessage2b(m)
                             /\ m.type = "decision" => ValidMessagedecision(m)
                             /\ m.type = "propose"  => ValidMessagepropose(m)
                             /\ m.type = "preempt"  => ValidMessagepreempt(m))'
          BY DEF ValidMessages
        <5>0. PICK m_1 \in msgs : Phase2a11(p)!(m_1)
          BY <2>3 DEF Phase2a11
        <5>1. (m.type \in {"1a", "1b", "2a", "2b", "decision", "propose", "preempt"})'
          BY <2>3 DEF Phase2a11, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose
        <5>2. (m.type = "1a" => ValidMessage1a(m))'
          BY <2>3 DEF Phase2a11, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose
        <5>3. (m.type = "1b" => ValidMessage1b(m))'
          BY <2>3 DEF Phase2a11, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose
        <5>4. (m.type = "2a" => ValidMessage2a(m))'
          BY <2>3, <5>0 DEF Phase2a11, TypeOK, Send, Inv, ValidMessages, ValidMessage2a, ValidMessagepropose
        <5>5. (m.type = "2b" => ValidMessage2b(m))'
          BY <2>3 DEF Phase2a11, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose
        <5>6. (m.type = "decision" => ValidMessagedecision(m))'
          BY <2>3 DEF Phase2a11, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose
        <5>7. (m.type = "propose"  => ValidMessagepropose(m))'
          BY <2>3 DEF Phase2a11, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose
        <5>9. (m.type = "preempt"  => ValidMessagepreempt(m))'
          BY <2>3 DEF Phase2a11, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessagepreempt,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose
        <5>8. QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>9
      <4>5. QED
        BY <4>1, <2>3 DEF Phase2a11, TypeOK, Send, Inv
      
    <3>2. MsgInv'
      <4> SUFFICES ASSUME NEW m \in msgs'
                   PROVE  (/\ (m.type = "1b") =>
                               /\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                     /\ \E mm \in msgs :
                                                          /\ m.from \in mm.to
                                                          /\ mm.type = "2a"
                                                          /\ mm.bal = r.bal
                                                          /\ mm.slot = r.slot
                                                          /\ mm.val = r.val
                               /\ \A v \in Values, s \in Slots, b \in Ballots :
                                     GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                       => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                               /\ \A s \in Slots, v \in Values, c \in Ballots :
                                   (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                       ~ VotedForIn(m.from, v, c, s)
                               /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                               /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                   (\A v \in Values, c \in Ballots :
                                                     GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s))
                           /\ (m.type = "2a") => 
                               /\ SafeAt(m.val, m.bal, m.slot)
                               /\ Proposed(m.val, m.slot)
                               /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val
                           /\ (m.type = "2b") => VotedForIn(m.from, m.val, m.bal, m.slot)
                           /\ (m.type = "decision") =>
                               \E Q \in Quorums, b \in Ballots : \A a \in Q : VotedForIn(a, m.val, b, m.slot))'
        BY DEF MsgInv
      <4>1. ((m.type = "1b") =>
                               /\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                     /\ \E mm \in msgs :
                                                          /\ m.from \in mm.to
                                                          /\ mm.type = "2a"
                                                          /\ mm.bal = r.bal
                                                          /\ mm.slot = r.slot
                                                          /\ mm.val = r.val
                               /\ \A v \in Values, s \in Slots, b \in Ballots :
                                     GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                       => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                               /\ \A s \in Slots, v \in Values, c \in Ballots :
                                   (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                       ~ VotedForIn(m.from, v, c, s)
                               /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                               /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                   (\A v \in Values, c \in Ballots :
                                                     GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
        <5> SUFFICES ASSUME (m.type = "1b")'
                     PROVE  (/\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                   /\ \E mm \in msgs :
                                                        /\ m.from \in mm.to
                                                        /\ mm.type = "2a"
                                                        /\ mm.bal = r.bal
                                                        /\ mm.slot = r.slot
                                                        /\ mm.val = r.val
                             /\ \A v \in Values, s \in Slots, b \in Ballots :
                                   GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                     => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                             /\ \A s \in Slots, v \in Values, c \in Ballots :
                                 (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                     ~ VotedForIn(m.from, v, c, s)
                             /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                             /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                 (\A v \in Values, c \in Ballots :
                                                   GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
          OBVIOUS
        <5>1. (\A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                  /\ \E mm \in msgs :
                                       /\ m.from \in mm.to
                                       /\ mm.type = "2a"
                                       /\ mm.bal = r.bal
                                       /\ mm.slot = r.slot
                                       /\ mm.val = r.val)'
          BY <2>3 DEF VotedForIn, MsgInv, Phase2a11, Inv, Send, VotedForIn, WontVoteIn, GreaterBallot
        <5>2. (\A v \in Values, s \in Slots, b \in Ballots :
                  GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                    => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)'
          <6> SUFFICES ASSUME NEW v \in Values', NEW s \in Slots', NEW b \in Ballots',
                              (GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s))'
                       PROVE  (\E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)'
            OBVIOUS
            <6>1. GreaterBallot(m.bal, b)
              BY DEF GreaterBallot
            <6>2. VotedForIn(m.from, v, b, s)
              BY <2>3 DEF VotedForIn, Phase2a11
            <6>3. \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
              BY <6>1, <6>2, <2>3 DEF Inv, MsgInv, Phase2a11, Send
          <6> QED
            BY <6>3, <2>3 DEF Phase2a11, Send
        <5>3. (\A s \in Slots, v \in Values, c \in Ballots :
                (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                    ~ VotedForIn(m.from, v, c, s))'
          <6> SUFFICES ASSUME NEW s \in Slots', NEW v \in Values', NEW c \in Ballots',
                              (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s)))'
                       PROVE  (~ VotedForIn(m.from, v, c, s))'
            OBVIOUS
            <6>1. GreaterBallot(m.bal, c)
              BY DEF GreaterBallot
            <6>2. GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))
              BY DEF GreaterBallot
            <6>3. ~ VotedForIn(m.from, v, c, s)
              BY <6>1, <6>2, <2>3 DEF Inv, MsgInv, Phase2a11, Send
          <6> QED
            BY <6>3, <2>3 DEF VotedForIn, Phase2a11, Send
          
        <5>4. GreaterOrEqualBallot(aBal[m.from], m.bal)'
          BY <2>3, QuorumAssumption, SystemAssumptions DEF MsgInv, Phase2a11, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot
        <5>5. (\A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                (\A v \in Values, c \in Ballots :
                                  GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
          BY <2>3, QuorumAssumption, SystemAssumptions DEF MsgInv, Phase2a11, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot
        <5>6. QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5
        
      <4>2. ((m.type = "2a") => 
              /\ SafeAt(m.val, m.bal, m.slot)
              /\ Proposed(m.val, m.slot)
              /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
        <5> SUFFICES ASSUME (m.type = "2a")'
                     PROVE  (/\ SafeAt(m.val, m.bal, m.slot)
                             /\ Proposed(m.val, m.slot)
                             /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
          OBVIOUS
        <5>1. SafeAt(m.val, m.bal, m.slot)'
          <6>1. CASE m \in msgs
            <7>1. SafeAt(m.val, m.bal, m.slot)
              BY <2>3, <6>1, <3>1 DEF MsgInv, Inv, Next
            <7>2. m.val \in Values
              BY <6>1, <3>1 DEF Inv, TypeOK, ValidMessages, ValidMessage2a
            <7>3. m.bal \in Ballots
              BY <6>1, <3>1 DEF Inv, TypeOK, ValidMessages, ValidMessage2a
            <7>4. m.slot \in Slots
              BY <6>1, <3>1 DEF Inv, TypeOK, ValidMessages, ValidMessage2a
            <7> QED BY SafeAtStable, <7>1, <6>1, <3>1, <7>2, <7>3, <7>4, <2>3 DEF Inv, Next
          <6>2. CASE m \in msgs' \ msgs
            <7> SUFFICES ASSUME NEW c \in Ballots',
                                GreaterBallot(m.bal, c)'
                         PROVE  (\E Q \in Quorums : 
                                  \A a \in Q : VotedForIn(a, m.val, c, m.slot) \/ WontVoteIn(a, c, m.slot))'
              BY DEF SafeAt
              <7>1. \E Q \in Quorums :
                        \A a \in Q :
                           \E mm \in msgs :
                              /\ mm.type = "1b"
                              /\ mm.from = a
                              /\ mm.to = p
                              /\ mm.bal = pBal[p]
                BY <2>3 DEF PropInv, Phase2a11, Inv
              <7>22. m.bal = pBal[p]
                BY <2>3, <6>2 DEF Phase2a11, Send
              <7>24. GreaterBallot(pBal[p], c)
                BY <7>22
              <7>25. pState[p] = 3
                BY <2>3 DEF Phase2a11
              <7>26. m.slot \in Slots
                BY <2>3, <3>1 DEF Phase2a11, Inv, Send, TypeOK, ValidMessages, ValidMessage2a
              <7>23. ~(\E m_1 \in msgs :
                        /\ m_1.type = "2a"
                        /\ m_1.bal = pBal[p]
                        /\ m_1.slot = m.slot)
                BY <2>3, <6>2 DEF Phase2a11, Send
              <7>2. (\E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, m.slot))
                BY <2>3, <7>24, <7>23, <7>25, <7>26, <6>2 DEF PropInv, Inv
            <7> QED
              BY <7>2, <2>3, <6>2, QuorumAssumption, SystemAssumptions, SafeAtStable DEF AccInv, MsgInv, Phase2a11, Inv, Send, VotedForIn, WontVoteIn, GreaterBallot
            
          <6> QED BY <6>1, <6>2
        <5>2. (\A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
          <6> SUFFICES ASSUME NEW mm \in msgs',
                              (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot)'
                       PROVE  (mm.val = m.val)'
            OBVIOUS
            <6>1. CASE mm \in msgs' \ msgs
              BY <2>3, <6>1 DEF Phase2a11, Send
            <6>2. CASE mm \in msgs
              BY <6>2, <2>3 DEF Phase2a11, Send, Inv, MsgInv
          <6> QED BY <6>1, <6>2
        <5>4. (Proposed(m.val, m.slot))'
          <6>1. CASE m \in msgs
            BY <6>1, <2>3 DEF Inv, MsgInv, Proposed, Phase2a11, Send
          <6>2. CASE m \in msgs' \ msgs
            BY <6>2, <2>3 DEF Inv, TypeOK, ValidMessages, ValidMessagepropose, MsgInv, Proposed, Phase2a11, Send
          <6> QED
          BY <6>1, <6>2
        <5>3. QED
          BY <5>1, <5>2, <5>4

      <4>3. ((m.type = "decision") =>
              \E Q \in Quorums, b \in Ballots : \A a \in Q : VotedForIn(a, m.val, b, m.slot))'
        BY <2>3, QuorumAssumption, SystemAssumptions DEF MsgInv, Phase2a11, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot
      <4>5. ((m.type = "2b") => VotedForIn(m.from, m.val, m.bal, m.slot))'
        BY <2>3, QuorumAssumption, SystemAssumptions DEF MsgInv, Phase2a11, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot
      <4>4. QED
        BY <4>1, <4>2, <4>3, <4>5
      
    <3>3. AccInv'
      BY <2>3, Phase2a11VotedForInv, <3>0 DEF AccInv, Inv, Send, Bmax, PartialBmax, TypeOK
      
    <3>4. PropInv'
      <4> SUFFICES ASSUME NEW p_1 \in Proposers'
                   PROVE  (/\ pState[p_1] = 1 => ~ \E m \in msgs :
                                                     /\ m.bal = pBal[p_1]
                                                   /\ m.type \in {"1a", "2a"}
                           /\ pState[p_1] = 2 => /\ \E m \in msgs : m.type = "1a" /\ m.bal = pBal[p_1] /\ m.to = Acceptors
                                                 /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = pBal[p_1]
                           /\ pState[p_1] = 3 => /\ \E Q \in Quorums : \A a \in Q : \E m \in msgs :
                                                     /\ m.type = "1b"
                                                   /\ m.from = a
                                                   /\ m.to = p_1
                                                   /\ m.bal = pBal[p_1]
                                                 /\ \A c \in Ballots, s \in Slots :
                                                   /\ GreaterBallot(pBal[p_1], c)
                                                   (*/\ \E m \in msgs :
                                                     /\ m.type = "2a"
                                                     /\ m.bal = pBal[p_1]*)
                                                   /\ ~ \E m \in msgs :
                                                     /\ m.type = "2a"
                                                     /\ m.bal = pBal[p_1]
                                                     /\ m.slot = s
                                                   =>
                                                   \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s)
                           /\ ~ \E m \in msgs :  /\ m.type \in {"1a", "2a"}
                                                 /\ GreaterBallot(m.bal, pBal[p_1])
                                                 /\ m.bal.id = p_1
                           /\ pBal[p_1].id = p_1)'
        BY DEF PropInv

      <4>5. (pBal[p_1].id = p_1)'
        BY <2>3, <3>1 DEF PropInv, Phase2a11, Inv, Send, TypeOK
      <4>1. (pState[p_1] = 1 => ~ \E m \in msgs :
                                    /\ m.bal = pBal[p_1]
                                  /\ m.type \in {"1a", "2a"})'
        BY <2>3, <3>1 DEF PropInv, Phase2a11, Inv, Send, TypeOK
      <4>2. (pState[p_1] = 2 => /\ \E m \in msgs : m.type = "1a" /\ m.bal = pBal[p_1] /\ m.to = Acceptors
                                /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = pBal[p_1])'
        BY <2>3, <3>1 DEF PropInv, Phase2a11, Inv, Send, TypeOK
      <4>3. (pState[p_1] = 3 => /\ \E Q \in Quorums : \A a \in Q : \E m \in msgs :
                                    /\ m.type = "1b"
                                  /\ m.from = a
                                  /\ m.to = p_1
                                  /\ m.bal = pBal[p_1]
                                /\ \A c \in Ballots, s \in Slots :
                                  /\ GreaterBallot(pBal[p_1], c)
                                  (*/\ \E m \in msgs :
                                    /\ m.type = "2a"
                                    /\ m.bal = pBal[p_1]*)
                                  /\ ~ \E m \in msgs :
                                    /\ m.type = "2a"
                                    /\ m.bal = pBal[p_1]
                                    /\ m.slot = s
                                  =>
                                  \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s))'
        <5> SUFFICES ASSUME (pState[p_1] = 3)'
                     PROVE  (/\ \E Q \in Quorums : \A a \in Q : \E m \in msgs :
                                 /\ m.type = "1b"
                               /\ m.from = a
                               /\ m.to = p_1
                               /\ m.bal = pBal[p_1]
                             /\ \A c \in Ballots, s \in Slots :
                               /\ GreaterBallot(pBal[p_1], c)
                               (*/\ \E m \in msgs :
                                 /\ m.type = "2a"
                                 /\ m.bal = pBal[p_1]*)
                               /\ ~ \E m \in msgs :
                                 /\ m.type = "2a"
                                 /\ m.bal = pBal[p_1]
                                 /\ m.slot = s
                               =>
                               \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s))'
          OBVIOUS
        <5>1. ( \E Q \in Quorums : \A a \in Q : \E m \in msgs :
                 /\ m.type = "1b"
               /\ m.from = a
               /\ m.to = p_1
               /\ m.bal = pBal[p_1])'
          BY <2>3, <3>1 DEF PropInv, Phase2a11, Inv, Send, TypeOK
        <5>2. ( \A c \in Ballots, s \in Slots :
               /\ GreaterBallot(pBal[p_1], c)
               (*/\ \E m \in msgs :
                 /\ m.type = "2a"
                 /\ m.bal = pBal[p_1]*)
               /\ ~ \E m \in msgs :
                 /\ m.type = "2a"
                 /\ m.bal = pBal[p_1]
                 /\ m.slot = s
               =>
               \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s))'
          <6> SUFFICES ASSUME NEW c \in Ballots', NEW s \in Slots',
                              GreaterBallot(pBal[p_1], c)',
                              ( ~ \E mm \in msgs :
                               /\ mm.type = "2a"
                               /\ mm.bal = pBal[p_1]
                               /\ mm.slot = s)'
                       PROVE  (\E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s))'
            OBVIOUS
          <6>11. GreaterBallot(pBal[p_1], c)
            BY <3>0
          <6>12. \A mm \in msgs' \ msgs : mm.bal = pBal[p]
            BY <3>0 DEF Send
          <6>13. p_1 # p => ~\E mm \in msgs' \ msgs : mm.bal = pBal[p_1]
            BY <4>5, <6>12 DEF Inv, PropInv
          <6>14. pState[p_1] = 3
            BY <3>0
          <6>1. CASE p_1 = p
            <7>1. CASE s = ms.slot
            BY <7>1, <6>1, Phase2a11WontVoteIn, QuorumAssumption, <6>11, <2>3, <6>14, <3>0,
                \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s) DEF PropInv, Send,
                Inv, MsgInv
            <7>2. CASE s # ms.slot
              <8>1. CASE \E mm \in msgs : mm.type = "2a" /\ mm.bal = pBal[p] /\ mm.slot = s
              BY <8>1, <7>2, <6>1, Phase2a11WontVoteIn, QuorumAssumption, <6>11, <2>3, <6>14, <3>0,
                ~ \E mm \in msgs' \ msgs : mm.slot = s,
                ~ \E mm \in msgs : mm.slot = s /\ mm.bal = pBal[p] /\ mm.type = "2a",
                \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s) DEF PropInv, Send,
                Inv, MsgInv
              <8>2. CASE ~\E mm \in msgs : mm.type = "2a" /\ mm.bal = pBal[p] /\ mm.slot = s
                <9>1. GreaterBallot(pBal[p_1], c)
                  BY <2>3 DEF Phase2a11
                <9>2. \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s)
                  BY <9>1, <8>2, <6>1, <2>3 DEF Inv, PropInv, Phase2a11
                <9> QED BY <9>2, Phase2a11WontVoteIn, <2>3, QuorumAssumption DEF Inv, Next
              <8> QED BY <8>1, <8>2
            <7> QED BY <7>1, <7>2
          <6>2. CASE p_1 # p
            BY <6>2, Phase2a11WontVoteIn, QuorumAssumption, <6>11, <6>13, <2>3, <6>14, <3>0,
                \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s) DEF PropInv, Send,
                Inv, MsgInv
          <6> QED
            BY <6>1, <6>2
          
        <5>3. QED
          BY <5>1, <5>2
        
      <4>4. (~ \E m \in msgs :  /\ m.type \in {"1a", "2a"}
                                /\ GreaterBallot(m.bal, pBal[p_1])
                                /\ m.bal.id = p_1)'
        <5>1. \A m \in msgs' \msgs : m.bal.id = p
          BY <2>3 DEF Phase2a11, Send, Inv, PropInv, GreaterBallot
        <5>2. ~ (GreaterBallot(pBal[p], pBal[p]))
          BY DEF GreaterBallot
        <5>3. \A m \in msgs' \msgs : ~( /\ GreaterBallot(m.bal, pBal[p])
                                        /\ m.bal.id = p)
          BY <2>3, <5>1, <5>2 DEF Phase2a11, Send, Inv, PropInv, GreaterBallot
        <5> QED BY <5>3, <2>3 DEF Phase2a11, Send, Inv, PropInv

      <4>6. QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5

    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Inv
      
      
  <2>4. ASSUME NEW p \in Proposers,
               Phase2a12(p)
        PROVE  Inv'
    <3>0. PICK m1 \in msgs : Phase2a12(p)!(m1)
      BY <2>4 DEF Phase2a12
        
    <3>1. TypeOK'
      <4>1. (ValidMessages(msgs))'
        BY <2>4 DEF Phase2a12, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                    ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose
      <4>5. QED
        BY <4>1, <2>4 DEF Phase2a12, TypeOK, Send, Inv

    <3>3. AccInv'
      BY <2>4, Phase2a12VotedForInv, <3>0 DEF AccInv, Inv, Send, Bmax, PartialBmax, TypeOK

    <3>2. MsgInv'
      <4> SUFFICES ASSUME NEW m \in msgs'
                   PROVE  (/\ (m.type = "1b") =>
                               /\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                     /\ \E mm \in msgs :
                                                          /\ m.from \in mm.to
                                                          /\ mm.type = "2a"
                                                          /\ mm.bal = r.bal
                                                          /\ mm.slot = r.slot
                                                          /\ mm.val = r.val
                               /\ \A v \in Values, s \in Slots, b \in Ballots :
                                     GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                       => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                               /\ \A s \in Slots, v \in Values, c \in Ballots :
                                   (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                       ~ VotedForIn(m.from, v, c, s)
                               /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                               /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                   (\A v \in Values, c \in Ballots :
                                                     GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s))
                           /\ (m.type = "2a") => 
                               /\ SafeAt(m.val, m.bal, m.slot)
                               /\ Proposed(m.val, m.slot)
                               /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val
                           /\ (m.type = "2b") => VotedForIn(m.from, m.val, m.bal, m.slot)
                           /\ (m.type = "decision") =>
                               \E Q \in Quorums, b \in Ballots : \A a \in Q : VotedForIn(a, m.val, b, m.slot))'
        BY DEF MsgInv
      <4>1. ((m.type = "1b") =>
                               /\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                     /\ \E mm \in msgs :
                                                          /\ m.from \in mm.to
                                                          /\ mm.type = "2a"
                                                          /\ mm.bal = r.bal
                                                          /\ mm.slot = r.slot
                                                          /\ mm.val = r.val
                               /\ \A v \in Values, s \in Slots, b \in Ballots :
                                     GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                       => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                               /\ \A s \in Slots, v \in Values, c \in Ballots :
                                   (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                       ~ VotedForIn(m.from, v, c, s)
                               /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                               /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                   (\A v \in Values, c \in Ballots :
                                                     GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
        <5> SUFFICES ASSUME (m.type = "1b")'
                     PROVE  (/\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                   /\ \E mm \in msgs :
                                                        /\ m.from \in mm.to
                                                        /\ mm.type = "2a"
                                                        /\ mm.bal = r.bal
                                                        /\ mm.slot = r.slot
                                                        /\ mm.val = r.val
                             /\ \A v \in Values, s \in Slots, b \in Ballots :
                                   GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                     => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                             /\ \A s \in Slots, v \in Values, c \in Ballots :
                                 (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                     ~ VotedForIn(m.from, v, c, s)
                             /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                             /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                 (\A v \in Values, c \in Ballots :
                                                   GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
          OBVIOUS
        <5>1. (\A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                  /\ \E mm \in msgs :
                                       /\ m.from \in mm.to
                                       /\ mm.type = "2a"
                                       /\ mm.bal = r.bal
                                       /\ mm.slot = r.slot
                                       /\ mm.val = r.val)'
          BY <2>4 DEF VotedForIn, MsgInv, Phase2a12, Inv, Send, VotedForIn, WontVoteIn, GreaterBallot
        <5>2. (\A v \in Values, s \in Slots, b \in Ballots :
                  GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                    => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)'
          <6> SUFFICES ASSUME NEW v \in Values', NEW s \in Slots', NEW b \in Ballots',
                              (GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s))'
                       PROVE  (\E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)'
            OBVIOUS
            <6>1. GreaterBallot(m.bal, b)
              BY DEF GreaterBallot
            <6>2. VotedForIn(m.from, v, b, s)
              BY <2>4 DEF VotedForIn, Phase2a12
            <6>3. \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
              BY <6>1, <6>2, <2>4 DEF Inv, MsgInv, Phase2a12, Send
          <6> QED
            BY <6>3, <2>4 DEF Phase2a12, Send
        <5>3. (\A s \in Slots, v \in Values, c \in Ballots :
                (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                    ~ VotedForIn(m.from, v, c, s))'
          <6> SUFFICES ASSUME NEW s \in Slots', NEW v \in Values', NEW c \in Ballots',
                              (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s)))'
                       PROVE  (~ VotedForIn(m.from, v, c, s))'
            OBVIOUS
            <6>1. GreaterBallot(m.bal, c)
              BY DEF GreaterBallot
            <6>2. GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))
              BY DEF GreaterBallot
            <6>3. ~ VotedForIn(m.from, v, c, s)
              BY <6>1, <6>2, <2>4 DEF Inv, MsgInv, Phase2a12, Send
          <6> QED
            BY <6>3, <2>4 DEF VotedForIn, Phase2a12, Send
          
        <5>4. GreaterOrEqualBallot(aBal[m.from], m.bal)'
          BY <2>4, QuorumAssumption, SystemAssumptions DEF MsgInv, Phase2a12, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot
        <5>5. (\A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                (\A v \in Values, c \in Ballots :
                                  GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
          BY <2>4, QuorumAssumption, SystemAssumptions DEF MsgInv, Phase2a12, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot
        <5>6. QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5
      <4>2. ((m.type = "2a") => 
              /\ SafeAt(m.val, m.bal, m.slot)
              /\ Proposed(m.val, m.slot)
              /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
        <5> SUFFICES ASSUME (m.type = "2a")'
                     PROVE  (/\ SafeAt(m.val, m.bal, m.slot)
                             /\ Proposed(m.val, m.slot)
                             /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
          OBVIOUS
        <5>1. SafeAt(m.val, m.bal, m.slot)'
          BY <2>4, QuorumAssumption, SystemAssumptions, m \in msgs, msgs \subseteq msgs'
          DEF MsgInv, Proposed, Phase2a12, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot
        <5>2. Proposed(m.val, m.slot)
          BY <3>0, m \in msgs DEF MsgInv, Inv, Send, TypeOK, ValidMessages, ValidMessage2a
        <5>5. Proposed(m.val, m.slot)'
          BY <3>0, <5>2 DEF Send, Proposed
        <5>3. (\A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
          BY <2>4, QuorumAssumption, SystemAssumptions, m \in msgs, msgs \subseteq msgs'
          DEF MsgInv, Proposed, Phase2a12, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot
        <5>4. QED
          BY <5>1, <5>5, <5>3

      <4>3. ((m.type = "decision") =>
              \E Q \in Quorums, b \in Ballots : \A a \in Q : VotedForIn(a, m.val, b, m.slot))'
        <5>1. PICK Q \in Quorums , S \in SUBSET {mm \in msgs : mm.type = "2b" /\ mm.bal = pBal[p] /\ mm.slot = m1.slot /\ mm.val = m1.val /\ mm.to = p} :
                   /\ \A a \in Q : \E mm \in S : mm.from = a
                   /\ msgs'
                      = msgs
                        \cup {[type |-> "decision", slot |-> m1.slot,
                               val |-> m1.val, from |-> p, to |-> Replicas]}
          BY <3>0 DEF Send
        <5>2. CASE m \in msgs
          BY <5>2, <3>3, <2>4, QuorumAssumption, SystemAssumptions DEF PropInv, AccInv, MsgInv, Phase2a12, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot, VotedForIn
        <5>30. pBal'[p] \in Ballots
          BY <3>1 DEF Inv, TypeOK
        <5>31. \A q \in Q : VotedForIn(q, m1.val, pBal[p], m1.slot)
          BY <5>1 DEF Inv, MsgInv
        <5>32. \A q \in Q : VotedForIn(q, m1.val, pBal[p], m1.slot)'
          BY <5>31, <3>0 DEF VotedForIn
        <5>3. CASE m \in msgs' \ msgs
          BY <5>32, <5>1, <5>3, <5>30 DEF Send, TypeOK, Inv
        <5> QED BY <5>2, <5>3
      <4>5. ((m.type = "2b") => VotedForIn(m.from, m.val, m.bal, m.slot))'
        BY <2>4, QuorumAssumption, SystemAssumptions DEF MsgInv, Phase2a12, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot
      <4>4. QED
        BY <4>1, <4>2, <4>3, <4>5

    <3>4. PropInv'
      <4> SUFFICES ASSUME NEW p_1 \in Proposers'
                   PROVE  (/\ pState[p_1] = 1 => ~ \E m \in msgs :
                                                   /\ m.bal = pBal[p_1]
                                                   /\ m.type \in {"1a", "2a"}
                           /\ pState[p_1] = 2 => /\ \E m \in msgs : m.type = "1a" /\ m.bal = pBal[p_1] /\ m.to = Acceptors
                                                 /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = pBal[p_1]
                           /\ pState[p_1] = 3 => /\ \E Q \in Quorums : \A a \in Q : \E m \in msgs :
                                                   /\ m.type = "1b"
                                                   /\ m.from = a
                                                   /\ m.to = p_1
                                                   /\ m.bal = pBal[p_1]
                                                 /\ \A c \in Ballots, s \in Slots :
                                                   /\ GreaterBallot(pBal[p_1], c)
                                                   /\ ~ \E m \in msgs :
                                                     /\ m.type = "2a"
                                                     /\ m.bal = pBal[p_1]
                                                     /\ m.slot = s
                                                   =>
                                                   \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s)
                           /\ ~ \E m \in msgs :  /\ m.type \in {"1a", "2a"}
                                                 /\ GreaterBallot(m.bal, pBal[p_1])
                                                 /\ m.bal.id = p_1
                           /\ pBal[p_1].id = p_1)'
        BY DEF PropInv
      <4>1. (pState[p_1] = 1 => ~ \E m \in msgs :
                                  /\ m.bal = pBal[p_1]
                                  /\ m.type \in {"1a", "2a"})'
        BY <2>4, <3>1, \A mm \in msgs' \ msgs : mm.type = "decision" DEF PropInv, Phase2a12, Inv, Send, TypeOK, WontVoteIn, VotedForIn
      <4>2. (pState[p_1] = 2 => /\ \E m \in msgs : m.type = "1a" /\ m.bal = pBal[p_1] /\ m.to = Acceptors
                                /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = pBal[p_1])'
        BY <2>4, <3>1, \A mm \in msgs' \ msgs : mm.type = "decision" DEF PropInv, Phase2a12, Inv, Send, TypeOK, WontVoteIn, VotedForIn
      <4>3. (pState[p_1] = 3 => /\ \E Q \in Quorums : \A a \in Q : \E m \in msgs :
                                  /\ m.type = "1b"
                                  /\ m.from = a
                                  /\ m.to = p_1
                                  /\ m.bal = pBal[p_1]
                                /\ \A c \in Ballots, s \in Slots :
                                  /\ GreaterBallot(pBal[p_1], c)
                                  /\ ~ \E m \in msgs :
                                    /\ m.type = "2a"
                                    /\ m.bal = pBal[p_1]
                                    /\ m.slot = s
                                  =>
                                  \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s))'
        <5> SUFFICES ASSUME (pState[p_1] = 3)'
                     PROVE  (/\ \E Q \in Quorums : \A a \in Q : \E m \in msgs :
                               /\ m.type = "1b"
                               /\ m.from = a
                               /\ m.to = p_1
                               /\ m.bal = pBal[p_1]
                             /\ \A c \in Ballots, s \in Slots :
                               /\ GreaterBallot(pBal[p_1], c)
                               /\ ~ \E m \in msgs :
                                 /\ m.type = "2a"
                                 /\ m.bal = pBal[p_1]
                                 /\ m.slot = s
                               =>
                               \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s))'
          OBVIOUS
        <5>1. ( \E Q \in Quorums : \A a \in Q : \E m \in msgs :
               /\ m.type = "1b"
               /\ m.from = a
               /\ m.to = p_1
               /\ m.bal = pBal[p_1])'
          BY <2>4, <3>1, \A mm \in msgs' \ msgs : mm.type = "decision" DEF PropInv, Phase2a12, Inv, Send, TypeOK, WontVoteIn, VotedForIn
        <5>2. ( \A c \in Ballots, s \in Slots :
               /\ GreaterBallot(pBal[p_1], c)
               /\ ~ \E m \in msgs :
                 /\ m.type = "2a"
                 /\ m.bal = pBal[p_1]
                 /\ m.slot = s
               =>
               \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s))'
          <6> SUFFICES ASSUME NEW c \in Ballots', NEW s \in Slots',
                              (/\ GreaterBallot(pBal[p_1], c)
                               /\ ~ \E m \in msgs :
                                 /\ m.type = "2a"
                                 /\ m.bal = pBal[p_1]
                                 /\ m.slot = s)'
                       PROVE  (\E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s))'
            OBVIOUS
            <6>1. GreaterBallot(pBal[p_1], c)
              BY <2>4 DEF GreaterBallot, Phase2a12
            <6>2. ~ \E m \in msgs :
                                 /\ m.type = "2a"
                                 /\ m.bal = pBal[p_1]
                                 /\ m.slot = s
              BY <2>4 DEF Phase2a12, Send
            <6>30. pState[p_1] = 3
              BY <2>4 DEF Phase2a12
            <6>3. \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s)
              BY <6>1, <6>2, <6>30 DEF Inv, PropInv
            <6>4. \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s)'
              BY <2>4, <6>3 DEF Phase2a12, WontVoteIn, VotedForIn
          <6> QED BY <6>4
        <5>3. QED
          BY <5>1, <5>2
        
      <4>4. (~ \E m \in msgs :  /\ m.type \in {"1a", "2a"}
                                /\ GreaterBallot(m.bal, pBal[p_1])
                                /\ m.bal.id = p_1)'
        BY <2>4, <3>1, \A mm \in msgs' \ msgs : mm.type = "decision" DEF PropInv, Phase2a12, Inv, Send, TypeOK, WontVoteIn, VotedForIn
      <4>5. (pBal[p_1].id = p_1)'
        BY <2>4, <3>1, \A mm \in msgs' \ msgs : mm.type = "decision" DEF PropInv, Phase2a12, Inv, Send, TypeOK, WontVoteIn, VotedForIn
      <4>6. QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5
      
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Inv

  <2>5. ASSUME NEW p \in Proposers,
               Phase2a13(p)
        PROVE  Inv'
    <3>1. TypeOK'
      <4>1. (ValidMessages(msgs))'
        BY <2>5 DEF Phase2a13, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                    ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                    ValidMessagepreempt
      <4>5. QED
        BY <4>1, <2>5 DEF Phase2a13, TypeOK, Send, Inv, ValidMessagepreempt, ValidMessages
    <3>2. MsgInv'
      <4> SUFFICES ASSUME NEW m \in msgs'
                   PROVE  (/\ (m.type = "1b") =>
                               /\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                     /\ \E mm \in msgs :
                                                          /\ m.from \in mm.to
                                                          /\ mm.type = "2a"
                                                          /\ mm.bal = r.bal
                                                          /\ mm.slot = r.slot
                                                          /\ mm.val = r.val
                               /\ \A v \in Values, s \in Slots, b \in Ballots :
                                     GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                       => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                               /\ \A s \in Slots, v \in Values, c \in Ballots :
                                   (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                       ~ VotedForIn(m.from, v, c, s)
                               /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                               /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                   (\A v \in Values, c \in Ballots :
                                                     GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s))
                           /\ (m.type = "2a") => 
                               /\ SafeAt(m.val, m.bal, m.slot)
                               /\ Proposed(m.val, m.slot)
                               /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val
                           /\ (m.type = "2b") => VotedForIn(m.from, m.val, m.bal, m.slot)
                           /\ (m.type = "decision") =>
                               \E Q \in Quorums, b \in Ballots : \A a \in Q : VotedForIn(a, m.val, b, m.slot))'
        BY DEF MsgInv
      <4>1. ((m.type = "1b") =>
              /\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                    /\ \E mm \in msgs :
                                         /\ m.from \in mm.to
                                         /\ mm.type = "2a"
                                         /\ mm.bal = r.bal
                                         /\ mm.slot = r.slot
                                         /\ mm.val = r.val
              /\ \A v \in Values, s \in Slots, b \in Ballots :
                    GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                      => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
              /\ \A s \in Slots, v \in Values, c \in Ballots :
                  (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                      ~ VotedForIn(m.from, v, c, s)
              /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
              /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                  (\A v \in Values, c \in Ballots :
                                    GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
        <5> SUFFICES ASSUME (m.type = "1b")'
                     PROVE  (/\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                   /\ \E mm \in msgs :
                                                        /\ m.from \in mm.to
                                                        /\ mm.type = "2a"
                                                        /\ mm.bal = r.bal
                                                        /\ mm.slot = r.slot
                                                        /\ mm.val = r.val
                             /\ \A v \in Values, s \in Slots, b \in Ballots :
                                   GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                     => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                             /\ \A s \in Slots, v \in Values, c \in Ballots :
                                 (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                     ~ VotedForIn(m.from, v, c, s)
                             /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                             /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                 (\A v \in Values, c \in Ballots :
                                                   GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
          OBVIOUS
        <5>1. (\A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                  /\ \E mm \in msgs :
                                       /\ m.from \in mm.to
                                       /\ mm.type = "2a"
                                       /\ mm.bal = r.bal
                                       /\ mm.slot = r.slot
                                       /\ mm.val = r.val)'
          BY <2>5 DEF VotedForIn, MsgInv, Phase2a13, Inv, Send, VotedForIn, WontVoteIn, GreaterBallot
        <5>2. (\A v \in Values, s \in Slots, b \in Ballots :
                  GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                    => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)'
          <6> SUFFICES ASSUME NEW v \in Values', NEW s \in Slots', NEW b \in Ballots',
                              (GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s))'
                       PROVE  (\E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)'
            OBVIOUS
            <6>1. GreaterBallot(m.bal, b)
              BY DEF GreaterBallot
            <6>2. VotedForIn(m.from, v, b, s)
              BY <2>5 DEF VotedForIn, Phase2a13
            <6>3. \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
              BY <6>1, <6>2, <2>5 DEF Inv, MsgInv, Phase2a13, Send
          <6> QED
            BY <6>3, <2>5 DEF Phase2a13, Send
        <5>3. (\A s \in Slots, v \in Values, c \in Ballots :
                (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                    ~ VotedForIn(m.from, v, c, s))'
          <6> SUFFICES ASSUME NEW s \in Slots', NEW v \in Values', NEW c \in Ballots',
                              (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s)))'
                       PROVE  (~ VotedForIn(m.from, v, c, s))'
            OBVIOUS
            <6>1. GreaterBallot(m.bal, c)
              BY DEF GreaterBallot
            <6>2. GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))
              BY DEF GreaterBallot
            <6>3. ~ VotedForIn(m.from, v, c, s)
              BY <6>1, <6>2, <2>5 DEF Inv, MsgInv, Phase2a13, Send
          <6> QED
            BY <6>3, <2>5 DEF VotedForIn, Phase2a13, Send
          
        <5>4. GreaterOrEqualBallot(aBal[m.from], m.bal)'
          BY <2>5, QuorumAssumption, SystemAssumptions DEF MsgInv, Phase2a13, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot
        <5>5. (\A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                (\A v \in Values, c \in Ballots :
                                  GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
          BY <2>5, QuorumAssumption, SystemAssumptions DEF MsgInv, Phase2a13, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot
        <5>6. QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5

      <4>2. ((m.type = "2a") => 
              /\ SafeAt(m.val, m.bal, m.slot)
              /\ Proposed(m.val, m.slot)
              /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
        <5> SUFFICES ASSUME (m.type = "2a")'
                     PROVE  (/\ SafeAt(m.val, m.bal, m.slot)
                             /\ Proposed(m.val, m.slot)
                             /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
          OBVIOUS
        <5>1. SafeAt(m.val, m.bal, m.slot)'
          BY <2>5, QuorumAssumption, SystemAssumptions DEF MsgInv, Phase2a13, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot, VotedForIn
        <5>2. Proposed(m.val, m.slot)'
          BY <2>5, m \in msgs, msgs \subseteq msgs' DEF
          MsgInv, Phase2a13, Inv, Send, Proposed
        <5>3. (\A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
          BY <2>5, QuorumAssumption, SystemAssumptions DEF MsgInv, Phase2a13, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot, VotedForIn
        <5>4. QED
          BY <5>1, <5>2, <5>3

      <4>3. ((m.type = "2b") => VotedForIn(m.from, m.val, m.bal, m.slot))'
        BY <2>5, QuorumAssumption, SystemAssumptions DEF MsgInv, Phase2a13, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot, VotedForIn
      <4>4. ((m.type = "decision") =>
              \E Q \in Quorums, b \in Ballots : \A a \in Q : VotedForIn(a, m.val, b, m.slot))'
        BY <2>5, QuorumAssumption, SystemAssumptions DEF MsgInv, Phase2a13, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot, VotedForIn
      <4>5. QED
        BY <4>1, <4>2, <4>3, <4>4
      
    <3>3. AccInv'
      <4>1. PICK m1 \in msgs: Phase2a13(p)!(m1)
        BY <2>5 DEF Phase2a13
      <4> QED BY <2>5, Phase2a13VotedForInv, <4>1 DEF AccInv, Inv, Send, Bmax, PartialBmax, TypeOK
      
    <3>4. PropInv'
      <4> SUFFICES ASSUME NEW p_1 \in Proposers'
                   PROVE  (/\ pState[p_1] = 1 => ~ \E m \in msgs :
                                                   /\ m.bal = pBal[p_1]
                                                   /\ m.type \in {"1a", "2a"}
                           /\ pState[p_1] = 2 => /\ \E m \in msgs : m.type = "1a" /\ m.bal = pBal[p_1] /\ m.to = Acceptors
                                                 /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = pBal[p_1]
                           /\ pState[p_1] = 3 => /\ \E Q \in Quorums : \A a \in Q : \E m \in msgs :
                                                   /\ m.type = "1b"
                                                   /\ m.from = a
                                                   /\ m.to = p_1
                                                   /\ m.bal = pBal[p_1]
                                                 /\ \A c \in Ballots, s \in Slots :
                                                   /\ GreaterBallot(pBal[p_1], c)
                                                   /\ ~ \E m \in msgs :
                                                     /\ m.type = "2a"
                                                     /\ m.bal = pBal[p_1]
                                                     /\ m.slot = s
                                                   =>
                                                   \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s)
                           /\ ~ \E m \in msgs :  /\ m.type \in {"1a", "2a"}
                                                 /\ GreaterBallot(m.bal, pBal[p_1])
                                                 /\ m.bal.id = p_1
                           /\ pBal[p_1].id = p_1)'
        BY DEF PropInv
      <4>5. (pBal[p_1].id = p_1)'
        BY <2>5, <3>1, msgs' = msgs DEF PropInv, Phase2a13, Inv, Send, TypeOK, WontVoteIn, VotedForIn
      <4>1. (pState[p_1] = 1 => ~ \E m \in msgs :
                                  /\ m.bal = pBal[p_1]
                                  /\ m.type \in {"1a", "2a"})'
        <5>0. PICK m1 \in msgs : Phase2a13(p)!(m1)
          BY <2>5 DEF Phase2a13
          <5>11. m1.bal \in Ballots
            BY <5>0 DEF Inv, TypeOK,
            ValidMessages, ValidMessagepreempt
          <5>12. m1.bal.num + 1 > m1.bal.num
            BY <5>11 DEF Ballots
          <5>10. GreaterBallot(pBal[p]', m1.bal)
            BY <5>0, <3>1, <5>11, pBal'[p].num = m1.bal.num + 1, <5>12 DEF Ballots, GreaterBallot, Inv, TypeOK
          <5>13. GreaterBallot(m1.bal, pBal[p])
            BY <5>0
          <5>15. GreaterBallot(pBal[p]', pBal[p])
            BY <5>10, <5>13, GBTransitive, <3>1, <5>11 DEF GreaterOrEqualBallot, Inv, TypeOK

        <5>1. CASE p_1 = p
          <6> SUFFICES ASSUME pState[p_1]' = 1,
                              NEW m \in msgs',
                              m.bal = pBal[p_1]',
                              m.type \in {"1a", "2a"}
                       PROVE  FALSE
          OBVIOUS
          <6> HIDE DEF Ballots
          <6>2. ~ \E mm \in msgs :  /\ mm.type \in {"1a", "2a"}
                                    /\ GreaterBallot(mm.bal, pBal[p_1])
                                    /\ mm.bal.id = p_1
            BY <2>5, <5>1 DEF Inv, PropInv
          <6>3. msgs' = msgs
            BY <2>5 DEF Phase2a13
          <6>4. m.bal.id = p
            BY <5>1, <4>5 DEF Ballots, Inv, TypeOK
          <6> QED BY <6>2, <6>3, <5>15, <6>4, <5>1
        <5>2. CASE p_1 # p
          BY <2>5, <3>1, <5>2 DEF PropInv, Phase2a13, Inv, TypeOK
        <5> QED BY <5>1, <5>2

      <4>2. (pState[p_1] = 2 => /\ \E m \in msgs : m.type = "1a" /\ m.bal = pBal[p_1] /\ m.to = Acceptors
                                /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = pBal[p_1])'
        BY <2>5, <3>1, msgs' = msgs DEF PropInv, Phase2a13, Inv, Send, TypeOK, WontVoteIn, VotedForIn
      <4>3. (pState[p_1] = 3 => /\ \E Q \in Quorums : \A a \in Q : \E m \in msgs :
                                    /\ m.type = "1b"
                                  /\ m.from = a
                                  /\ m.to = p_1
                                  /\ m.bal = pBal[p_1]
                                /\ \A c \in Ballots, s \in Slots :
                                  /\ GreaterBallot(pBal[p_1], c)
                                  (*/\ \E m \in msgs :
                                    /\ m.type = "2a"
                                    /\ m.bal = pBal[p_1]*)
                                  /\ ~ \E m \in msgs :
                                    /\ m.type = "2a"
                                    /\ m.bal = pBal[p_1]
                                    /\ m.slot = s
                                  =>
                                  \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s))'
        <5> SUFFICES ASSUME (pState[p_1] = 3)'
                     PROVE  (/\ \E Q \in Quorums : \A a \in Q : \E m \in msgs :
                                 /\ m.type = "1b"
                               /\ m.from = a
                               /\ m.to = p_1
                               /\ m.bal = pBal[p_1]
                             /\ \A c \in Ballots, s \in Slots :
                               /\ GreaterBallot(pBal[p_1], c)
                               (*/\ \E m \in msgs :
                                 /\ m.type = "2a"
                                 /\ m.bal = pBal[p_1]*)
                               /\ ~ \E m \in msgs :
                                 /\ m.type = "2a"
                                 /\ m.bal = pBal[p_1]
                                 /\ m.slot = s
                               =>
                               \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s))'
          OBVIOUS
        <5>1. ( \E Q \in Quorums : \A a \in Q : \E m \in msgs :
                 /\ m.type = "1b"
               /\ m.from = a
               /\ m.to = p_1
               /\ m.bal = pBal[p_1])'
          BY <2>5, <3>1, msgs' = msgs, Phase2a13WontVoteIn DEF PropInv, Phase2a13, Inv, Send, TypeOK
        <5>2. ( \A c \in Ballots, s \in Slots :
               /\ GreaterBallot(pBal[p_1], c)
               (*/\ \E m \in msgs :
                 /\ m.type = "2a"
                 /\ m.bal = pBal[p_1]*)
               /\ ~ \E m \in msgs :
                 /\ m.type = "2a"
                 /\ m.bal = pBal[p_1]
                 /\ m.slot = s
               =>
               \E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s))'
          <6>1. CASE p = p_1
            BY <6>1, <2>5, <3>1, msgs' = msgs, Phase2a13WontVoteIn, p_1 # p => pState[p_1]' # 3 DEF PropInv, Phase2a13, Inv, Send, TypeOK
          <6>2. CASE p # p_1
            <7> SUFFICES ASSUME NEW c \in Ballots', NEW s \in Slots',
                                    GreaterBallot(pBal[p_1], c)',
                                    (~ \E m \in msgs :
                                      /\ m.type = "2a"
                                      /\ m.bal = pBal[p_1]
                                      /\ m.slot = s)'
                         PROVE  (\E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s))'
              OBVIOUS
            <7>1. GreaterBallot(pBal[p_1], c)
              BY <6>2, <2>5 DEF Phase2a13, Inv, TypeOK
            <7>2. (~ \E m \in msgs :
                                      /\ m.type = "2a"
                                      /\ m.bal = pBal[p_1]
                                      /\ m.slot = s)
              BY <6>2, <2>5 DEF Phase2a13, Inv, TypeOK
            <7>3. (\E Q \in Quorums : \A a \in Q : WontVoteIn(a, c, s))
              BY <7>1, <7>2, <6>2, <2>5 DEF Inv, PropInv, Phase2a13, TypeOK
            <7> QED
            BY <2>5, <7>3, Phase2a13WontVoteIn, QuorumAssumption DEF Inv
          <6> QED BY <6>1, <6>2
        <5>3. QED
          BY <5>1, <5>2
        
      <4>4. (~ \E m \in msgs :  /\ m.type \in {"1a", "2a"}
                                /\ GreaterBallot(m.bal, pBal[p_1])
                                /\ m.bal.id = p_1)'
        <5>0. PICK m1 \in msgs : Phase2a13(p)!(m1)
          BY <2>5 DEF Phase2a13
          <5>11. m1.bal \in Ballots
            BY <5>0 DEF Inv, TypeOK,
            ValidMessages, ValidMessagepreempt
          <5>12. m1.bal.num + 1 > m1.bal.num
            BY <5>11 DEF Ballots
          <5>10. GreaterBallot(pBal[p]', m1.bal)
            BY <5>0, <3>1, <5>11, pBal'[p].num = m1.bal.num + 1, <5>12 DEF Ballots, GreaterBallot, Inv, TypeOK
          <5>13. GreaterBallot(m1.bal, pBal[p])
            BY <5>0
          <5>15. GreaterBallot(pBal[p]', pBal[p])
            BY <5>10, <5>13, GBTransitive, <3>1, <5>11 DEF GreaterOrEqualBallot, Inv, TypeOK

        <5>1. CASE p_1 = p
            <6> SUFFICES ASSUME NEW m \in msgs',
                                    (m.type \in {"1a", "2a"})',
                                    (GreaterBallot(m.bal, pBal[p_1]))',
                                    (m.bal.id = p_1)'
                         PROVE      FALSE
              OBVIOUS
              <6> HIDE DEF Ballots
              <6>1. GreaterBallot(pBal[p]', pBal[p])
                BY <5>15
              <6>2. m.bal \in Ballots
                BY <3>1 DEF TypeOK, Inv, ValidMessages, ValidMessage1a, ValidMessage2a
              <6>3. GreaterBallot(m.bal, pBal[p])
                BY GBTransitive, <6>1, <3>1, <6>2, <5>1 DEF Inv, TypeOK, GreaterOrEqualBallot
            <6> QED BY <2>5, <3>1, <6>3, <5>1 DEF PropInv, Phase2a13, Inv, TypeOK
        <5>2. CASE p_1 # p
          BY <2>5, <3>1, <5>2 DEF PropInv, Phase2a13, Inv, TypeOK
        <5> QED BY <5>1, <5>2
      <4>6. QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Inv

  <2>6. ASSUME NEW a \in Acceptors,
               Phase1b(a)
        PROVE  Inv'
    <3>1. TypeOK'
      <4>0. PICK m1 \in msgs : Phase1b(a)!(m1)
        BY <2>6 DEF Phase1b
      <4>21. m1.bal \in Ballots
        BY <4>0 DEF Inv, TypeOK, ValidMessages, ValidMessage1a
      <4>22. aBal[a] \in Ballots \cup {[num |-> -1, id |-> -1]}
        BY <4>0 DEF Inv, TypeOK
      <4>24. {aBal[a], m1.bal} # {}
        BY <4>21, <4>22
      <4>23. MaximumBallot({aBal[a], m1.bal}) \in Ballots
        <8>1. CASE aBal[a] = [num |-> -1, id |-> -1]
          BY <8>1, SystemAssumptions, <4>21, <4>22, <4>24
            DEF MaximumBallot, GreaterBallot
        <8>2. CASE aBal[a] # [num |-> -1, id |-> -1]
          BY <8>2, SystemAssumptions, <4>21, <4>22, <4>24, {aBal[a], m1.bal} \subseteq Ballots, MaxBalInSet
        <8> QED BY  <8>1, <8>2
      <4>1. ValidMessages(msgs)'
        <5> SUFFICES ASSUME NEW m \in msgs'
                     PROVE  (/\ m.type \in {"1a", "1b", "2a", "2b", "decision", "propose", "preempt"}
                             /\ m.type = "1a" => ValidMessage1a(m)
                             /\ m.type = "1b" => ValidMessage1b(m)
                             /\ m.type = "2a" => ValidMessage2a(m)
                             /\ m.type = "2b" => ValidMessage2b(m)
                             /\ m.type = "decision" => ValidMessagedecision(m)
                             /\ m.type = "preempt"  => ValidMessagepreempt(m)
                             /\ m.type = "propose"  => ValidMessagepropose(m))'
          BY DEF ValidMessages
        <5>1. (m.type \in {"1a", "1b", "2a", "2b", "decision", "propose", "preempt"})'
          BY <2>6 DEF Phase1b, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      MaximumBallot, Bmax, PartialBmax, GreaterBallot
        <5>2. (m.type = "1a" => ValidMessage1a(m))'
          BY <2>6 DEF Phase1b, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      MaximumBallot, Bmax, PartialBmax, GreaterBallot
        <5>3. (m.type = "1b" => ValidMessage1b(m))'
          <6> SUFFICES ASSUME (m.type = "1b")'
                       PROVE  ValidMessage1b(m)'
            OBVIOUS
          <6>0. PICK m_1 \in msgs : Phase1b(a)!(m_1)
            BY <2>6 DEF Phase1b
          <6>1. (m.bal \in Ballots)'
            <7>1. CASE m \in msgs
              BY <7>1, <6>0, <4>23 DEF TypeOK, Send, Inv, ValidMessages, ValidMessage1b
            <7>2. CASE m \in msgs' \ msgs
              BY <7>2, <6>0, <4>23, m_1.bal \in Ballots DEF TypeOK, Send, Inv, ValidMessages, ValidMessage1a
            <7> QED BY <7>1, <7>2
          <6>2. (m.voted \subseteq [bal : Ballots, slot : Slots, val : Values])'
            BY <6>0 DEF TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                        Bmax, PartialBmax
          <6>3. (m.from \in Acceptors)'
            BY <2>6 DEF Phase1b, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                        ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                        MaximumBallot, Bmax, PartialBmax, GreaterBallot
          <6>4. (m.to \in Proposers)'
            BY <2>6 DEF Phase1b, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                        ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                        MaximumBallot, Bmax, PartialBmax, GreaterBallot
          <6>5. QED
            BY <6>1, <6>2, <6>3, <6>4 DEF ValidMessage1b
          
        <5>4. (m.type = "2a" => ValidMessage2a(m))'
          BY <2>6 DEF Phase1b, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      MaximumBallot, Bmax, PartialBmax, GreaterBallot
        <5>5. (m.type = "2b" => ValidMessage2b(m))'
          BY <2>6 DEF Phase1b, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      MaximumBallot, Bmax, PartialBmax, GreaterBallot
        <5>6. (m.type = "decision" => ValidMessagedecision(m))'
          BY <2>6 DEF Phase1b, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      MaximumBallot, Bmax, PartialBmax, GreaterBallot
        <5>7. (m.type = "propose"  => ValidMessagepropose(m))'
          BY <2>6 DEF Phase1b, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      MaximumBallot, Bmax, PartialBmax, GreaterBallot
        <5>9. (m.type = "preempt"  => ValidMessagepreempt(m))'
            <7> SUFFICES ASSUME (m.type = "preempt")'
                         PROVE  ValidMessagepreempt(m)'
              OBVIOUS
            <7>1. CASE m \in msgs
              BY <7>1, <4>0, <4>23 DEF TypeOK, Send, Inv, ValidMessages, ValidMessagepreempt
            <7>2. CASE m \in msgs' \ msgs
              BY <7>2, <4>0, <4>23, m1.from \in Proposers, aBal[a] \in Ballots
              DEF TypeOK, Send, Inv, ValidMessagepreempt, ValidMessage1a, ValidMessages,
              GreaterBallot, GreaterOrEqualBallot
            <7> QED BY <7>1, <7>2
        <5>8. QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>9

      <4>2. (pBal \in [Proposers -> Ballots])'
        BY <4>1, <2>6 DEF Phase1b, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage2a, PartialBmax, MaximumBallot
      <4>3. (pState \in [Proposers -> {1, 2, 3}])'
        BY <4>1, <2>6 DEF Phase1b, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage2a, PartialBmax, MaximumBallot
      <4>4. (\A a_1 \in Acceptors : /\ aVoted[a_1] \subseteq [bal : Ballots, slot : Slots, val : Values]
                                    /\ aBal[a_1] \in Ballots \cup {[num |-> -1, id |-> -1]}
                                    /\ aVoted[a_1] \subseteq [bal : Ballots, slot : Slots, val : Values])'
        <5> SUFFICES ASSUME NEW a_1 \in Acceptors'
                     PROVE  (/\ aVoted[a_1] \subseteq [bal : Ballots, slot : Slots, val : Values]
                             /\ aBal[a_1] \in Ballots \cup {[num |-> -1, id |-> -1]}
                             /\ aVoted[a_1] \subseteq [bal : Ballots, slot : Slots, val : Values])'
          OBVIOUS
        <5>1. (aVoted[a_1] \subseteq [bal : Ballots, slot : Slots, val : Values])'
          BY <4>1, <2>6 DEF Phase1b, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage2a, PartialBmax, MaximumBallot
        <5>2. (aBal[a_1] \in Ballots \cup {[num |-> -1, id |-> -1]})'
          BY <4>1, <2>6, <4>0, <4>23 DEF TypeOK, Send, Inv, ValidMessages, ValidMessage1a
        <5>3. (aVoted[a_1] \subseteq [bal : Ballots, slot : Slots, val : Values])'
          BY <4>1, <2>6 DEF Phase1b, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage2a, PartialBmax, MaximumBallot
        <5>4. QED
          BY <5>1, <5>2, <5>3
        
      <4>5. QED
        BY <4>1, <4>2, <4>3, <4>4 DEF TypeOK

    <3>3. AccInv'
      <4> SUFFICES ASSUME NEW a_1 \in Acceptors'
                   PROVE  (/\ \A vote \in aVoted[a_1] :
                                /\ \E m \in msgs :
                                     /\ a_1 \in m.to
                                     /\ m.type = "2a"
                                     /\ m.bal = vote.bal
                                     /\ m.slot = vote.slot
                                     /\ m.val = vote.val
                                /\ \E m \in msgs:
                                     /\ m.from = a_1
                                     /\ m.type = "2b"
                                     /\ m.bal = vote.bal
                                     /\ m.slot = vote.slot
                                     /\ m.val = vote.val
                           /\ \A c \in Ballots, s \in Slots, v \in Values :
                               GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a_1], s)) => ~ VotedForIn(a_1, v, c, s))'
        BY DEF AccInv
      <4>0. PICK m \in msgs : Phase1b(a)!(m)
        BY <2>6 DEF Phase1b
      <4>1. (\A vote \in aVoted[a_1] :
               /\ \E m1 \in msgs :
                    /\ a_1 \in m1.to
                    /\ m1.type = "2a"
                    /\ m1.bal = vote.bal
                    /\ m1.slot = vote.slot
                    /\ m1.val = vote.val
               /\ \E m1 \in msgs:
                    /\ m1.from = a_1
                    /\ m1.type = "2b"
                    /\ m1.bal = vote.bal
                    /\ m1.slot = vote.slot
                    /\ m1.val = vote.val)'
        BY <2>6, Phase1bVotedForInv, <4>0 DEF AccInv, Inv, Send, Bmax, PartialBmax, TypeOK
      <4>5. \A s \in Slots: MaxVotedBallotInSlot(aVoted[a_1], s) = MaxVotedBallotInSlot(aVoted[a_1], s)'
        BY <2>6, Phase1bVotedForInv, <3>1, <4>0 DEF AccInv, Inv, TypeOK
      <4>6. \A c \in Ballots, s \in Slots, v \in Values: VotedForIn(a_1, v, c, s)' <=> VotedForIn(a_1, v, c, s)
        BY <4>0 DEF VotedForIn
      <4>2. (\A c \in Ballots, s \in Slots, v \in Values :
              GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a_1], s)) => ~ VotedForIn(a_1, v, c, s))'
        BY <4>6, <4>5 DEF AccInv, Inv, TypeOK
      <4>21. m.bal \in Ballots
        BY <4>0 DEF Inv, TypeOK, ValidMessages, ValidMessage1a
      <4>22. aBal[a] \in Ballots \cup {[num |-> -1, id |-> -1]}
        BY <4>0 DEF Inv, TypeOK
      <4>222. aBal'[a] \in Ballots \cup {[num |-> -1, id |-> -1]}
        BY <4>0, <3>1 DEF Inv, TypeOK
      <4>24. {aBal[a], m.bal} # {}
        BY <4>21, <4>22
      <4>23. MaximumBallot({aBal[a], m.bal}) \in {aBal[a], m.bal}
        <8>1. CASE aBal[a] = [num |-> -1, id |-> -1]
          BY <8>1, SystemAssumptions, <4>21, <4>22, <4>24
            DEF MaximumBallot, GreaterBallot
        <8>2. CASE aBal[a] # [num |-> -1, id |-> -1]
          BY <8>2, SystemAssumptions, <4>21, <4>22, <4>24, {aBal[a], m.bal} \subseteq Ballots, MaxBalInSet
        <8> QED BY  <8>1, <8>2
      <4>11. aBal[a]' # aBal[a] => aBal[a]' = m.bal /\ GreaterBallot(m.bal, aBal[a])
        BY <4>0, <4>23 DEF MaximumBallot, TypeOK, ValidMessages, ValidMessage1a, Inv, GreaterOrEqualBallot
      <4>10. GreaterOrEqualBallot(aBal[a]', aBal[a])
        BY <4>0, <4>11 DEF GreaterOrEqualBallot, Inv, AccInv
      <4>40. \A s \in Slots: MaxVotedBallotInSlot(aVoted'[a_1], s) \in Ballots \cup {[num |-> -1, id |-> -1]}
        BY <4>0 DEF MaxVotedBallotInSlot, MaximumBallot, Inv, TypeOK
      <4>4. QED
        BY <4>1, <4>2
        
    <3>20. Next BY <2>6 DEF Next
    <3>21. {vote.slot : vote \in aVoted[a]} = {vote.slot : vote \in PartialBmax(aVoted[a])}
      BY  aVoted[a] \in SUBSET [bal : Ballots, val : Values, slot : Slots], PBmaxVotes DEF Inv, TypeOK
    <3>2. MsgInv'
      <4> SUFFICES ASSUME NEW m \in msgs'
                   PROVE  (/\ (m.type = "1b") =>
                               /\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                     /\ \E mm \in msgs :
                                                          /\ m.from \in mm.to
                                                          /\ mm.type = "2a"
                                                          /\ mm.bal = r.bal
                                                          /\ mm.slot = r.slot
                                                          /\ mm.val = r.val
                               /\ \A v \in Values, s \in Slots, b \in Ballots :
                                     GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                       => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                               /\ \A s \in Slots, v \in Values, c \in Ballots :
                                   (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                       ~ VotedForIn(m.from, v, c, s)
                               /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                               /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                   (\A v \in Values, c \in Ballots :
                                                     GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s))
                           /\ (m.type = "2a") => 
                               /\ SafeAt(m.val, m.bal, m.slot)
                               /\ Proposed(m.val, m.slot)
                               /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val
                           /\ (m.type = "2b") => VotedForIn(m.from, m.val, m.bal, m.slot)
                           /\ (m.type = "decision") =>
                               \E Q \in Quorums, b \in Ballots : \A a_1 \in Q : VotedForIn(a_1, m.val, b, m.slot))'
        BY DEF MsgInv
      <4>0. PICK m1 \in msgs : Phase1b(a)!(m1)
        BY <2>6 DEF Phase1b
      <4>1. ((m.type = "1b") =>
                               /\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                     /\ \E mm \in msgs :
                                                          /\ m.from \in mm.to
                                                          /\ mm.type = "2a"
                                                          /\ mm.bal = r.bal
                                                          /\ mm.slot = r.slot
                                                          /\ mm.val = r.val
                               /\ \A v \in Values, s \in Slots, b \in Ballots :
                                     GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                       => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                               /\ \A s \in Slots, v \in Values, c \in Ballots :
                                   (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                       ~ VotedForIn(m.from, v, c, s)
                               /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                               /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                   (\A v \in Values, c \in Ballots :
                                                     GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
        <5> SUFFICES ASSUME (m.type = "1b")'
                     PROVE  (  /\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                     /\ \E mm \in msgs :
                                                          /\ m.from \in mm.to
                                                          /\ mm.type = "2a"
                                                          /\ mm.bal = r.bal
                                                          /\ mm.slot = r.slot
                                                          /\ mm.val = r.val
                               /\ \A v \in Values, s \in Slots, b \in Ballots :
                                     GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                       => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                               /\ \A s \in Slots, v \in Values, c \in Ballots :
                                   (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                       ~ VotedForIn(m.from, v, c, s)
                               /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                               /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                   (\A v \in Values, c \in Ballots :
                                                     GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
          OBVIOUS
        <5>10.(\A r \in m.voted : \E mm \in msgs :
                   /\ m.from \in mm.to
                   /\ mm.type = "2a"
                   /\ mm.bal = r.bal
                   /\ mm.slot = r.slot
                   /\ mm.val = r.val)'
          BY <4>0 DEF Send, Inv, MsgInv, AccInv, PartialBmax
        <5>1. (\A r \in m.voted : VotedForIn(m.from, r.val, r.bal, r.slot))'
          <6> SUFFICES ASSUME NEW r \in m.voted'
                       PROVE  VotedForIn(m.from, r.val, r.bal, r.slot)'
              OBVIOUS
          <6>1. CASE m \in msgs
            <7>1. VotedForIn(m.from, r.val, r.bal, r.slot)
              BY <6>1 DEF Inv, MsgInv
            <7>2. r.val \in Values /\ r.bal \in Ballots /\ r.slot \in Slots /\ m.from \in Acceptors
              BY <6>1 DEF Inv, TypeOK, ValidMessages, ValidMessage1b
            <7> QED BY <6>1, <2>6, <7>1, <7>2 DEF Inv, VotedForIn, Phase1b
          <6>2. CASE m \in msgs' \ msgs
            <7>1. CASE m.from # a
              BY <7>1, <6>2, <2>6, QuorumAssumption, SystemAssumptions, <4>0 DEF MsgInv, Inv,
              Send, VotedForIn, VotedForIn
            <7>2. CASE m.from = a
              <8>1. m.voted \subseteq [bal : Ballots, slot : Slots, val : Values]
                BY <4>0, <3>1 DEF Send, TypeOK, ValidMessages, ValidMessage1b
              <8>2. m.voted \subseteq aVoted[a]
                BY <6>2, <7>2, <4>0 DEF Send, PartialBmax
              <8> QED
                BY <2>6, <8>2, <6>2, <7>2, <8>1 DEF Inv, AccInv, VotedForIn, Phase1b
            <7> QED BY <7>1, <7>2
          <6> QED BY <6>1, <6>2
          
        <5>4. GreaterOrEqualBallot(aBal[m.from], m.bal)' 
          <6>1. CASE m.from # a
            BY <4>0, <6>1 DEF Send, Inv, MsgInv, TypeOK, ValidMessages, ValidMessage1b, GreaterOrEqualBallot, GreaterBallot
          <6>2. CASE m.from = a
            <7>21. m1.bal \in Ballots
              BY <4>0 DEF Inv, TypeOK, ValidMessages, ValidMessage1a
            <7>22. aBal[a] \in Ballots \cup {[num |-> -1, id |-> -1]}
              BY <4>0 DEF Inv, TypeOK
            <7>24. {aBal[a], m1.bal} # {}
              BY <7>21, <7>22
            <7>23. MaximumBallot({aBal[a], m1.bal}) \in {aBal[a], m1.bal}
              <8>1. CASE aBal[a] = [num |-> -1, id |-> -1]
                BY <8>1, SystemAssumptions, <7>21, <7>22, <7>24
                DEF MaximumBallot, GreaterBallot
              <8>2. CASE aBal[a] # [num |-> -1, id |-> -1]
                BY <8>2, SystemAssumptions, <7>21, <7>22, <7>24, {aBal[a], m1.bal} \subseteq Ballots, MaxBalInSet
              <8> QED BY  <8>1, <8>2
            <7>11. aBal[a]' # aBal[a] => aBal[a]' = m1.bal /\ GreaterBallot(m1.bal, aBal[a])
              BY <4>0, <7>23 DEF MaximumBallot, TypeOK, ValidMessages, ValidMessage1a, Inv, GreaterOrEqualBallot
            <7>1. GreaterOrEqualBallot(aBal[a]', aBal[a])
              BY <2>6, <6>2, <4>0, <7>11 DEF GreaterOrEqualBallot, Inv, AccInv\*, MaximumBallot
            <7>41. m.bal \in Ballots
              BY <3>1 DEF Inv, TypeOK, ValidMessages, ValidMessage1b
            <7>2. CASE GreaterBallot(aBal[a], m1.bal)
              BY <4>0, <6>2, <7>2,
              GBNotCommutative, <7>21, <7>22, ~GreaterBallot(m1.bal, aBal[a]),
              aBal[a]' = aBal[a],
              m \in msgs => GreaterOrEqualBallot(aBal[a], m.bal),
              m \in msgs' \ msgs => m.bal = aBal'[a]
              DEF Inv, MsgInv, GreaterOrEqualBallot, Send
            <7>3. CASE GreaterBallot(m1.bal, aBal[a])
              <8>1. aBal[a]' = m1.bal
                BY <4>0, <6>2, <7>3 DEF GreaterOrEqualBallot
              <8>21. m \in msgs => GreaterOrEqualBallot(aBal[a], m.bal)
                BY <6>2, <7>3, <7>41 DEF Inv, MsgInv, TypeOK
              <8>2. m \in msgs => GreaterOrEqualBallot(aBal'[a], m.bal)
                BY <8>21, <7>1, <3>1, <7>41, GEBTransitive DEF Inv, TypeOK
              <8>3. m \in msgs' \ msgs => m.bal = m1.bal
                BY <4>0, <8>1 DEF Send
              <8>4. m \in msgs' \ msgs => GreaterOrEqualBallot(aBal'[a], m.bal)
                BY <8>3, <8>1 DEF GreaterOrEqualBallot
              <8> QED BY <8>2, <8>4, <6>2, <7>3
            <7>4. CASE aBal[a] = m1.bal
              BY <4>0, <6>2, <7>4, aBal[a]' = aBal[a], m \in msgs => GreaterOrEqualBallot(aBal[a], m.bal),
              m \in msgs' \ msgs => m.bal = aBal'[a]
              DEF Inv, MsgInv, GreaterOrEqualBallot, MaximumBallot, Send
            <7> QED BY <7>2, <7>3, <7>4, GBTotal, <7>41, <7>22, <7>21\* DEF GreaterOrEqualBallot
          <6> QED BY <6>1, <6>2
          
        <5>2. (\A s \in Slots, v \in Values, c \in Ballots :
                (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                    ~ VotedForIn(m.from, v, c, s))'
          <6> SUFFICES ASSUME NEW s \in Slots', NEW v \in Values', NEW c \in Ballots',
                              GreaterBallot(m.bal, c)',
                              GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))'
                       PROVE  (~ VotedForIn(m.from, v, c, s))'
            OBVIOUS
            <6>11. GreaterBallot(m.bal, c)
              BY DEF GreaterBallot, TypeOK, ValidMessages, ValidMessage1b
            <6>12. GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))
              BY DEF GreaterBallot, TypeOK, ValidMessages, ValidMessage1b
            <6>0. m \in msgs => ~ VotedForIn(m.from, v, c, s)
              BY <4>0, <6>11, <6>12 DEF Inv, Send, MsgInv, TypeOK, ValidMessages, ValidMessage1b
            <6>1. CASE m.from # a
              BY <3>1, <6>1, <6>0, <4>0
                DEF VotedForIn, Send, Inv, TypeOK, ValidMessages, ValidMessage1b
            <6>2. CASE m.from = a
            <8>1. CASE m \in msgs
              BY <4>0, <8>1, <6>2, UNCHANGED <<aVoted>>, <6>0, m \in msgs DEF Send, VotedForIn, TypeOK, MsgInv, Inv
            <8>2. CASE m \in msgs' \ msgs
              <9>0. m.voted = PartialBmax(aVoted[a]) BY <4>0, <8>2 DEF Send
              <9>1. MaxVotedBallotInSlot(aVoted[a], s) = MaxVotedBallotInSlot(m.voted, s)
                BY <9>0, MVBISPbmax DEF Inv, TypeOK
              <9> QED
              BY <2>6, <8>2, <6>2, <4>0, <3>3, <9>1 DEF AccInv, Inv, Send, PartialBmax
            <8> QED BY <8>1, <8>2          

          <6> QED
            BY <6>1, <6>2
        <5>5. (\A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                (\A v \in Values, c \in Ballots :
                                  GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
          <6> SUFFICES ASSUME NEW s \in Slots',
                              (~ \E vote \in m.voted : vote.slot = s)',
                              NEW v \in Values', NEW c \in Ballots',
                              GreaterBallot(m.bal, c)'
                       PROVE  (~ VotedForIn(m.from, v, c, s))'
            OBVIOUS
            <6>1. CASE m \in msgs
              BY <4>0, <6>1 DEF AccInv, MsgInv, Inv, VotedForIn, TypeOK
            <6>2. CASE m \in msgs' \ msgs
              <7>5. m.voted \in SUBSET [bal : Ballots, val : Values, slot : Slots]
                BY <4>0, <6>2 DEF Send, PartialBmax, Inv, TypeOK
              <7>1. {vote.slot: vote \in aVoted[a]} = {vote.slot: vote \in m.voted}
                BY <6>2, <4>0, <7>5, m.voted = PartialBmax(aVoted[a]), PBmaxVotes DEF Inv, TypeOK, Send
              <7>0. ~ \E vote \in aVoted[a] : vote.slot = s BY <7>1
              <7>2. MaxVotedBallotInSlot(aVoted[a], s) = [num |-> -1, id |-> -1]
                BY <7>0 DEF MaxVotedBallotInSlot, MaximumBallot
              <7>3. GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a], s))
                BY <7>2 DEF GreaterBallot
              <7>4. ~VotedForIn(a, v, c, s)
                BY <7>3 DEF AccInv, Inv
              <7> QED
              BY <7>4, <4>0, <6>2 DEF Send, VotedForIn
          <6> QED
            BY <6>1, <6>2
          
        <5>7. (\A v \in Values, s \in Slots, b \in Ballots :
                                     GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                       => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)'
          <6> SUFFICES ASSUME NEW v \in Values', NEW s \in Slots', NEW b \in Ballots',
                              (GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s))'
                       PROVE  (\E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)'
            OBVIOUS
            <6>1. CASE m \in msgs
              <7>3. GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                BY <6>1, <4>0 DEF VotedForIn
              <7>4. \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                BY <6>1, <7>3 DEF Inv, MsgInv
              <7>5. (\E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)'
                BY <7>4, <6>1
              <7> QED BY <7>5
            <6>2. CASE m \in msgs' \ msgs
              <7>3. GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                BY <6>2, <4>0 DEF VotedForIn
              <7>1. m.voted = PartialBmax(aVoted[a]) BY <6>2, <4>0 DEF Send
              <7>21. m.from = a BY <4>0, <6>2 DEF Send
              <7>2. \E r \in aVoted[a]: r.slot = s BY <7>21, <4>0 DEF VotedForIn
              <7>6. PICK r2 \in m.voted: r2.slot = s BY <7>2, <7>21, <7>1, <3>21 DEF Send, VotedForIn
              <7>4. \A r \in aVoted[a] : r.slot = s => GreaterOrEqualBallot(r2.bal, r.bal) 
                BY <7>6, <7>1 DEF PartialBmax
              <7>41. \E r \in aVoted[a]: r.bal = b /\ r.slot = s BY <7>21, <4>0 DEF VotedForIn
              <7>5. (\E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)'
                BY <7>6, <7>4, <7>41, <4>0
              <7> QED BY <7>5

\*              BY <4>0, <6>2, <3>3 DEF Send, VotedForIn, Inv, AccInv
          <6> QED
            BY <6>1, <6>2
        <5>6. QED
          BY <5>1, <5>2, <5>4, <5>5, <5>10, <5>7
      
      <4>2. ((m.type = "2a") => 
              /\ SafeAt(m.val, m.bal, m.slot)
              /\ Proposed(m.val, m.slot)
              /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
        <5> SUFFICES ASSUME (m.type = "2a")'
                     PROVE  (/\ SafeAt(m.val, m.bal, m.slot)
                             /\ Proposed(m.val, m.slot)
                             /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
          OBVIOUS
        <5>1. SafeAt(m.val, m.bal, m.slot)
          BY <3>1, <2>6, <4>0, \A mm \in msgs' \ msgs : mm.type # "2a" DEF TypeOK, ValidMessages, ValidMessage2a, MsgInv, Inv, Send
        <5>5. m.val \in Values /\ m.bal \in Ballots /\ m.slot \in Slots BY <3>1 DEF TypeOK, ValidMessages, ValidMessage2a
        <5>7. SafeAt(m.val, m.bal, m.slot)'
          BY <5>1, <5>5, <3>1, <2>6, <3>20, SafeAtStable DEF Inv
        <5>2. (\A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
          BY <4>0, \A mm \in msgs' \ msgs : mm.type # "2a" DEF Send, VotedForIn, Inv, MsgInv
        <5>4. (Proposed(m.val, m.slot))'
          BY <4>0, m \in msgs, msgs \subseteq msgs' DEF Send, Inv, MsgInv, Proposed
        <5>3. QED
          BY <5>7, <5>2, <5>4
        
      <4>3. ((m.type = "decision") =>
              \E Q \in Quorums, b \in Ballots : \A a_1 \in Q : VotedForIn(a_1, m.val, b, m.slot))'
        <5> SUFFICES ASSUME (m.type = "decision")'
                     PROVE  (\E Q \in Quorums, b \in Ballots : \A a_1 \in Q : VotedForIn(a_1, m.val, b, m.slot))'
          OBVIOUS
          <5>1. m \in msgs
            BY <4>0 DEF Send
          <5>2. m.val \in Values /\ m.slot \in Slots
            BY <5>1 DEF TypeOK, ValidMessages, ValidMessagedecision, Inv
          <5>3. (\E Q \in Quorums, b \in Ballots : \A a_1 \in Q : VotedForIn(a_1, m.val, b, m.slot))
            BY <5>1 DEF Inv, MsgInv
        <5> QED
          BY <5>1, <5>2, <2>6, QuorumAssumption, <5>3 DEF Phase1b, Inv, VotedForIn
      <4>5. ((m.type = "2b") => VotedForIn(m.from, m.val, m.bal, m.slot))'
        BY <4>0 DEF Send, VotedForIn, Inv, MsgInv
      <4>4. QED
        BY <4>5, <4>1, <4>2, <4>3      

    <3>4. PropInv'
      <4> SUFFICES ASSUME NEW p \in Proposers'
                   PROVE  (    /\ pState[p] = 1 => ~ \E m \in msgs :
                                                       /\ m.bal = pBal[p]
                                                       /\ m.type \in {"1a", "2a"}
                               /\ pState[p] = 2 => /\ \E m \in msgs : m.type = "1a" /\ m.bal = pBal[p] /\ m.to = Acceptors
                                                   /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = pBal[p]
                               /\ pState[p] = 3 => /\ \E Q \in Quorums : \A a_1 \in Q : \E m \in msgs :
                                                       /\ m.type = "1b"
                                                       /\ m.from = a_1
                                                       /\ m.to = p
                                                       /\ m.bal = pBal[p]
                                                   /\ \A c \in Ballots, s \in Slots :
                                                       /\ GreaterBallot(pBal[p], c)
                           (*                            /\ \E m \in msgs :
                                                         /\ m.type = "2a"
                                                         /\ m.bal = pBal[p]*)
                                                       /\ ~ \E m \in msgs :
                                                         /\ m.type = "2a"
                                                         /\ m.bal = pBal[p]
                                                         /\ m.slot = s
                                                       =>
                                                       \E Q \in Quorums : \A a_1 \in Q : WontVoteIn(a_1, c, s)
                               /\ ~ \E m \in msgs :  /\ m.type \in {"1a", "2a"}
                                                     /\ GreaterBallot(m.bal, pBal[p])
                                                     /\ m.bal.id = p
                               /\ pBal[p].id = p)'
        BY DEF PropInv
      <4>0. PICK m1 \in msgs : Phase1b(a)!(m1)
        BY <2>6 DEF Phase1b
      <4>1. (pState[p] = 1 => ~ \E m \in msgs :
                                  /\ m.bal = pBal[p]
                                  /\ m.type \in {"1a", "2a"})'
        BY <2>6, <3>1, Phase1bWontVoteIn, Phase1bVotedForInv DEF PropInv, Phase1b, Inv, TypeOK, Send, PartialBmax, MaximumBallot
      <4>2. (pState[p] = 2 => /\ \E m \in msgs : m.type = "1a" /\ m.bal = pBal[p] /\ m.to = Acceptors
                              /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = pBal[p])'
        BY <2>6, <3>1, Phase1bWontVoteIn, Phase1bVotedForInv DEF PropInv, Phase1b, Inv, TypeOK, Send, PartialBmax, MaximumBallot
      <4>3. (       pState[p] = 3 => /\ \E Q \in Quorums : \A a_1 \in Q : \E m \in msgs :
                                         /\ m.type = "1b"
                                         /\ m.from = a_1
                                         /\ m.to = p
                                         /\ m.bal = pBal[p]
                                     /\ \A c \in Ballots, s \in Slots :
                                         /\ GreaterBallot(pBal[p], c)
                                         /\ ~ \E m \in msgs :
                                           /\ m.type = "2a"
                                           /\ m.bal = pBal[p]
                                           /\ m.slot = s
                                         =>
                                         \E Q \in Quorums : \A a_1 \in Q : WontVoteIn(a_1, c, s))'
        <5> SUFFICES ASSUME (pState[p] = 3)'
                     PROVE  (                        /\ \E Q \in Quorums : \A a_1 \in Q : \E m \in msgs :
                                                         /\ m.type = "1b"
                                                         /\ m.from = a_1
                                                         /\ m.to = p
                                                         /\ m.bal = pBal[p]
                                                     /\ \A c \in Ballots, s \in Slots :
                                                         /\ GreaterBallot(pBal[p], c)
                             (*                            /\ \E m \in msgs :
                                                           /\ m.type = "2a"
                                                           /\ m.bal = pBal[p]*)
                                                         /\ ~ \E m \in msgs :
                                                           /\ m.type = "2a"
                                                           /\ m.bal = pBal[p]
                                                           /\ m.slot = s
                                                         =>
                                                         \E Q \in Quorums : \A a_1 \in Q : WontVoteIn(a_1, c, s))'
          OBVIOUS
        <5>1. (\E Q \in Quorums : \A a_1 \in Q : \E m \in msgs :
                /\ m.type = "1b"
                /\ m.from = a_1
                /\ m.to = p
                /\ m.bal = pBal[p])'
          BY <2>6, <3>1, Phase1bWontVoteIn, Phase1bVotedForInv DEF PropInv, Phase1b, Inv, TypeOK, Send, PartialBmax, MaximumBallot
        <5>21. \A c \in Ballots, s \in Slots: 
                (/\ GreaterBallot(pBal[p], c)
                 /\ ~(\E m \in msgs :
                        /\ m.type = "2a"
                        /\ m.bal = pBal[p]
                        /\ m.slot = s)) =>
                \E Q \in Quorums : \A a_1 \in Q : WontVoteIn(a_1, c, s)
          BY <2>6, <3>1, <4>0, \A mm \in msgs' \ msgs : mm.type # "2a", <3>2 DEF SafeAt, PropInv, Inv, TypeOK, Send
        <5>2. (                           \A c \in Ballots, s \in Slots :
                                           /\ GreaterBallot(pBal[p], c)
               (*                            /\ \E m \in msgs :
                                             /\ m.type = "2a"
                                             /\ m.bal = pBal[p]*)
                                           /\ ~ \E m \in msgs :
                                             /\ m.type = "2a"
                                             /\ m.bal = pBal[p]
                                             /\ m.slot = s
                                           =>
                                           \E Q \in Quorums : \A a_1 \in Q : WontVoteIn(a_1, c, s))'
          <6> SUFFICES ASSUME NEW c \in Ballots', NEW s \in Slots',
                              ( ~ \E m \in msgs :
                               /\ m.type = "2a"
                               /\ m.bal = pBal[p]
                               /\ m.slot = s)',
                              GreaterBallot(pBal[p], c)'
                       PROVE  (\E Q \in Quorums : \A a_1 \in Q : WontVoteIn(a_1, c, s))'
            OBVIOUS
            <6>1. GreaterBallot(pBal[p], c)
              BY <2>6 DEF Phase1b
            <6>2. ( ~ \E m \in msgs :
                               /\ m.type = "2a"
                               /\ m.bal = pBal[p]
                               /\ m.slot = s)
              BY  <2>6 DEF Phase1b, Send
            <6>3. PICK Q \in Quorums : \A a_1 \in Q : WontVoteIn(a_1, c, s)
              BY <6>1, <6>2, <5>21
            <6>4. GreaterBallot(aBal'[a], aBal[a])
              BY <4>0
            <6>5. \A a_1 \in Acceptors: GreaterBallot(aBal[a_1], c) => GreaterBallot(aBal'[a_1], c)
              BY <6>4, GBTransitive3, <3>1, <4>0 DEF Inv, TypeOK 
            <6>6. \A a_1 \in Q: \A v \in Values: ~VotedForIn(a_1, v, c, s)'
              BY <6>3, <4>0 DEF WontVoteIn, VotedForIn
            <6>7. \A a_1 \in Q: GreaterBallot(aBal'[a_1], c)
              BY <6>5, <6>3, QuorumAssumption DEF WontVoteIn
          <6>. QED BY <6>6, <6>7 DEF WontVoteIn
        <5>3. QED
          BY <5>1, <5>2
        
      <4>4. (~ \E m \in msgs :  /\ m.type \in {"1a", "2a"}
                                /\ GreaterBallot(m.bal, pBal[p])
                                /\ m.bal.id = p)'
        BY <2>6, <3>1, Phase1bWontVoteIn, Phase1bVotedForInv DEF PropInv, Phase1b, Inv, TypeOK, Send, PartialBmax, MaximumBallot
      <4>5. (pBal[p].id = p)'
        BY <2>6, <3>1, Phase1bWontVoteIn, Phase1bVotedForInv DEF PropInv, Phase1b, Inv, TypeOK, Send, PartialBmax, MaximumBallot
      <4>6. QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5
      \*, WontVoteIn, VotedForIn
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Inv

  <2>7. ASSUME NEW a \in Acceptors,
               Phase2b(a)
        PROVE  Inv'
    <3>1. TypeOK'
      <4>1. (ValidMessages(msgs))'
        <5> SUFFICES ASSUME NEW m \in msgs'
                     PROVE  (/\ m.type \in {"1a", "1b", "2a", "2b", "decision", "propose", "preempt"}
                             /\ m.type = "1a" => ValidMessage1a(m)
                             /\ m.type = "1b" => ValidMessage1b(m)
                             /\ m.type = "2a" => ValidMessage2a(m)
                             /\ m.type = "2b" => ValidMessage2b(m)
                             /\ m.type = "decision" => ValidMessagedecision(m)
                             /\ m.type = "preempt" => ValidMessagepreempt(m)
                             /\ m.type = "propose"  => ValidMessagepropose(m))'
          BY DEF ValidMessages
        <5>1. (m.type \in {"1a", "1b", "2a", "2b", "decision", "propose", "preempt"})'
          BY <2>7 DEF Phase2b, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      MaximumBallot, Bmax, PartialBmax, GreaterBallot,
                      MaxVotedBallotInSlot
        <5>2. (m.type = "1a" => ValidMessage1a(m))'
          BY <2>7 DEF Phase2b, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      MaximumBallot, Bmax, PartialBmax, GreaterBallot,
                      MaxVotedBallotInSlot
        <5>3. (m.type = "1b" => ValidMessage1b(m))'
          BY <2>7 DEF Phase2b, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      MaximumBallot, Bmax, PartialBmax, GreaterBallot,
                      MaxVotedBallotInSlot
        <5>4. (m.type = "2a" => ValidMessage2a(m))'
          BY <2>7 DEF Phase2b, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      MaximumBallot, Bmax, PartialBmax, GreaterBallot,
                      MaxVotedBallotInSlot
        <5>5. (m.type = "2b" => ValidMessage2b(m))'
          <6> SUFFICES ASSUME (m.type = "2b")'
                       PROVE  ValidMessage2b(m)'
            OBVIOUS
          <6>0. PICK m_1 \in msgs : Phase2b(a)!(m_1)
            BY <2>7 DEF Phase2b
          <6>11. m_1.bal \in Ballots
            BY <6>0 DEF Inv, TypeOK, ValidMessages, ValidMessage2a
          <6>12. aBal[a] \in Ballots \cup {[num |-> -1, id |-> -1]}
            BY <6>0 DEF Inv, TypeOK
          <6>13. MaximumBallot({aBal[a], m_1.bal}) \in Ballots
            <7>1. CASE aBal[a] = [num |-> -1, id |-> -1]
              BY SystemAssumptions, <7>1, <6>11, GreaterBallot(m_1.bal, aBal[a]) DEF MaximumBallot, GreaterBallot
            <7>2. CASE aBal[a] # [num |-> -1, id |-> -1]
              BY SystemAssumptions, <7>2, <6>11, <6>12, MBType
            <7> QED BY <7>1, <7>2
          <6>1. (m.bal \in Ballots)'
            BY <6>0 DEF TypeOK, Send, Inv, ValidMessages, ValidMessage2b, ValidMessage2a
          <6>2. (m.slot \in Slots)'
            BY <6>0 DEF TypeOK, Send, Inv, ValidMessages,
                      ValidMessage2a, ValidMessage2b, MaximumBallot, Bmax, PartialBmax, GreaterBallot
          <6>3. (m.val \in Values)'
            BY <6>0 DEF TypeOK, Send, Inv, ValidMessages,
                      ValidMessage2a, ValidMessage2b, MaximumBallot, Bmax, PartialBmax, GreaterBallot
          <6>4. (m.from \in Acceptors)'
            BY <6>0 DEF TypeOK, Send, Inv, ValidMessages,
                      ValidMessage2a, ValidMessage2b, MaximumBallot, Bmax, PartialBmax, GreaterBallot
          <6>5. (m.to \in Proposers)'
            BY <6>0 DEF TypeOK, Send, Inv, ValidMessages,
                      ValidMessage2a, ValidMessage2b, MaximumBallot, Bmax, PartialBmax, GreaterBallot
          <6>6. QED
            BY <6>1, <6>2, <6>3, <6>4, <6>5 DEF ValidMessage2b
        <5>6. (m.type = "decision" => ValidMessagedecision(m))'
          BY <2>7 DEF Phase2b, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      MaximumBallot, Bmax, PartialBmax, GreaterBallot,
                      MaxVotedBallotInSlot
        <5>7. (m.type = "propose"  => ValidMessagepropose(m))'
          BY <2>7 DEF Phase2b, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      MaximumBallot, Bmax, PartialBmax, GreaterBallot,
                      MaxVotedBallotInSlot
        <5>9. (m.type = "preempt" => ValidMessagepreempt(m))'
            <7> SUFFICES ASSUME (m.type = "preempt")'
                         PROVE  ValidMessagepreempt(m)'
              OBVIOUS
            <7>0. PICK m_1 \in msgs : Phase2b(a)!(m_1)
              BY <2>7 DEF Phase2b
            <7>1. CASE m \in msgs
              BY <7>1, <2>7 DEF Phase2b, TypeOK, Send, Inv, ValidMessages, ValidMessagepreempt
            <7>33. m \in msgs' \ msgs => GreaterBallot(aBal[a], m_1.bal)
              BY <7>0, GEBNotCommutative DEF TypeOK, ValidMessages, ValidMessage2a, Inv, Send
            <7>34. m_1.bal \in Ballots
              BY <7>0 DEF TypeOK, ValidMessages, ValidMessage2a, Inv, Send
            <7>36. m_1.bal.num >= 0
              BY <7>0 DEF TypeOK, ValidMessages, ValidMessage2a, Inv, Send
            <7>37. aBal[a].num \in Nat \cup {-1}
              BY DEF Inv, TypeOK
            <7>35. m \in msgs' \ msgs => aBal[a].num >= 0
              BY <7>36, <7>33, <7>34, <7>37 DEF GreaterBallot
            <7>3. m \in msgs' \ msgs => aBal[a] \in Ballots
              BY <7>35
              DEF TypeOK, Inv
            <7>2. CASE m \in msgs' \ msgs
              BY <7>2, <7>0, <7>3, m_1.from \in Proposers
              DEF TypeOK, Send, Inv, ValidMessagepreempt, ValidMessage2a, ValidMessages,
              GreaterBallot, GreaterOrEqualBallot
            <7> QED BY <7>1, <7>2

        <5>8. QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>9
        
      <4>2. (pBal \in [Proposers -> Ballots])'
        BY <2>7 DEF Phase2b, TypeOK, Sends, Inv
      <4>3. (pState \in [Proposers -> {1, 2, 3}])'
        BY <2>7 DEF Phase2b, TypeOK, Sends, Inv
      <4>4. (\A a_1 \in Acceptors : /\ aVoted[a_1] \subseteq [bal : Ballots, slot : Slots, val : Values]
                                    /\ aBal[a_1] \in Ballots \cup {[num |-> -1, id |-> -1]})'
        <5> SUFFICES ASSUME NEW a_1 \in Acceptors'
                     PROVE  (/\ aVoted[a_1] \subseteq [bal : Ballots, slot : Slots, val : Values]
                             /\ aBal[a_1] \in Ballots \cup {[num |-> -1, id |-> -1]}
                             /\ aVoted[a_1] \subseteq [bal : Ballots, slot : Slots, val : Values])'
          OBVIOUS
        <5>16. \A mm \in msgs' \ msgs : mm.type \in {"2b", "preempt"}
          BY <2>7 DEF Phase2b, Send, MaximumBallot
        <5>0. PICK m_1 \in msgs : Phase2b(a)!(m_1)
          BY <2>7 DEF Phase2b
        <5>21. m_1.bal \in Ballots
          BY <5>0 DEF Inv, TypeOK, ValidMessages, ValidMessage2a
        <5>22. aBal[a] \in Ballots \cup {[num |-> -1, id |-> -1]}
          BY <5>0 DEF Inv, TypeOK
        <5>23. MaximumBallot({aBal[a], m_1.bal}) \in Ballots
          <7>1. CASE aBal[a] = [num |-> -1, id |-> -1]
            BY SystemAssumptions, <7>1, <5>21, GreaterBallot(m_1.bal, aBal[a]) DEF MaximumBallot, GreaterBallot
          <7>2. CASE aBal[a] # [num |-> -1, id |-> -1]
            BY SystemAssumptions, <7>2, <5>21, <5>22, MBType
          <7> QED BY <7>1, <7>2
        <5>1. (aVoted[a_1] \subseteq [bal : Ballots, slot : Slots, val : Values])'
          BY <2>7, <5>0 DEF Inv, Phase2b, TypeOK, ValidMessages, ValidMessage1a, ValidMessage2a, MaximumBallot
        <5>2. (aBal[a_1] \in Ballots \cup {[num |-> -1, id |-> -1]})'
          BY <2>7, <5>23, <5>0 DEF Inv, TypeOK, ValidMessages, ValidMessage1a, ValidMessage2a\*, MaximumBallot, SeenBallots
        <5>4. QED
          BY <5>1, <5>2
        
          
      <4>5. QED
        BY <4>1, <4>2, <4>3, <4>4 DEF TypeOK
      
    <3>2. MsgInv'
      <4> SUFFICES ASSUME NEW m \in msgs'
                   PROVE  (/\ (m.type = "1b") =>
                               /\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                     /\ \E mm \in msgs :
                                                          /\ m.from \in mm.to
                                                          /\ mm.type = "2a"
                                                          /\ mm.bal = r.bal
                                                          /\ mm.slot = r.slot
                                                          /\ mm.val = r.val
                               /\ \A v \in Values, s \in Slots, b \in Ballots :
                                     GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                       => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                               /\ \A s \in Slots, v \in Values, c \in Ballots :
                                   (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                       ~ VotedForIn(m.from, v, c, s)
                               /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                               /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                   (\A v \in Values, c \in Ballots :
                                                     GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s))
                           /\ (m.type = "2a") => 
                               /\ SafeAt(m.val, m.bal, m.slot)
                               /\ Proposed(m.val, m.slot)
                               /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val
                           /\ (m.type = "2b") => VotedForIn(m.from, m.val, m.bal, m.slot)
                           /\ (m.type = "decision") =>
                               \E Q \in Quorums, b \in Ballots : \A a_1 \in Q : VotedForIn(a_1, m.val, b, m.slot))'
        BY DEF MsgInv
      <4>0. PICK m1 \in msgs : Phase2b(a)!(m1)
        BY <2>7 DEF Phase2b
      <4>1. ((m.type = "1b") =>
                               /\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                     /\ \E mm \in msgs :
                                                          /\ m.from \in mm.to
                                                          /\ mm.type = "2a"
                                                          /\ mm.bal = r.bal
                                                          /\ mm.slot = r.slot
                                                          /\ mm.val = r.val
                               /\ \A v \in Values, s \in Slots, b \in Ballots :
                                     GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                       => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                               /\ \A s \in Slots, v \in Values, c \in Ballots :
                                   (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                       ~ VotedForIn(m.from, v, c, s)
                               /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                               /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                   (\A v \in Values, c \in Ballots :
                                                     GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
        <5> SUFFICES ASSUME (m.type = "1b")'
                     PROVE  (
                               /\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                     /\ \E mm \in msgs :
                                                          /\ m.from \in mm.to
                                                          /\ mm.type = "2a"
                                                          /\ mm.bal = r.bal
                                                          /\ mm.slot = r.slot
                                                          /\ mm.val = r.val
                               /\ \A v \in Values, s \in Slots, b \in Ballots :
                                     GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                       => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                               /\ \A s \in Slots, v \in Values, c \in Ballots :
                                   (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                       ~ VotedForIn(m.from, v, c, s)
                               /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                               /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                   (\A v \in Values, c \in Ballots :
                                                     GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
          OBVIOUS
        <5>0. m \in msgs
          BY <4>0 DEF Send
        <5>10. (/\ \A r \in m.voted : \E mm \in msgs :
                                       /\ m.from \in mm.to
                                       /\ mm.type = "2a"
                                       /\ mm.bal = r.bal
                                       /\ mm.slot = r.slot
                                       /\ mm.val = r.val)'
          BY <4>0, <5>0 DEF Send, Inv, MsgInv
        <5>1. (\A r \in m.voted : VotedForIn(m.from, r.val, r.bal, r.slot))'
          <6>1. CASE m.from # a
            BY <4>0, <5>0, <6>1 DEF WontVoteIn, Send, Inv, VotedForIn, VotedForIn, MsgInv, TypeOK, ValidMessages, ValidMessage1b, GreaterOrEqualBallot, GreaterBallot
          <6>2. CASE m.from = a
            BY <4>0, <6>2, <5>0 DEF VotedForIn, Inv, MsgInv
          <6> QED BY <6>1, <6>2
        <5>7. (GreaterOrEqualBallot(aBal[m.from], m.bal))'
          <6>1. CASE m.from # a
            BY <4>0, <5>0, <6>1 DEF Send, Inv, MsgInv, TypeOK, ValidMessages, ValidMessage1b, GreaterOrEqualBallot, GreaterBallot
          <6>2. CASE m.from = a
            <7>21. m1.bal \in Ballots
              BY <4>0 DEF Inv, TypeOK, ValidMessages, ValidMessage2a
            <7>22. aBal[a] \in Ballots \cup {[num |-> -1, id |-> -1]}
              BY <4>0 DEF Inv, TypeOK
            <7>24. {aBal[a], m1.bal} # {}
              BY <7>21, <7>22
            <7>23. MaximumBallot({aBal[a], m1.bal}) \in {aBal[a], m1.bal}
              <8>1. CASE aBal[a] = [num |-> -1, id |-> -1]
                BY <8>1, SystemAssumptions, <7>21, <7>22, <7>24
                DEF MaximumBallot, GreaterBallot
              <8>2. CASE aBal[a] # [num |-> -1, id |-> -1]
                BY <8>2, SystemAssumptions, <7>21, <7>22, <7>24, {aBal[a], m1.bal} \subseteq Ballots, MaxBalInSet
              <8> QED BY  <8>1, <8>2
            <7>11. aBal[a]' # aBal[a] => aBal[a]' = m1.bal /\ GreaterBallot(m1.bal, aBal[a])
              BY <4>0, <7>23 DEF MaximumBallot, TypeOK, ValidMessages, ValidMessage2a, Inv, GreaterOrEqualBallot
            <7>1. GreaterOrEqualBallot(aBal[a]', aBal[a])
              BY <2>7, <6>2, <4>0, <7>11 DEF GreaterOrEqualBallot, Inv, AccInv\*, MaximumBallot
            <7>2. GreaterOrEqualBallot(aBal[a], m.bal)
              BY <5>0, <6>2 DEF Inv, MsgInv
            <7>3. m.bal \in Ballots
              BY <3>1 DEF Inv, TypeOK, ValidMessages, ValidMessage1b
            <7>4. GreaterOrEqualBallot(aBal[a]', m.bal)
              BY <7>1, <7>2, <7>3, <3>1, GEBTransitive DEF Inv, TypeOK
            <7> QED BY <6>2, <7>4
          <6> QED BY <6>1, <6>2
        
        <5>2. (\A s \in Slots, v \in Values, c \in Ballots :
                (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                    ~ VotedForIn(m.from, v, c, s))'
          <6> SUFFICES ASSUME NEW s \in Slots', NEW v \in Values', NEW c \in Ballots',
                              GreaterBallot(m.bal, c)',
                              GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))'
                       PROVE  (~ VotedForIn(m.from, v, c, s))'
            OBVIOUS
            <6>11. GreaterBallot(m.bal, c)
              BY DEF GreaterBallot, TypeOK, ValidMessages, ValidMessage1b
            <6>12. GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))
              BY DEF GreaterBallot, TypeOK, ValidMessages, ValidMessage1b
            <6>0. ~ VotedForIn(m.from, v, c, s)
              BY <4>0, <5>0, <6>11, <6>12 DEF Inv, Send, MsgInv, TypeOK, ValidMessages, ValidMessage1b
            <6>1. CASE m.from # a
              BY <3>1, <6>1, <6>0, <5>0, <4>0
                DEF VotedForIn, Send, Inv, TypeOK, ValidMessages, ValidMessage1b
            <6>2. CASE m.from = a
            <8>1. CASE ~GreaterOrEqualBallot(m1.bal, aBal[a])
              BY <4>0, <8>1, <6>0, <6>2, m \in msgs DEF Send, VotedForIn
            <8>2. CASE GreaterOrEqualBallot(m1.bal, aBal[a])
                <9>21. m1.bal \in Ballots
                  BY <4>0 DEF Inv, TypeOK, ValidMessages, ValidMessage2a
                <9>22. aBal[a] \in Ballots \cup {[num |-> -1, id |-> -1]}
                  BY <4>0 DEF Inv, TypeOK
                <9>23. GreaterBallot(m1.bal, aBal[a]) => MaximumBallot({m1.bal, aBal[a]}) = m1.bal
                  BY <9>21, <9>22, GBNotCommutative,
                  GreaterBallot(m1.bal, aBal[a]) => ~GreaterBallot(aBal[a], m1.bal)
                  DEF MaximumBallot
                <9>24. m1.bal = aBal[a] => MaximumBallot({m1.bal, aBal[a]}) = m1.bal
                  BY DEF MaximumBallot
                <9>3. \A mm \in msgs' \ msgs : mm.bal = m1.bal
                  BY <5>0, <4>0, <8>2, <6>2, <9>23, <9>24
                  DEF Send, TypeOK, GreaterOrEqualBallot
                <9>44. GreaterBallot(m1.bal, c)
                  BY <8>2, <6>2, GBTransitive, <4>0, <5>0 DEF MsgInv, GreaterOrEqualBallot, TypeOK, ValidMessages, ValidMessage1b, Inv, ValidMessage2a
                <9>4. m1.bal # c
                  BY <9>44 DEF GreaterBallot
                <9>5. \A mm \in msgs' \ msgs : mm.bal # c
                  BY <9>4, <9>3
                <9>6. \A mm \in aVoted[a]' \ aVoted[a] : mm.bal # c
                  BY <9>4, <4>0, <8>2, <6>2 DEF Send
                <9> QED BY <8>2, <6>2, <6>0, <9>6 DEF VotedForIn, TypeOK, ValidMessages, ValidMessage1b
            <8> QED BY <8>1, <8>2          

          <6> QED
            BY <6>1, <6>2
        <5>4. (\A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                (\A v \in Values, c \in Ballots :
                                  GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
          <6> SUFFICES ASSUME NEW s \in Slots',
                              (~ \E vote \in m.voted : vote.slot = s)',
                              NEW v \in Values', NEW c \in Ballots',
                              GreaterBallot(m.bal, c)'
                       PROVE  (~ VotedForIn(m.from, v, c, s))'
            OBVIOUS
            <6>1. GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))
              BY SystemAssumptions DEF GreaterBallot, MaxVotedBallotInSlot, MaximumBallot
          <6> QED
            BY <5>2, <6>1
          \*<5>0, <2>7, <4>0, Phase2bVotedForInv DEF TypeOK, ValidMessages, ValidMessage1b, MsgInv, Inv
        <5>8. (\A v \in Values, s \in Slots, b \in Ballots :
                GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)'
          <6> SUFFICES ASSUME NEW v \in Values', NEW s \in Slots', NEW b \in Ballots',
                              (GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s))'
                       PROVE  (\E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)'
            OBVIOUS
            <6>1. GreaterBallot(m.bal, b)
              BY DEF GreaterBallot
            <6>2. CASE GreaterOrEqualBallot(m1.bal, aBal[a])
              <7>1. aVoted[m.from] \subseteq aVoted'[m.from]
                BY <4>0, <6>2, <5>0 DEF Inv, TypeOK, ValidMessages, ValidMessage1b
              <7>2. CASE VotedForIn(m.from, v, b, s)
                BY <7>2, <6>1, <5>0, <4>0, <6>2 DEF Inv, MsgInv, TypeOK
              <7>3. CASE ~VotedForIn(m.from, v, b, s)
                <8>11. (\E d \in aVoted'[m.from] \ aVoted[m.from] :
                          /\ d.bal = b
                          /\ d.val = v
                          /\ d.slot = s)
                  BY <4>0, <7>3 DEF VotedForIn
                <8>10. m.from = a
                  BY <4>0, <8>11, <5>0 DEF TypeOK, Inv, ValidMessages, ValidMessage1b
                <8>12. \A dd \in aVoted'[m.from] \ aVoted[m.from] :
                          /\ dd.bal = m1.bal
                          /\ dd.val = m1.val
                          /\ dd.slot = m1.slot
                  BY <4>0, <5>0, m.from = a => <8>12, m.from # a => <8>12 DEF TypeOK, Inv, ValidMessages, ValidMessage1b
                <8>1. b = m1.bal
                  BY <8>12, <7>3 DEF VotedForIn
                <8>4. GreaterOrEqualBallot(m1.bal, aBal[a])
                  BY <5>0, <8>10, <8>12, <7>3, <4>0, <8>11 DEF VotedForIn
                <8>51. GreaterOrEqualBallot(b, aBal[a])
                  BY <8>4, <8>1
                <8>5. GreaterBallot(m.bal, aBal[a])
                  BY <5>0, <8>1, <8>51, GBTransitive2 DEF TypeOK, ValidMessages, ValidMessage1b, Inv
                <8>6. ~GreaterOrEqualBallot(aBal[a], m.bal)
                  BY <8>5, <5>0, <8>1, <8>51, GEBNotCommutative DEF TypeOK, ValidMessages, ValidMessage1b, Inv
                <8>7. GreaterOrEqualBallot(aBal[m.from], m.bal)
                  BY <5>0 DEF Inv, MsgInv
                <8>2. CASE m.from # a
                  BY <8>10, <8>2, FALSE
                <8>3. CASE m.from = a
                  BY <8>6, <5>0, <8>3, <8>7, FALSE
                <8> QED
                  BY <8>2, <8>3
              <7> QED BY <7>3, <7>2
            <6>3. CASE ~GreaterOrEqualBallot(m1.bal, aBal[a])
              <7>1. aVoted[m.from] = aVoted'[m.from]
                BY <4>0, <6>3, <5>0 DEF Inv, TypeOK, ValidMessages, ValidMessage1b
              <7>2. VotedForIn(m.from, v, b, s)
                BY <7>1 DEF VotedForIn
              <7>3. (\E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)
                BY <7>2, <6>1, <5>0 DEF Inv, MsgInv
              <7> QED BY <4>0, <6>3, <5>0, <7>3 DEF Inv, MsgInv, TypeOK
          <6> QED
            BY <6>1, <6>2, <6>3
          
        <5>5. QED
          BY <5>1, <5>2, <5>4, <5>7, <5>10, <5>8
        
      <4>2. ((m.type = "2a") => 
              /\ SafeAt(m.val, m.bal, m.slot)
              /\ Proposed(m.val, m.slot)
              /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
        <5> SUFFICES ASSUME (m.type = "2a")'
                     PROVE  (/\ SafeAt(m.val, m.bal, m.slot)
                             /\ Proposed(m.val, m.slot)
                             /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
          OBVIOUS
        <5>1. SafeAt(m.val, m.bal, m.slot)'
          BY <3>1, <2>7, <4>0, SafeAtStable, \A mm \in msgs' \ msgs : mm.type # "2a" DEF TypeOK, ValidMessages, ValidMessage2a, MsgInv, Inv, Send, Next 
        <5>2. (\A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
          BY <3>1, <2>7, SafeAtStable, QuorumAssumption, SystemAssumptions, \A mm \in msgs' \ msgs : mm.type # "2a" DEF MaximumBallot, TypeOK, ValidMessages, ValidMessage2a, MsgInv, Phase2b, Inv, Send
        <5>4. (Proposed(m.val, m.slot))'
          BY <4>0, m \in msgs, msgs \subseteq msgs' DEF Send, Inv, MsgInv, Proposed
        <5>3. QED
          BY <5>1, <5>2, <5>4
        
      <4>3. ((m.type = "decision") =>
              \E Q \in Quorums, b \in Ballots : \A a_1 \in Q : VotedForIn(a_1, m.val, b, m.slot))'
        <5> SUFFICES ASSUME (m.type = "decision")'
                     PROVE  (\E Q \in Quorums, b \in Ballots : \A a_1 \in Q : VotedForIn(a_1, m.val, b, m.slot))'
          OBVIOUS
          <5>1. m \in msgs
            BY <4>0 DEF Send
          <5>2. \E Q \in Quorums, b \in Ballots : \A a_1 \in Q : VotedForIn(a_1, m.val, b, m.slot)
            BY <5>1 DEF Inv, MsgInv
          <5>3. m.val \in Values /\ m.slot \in Slots
            BY <5>1 DEF Inv, ValidMessages, ValidMessagedecision, TypeOK
          <5>4. \E Q \in Quorums, b \in Ballots : \A a_1 \in Q : VotedForIn(a_1, m.val, b, m.slot)'
            BY <5>2, <5>3, QuorumAssumption, <2>7, Phase2bVotedForInv DEF Inv
        <5> QED
          BY <5>4
      <4>5. (m.type = "2b" => VotedForIn(m.from, m.val, m.bal, m.slot))'
        <5> SUFFICES ASSUME (m.type = "2b")'
                     PROVE  VotedForIn(m.from, m.val, m.bal, m.slot)'
          OBVIOUS
          <5>0. aVoted[m.from] \subseteq aVoted'[m.from]
            BY <4>0, <3>1, m.from \in Acceptors DEF ValidMessages, ValidMessage2b, Inv, TypeOK
          <5>1. CASE m \in msgs
            BY <5>1, <4>0, <5>0 DEF Send, Inv, MsgInv, VotedForIn
          <5>2. CASE m \in msgs' \ msgs
            BY <5>2, <4>0 DEF Send, Inv, MsgInv, VotedForIn
        <5> QED BY <5>1, <5>2
        
      <4>4. QED
        BY <4>1, <4>2, <4>3, <4>5

    <3>3. AccInv'
      <4> SUFFICES ASSUME NEW a_1 \in Acceptors'
                   PROVE  (/\ \A vote \in aVoted[a_1] :
                                /\ \E m \in msgs :
                                     /\ a_1 \in m.to
                                     /\ m.type = "2a"
                                     /\ m.bal = vote.bal
                                     /\ m.slot = vote.slot
                                     /\ m.val = vote.val
                                /\ \E m \in msgs:
                                     /\ m.from = a_1
                                     /\ m.type = "2b"
                                     /\ m.bal = vote.bal
                                     /\ m.slot = vote.slot
                                     /\ m.val = vote.val
                           /\ \A c \in Ballots, s \in Slots, v \in Values :
                               GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a_1], s)) => ~ VotedForIn(a_1, v, c, s))'
        BY DEF AccInv
      <4>0. PICK m \in msgs : Phase2b(a)!(m)
        BY <2>7 DEF Phase2b
      <4>1. (\A vote \in aVoted[a_1] :
               /\ \E m2 \in msgs :
                    /\ a_1 \in m2.to
                    /\ m2.type = "2a"
                    /\ m2.bal = vote.bal
                    /\ m2.slot = vote.slot
                    /\ m2.val = vote.val
               /\ \E m2 \in msgs:
                    /\ m2.from = a_1
                    /\ m2.type = "2b"
                    /\ m2.bal = vote.bal
                    /\ m2.slot = vote.slot
                    /\ m2.val = vote.val)'
        <5>1. CASE a_1 = a
          <6>1. \A vote \in aVoted[a_1] :
                  /\ \E m2 \in msgs' :
                    /\ a_1 \in m2.to
                    /\ m2.type = "2a"
                    /\ m2.bal = vote.bal
                    /\ m2.slot = vote.slot
                    /\ m2.val = vote.val
                  /\ \E m2 \in msgs':
                    /\ m2.from = a_1
                    /\ m2.type = "2b"
                    /\ m2.bal = vote.bal
                    /\ m2.slot = vote.slot
                    /\ m2.val = vote.val
            BY <4>0, <5>1 DEF AccInv, Inv, Send, TypeOK
          <6>2. \A vote \in aVoted'[a_1] \ aVoted[a_1]:
                  /\ vote.bal = m.bal
                  /\ vote.val = m.val
                  /\ vote.slot = m.slot
            BY <4>0, <5>1 DEF AccInv, Inv, Send, TypeOK
          <6>3. \A vote \in aVoted'[a_1] \ aVoted[a_1]: \E m2 \in msgs' :
                    /\ a_1 \in m2.to
                    /\ m2.type = "2a"
                    /\ vote.bal = m2.bal
                    /\ vote.slot = m2.slot
                    /\ vote.val = m2.val
            BY <6>2, <4>0, <5>1 DEF AccInv, Inv, Send, TypeOK
          <6>4. \E m2 \in msgs' :
                    /\ m2.from = a_1
                    /\ m2.type = "2b"
                    /\ m2.bal = m.bal
                    /\ m2.slot = m.slot
                    /\ m2.val = m.val
            BY <6>2, <4>0, <5>1, [type |-> "2b", slot |-> m.slot, val |-> m.val,
                   bal |-> m.bal, from |-> a, to |-> m.from] \in msgs'
            DEF Inv, Send
          <6> QED BY <6>1, <6>2, <6>3, <6>4
        <5>2. CASE a_1 # a
          BY <4>0, <5>2 DEF AccInv, Inv, Send, TypeOK
        <5> QED BY <5>1, <5>2
      <4>21. m.bal \in Ballots
        BY <4>0 DEF Inv, TypeOK, ValidMessages, ValidMessage2a
      <4>25. m.slot \in Slots /\ m.val \in Values
        BY <4>0 DEF Inv, TypeOK, ValidMessages, ValidMessage2a
      <4>22. aBal[a] \in Ballots \cup {[num |-> -1, id |-> -1]}
        BY <4>0 DEF Inv, TypeOK
      <4>24. {aBal[a], m.bal} # {}
        BY <4>21, <4>22   
      <4>30. \A s \in Slots, a_2 \in Acceptors : MaxVotedBallotInSlot(aVoted[a_2], s) \in Ballots \cup {[num |-> -1, id |-> -1]}
        BY DEF MaxVotedBallotInSlot, MaximumBallot, Inv, TypeOK
      <4>31. \A s \in Slots, a_2 \in Acceptors : MaxVotedBallotInSlot(aVoted'[a_2], s) \in Ballots \cup {[num |-> -1, id |-> -1]}
        BY <4>0, <3>1 DEF MaxVotedBallotInSlot, MaximumBallot, Inv, TypeOK       
      <4>2. (\A c \in Ballots, s \in Slots, v \in Values :
              GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a_1], s)) => ~ VotedForIn(a_1, v, c, s))'
          <6> SUFFICES ASSUME NEW c \in Ballots', NEW s \in Slots', NEW v \in Values',
                              GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a_1], s))',
                              (VotedForIn(a_1, v, c, s))'
                       PROVE  FALSE
            OBVIOUS
            <6>3. CASE a # a_1
              <7>1. ~VotedForIn(a_1, v, c, s)
                BY <4>0, <6>3 DEF AccInv, Inv
              <7>2. VotedForIn(a_1, v, c, s)
                BY <4>0, <6>3 DEF VotedForIn
              <7> QED BY <7>1, <7>2
            <6>1. CASE a = a_1 /\ s # m.slot
              <7>1. MaxVotedBallotInSlot(aVoted'[a_1], s) = MaxVotedBallotInSlot(aVoted[a_1], s)
                BY <4>0, <6>1 DEF MaxVotedBallotInSlot
              <7>2. GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a_1], s))
                BY <7>1
              <7>3. ~ VotedForIn(a_1, v, c, s)
                BY <7>2 DEF Inv, AccInv
              <7>4. ~ VotedForIn(a_1, v, c, s)'
                BY <7>3, <6>1, <4>0 DEF VotedForIn
              <7> QED BY <7>4
            <6>2. CASE a = a_1 /\ s = m.slot
              <7>0. aVoted'[a_1] = aVoted[a_1] \cup {[bal |-> m.bal, val |-> m.val, slot |-> m.slot]}
                BY <4>0, <6>2
              <7>10. aVoted[a_1] \in SUBSET [bal : Ballots, slot : Slots, val : Values]
                BY DEF Inv, TypeOK
              <7>11. \/ MaxVotedBallotInSlot(aVoted[a_1] \cup {[bal |-> m.bal, val |-> m.val, slot |-> m.slot]}, s) = MaxVotedBallotInSlot(aVoted[a_1], s)
                     \/ MaxVotedBallotInSlot(aVoted[a_1] \cup {[bal |-> m.bal, val |-> m.val, slot |-> m.slot]}, s) = m.bal
                BY <4>21, <4>25, <7>10, <6>2, MVBISUnion
              <7>12. \/ MaxVotedBallotInSlot(aVoted'[a_1], s) = MaxVotedBallotInSlot(aVoted[a_1], s)
                     \/ MaxVotedBallotInSlot(aVoted'[a_1], s) = m.bal
                BY <7>11, <7>0
              <7>21. \A d \in aVoted'[a_1] : d.slot = s => GreaterOrEqualBallot(MaxVotedBallotInSlot(aVoted'[a_1], s), d.bal)
                BY <3>1, <6>2, MVBISNoMore, <4>31, GEBNotCommutative DEF Inv, TypeOK
              <7>22. [bal |-> m.bal, val |-> m.val, slot |-> m.slot] \in aVoted'[a]
                BY <6>2, <4>0
              <7>23. \A d \in aVoted[a_1] : d.slot = s => GreaterBallot(c, d.bal)
                BY <7>21, <7>0, <7>10, <4>31, GBTransitive2
              <7>24. GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a_1], s))
                <8>1. CASE MaxVotedBallotInSlot(aVoted[a_1], s) = [num |-> -1, id |-> -1]
                  BY <8>1 DEF GreaterBallot
                <8>2. CASE MaxVotedBallotInSlot(aVoted[a_1], s) \in Ballots
                  <9>1. PICK d \in aVoted[a_1] : d.slot = s /\ d.bal = MaxVotedBallotInSlot(aVoted[a_1], s)
                    BY <7>10, <8>2, MVBISExists
                  <9>2. GreaterBallot(c, d.bal) BY <9>1, <7>23
                  <9> QED BY <9>1, <9>2  
                <8> QED BY <8>1, <8>2, <7>10, MVBISType
              <7>6. ~ VotedForIn(a_1, v, c, s)
                BY <7>24 DEF Inv, AccInv
              <7>2. CASE GreaterBallot(m.bal, MaxVotedBallotInSlot(aVoted[a_1], s))
                  <9>1. \A d \in aVoted[a] : d.slot = s => GreaterOrEqualBallot(MaxVotedBallotInSlot(aVoted[a_1], s), d.bal)
                    BY <6>2, <4>30, GEBNotCommutative, MVBISNoMore DEF Inv, TypeOK
                  <9>2. \A d \in aVoted[a] : d.slot = s => GreaterBallot(m.bal, d.bal)
                    BY <7>2, <9>1, <4>30, <4>21, GBTransitive2 DEF TypeOK, Inv
                  <9>3. \A n \in {d.bal : d \in {d \in aVoted'[a] : d.slot = s}} \ {m.bal} : GreaterBallot(m.bal, n)
                    BY <6>2, <7>0, <9>2
                  <9>4. \A n \in {d.bal : d \in {d \in aVoted'[a] : d.slot = s}} \ {m.bal} : ~GreaterBallot(n, m.bal)
                    BY <9>3, <4>21, GBNotCommutative, <3>1 DEF Inv, TypeOK
                  <9>5. m.bal \in {d.bal : d \in {d \in aVoted'[a] : d.slot = s}}
                    BY <6>2, <7>0
                  <9>6. MaxVotedBallotInSlot(aVoted'[a_1], s) = m.bal
                    BY <6>2, <7>22, <9>5, <9>3, <9>4 DEF MaxVotedBallotInSlot, MaximumBallot
                  <9>7. ~ VotedForIn(a_1, v, c, s)'
                    BY <7>2, <9>6, GreaterBallot(c, m.bal), <4>21, GEBNotCommutative, c # m.bal,
                    <7>6, <6>2, <4>0  DEF GreaterOrEqualBallot, VotedForIn
                  <9> QED BY <9>7
              <7>3. CASE m.bal = MaxVotedBallotInSlot(aVoted[a_1], s)
                <8>1. MaxVotedBallotInSlot(aVoted'[a_1], s) = m.bal
                  BY <7>3, <7>12
                <8>2. ~ VotedForIn(a_1, v, c, s)'
                    BY <7>3, <8>1, GreaterBallot(c, m.bal), <4>21, GEBNotCommutative, c # m.bal,
                    <7>6, <6>2, <4>0  DEF GreaterOrEqualBallot, VotedForIn
                <8> QED BY <8>2
              <7>4. CASE GreaterBallot(MaxVotedBallotInSlot(aVoted[a_1], s), m.bal)
                  <9>1. MaxVotedBallotInSlot(aVoted'[a_1], s) = MaxVotedBallotInSlot(aVoted[a_1], s)
                    <10> SUFFICES ASSUME MaxVotedBallotInSlot(aVoted'[a_1], s) # MaxVotedBallotInSlot(aVoted[a_1], s)
                                  PROVE  FALSE
                         OBVIOUS
                      <10>1. MaxVotedBallotInSlot(aVoted'[a_1], s) = m.bal
                        BY <7>12
                      <10>2. \A d \in aVoted'[a_1] : d.slot = s => GreaterOrEqualBallot(m.bal, d.bal)
                        BY <10>1, <7>21
                      <10>3. CASE ~\E d \in aVoted[a_1]: d.slot = s
                        <11>1. MaxVotedBallotInSlot(aVoted[a_1], s) = [num |-> -1, id |-> -1]
                          BY <10>3 DEF MaxVotedBallotInSlot, MaximumBallot
                        <11> QED BY <4>21, <11>1, <7>4 DEF GreaterBallot
                      <10>4. CASE \E d \in aVoted[a_1]: d.slot = s
                        <11>1. MaxVotedBallotInSlot(aVoted[a_1], s) \in Ballots
                          BY <10>4, <7>10, <4>21, <4>25, MVBISNoSlot, MVBISType
                        <11>2. PICK d \in aVoted[a_1]: d.slot = s /\ d.bal = MaxVotedBallotInSlot(aVoted[a_1], s) 
                          BY <11>1, <7>10, <4>21, <4>25, MVBISExists
                        <11>3. d \in aVoted'[a_1] BY <11>2, <7>0
                        <11>4. \A d2 \in aVoted'[a_1]: d2.slot = s => ~GreaterBallot(d2.bal, MaxVotedBallotInSlot(aVoted'[a_1], s))
                          BY <4>21, <4>25, <3>1, MVBISNoMore DEF TypeOK
                        <11> QED BY <11>2, <11>3, <11>4, <10>1, <7>4
                      <10> QED BY <10>3, <10>4
                  <9>2. GreaterBallot(c, m.bal)
                    BY <9>1, GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a_1], s)), <7>4, <4>21,
                    <7>10, MVBISType, MaxVotedBallotInSlot(aVoted[a_1], s) \in Ballots \cup {[num |-> -1, id |-> -1]}, GBTransitive3
                  <9>7.~ VotedForIn(a_1, v, c, s)'
                    BY <7>4, <9>1, <9>2, <4>21, GEBNotCommutative, c # m.bal, <7>6, <6>2, <4>0  DEF GreaterOrEqualBallot, VotedForIn
                  <9> QED BY <9>7
              <7> QED BY <7>2, <7>3, <7>4, <4>21, <7>10, MVBISType, GBTotal
          <6> QED
            BY <6>1, <6>2, <6>3\* DEF AccInv, Send, Inv, TypeOK, VotedForIn
      <4>4. QED
        BY <4>1, <4>2
    <3>4. PropInv'
      <4> SUFFICES ASSUME NEW p \in Proposers'
                   PROVE  (/\ pState[p] = 1 => ~ \E m \in msgs :
                                                   /\ m.bal = pBal[p]
                                                   /\ m.type \in {"1a", "2a"}
                           /\ pState[p] = 2 => /\ \E m \in msgs : m.type = "1a" /\ m.bal = pBal[p] /\ m.to = Acceptors
                                               /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = pBal[p]
                           /\ pState[p] = 3 => /\ \E Q \in Quorums : \A a_1 \in Q : \E m \in msgs :
                                                   /\ m.type = "1b"
                                                   /\ m.from = a_1
                                                   /\ m.to = p
                                                   /\ m.bal = pBal[p]
                                               /\ \A c \in Ballots, s \in Slots :
                                                   /\ GreaterBallot(pBal[p], c)
                                                   (*/\ \E m \in msgs :
                                                     /\ m.type = "2a"
                                                     /\ m.bal = pBal[p]*)
                                                   /\ ~ \E m \in msgs :
                                                     /\ m.type = "2a"
                                                     /\ m.bal = pBal[p]
                                                     /\ m.slot = s
                                                   =>
                                                   \E Q \in Quorums : \A a_1 \in Q : WontVoteIn(a_1, c, s)
                           /\ ~ \E m \in msgs :  /\ m.type \in {"1a", "2a"}
                                                 /\ GreaterBallot(m.bal, pBal[p])
                                                 /\ m.bal.id = p
                           /\ pBal[p].id = p)'
        BY DEF PropInv
      <4>0. PICK m1 \in msgs : Phase2b(a)!(m1)
        BY <2>7 DEF Phase2b
      <4>1. (pState[p] = 1 => ~ \E m \in msgs :
                                  /\ m.bal = pBal[p]
                                  /\ m.type \in {"1a", "2a"})'
        BY <2>7, <3>1 DEF PropInv, Phase2b, Inv, TypeOK, Send, PartialBmax, MaximumBallot
      <4>2. (pState[p] = 2 => /\ \E m \in msgs : m.type = "1a" /\ m.bal = pBal[p] /\ m.to = Acceptors
                              /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = pBal[p])'
        BY <2>7, <3>1 DEF PropInv, Phase2b, Inv, TypeOK, Send, PartialBmax, MaximumBallot
      <4>3. (pState[p] = 3 => /\ \E Q \in Quorums : \A a_1 \in Q : \E m \in msgs :
                                  /\ m.type = "1b"
                                  /\ m.from = a_1
                                  /\ m.to = p
                                  /\ m.bal = pBal[p]
                              /\ \A c \in Ballots, s \in Slots :
                                  /\ GreaterBallot(pBal[p], c)
                                  /\ ~ \E m \in msgs :
                                    /\ m.type = "2a"
                                    /\ m.bal = pBal[p]
                                    /\ m.slot = s
                                  =>
                                  \E Q \in Quorums : \A a_1 \in Q : WontVoteIn(a_1, c, s))'
        <5> SUFFICES ASSUME (pState[p] = 3)'
                     PROVE  (/\ \E Q \in Quorums : \A a_1 \in Q : \E m \in msgs :
                                 /\ m.type = "1b"
                                 /\ m.from = a_1
                                 /\ m.to = p
                                 /\ m.bal = pBal[p]
                             /\ \A c \in Ballots, s \in Slots :
                                 /\ GreaterBallot(pBal[p], c)
                                 (*/\ \E m \in msgs :
                                   /\ m.type = "2a"
                                   /\ m.bal = pBal[p]*)
                                 /\ ~ \E m \in msgs :
                                   /\ m.type = "2a"
                                   /\ m.bal = pBal[p]
                                   /\ m.slot = s
                                 =>
                                 \E Q \in Quorums : \A a_1 \in Q : WontVoteIn(a_1, c, s))'
          OBVIOUS
        <5>1. (\E Q \in Quorums : \A a_1 \in Q : \E m \in msgs :
                /\ m.type = "1b"
                /\ m.from = a_1
                /\ m.to = p
                /\ m.bal = pBal[p])'
          BY <2>7, <3>1 DEF PropInv, Phase2b, Inv, TypeOK, Send, PartialBmax, MaximumBallot
        <5>2. (\A c \in Ballots, s \in Slots :
                /\ GreaterBallot(pBal[p], c)
                /\ ~ \E m \in msgs :
                  /\ m.type = "2a"
                  /\ m.bal = pBal[p]
                  /\ m.slot = s
                =>
                \E Q \in Quorums : \A a_1 \in Q : WontVoteIn(a_1, c, s))'
          <6> SUFFICES ASSUME NEW c \in Ballots', NEW s \in Slots',
                              (/\ GreaterBallot(pBal[p], c)
                               /\ ~ \E m \in msgs :
                                 /\ m.type = "2a"
                                 /\ m.bal = pBal[p]
                                 /\ m.slot = s)'
                       PROVE  (\E Q \in Quorums : \A a_1 \in Q : WontVoteIn(a_1, c, s))'
            OBVIOUS
            <6>1. \E Q \in Quorums : \A a_1 \in Q : WontVoteIn(a_1, c, s)
              BY <2>7, <3>1, <4>0, \A mm \in msgs' \ msgs : mm.type # "2a", <3>2 DEF SafeAt, PropInv, Inv, TypeOK, Send
          <6> QED
            BY <2>7, <6>1, Phase2bWontVoteIn, QuorumAssumption DEF Inv\*, TypeOK, Send
          \*, PartialBmax, MaximumBallot
        <5>3. QED
          BY <5>1, <5>2
        
      <4>4. (~ \E m \in msgs :  /\ m.type \in {"1a", "2a"}
                                /\ GreaterBallot(m.bal, pBal[p])
                                /\ m.bal.id = p)'
        BY <2>7, <3>1 DEF PropInv, Phase2b, Inv, TypeOK, Send, PartialBmax, MaximumBallot
      <4>5. (pBal[p].id = p)'
        BY <2>7, <3>1 DEF PropInv, Phase2b, Inv, TypeOK, Send, PartialBmax, MaximumBallot
      <4>6. QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5
      
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Inv

  <2>8. CASE UNCHANGED vars
    <3>1. TypeOK'
      BY <2>8, QuorumAssumption, SystemAssumptions DEF TypeOK, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot, PartialBmax, MaximumBallot, MaxVotedBallotInSlot, vars
    <3>2. MsgInv'
      <4> SUFFICES ASSUME NEW m \in msgs'
                   PROVE  (/\ (m.type = "1b") =>
                               /\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                     /\ \E mm \in msgs :
                                                          /\ m.from \in mm.to
                                                          /\ mm.type = "2a"
                                                          /\ mm.bal = r.bal
                                                          /\ mm.slot = r.slot
                                                          /\ mm.val = r.val
                               /\ \A v \in Values, s \in Slots, b \in Ballots :
                                     GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                       => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                               /\ \A s \in Slots, v \in Values, c \in Ballots :
                                   (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                       ~ VotedForIn(m.from, v, c, s)
                               /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                               /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                   (\A v \in Values, c \in Ballots :
                                                     GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s))
                           /\ (m.type = "2a") => 
                               /\ SafeAt(m.val, m.bal, m.slot)
                               /\ Proposed(m.val, m.slot)
                               /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val
                           /\ (m.type = "2b") => VotedForIn(m.from, m.val, m.bal, m.slot)
                           /\ (m.type = "decision") =>
                               \E Q \in Quorums, b \in Ballots : \A a \in Q : VotedForIn(a, m.val, b, m.slot))'
        BY DEF MsgInv
      <4>1. ((m.type = "1b") =>
              /\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                    /\ \E mm \in msgs :
                                         /\ m.from \in mm.to
                                         /\ mm.type = "2a"
                                         /\ mm.bal = r.bal
                                         /\ mm.slot = r.slot
                                         /\ mm.val = r.val
              /\ \A v \in Values, s \in Slots, b \in Ballots :
                    GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                      => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
              /\ \A s \in Slots, v \in Values, c \in Ballots :
                  (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                      ~ VotedForIn(m.from, v, c, s)
              /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
              /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                  (\A v \in Values, c \in Ballots :
                                    GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
        <5> SUFFICES ASSUME (m.type = "1b")'
                     PROVE  (/\ \A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                                   /\ \E mm \in msgs :
                                                        /\ m.from \in mm.to
                                                        /\ mm.type = "2a"
                                                        /\ mm.bal = r.bal
                                                        /\ mm.slot = r.slot
                                                        /\ mm.val = r.val
                             /\ \A v \in Values, s \in Slots, b \in Ballots :
                                   GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                                     => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                             /\ \A s \in Slots, v \in Values, c \in Ballots :
                                 (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                                     ~ VotedForIn(m.from, v, c, s)
                             /\ GreaterOrEqualBallot(aBal[m.from], m.bal)
                             /\ \A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                                 (\A v \in Values, c \in Ballots :
                                                   GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
          OBVIOUS
        <5>1. (\A r \in m.voted : /\ VotedForIn(m.from, r.val, r.bal, r.slot)
                                  /\ \E mm \in msgs :
                                       /\ m.from \in mm.to
                                       /\ mm.type = "2a"
                                       /\ mm.bal = r.bal
                                       /\ mm.slot = r.slot
                                       /\ mm.val = r.val)'
          BY <2>8, QuorumAssumption, SystemAssumptions
          DEF MsgInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, vars, VotedForIn, GreaterOrEqualBallot
        <5>2. (\A v \in Values, s \in Slots, b \in Ballots :
                  GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s)
                    => \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)'
          <6> SUFFICES ASSUME NEW v \in Values', NEW s \in Slots', NEW b \in Ballots',
                              (GreaterBallot(m.bal, b) /\ VotedForIn(m.from, v, b, s))'
                       PROVE  (\E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)'
            OBVIOUS
            <6>1. GreaterBallot(m.bal, b)
              BY <2>8 DEF MsgInv, Inv, VotedForIn, vars, MaxVotedBallotInSlot, MaximumBallot, GreaterBallot
            <6>2. VotedForIn(m.from, v, b, s)
              BY <2>8 DEF MsgInv, Inv, VotedForIn, vars, MaxVotedBallotInSlot, MaximumBallot, GreaterBallot
            <6>3. \E r \in m.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
              BY <6>1, <6>2, <2>8 DEF MsgInv, Inv, vars
          <6> QED
            BY <2>8, <6>3 DEF  vars
          \*, GreaterOrEqualBallot, GreaterBallot
        <5>3. (\A s \in Slots, v \in Values, c \in Ballots :
                (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))) =>
                    ~ VotedForIn(m.from, v, c, s))'
          <6> SUFFICES ASSUME NEW s \in Slots', NEW v \in Values', NEW c \in Ballots',
                              (GreaterBallot(m.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s)))'
                       PROVE  (~ VotedForIn(m.from, v, c, s))'
            OBVIOUS
            <6>1. GreaterBallot(m.bal, c)
              BY <2>8 DEF MsgInv, Inv, VotedForIn, vars, MaxVotedBallotInSlot, MaximumBallot, GreaterBallot
            <6>2. GreaterBallot(c, MaxVotedBallotInSlot(m.voted, s))
              BY <2>8 DEF MsgInv, Inv, VotedForIn, vars, MaxVotedBallotInSlot, MaximumBallot, GreaterBallot
            <6>3. (~ VotedForIn(m.from, v, c, s))
              BY <6>1, <6>2, <2>8 DEF MsgInv, Inv, vars
          <6> QED
            BY <2>8, <6>3 DEF  vars, VotedForIn
          
        <5>4. GreaterOrEqualBallot(aBal[m.from], m.bal)'
          BY <2>8, QuorumAssumption, SystemAssumptions
          DEF MsgInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, vars, VotedForIn, GreaterOrEqualBallot
        <5>5. (\A s \in Slots : (~ \E vote \in m.voted : vote.slot = s) => 
                                (\A v \in Values, c \in Ballots :
                                  GreaterBallot(m.bal, c) => ~ VotedForIn(m.from, v, c, s)))'
          BY <2>8, QuorumAssumption, SystemAssumptions
          DEF MsgInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, vars, VotedForIn, GreaterOrEqualBallot
        <5>6. QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5
        
      <4>2. ((m.type = "2a") => 
              /\ SafeAt(m.val, m.bal, m.slot)
              /\ Proposed(m.val, m.slot)
              /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
        <5> SUFFICES ASSUME (m.type = "2a")'
                     PROVE  (/\ SafeAt(m.val, m.bal, m.slot)
                             /\ Proposed(m.val, m.slot)
                             /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
          OBVIOUS
        <5>1. SafeAt(m.val, m.bal, m.slot)'
          BY <2>8, QuorumAssumption, SystemAssumptions
          DEF Proposed, MsgInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, vars
        <5>2. Proposed(m.val, m.slot)'
          BY <2>8, QuorumAssumption, SystemAssumptions
          DEF Proposed, MsgInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, vars
        <5>3. (\A mm \in msgs : (mm.type = "2a" /\ mm.bal = m.bal /\ mm.slot = m.slot) => mm.val = m.val)'
          BY <2>8, QuorumAssumption, SystemAssumptions
          DEF Proposed, MsgInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, vars
        <5>4. QED
          BY <5>1, <5>2, <5>3
      <4>3. ((m.type = "2b") => VotedForIn(m.from, m.val, m.bal, m.slot))'
        BY <2>8, QuorumAssumption, SystemAssumptions
        DEF MsgInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, vars
      <4>4. ((m.type = "decision") =>
              \E Q \in Quorums, b \in Ballots : \A a \in Q : VotedForIn(a, m.val, b, m.slot))'
        BY <2>8, QuorumAssumption, SystemAssumptions
        DEF MsgInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, vars
      <4>5. QED
        BY <4>1, <4>2, <4>3, <4>4
      
    <3>3. AccInv'
      <4> SUFFICES ASSUME NEW a \in Acceptors'
                   PROVE  (/\ \A vote \in aVoted[a] :
                             /\ \E m \in msgs :
                                  /\ a \in m.to
                                  /\ m.type = "2a"
                                  /\ m.bal = vote.bal
                                  /\ m.slot = vote.slot
                                  /\ m.val = vote.val
                             /\ \E m \in msgs :
                                  /\ m.from = a
                                  /\ m.type = "2b"
                                  /\ m.bal = vote.bal
                                  /\ m.slot = vote.slot
                                  /\ m.val = vote.val
                           /\ \A c \in Ballots, s \in Slots, v \in Values :
                               GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a], s)) => ~ VotedForIn(a, v, c, s))'
        BY DEF AccInv
      <4>2. (\A vote \in aVoted[a] :
               /\ \E m \in msgs :
                    /\ a \in m.to
                    /\ m.type = "2a"
                    /\ m.bal = vote.bal
                    /\ m.slot = vote.slot
                    /\ m.val = vote.val
               /\ \E m \in msgs :
                    /\ m.from = a
                    /\ m.type = "2b"
                    /\ m.bal = vote.bal
                    /\ m.slot = vote.slot
                    /\ m.val = vote.val)'
        BY <2>8, QuorumAssumption, SystemAssumptions DEF AccInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, vars
      <4>3. (\A c \in Ballots, s \in Slots, v \in Values :
              GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a], s)) => ~ VotedForIn(a, v, c, s))'
        <5> SUFFICES ASSUME NEW c \in Ballots', NEW s \in Slots', NEW v \in Values',
                            GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a], s))'
                     PROVE  (~ VotedForIn(a, v, c, s))'
          OBVIOUS
          <5>1. GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a], s))
            BY <2>8 DEF AccInv, Inv, VotedForIn, WontVoteIn, vars
          <5>2. (~ VotedForIn(a, v, c, s))
            BY <2>8 DEF AccInv, Inv, WontVoteIn, vars
        <5> QED
          BY <2>8, <5>2 DEF vars, VotedForIn
      <4>6. QED
        BY <4>2, <4>3
      
    <3>4. PropInv'
      BY <2>8, QuorumAssumption, SystemAssumptions DEF PropInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot, PartialBmax, MaximumBallot, MaxVotedBallotInSlot, vars
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Inv
  
  <2>9. ASSUME NEW a \in Acceptors,
               PhasePr(a)
        PROVE  Inv'
    <3>1. TypeOK'
      <4>1. (ValidMessages(msgs))'
        <5> SUFFICES ASSUME NEW m \in msgs'
                     PROVE  (/\ m.type \in {"1a", "1b", "2a", "2b", "decision", "propose", "preempt"}
                             /\ m.type = "1a" => ValidMessage1a(m)
                             /\ m.type = "1b" => ValidMessage1b(m)
                             /\ m.type = "2a" => ValidMessage2a(m)
                             /\ m.type = "2b" => ValidMessage2b(m)
                             /\ m.type = "decision" => ValidMessagedecision(m)
                             /\ m.type = "preempt" => ValidMessagepreempt(m)
                             /\ m.type = "propose"  => ValidMessagepropose(m))'
          BY DEF ValidMessages
        <5>1. (m.type \in {"1a", "1b", "2a", "2b", "decision", "propose", "preempt"})'
          BY <2>9 DEF PhasePr, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      MaximumBallot, Bmax, PartialBmax, GreaterBallot,
                      MaxVotedBallotInSlot
        <5>2. (m.type = "1a" => ValidMessage1a(m))'
          BY <2>9 DEF PhasePr, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      MaximumBallot, Bmax, PartialBmax, GreaterBallot,
                      MaxVotedBallotInSlot
        <5>3. (m.type = "1b" => ValidMessage1b(m))'
          BY <2>9 DEF PhasePr, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      MaximumBallot, Bmax, PartialBmax, GreaterBallot,
                      MaxVotedBallotInSlot
        <5>4. (m.type = "2a" => ValidMessage2a(m))'
          BY <2>9 DEF PhasePr, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      MaximumBallot, Bmax, PartialBmax, GreaterBallot,
                      MaxVotedBallotInSlot
        <5>5. (m.type = "2b" => ValidMessage2b(m))'
          BY <2>9 DEF PhasePr, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      MaximumBallot, Bmax, PartialBmax, GreaterBallot,
                      MaxVotedBallotInSlot
        <5>6. (m.type = "decision" => ValidMessagedecision(m))'
          BY <2>9 DEF PhasePr, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      MaximumBallot, Bmax, PartialBmax, GreaterBallot,
                      MaxVotedBallotInSlot
        <5>7. (m.type = "propose"  => ValidMessagepropose(m))'
          BY <2>9 DEF PhasePr, TypeOK, Send, Inv, ValidMessages, ValidMessage1a, ValidMessage1b,
                      ValidMessage2a, ValidMessage2b, ValidMessagedecision, ValidMessagepropose,
                      MaximumBallot, Bmax, PartialBmax, GreaterBallot,
                      MaxVotedBallotInSlot
        <5>9. (m.type = "preempt" => ValidMessagepreempt(m))'
            <7> SUFFICES ASSUME (m.type = "preempt")'
                         PROVE  ValidMessagepreempt(m)'
              OBVIOUS
            <7>0. PICK m_1 \in msgs : PhasePr(a)!(m_1)
              BY <2>9 DEF PhasePr
            <7>1. CASE m \in msgs
              BY <7>1, <2>9 DEF PhasePr, TypeOK, Send, Inv, ValidMessages, ValidMessagepreempt
            <7>2. CASE m \in msgs' \ msgs
              BY <7>0, m_1.from \in Proposers
              DEF TypeOK, Send, Inv, ValidMessagepreempt, ValidMessage1a, ValidMessage2a, ValidMessages
            <7> QED BY <7>1, <7>2

        <5>8. QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>9
        
      <4>2. (pBal \in [Proposers -> Ballots])'
        BY <2>9 DEF PhasePr, TypeOK, Sends, Inv
      <4>3. (pState \in [Proposers -> {1, 2, 3}])'
        BY <2>9 DEF PhasePr, TypeOK, Sends, Inv
      <4>4. (\A a_1 \in Acceptors : /\ aVoted[a_1] \subseteq [bal : Ballots, slot : Slots, val : Values]
                                    /\ aBal[a_1] \in Ballots \cup {[num |-> -1, id |-> -1]})'
        <5> SUFFICES ASSUME NEW a_1 \in Acceptors'
                     PROVE  (/\ aVoted[a_1] \subseteq [bal : Ballots, slot : Slots, val : Values]
                             /\ aBal[a_1] \in Ballots \cup {[num |-> -1, id |-> -1]})'
          OBVIOUS
        <5>16. \A mm \in msgs' \ msgs : mm.type \in {"2b", "preempt"}
          BY <2>9 DEF PhasePr, Send, MaximumBallot
        <5>0. PICK m_1 \in msgs : PhasePr(a)!(m_1)
          BY <2>9 DEF PhasePr
        <5>21. m_1.bal \in Ballots
          BY <5>0 DEF Inv, TypeOK, ValidMessages, ValidMessage2a, ValidMessage1a
        <5>22. aBal[a] \in Ballots \cup {[num |-> -1, id |-> -1]}
          BY <5>0 DEF Inv, TypeOK
        <5>23. MaximumBallot({aBal[a], m_1.bal}) \in Ballots
          <7>1. CASE aBal[a] = [num |-> -1, id |-> -1]
            BY SystemAssumptions, <7>1, <5>21, GreaterBallot(m_1.bal, aBal[a]) DEF MaximumBallot, GreaterBallot
          <7>2. CASE aBal[a] # [num |-> -1, id |-> -1]
            BY SystemAssumptions, <7>2, <5>21, <5>22, MBType
          <7> QED BY <7>1, <7>2
        <5>1. (aVoted[a_1] \subseteq [bal : Ballots, slot : Slots, val : Values])'
          BY <2>9, <5>0 DEF Inv, PhasePr, TypeOK, ValidMessages, ValidMessage1a, ValidMessage2a, MaximumBallot
        <5>2. (aBal[a_1] \in Ballots \cup {[num |-> -1, id |-> -1]})'
          BY <2>9, <5>23, <5>0 DEF Inv, TypeOK, ValidMessages, ValidMessage1a, ValidMessage2a\*, MaximumBallot, SeenBallots
        <5>4. QED
          BY <5>1, <5>2
        
          
      <4>5. QED
        BY <4>1, <4>2, <4>3, <4>4 DEF TypeOK
    <3>0. PICK m \in msgs: PhasePr(a)!(m) BY <2>9 DEF PhasePr
    <3>2. MsgInv'
      <4> SUFFICES ASSUME NEW m_1 \in msgs'
                   PROVE  (/\ (m_1.type = "1b") =>
                               /\ \A r \in m_1.voted : /\ VotedForIn(m_1.from, r.val, r.bal, r.slot)
                                                       /\ \E mm \in msgs :
                                                          /\ m_1.from \in mm.to
                                                          /\ mm.type = "2a"
                                                          /\ mm.bal = r.bal
                                                          /\ mm.slot = r.slot
                                                          /\ mm.val = r.val
                               /\ \A v \in Values, s \in Slots, b \in Ballots :
                                     GreaterBallot(m_1.bal, b) /\ VotedForIn(m_1.from, v, b, s)
                                       => \E r \in m_1.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                               /\ \A s \in Slots, v \in Values, c \in Ballots :
                                   (GreaterBallot(m_1.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m_1.voted, s))) =>
                                       ~ VotedForIn(m_1.from, v, c, s)
                               /\ GreaterOrEqualBallot(aBal[m_1.from], m_1.bal)
                               /\ \A s \in Slots : (~ \E vote \in m_1.voted : vote.slot = s) => 
                                                   (\A v \in Values, c \in Ballots :
                                                     GreaterBallot(m_1.bal, c) => ~ VotedForIn(m_1.from, v, c, s))
                           /\ (m_1.type = "2a") => 
                               /\ SafeAt(m_1.val, m_1.bal, m_1.slot)
                               /\ Proposed(m_1.val, m_1.slot)
                               /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m_1.bal /\ mm.slot = m_1.slot) => mm.val = m_1.val
                           /\ (m_1.type = "2b") => VotedForIn(m_1.from, m_1.val, m_1.bal, m_1.slot)
                           /\ (m_1.type = "decision") =>
                               \E Q \in Quorums, b \in Ballots : \A a_1 \in Q : VotedForIn(a_1, m_1.val, b, m_1.slot))'
        BY DEF MsgInv
      <4>1. ((m_1.type = "1b") =>
              /\ \A r \in m_1.voted : /\ VotedForIn(m_1.from, r.val, r.bal, r.slot)
                                      /\ \E mm \in msgs :
                                         /\ m_1.from \in mm.to
                                         /\ mm.type = "2a"
                                         /\ mm.bal = r.bal
                                         /\ mm.slot = r.slot
                                         /\ mm.val = r.val
              /\ \A v \in Values, s \in Slots, b \in Ballots :
                    GreaterBallot(m_1.bal, b) /\ VotedForIn(m_1.from, v, b, s)
                      => \E r \in m_1.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
              /\ \A s \in Slots, v \in Values, c \in Ballots :
                  (GreaterBallot(m_1.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m_1.voted, s))) =>
                      ~ VotedForIn(m_1.from, v, c, s)
              /\ GreaterOrEqualBallot(aBal[m_1.from], m_1.bal)
              /\ \A s \in Slots : (~ \E vote \in m_1.voted : vote.slot = s) => 
                                  (\A v \in Values, c \in Ballots :
                                    GreaterBallot(m_1.bal, c) => ~ VotedForIn(m_1.from, v, c, s)))'
        <5> SUFFICES ASSUME (m_1.type = "1b")'
                     PROVE  (/\ \A r \in m_1.voted : /\ VotedForIn(m_1.from, r.val, r.bal, r.slot)
                                                     /\ \E mm \in msgs :
                                                        /\ m_1.from \in mm.to
                                                        /\ mm.type = "2a"
                                                        /\ mm.bal = r.bal
                                                        /\ mm.slot = r.slot
                                                        /\ mm.val = r.val
                             /\ \A v \in Values, s \in Slots, b \in Ballots :
                                   GreaterBallot(m_1.bal, b) /\ VotedForIn(m_1.from, v, b, s)
                                     => \E r \in m_1.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
                             /\ \A s \in Slots, v \in Values, c \in Ballots :
                                 (GreaterBallot(m_1.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m_1.voted, s))) =>
                                     ~ VotedForIn(m_1.from, v, c, s)
                             /\ GreaterOrEqualBallot(aBal[m_1.from], m_1.bal)
                             /\ \A s \in Slots : (~ \E vote \in m_1.voted : vote.slot = s) => 
                                                 (\A v \in Values, c \in Ballots :
                                                   GreaterBallot(m_1.bal, c) => ~ VotedForIn(m_1.from, v, c, s)))'
          OBVIOUS
        <5>1. (\A r \in m_1.voted : /\ VotedForIn(m_1.from, r.val, r.bal, r.slot)
                                    /\ \E mm \in msgs :
                                       /\ m_1.from \in mm.to
                                       /\ mm.type = "2a"
                                       /\ mm.bal = r.bal
                                       /\ mm.slot = r.slot
                                       /\ mm.val = r.val)'
          BY <3>0, QuorumAssumption, SystemAssumptions, \A mm \in msgs' \ msgs: mm.type = "preempt"
          DEF MsgInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, vars, VotedForIn, GreaterOrEqualBallot
        <5>2. (\A v \in Values, s \in Slots, b \in Ballots :
                  GreaterBallot(m_1.bal, b) /\ VotedForIn(m_1.from, v, b, s)
                    => \E r \in m_1.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)'
          <6> SUFFICES ASSUME NEW v \in Values', NEW s \in Slots', NEW b \in Ballots',
                              (GreaterBallot(m_1.bal, b) /\ VotedForIn(m_1.from, v, b, s))'
                       PROVE  (\E r \in m_1.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s)'
            OBVIOUS
            <6>1. GreaterBallot(m_1.bal, b)
              BY <2>9 DEF PhasePr, MsgInv, Inv, VotedForIn, vars, MaxVotedBallotInSlot, MaximumBallot, GreaterBallot
            <6>2. VotedForIn(m_1.from, v, b, s)
              BY <2>9 DEF PhasePr, MsgInv, Inv, VotedForIn, vars, MaxVotedBallotInSlot, MaximumBallot, GreaterBallot
            <6>3. \E r \in m_1.voted : GreaterOrEqualBallot(r.bal, b) /\ r.slot = s
              BY <6>1, <6>2, <2>9 DEF PhasePr, Send, MsgInv, Inv
          <6> QED BY <2>9, <6>3 DEF  vars
        <5>3. (\A s \in Slots, v \in Values, c \in Ballots :
                (GreaterBallot(m_1.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m_1.voted, s))) =>
                    ~ VotedForIn(m_1.from, v, c, s))'
          <6> SUFFICES ASSUME NEW s \in Slots', NEW v \in Values', NEW c \in Ballots',
                              (GreaterBallot(m_1.bal, c) /\ GreaterBallot(c, MaxVotedBallotInSlot(m_1.voted, s)))'
                       PROVE  (~ VotedForIn(m_1.from, v, c, s))'
            OBVIOUS
            <6>1. GreaterBallot(m_1.bal, c)
              BY <2>9 DEF MsgInv, Inv, VotedForIn, vars, MaxVotedBallotInSlot, MaximumBallot, GreaterBallot
            <6>2. GreaterBallot(c, MaxVotedBallotInSlot(m_1.voted, s))
              BY <2>9 DEF MsgInv, Inv, VotedForIn, vars, MaxVotedBallotInSlot, MaximumBallot, GreaterBallot
            <6>3. (~ VotedForIn(m_1.from, v, c, s))
              BY <6>1, <6>2, <2>9 DEF PhasePr, Send, MsgInv, Inv, vars
          <6> QED
            BY <2>9, <6>3 DEF PhasePr, vars, VotedForIn
        <5>4. GreaterOrEqualBallot(aBal[m_1.from], m_1.bal)'
          BY <3>0, QuorumAssumption, SystemAssumptions, \A mm \in msgs' \ msgs: mm.type = "preempt"
          DEF MsgInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, vars, VotedForIn, GreaterOrEqualBallot
        <5>5. (\A s \in Slots : (~ \E vote \in m_1.voted : vote.slot = s) => 
                                (\A v \in Values, c \in Ballots :
                                  GreaterBallot(m_1.bal, c) => ~ VotedForIn(m_1.from, v, c, s)))'
          BY <3>0, QuorumAssumption, SystemAssumptions, \A mm \in msgs' \ msgs: mm.type = "preempt"
          DEF MsgInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, vars, VotedForIn, GreaterOrEqualBallot
        <5>6. QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5
        
      <4>2. ((m_1.type = "2a") => 
              /\ SafeAt(m_1.val, m_1.bal, m_1.slot)
              /\ Proposed(m_1.val, m_1.slot)
              /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m_1.bal /\ mm.slot = m_1.slot) => mm.val = m_1.val)'
        <5> SUFFICES ASSUME (m_1.type = "2a")'
                     PROVE  (/\ SafeAt(m_1.val, m_1.bal, m_1.slot)
                             /\ Proposed(m_1.val, m_1.slot)
                             /\ \A mm \in msgs : (mm.type = "2a" /\ mm.bal = m_1.bal /\ mm.slot = m_1.slot) => mm.val = m_1.val)'
          OBVIOUS
        <5>1. SafeAt(m_1.val, m_1.bal, m_1.slot)'
          BY <3>0, QuorumAssumption, SystemAssumptions, \A mm \in msgs' \ msgs: mm.type = "preempt"
          DEF MsgInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, vars, VotedForIn, GreaterOrEqualBallot
        <5>2. Proposed(m_1.val, m_1.slot)'
          BY <2>9, QuorumAssumption, SystemAssumptions
          DEF PhasePr, Proposed, MsgInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, vars
        <5>3. (\A mm \in msgs : (mm.type = "2a" /\ mm.bal = m_1.bal /\ mm.slot = m_1.slot) => mm.val = m_1.val)'
          BY <3>0, QuorumAssumption, SystemAssumptions, \A mm \in msgs' \ msgs: mm.type = "preempt"
          DEF MsgInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, vars, VotedForIn, GreaterOrEqualBallot
        <5>4. QED
          BY <5>1, <5>2, <5>3
        
      <4>3. ((m_1.type = "2b") => VotedForIn(m_1.from, m_1.val, m_1.bal, m_1.slot))'
        BY <3>0, QuorumAssumption, SystemAssumptions, \A mm \in msgs' \ msgs: mm.type = "preempt"
        DEF MsgInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, vars, VotedForIn, GreaterOrEqualBallot
      <4>4. ((m_1.type = "decision") =>
              \E Q \in Quorums, b \in Ballots : \A a_1 \in Q : VotedForIn(a_1, m_1.val, b, m_1.slot))'
        BY <3>0, QuorumAssumption, SystemAssumptions, \A mm \in msgs' \ msgs: mm.type = "preempt"
        DEF MsgInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, vars, VotedForIn, GreaterOrEqualBallot
      <4>5. QED
        BY <4>1, <4>2, <4>3, <4>4
      
    <3>3. AccInv'
      <4> SUFFICES ASSUME NEW a_1 \in Acceptors'
                   PROVE  (/\ \A vote \in aVoted[a_1] :
                                /\ \E m_1 \in msgs :
                                     /\ a_1 \in m_1.to
                                     /\ m_1.type = "2a"
                                     /\ m_1.bal = vote.bal
                                     /\ m_1.slot = vote.slot
                                     /\ m_1.val = vote.val
                                /\ \E m_1 \in msgs:
                                     /\ m_1.from = a_1
                                     /\ m_1.type = "2b"
                                     /\ m_1.bal = vote.bal
                                     /\ m_1.slot = vote.slot
                                     /\ m_1.val = vote.val
                           /\ \A c \in Ballots, s \in Slots, v \in Values :
                               GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a_1], s)) => ~ VotedForIn(a_1, v, c, s))'
        BY DEF AccInv
      <4>1. (\A vote \in aVoted[a_1] :
               /\ \E m_1 \in msgs :
                    /\ a_1 \in m_1.to
                    /\ m_1.type = "2a"
                    /\ m_1.bal = vote.bal
                    /\ m_1.slot = vote.slot
                    /\ m_1.val = vote.val
               /\ \E m_1 \in msgs:
                    /\ m_1.from = a_1
                    /\ m_1.type = "2b"
                    /\ m_1.bal = vote.bal
                    /\ m_1.slot = vote.slot
                    /\ m_1.val = vote.val)'
        BY <3>0 DEF Send, Inv, AccInv
      <4>2. (\A c \in Ballots, s \in Slots, v \in Values :
              GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a_1], s)) => ~ VotedForIn(a_1, v, c, s))'
        <5> SUFFICES ASSUME NEW c \in Ballots', NEW s \in Slots', NEW v \in Values',
                            GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a_1], s))'
                     PROVE  (~ VotedForIn(a_1, v, c, s))'
          OBVIOUS
          <5>1. GreaterBallot(c, MaxVotedBallotInSlot(aVoted[a_1], s))
            BY <3>0
          <5>2. (~ VotedForIn(a_1, v, c, s))
            BY <5>1 DEF AccInv, Inv
        <5> QED BY <5>2, <3>0 DEF VotedForIn
      <4>3. QED
        BY <4>1, <4>2
    <3>4. PropInv'
      <4> SUFFICES ASSUME NEW p \in Proposers'
                   PROVE  (/\ pState[p] = 1 => ~ \E m_1 \in msgs :
                                                   /\ m_1.bal = pBal[p]
                                                   /\ m_1.type \in {"1a", "2a"}
                           /\ pState[p] = 2 => /\ \E m_1 \in msgs : m_1.type = "1a" /\ m_1.bal = pBal[p] /\ m_1.to = Acceptors
                                               /\ ~ \E m_1 \in msgs : m_1.type = "2a" /\ m_1.bal = pBal[p]
                           /\ pState[p] = 3 => /\ \E Q \in Quorums : \A a_1 \in Q : \E m_1 \in msgs :
                                                   /\ m_1.type = "1b"
                                                   /\ m_1.from = a_1
                                                   /\ m_1.to = p
                                                   /\ m_1.bal = pBal[p]
                                               /\ \A c \in Ballots, s \in Slots :
                                                   /\ GreaterBallot(pBal[p], c)
                                                   /\ ~ \E m_1 \in msgs :
                                                     /\ m_1.type = "2a"
                                                     /\ m_1.bal = pBal[p]
                                                     /\ m_1.slot = s
                                                   =>
                                                   \E Q \in Quorums : \A a_1 \in Q : WontVoteIn(a_1, c, s)
                           /\ ~ \E m_1 \in msgs :  /\ m_1.type \in {"1a", "2a"}
                                                   /\ GreaterBallot(m_1.bal, pBal[p])
                                                 /\ m_1.bal.id = p
                           /\ pBal[p].id = p)'
        BY DEF PropInv
      <4>1. (pState[p] = 1 => ~ \E m_1 \in msgs :
                                  /\ m_1.bal = pBal[p]
                                  /\ m_1.type \in {"1a", "2a"})'
        BY <3>0, QuorumAssumption, SystemAssumptions DEF PropInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot, PartialBmax, MaximumBallot, MaxVotedBallotInSlot, vars
      <4>2. (pState[p] = 2 => /\ \E m_1 \in msgs : m_1.type = "1a" /\ m_1.bal = pBal[p] /\ m_1.to = Acceptors
                              /\ ~ \E m_1 \in msgs : m_1.type = "2a" /\ m_1.bal = pBal[p])'
        BY <3>0, QuorumAssumption, SystemAssumptions DEF PropInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot, PartialBmax, MaximumBallot, MaxVotedBallotInSlot, vars
      <4>3. (pState[p] = 3 => /\ \E Q \in Quorums : \A a_1 \in Q : \E m_1 \in msgs :
                                  /\ m_1.type = "1b"
                                  /\ m_1.from = a_1
                                  /\ m_1.to = p
                                  /\ m_1.bal = pBal[p]
                              /\ \A c \in Ballots, s \in Slots :
                                  /\ GreaterBallot(pBal[p], c)
                                  /\ ~ \E m_1 \in msgs :
                                    /\ m_1.type = "2a"
                                    /\ m_1.bal = pBal[p]
                                    /\ m_1.slot = s
                                  =>
                                  \E Q \in Quorums : \A a_1 \in Q : WontVoteIn(a_1, c, s))'
        <5> SUFFICES ASSUME (pState[p] = 3)'
                     PROVE  (/\ \E Q \in Quorums : \A a_1 \in Q : \E m_1 \in msgs :
                                 /\ m_1.type = "1b"
                                 /\ m_1.from = a_1
                                 /\ m_1.to = p
                                 /\ m_1.bal = pBal[p]
                             /\ \A c \in Ballots, s \in Slots :
                                 /\ GreaterBallot(pBal[p], c)
                                 /\ ~ \E m_1 \in msgs :
                                   /\ m_1.type = "2a"
                                   /\ m_1.bal = pBal[p]
                                   /\ m_1.slot = s
                                 =>
                                 \E Q \in Quorums : \A a_1 \in Q : WontVoteIn(a_1, c, s))'
          OBVIOUS
        <5>1. (\E Q \in Quorums : \A a_1 \in Q : \E m_1 \in msgs :
                /\ m_1.type = "1b"
                /\ m_1.from = a_1
                /\ m_1.to = p
                /\ m_1.bal = pBal[p])'
          BY <3>0, QuorumAssumption, SystemAssumptions DEF PropInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot, PartialBmax, MaximumBallot, MaxVotedBallotInSlot, vars
        <5>2. (\A c \in Ballots, s \in Slots :
                /\ GreaterBallot(pBal[p], c)
                /\ ~ \E m_1 \in msgs :
                  /\ m_1.type = "2a"
                  /\ m_1.bal = pBal[p]
                  /\ m_1.slot = s
                =>
                \E Q \in Quorums : \A a_1 \in Q : WontVoteIn(a_1, c, s))'
          <6> SUFFICES ASSUME NEW c \in Ballots', NEW s \in Slots',
                              (/\ GreaterBallot(pBal[p], c)
                               /\ ~ \E m_1 \in msgs :
                                 /\ m_1.type = "2a"
                                 /\ m_1.bal = pBal[p]
                                 /\ m_1.slot = s)'
                       PROVE  (\E Q \in Quorums : \A a_1 \in Q : WontVoteIn(a_1, c, s))'
            OBVIOUS
          <6>1. \E Q \in Quorums : \A a_1 \in Q : WontVoteIn(a_1, c, s)
            BY <3>0, SystemAssumptions DEF PropInv, Inv, Send
          <6> QED BY <6>1, QuorumAssumption, <3>0 DEF Send, WontVoteIn, VotedForIn
        <5>3. QED
          BY <5>1, <5>2
        
      <4>4. (~ \E m_1 \in msgs :  /\ m_1.type \in {"1a", "2a"}
                                  /\ GreaterBallot(m_1.bal, pBal[p])
                                /\ m_1.bal.id = p)'
        BY <3>0, QuorumAssumption, SystemAssumptions DEF PropInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot, PartialBmax, MaximumBallot, MaxVotedBallotInSlot, vars
      <4>5. (pBal[p].id = p)'
        BY <3>0, QuorumAssumption, SystemAssumptions DEF PropInv, Inv, Send, SafeAt, VotedForIn, WontVoteIn, GreaterBallot, PartialBmax, MaximumBallot, MaxVotedBallotInSlot, vars
      <4>6. QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5
      
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Inv
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Next
<1> QED BY <1>1, <1>2, PTL DEF Spec

THEOREM Consistent == Spec => []Consistency
<1>1. Inv => Consistency
  <2> SUFFICES ASSUME Inv,
                      NEW v1 \in Values, NEW v2 \in Values, NEW s \in Slots,
                      NEW m \in msgs,
                      /\ m.type = "decision"
                      /\ m.slot = s
                      /\ m.val = v1,
                      NEW m_1 \in msgs,
                      /\ m_1.type = "decision"
                      /\ m_1.slot = s
                      /\ m_1.val = v2
               PROVE  v1 = v2
    BY DEF Chosen, Consistency
  <2>1. PICK b1 \in Ballots : \E Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1, s)
    BY DEF MsgInv, Inv, SafeAt
  <2>2. PICK b2 \in Ballots : \E Q2 \in Quorums : \A a \in Q2 : VotedForIn(a, v2, b2, s)
    BY DEF MsgInv, Inv, SafeAt
  <2>3. CASE b1 = b2
    <3>1. \E a \in Acceptors : VotedForIn(a, v1, b1, s) /\ VotedForIn(a, v2, b1, s)
      BY <2>1, <2>2, QuorumAssumption, <2>3
    <3> QED 
    BY <3>1, VotedOnce DEF Inv
  <2>4. CASE GreaterBallot(b2, b1)
    <3>1. SafeAt(v2, b2, s)
      BY VotedInv, QuorumNonEmpty, QuorumAssumption, <2>2 DEF Inv, MsgInv
    <3>2. PICK Q2 \in Quorums : 
                  \A a \in Q2 : VotedForIn(a, v2, b1, s) \/ WontVoteIn(a, b1, s)
      BY <3>1, <2>4 DEF SafeAt
    <3>3. PICK Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1, s)
      BY <2>1 
    <3>4. QED
      BY <3>2, <3>3, QuorumAssumption, VotedOnce, Z3 DEF WontVoteIn, Inv
  <2>5. CASE GreaterBallot(b1, b2)
    <3>1. SafeAt(v1, b1, s)
      BY VotedInv, QuorumNonEmpty, QuorumAssumption, <2>2, <2>1 DEF Inv, MsgInv
    <3>2. PICK Q4 \in Quorums : 
                  \A a \in Q4 : VotedForIn(a, v1, b2, s) \/ WontVoteIn(a, b2, s)
      BY <3>1, <2>5 DEF SafeAt
    <3>3. PICK Q3 \in Quorums : \A a \in Q3 : VotedForIn(a, v2, b2, s)
      BY <2>2
    <3>4. QED
      BY <3>2, <3>3, QuorumAssumption, VotedOnce, Z3 DEF WontVoteIn, Inv

  <2> QED BY <2>3, <2>4, <2>5, GBTotal
<1>2. QED
  BY Invariant, <1>1, PTL

THEOREM OnlyProposedDecided == Spec => []DecideProposed
<1>1. Inv => DecideProposed
  <2> SUFFICES ASSUME Inv,
                      NEW v \in Values, NEW s \in Slots,
                      NEW m \in msgs,
                      /\ m.type = "decision"
                      /\ m.slot = s
                      /\ m.val = v
               PROVE  Proposed(v, s)
    BY DEF Chosen, DecideProposed
  <2>1. \E mm \in msgs : mm.type = "2a" /\ mm.val = v /\ mm.slot = s
    BY QuorumAssumption DEF Inv, MsgInv, VotedForIn, AccInv
  <2> QED BY <2>1 DEF Inv, MsgInv
<1>2. QED
  BY Invariant, <1>1, PTL
=============
