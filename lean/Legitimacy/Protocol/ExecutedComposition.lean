import Legitimacy.MultiAgentJointCapabilityComposition.BoolFixtures

/-!
# Executed controlled release

A finite declared two-principal/two-channel experiment. The host records actual
fragment deliveries. Exposure is cumulative, not an event count. The fixed harm
is both synthetic fragments on the public channel. Authorization is separate
from authentication; no observation field is silently defaulted here.
-/
set_option autoImplicit false
namespace Legitimacy.ExecutedComposition

structure Exposure where
  a : Bool
  b : Bool
  deriving DecidableEq, Repr

structure Request where
  actorB : Bool
  fragment : Bool
  publicChannel : Bool
  authenticated : Bool
  delegated : Bool
  deriving DecidableEq, Repr

def empty : Exposure := ⟨false, false⟩
def forbidden (s : Exposure) : Bool := s.a && s.b

def localPermit (r : Request) : Bool := r.authenticated && r.delegated

/-- Actual delivery effects; summaries and vault deliveries do not expose shares. -/
def deliver (s : Exposure) (r : Request) : Exposure :=
  if r.fragment && r.publicChannel then
    if r.actorB then ⟨s.a, true⟩ else ⟨true, s.b⟩
  else s

/-- The missing composition obligation: an authorized delivery must preserve
exclusion of the *same* conjunctive property in its actual context. -/
def permit (s : Exposure) (r : Request) : Bool :=
  localPermit r && !forbidden (deliver s r)

def step (guard : Bool) (s : Exposure) (r : Request) : Exposure :=
  if (if guard then permit s r else localPermit r) then deliver s r else s

def run (guard : Bool) (rs : List Request) : Exposure :=
  rs.foldl (step guard) empty

/-- Explicit realized delivery log. Denied requests contribute no delivery. -/
def deliveries (guard : Bool) (s : Exposure) : List Request → List Request
  | [] => []
  | r :: rs =>
    if (if guard then permit s r else localPermit r) then
      r :: deliveries guard (deliver s r) rs
    else deliveries guard s rs

/-- Refinement from the admitted delivery log to the state transition execution. -/
theorem delivery_log_refines (guard : Bool) (s : Exposure) (rs : List Request) :
    (deliveries guard s rs).foldl deliver s = rs.foldl (step guard) s := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    rw [List.foldl_cons]
    by_cases h : (if guard then permit s r else localPermit r) = true
    · rw [show step guard s r = deliver s r by simp [step, h]]
      simp only [deliveries, h, ↓reduceIte, List.foldl_cons]
      exact ih _
    · rw [show step guard s r = s by simp [step, h]]
      simp only [deliveries, h]
      exact ih _

def exposesA (r : Request) : Bool := !r.actorB && r.fragment && r.publicChannel
def exposesB (r : Request) : Bool := r.actorB && r.fragment && r.publicChannel

lemma deliver_a (s : Exposure) (r : Request) :
    (deliver s r).a = (s.a || exposesA r) := by
  rcases s with ⟨a, b⟩
  rcases r with ⟨actor, fragment, channel, auth, scope⟩
  cases a <;> cases b <;> cases actor <;> cases fragment <;> cases channel <;> rfl

lemma deliver_b (s : Exposure) (r : Request) :
    (deliver s r).b = (s.b || exposesB r) := by
  rcases s with ⟨a, b⟩
  rcases r with ⟨actor, fragment, channel, auth, scope⟩
  cases a <;> cases b <;> cases actor <;> cases fragment <;> cases channel <;> rfl

lemma fold_deliver_a (rs : List Request) (s : Exposure) :
    (rs.foldl deliver s).a = (s.a || rs.any exposesA) := by
  induction rs generalizing s with
  | nil => simp
  | cons r rs ih => simp [List.foldl_cons, ih, deliver_a, Bool.or_assoc]

lemma fold_deliver_b (rs : List Request) (s : Exposure) :
    (rs.foldl deliver s).b = (s.b || rs.any exposesB) := by
  induction rs generalizing s with
  | nil => simp
  | cons r rs ih => simp [List.foldl_cons, ih, deliver_b, Bool.or_assoc]

/-- Harm is witnessed by actually admitted public fragment deliveries by both
principals. Merely possessing the corresponding capabilities cannot satisfy it. -/
theorem public_delivery_witness (guard : Bool) (rs : List Request) :
    forbidden (run guard rs) = true ↔
      (∃ r ∈ deliveries guard empty rs, exposesA r = true) ∧
      (∃ r ∈ deliveries guard empty rs, exposesB r = true) := by
  unfold run
  rw [← delivery_log_refines guard empty rs]
  simp [forbidden, fold_deliver_a, fold_deliver_b, empty, List.any_eq_true]

theorem step_preserves (s : Exposure) (r : Request)
    (h : forbidden s = false) : forbidden (step true s r) = false := by
  change forbidden (if permit s r then deliver s r else s) = false
  split
  next hp =>
    cases he : forbidden (deliver s r) <;> simp_all [permit]
  next => exact h

theorem fold_preserves (rs : List Request) (s : Exposure)
    (h : forbidden s = false) :
    forbidden (rs.foldl (step true) s) = false := by
  induction rs generalizing s with
  | nil => exact h
  | cons r rs ih => exact ih _ (step_preserves s r h)

theorem repair_safe (rs : List Request) : forbidden (run true rs) = false :=
  fold_preserves rs empty rfl

def releaseA : Request := ⟨false, true, true, true, true⟩
def releaseB : Request := ⟨true, true, true, true, true⟩
def vaultB : Request := { releaseB with publicChannel := false }
def summaryB : Request := { releaseB with fragment := false }

theorem equal_length_action_control :
    [releaseA, releaseB].length = [releaseA, vaultB].length ∧
    ([releaseA, releaseB].all localPermit = true) ∧
    forbidden (run false [releaseA, releaseB]) = true ∧
    forbidden (run false [releaseA, vaultB]) = false := by decide

/-- Concrete selectivity, useful work, profile sensitivity, and context sensitivity.
These witnesses exclude constant, length-only, and metadata-only operators. -/
theorem useful_repair :
    permit empty releaseA = true ∧
    permit (deliver empty releaseA) releaseB = false ∧
    permit (deliver empty releaseA) vaultB = true ∧
    permit (deliver empty releaseA) summaryB = true ∧
    permit empty releaseB = true ∧
    permit empty { releaseA with delegated := false } = false ∧
    run true [releaseA, vaultB] = ⟨true, false⟩ := by decide

theorem authentication_not_authorization (s : Exposure) (r : Request)
    (h : r.delegated = false) : permit s r = false := by
  simp [permit, localPermit, h]

/-- Kernel action projection. Bool encodings are principal dependent, matching
exactly the pre-existing forbidden list, rather than substituting a safe list. -/
noncomputable def actions (s : Exposure) (agent : KernelGovernedAgent)
    (hm : agent ∈ [speraBoolAgentA, speraBoolAgentB]) :
    agent.kernel.actionSpace.Action := by
  have hb : agent.kernel.actionSpace.Action = Bool := by
    rcases List.mem_cons.mp hm with rfl | ht
    · rfl
    · rcases List.mem_cons.mp ht with rfl | hn
      · rfl
      · cases hn
  exact hb.symm ▸ (if agent.id = 0 then s.a else !s.b)

noncomputable def realized (s : Exposure) : JointCapability speraBoolFixture where
  participating_agents := [speraBoolAgentA, speraBoolAgentB]
  participating_agent_ids_nodup := speraBoolJointCapability.participating_agent_ids_nodup
  participation_proof := speraBoolJointCapability.participation_proof
  agent_action := actions s
  cardinality_two_or_more := by decide
  not_single_declared_edge := by
    intro edge hedge he
    simp [speraBoolFixture, speraBoolSystemWithEdge] at hedge
    subst edge
    simp [EdgeRealizesJointCapability, speraBoolTrackedToolEdge,
      compatibleDelegationEdge, speraBoolAgentA, speraBoolAgentB] at he

/-- The execution restriction is explicit. The unrestricted historical
JointCapabilityViolatesForbidden still describes available capability. -/
def ExecutedViolation (s : Exposure) : Prop :=
  JointCapabilityReaches (realized s)
    (fun agent hm => speraBoolTrajectory.perAgent agent
      ((realized s).participation_proof agent hm)) boolJointForbiddenList

theorem executed_refinement (s : Exposure) :
    ExecutedViolation s ↔ forbidden s = true := by
  simp only [ExecutedViolation, JointCapabilityReaches, boolJointForbiddenList,
    List.mem_singleton, exists_eq_left]
  constructor
  · rintro ⟨⟨ha, hb, hA, hB⟩, _⟩
    cases hs : s.b <;>
      simpa [realized, actions, speraBoolAgentA, speraBoolAgentB, forbidden, hs] using
        And.intro hA hB
  · intro h
    refine ⟨?_, ?_⟩
    · cases hs : s.b <;>
        simp_all [boolJointForbidden, realized, actions, speraBoolAgentA,
          speraBoolAgentB, forbidden]
    · intro agent hm
      simp [realized] at hm
      rcases hm with rfl | rfl <;>
        simp [boolJointForbidden, speraBoolAgentA, speraBoolAgentB]

/-- End-to-end formal origin of the participating kernel action terms. -/
theorem executed_delivery_witness (guard : Bool) (rs : List Request) :
    ExecutedViolation (run guard rs) ↔
      (∃ r ∈ deliveries guard empty rs, exposesA r = true) ∧
      (∃ r ∈ deliveries guard empty rs, exposesB r = true) :=
  (executed_refinement _).trans (public_delivery_witness guard rs)

theorem executed_repair_same_property (rs : List Request) :
    ¬ ExecutedViolation (run true rs) := by
  rw [executed_refinement, repair_safe]
  decide

theorem executed_negative : ExecutedViolation (run false [releaseA, releaseB]) := by
  rw [executed_refinement]
  decide

/-- An actual executed violation implies the original composed violation;
the converse is intentionally not claimed. -/
theorem executed_implies_composed (s : Exposure) (h : ExecutedViolation s) :
    ComposedTrajectoryViolatesForbidden speraBoolTrajectory boolJointForbiddenList :=
  Or.inr (Or.inr ⟨realized s, h⟩)

/-- Declared edge tracking is present in both outcomes, so cannot be the repair. -/
theorem realized_tracked (s : Exposure) :
    EdgeTracksJointCapability speraBoolTrackedToolEdge (realized s) := by
  refine ⟨speraBoolAgentA, by simp [realized], speraBoolAgentB,
    by simp [realized], rfl, rfl, rfl, rfl⟩

/-- Query sufficiency is constancy on observation fibers. Classical partition
factorization, specialized below to this governance query. -/
def Sufficient {H O Q : Type} (observe : H → O) (query : H → Q) : Prop :=
  ∀ x y, observe x = observe y → query x = query y

theorem sufficient_iff_factor {H O Q : Type} [Nonempty Q]
    (observe : H → O) (query : H → Q) :
    Sufficient observe query ↔ ∃ f : O → Q, ∀ h, f (observe h) = query h := by
  classical
  constructor
  · intro hs
    let f := fun o => if he : ∃ h, observe h = o then
      query (Classical.choose he) else Classical.choice inferInstance
    refine ⟨f, ?_⟩
    intro h
    dsimp [f]
    split
    next he => exact hs _ h (Classical.choose_spec he)
    next he => exact False.elim (he ⟨h, rfl⟩)
  · rintro ⟨f, hf⟩ x y he
    rw [← hf x, ← hf y, he]

/-- Erasing scoped delegation leaves observation-identical requests that
require different decisions, even with authentication held true. -/
def eraseDelegation (r : Request) : Request := { r with delegated := false }

theorem missing_authority_ambiguity :
    eraseDelegation releaseA = eraseDelegation { releaseA with delegated := false } ∧
    permit empty releaseA ≠ permit empty { releaseA with delegated := false } := by decide

theorem authority_observation_insufficient :
    ¬ Sufficient eraseDelegation (permit empty) := by
  intro hs
  exact missing_authority_ambiguity.2 (hs _ _ missing_authority_ambiguity.1)

theorem full_observation_sufficient (s : Exposure) :
    Sufficient (fun r : Request => r) (permit s) := by
  intro x y h
  exact congrArg (permit s) h


/-- Three reachable safe contexts: neither fragment public, only A, only B. -/
def safeContext (i : Fin 3) : Exposure :=
  if i = 0 then empty else if i = 1 then ⟨true, false⟩ else ⟨false, true⟩

theorem safe_context_safe (i : Fin 3) : forbidden (safeContext i) = false := by
  fin_cases i <;> decide

theorem safe_context_reachable (i : Fin 3) :
    ∃ rs : List Request, run true rs = safeContext i := by
  fin_cases i
  · exact ⟨[], rfl⟩
  · exact ⟨[releaseA], rfl⟩
  · exact ⟨[releaseB], rfl⟩

theorem safe_context_queries_injective :
    Function.Injective (fun i : Fin 3 =>
      (permit (safeContext i) releaseA, permit (safeContext i) releaseB)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> revert h <;> decide

/-- Exact next-request answers on every safe context require at least three
observation values. This is a selectivity bound, not a safety-only bound:
a deny-all monitor need not retain any exposure memory. -/
theorem exact_safe_observation_requires_three {O : Type} [Fintype O]
    (observe : Exposure → O) (answer : O → Request → Bool)
    (correct : ∀ s, forbidden s = false → ∀ r, answer (observe s) r = permit s r) :
    3 ≤ Fintype.card O := by
  have inj : Function.Injective (fun i : Fin 3 => observe (safeContext i)) := by
    intro i j h
    apply safe_context_queries_injective
    have ha := congrArg (fun o => answer o releaseA) h
    have hb := congrArg (fun o => answer o releaseB) h
    dsimp only at ha hb
    rw [correct _ (safe_context_safe i), correct _ (safe_context_safe j)] at ha hb
    exact Prod.ext ha hb
  simpa using Fintype.card_le_of_injective _ inj

theorem one_bit_observation_insufficient (observe : Exposure → Bool)
    (answer : Bool → Request → Bool) :
    ¬ (∀ s, forbidden s = false → ∀ r, answer (observe s) r = permit s r) := by
  intro correct
  have h := exact_safe_observation_requires_three observe answer correct
  have hc : Fintype.card Bool = 2 := rfl
  rw [hc] at h
  omega

/-- The two public-exposure bits suffice for all requests, not only the witnesses. -/
theorem two_exposure_bits_suffice (s : Exposure) (r : Request) :
    permit ⟨s.a, s.b⟩ r = permit s r := rfl

end Legitimacy.ExecutedComposition
