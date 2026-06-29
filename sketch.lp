
///////////////////////////////////////////////////////////////////////////////
// path_algebra.framework.lp
//
// Scratch of OUR FRAMEWORK — extended Lambdapi with
//     (a) `when`   : context-aware constraint rules (guard = a judgment/predicate,
//                    head = equations merged into the congruence structure), and
//     (b) `theory` : registration of a decision procedure as the X of CC(X).
//
// This is NOT stock Lambdapi and will not parse in it.  Contrast with
// path_algebra.lp, where the interval had to be REIFIED (ICode) and equality
// invoked by hand (eqI).  Here the interval is a REAL type: you write `i ∧ j`,
// `p @ i0`, and conversion `≡` decides them, because:
//     • `when` saturates the path boundary into the e-graph, and
//     • the registered `theory Interval` makes CC consult the canonizer `can`
//       to pick each interval e-class's representative.
//
// The data layer (Dnf, conjD, disjD, negD, eqDnf, wf) is UNCHANGED from
// path_algebra.lp — ordinary terminating functions.  We elide it here:
require open path_algebra;   // Dnf, conjD, disjD, negD, eqDnf, wf, Lit, gen …

///////////////////////////////////////////////////////////////////////////////
// DESIGN (settled).  Conversion is read as a single judgement  Θ′ ⊢ a ≡ b ,
// where Θ′ is an e-graph (a congruence-closure structure).
//   • `theory`  canonizes I/F terms into Dnf (a Shostak canonizer — the algebra
//               itself needs NO e-graph).
//   • `when`    MERGES its head equations into Θ′ (boundary, η, hcomp/comp face
//               laws, primPOr overlap-agreement) — it does NOT orient them as
//               rewrites.  Deciding a ≡ b = "same Θ′-class after congruence
//               closure".  We MERGE rather than orient precisely to stop fighting
//               confluence: η and overlap-agreement have no canonical direction,
//               and a congruence closure is order-independent (egglog fixpoint).
//   GROUND vs METAVARIABLE.  When the SUBJECT is ground (everything below: §1–§6,
//   the four-corner squares, funext) the `$`-pattern `when`s instantiate to
//   ground equations, so Θ′ stays ground ⇒ congruence closure is finite,
//   order-independent, DECIDABLE.  Only when the subject still carries a
//   metavariable does merging interleave with unification (E-unification) — that
//   single case (§7c, under metavars) is the one open question.  KERNEL stays
//   ground-only; metavariable solving lives in the elaborator (ordinary pattern
//   unification, not modulo the theory).  See proposal.md §"Design conclusion".
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// 1.  The interval as a REAL pretype  (no ICode, no quote at use sites)
///////////////////////////////////////////////////////////////////////////////
symbol I  : TYPE;
symbol i0 : I;
symbol i1 : I;
symbol ∧  : I → I → I; notation ∧ infix left 7;
symbol ∨  : I → I → I; notation ∨ infix left 6;
symbol ~  : I → I;      notation ~ prefix 9;

// The canonizer = f.  It matches the REAL interpreted heads (not ICode codes).
// Opaque I-classes — interval variables, alien subterms — are routed by the
// framework through the theory's `atom` hook `gen` (the CC↔X leaf), so `can`
// only needs the interpreted cases:
symbol can : I → Dnf;
rule can i0        ↪ ⊥
with can i1        ↪ ⊤
with can ($a ∧ $b) ↪ conjD (can $a) (can $b)
with can ($a ∨ $b) ↪ disjD (can $a) (can $b)
with can (~ $a)    ↪ negD  (can $a);
//   (any other head x : I  ⟶  framework inserts  can x ↪ gen x , an opaque generator)

///////////////////////////////////////////////////////////////////////////////
// 2.  Register it as the X of CC(X)  — the new `theory` construct
///////////////////////////////////////////////////////////////////////////////
theory Interval {
  carrier     ≔ I;                    // this theory governs I-typed classes
  interpreted ≔ i0, i1, (∧), (∨), (~);// frozen heads `can` handles
  value       ≔ Dnf;                  // semantic representative (the "(X)")
  atom        ≔ gen;                  // leaf hook: opaque I-class ↦ generator value
  canon       ≔ can;                  // make(node) = can folded over children
  equal       ≔ eqDnf;                // THE decision procedure: a ≡_X b ⟺ eqDnf
  consistent  ≔ wf;                   // join-guard: reject value collapse (i0 = i1)
  solve       ≔ none;                 // canonizer-only — NOT Shostak-solvable
}
// Effect on conversion: when CC unions two I-classes it indexes them by `can`;
// `rebuild` re-canonizes after every merge (CC → X), and `equal` decides ≡ on I.

///////////////////////////////////////////////////////////////////////////////
// 3.  Paths — boundary, β and η via `when` (no endpoint annotation needed)
///////////////////////////////////////////////////////////////////////////////
symbol Path : Π (T : TYPE), T → T → TYPE;
symbol pabs : Π (T : TYPE) (f : I → T), Path T (f i0) (f i1);   // ⟨i⟩ t
symbol papp : Π (T : TYPE) (u v : T), Path T u v → I → T;       // p @ e
notation papp postfix-app "@";                                  // p @ e  ≔ papp _ _ _ p e

// β is an ordinary rewrite (orientable, type-erased):
rule papp $T _ _ (pabs $T $f) $e ↪ $f $e;

// boundary is a context-aware constraint: guard reads the TYPE, head is an equation.
// note `p` is unannotated — u,v come from the guard, not from the term.
when p : Path T u v
   ⊢ p @ i0 ≡ u
   ⊢ p @ i1 ≡ v;

// path-η, also a `when`.  Safe here precisely because the e-graph SATURATES an
// equivalence (p and ⟨i⟩(p @ i) coexist in one class) instead of orienting —
// this is the rule that cannot be a confluent rewrite in stock Lambdapi.
when p : Path T u v
   ⊢ pabs T (λ i, p @ i) ≡ p;

///////////////////////////////////////////////////////////////////////////////
// 4.  Faces reuse the SAME machinery; entailment is a usable `when` guard
///////////////////////////////////////////////////////////////////////////////
symbol F   : TYPE;
symbol f0  : F;  symbol f1 : F;                 // empty / whole cube
symbol _=0 : I → F; symbol _=1 : I → F;         // (i=0), (i=1)
symbol ⊓   : F → F → F; notation ⊓ infix left 7;
symbol ⊔   : F → F → F; notation ⊔ infix left 6;

symbol canF : F → Dnf;                           // identical to `can`, plus one rule:
rule canF (($i =0) ⊓ ($i =1)) ↪ ⊥;               // Fdiscr: opposite faces are disjoint
// … (the i0/i1/⊓/⊔/atom cases mirror `can`, omitted)

theory Face {
  carrier ≔ F; interpreted ≔ f0,f1,(_=0),(_=1),(⊓),(⊔);
  value ≔ Dnf; atom ≔ gen; canon ≔ canF; equal ≔ eqDnf; consistent ≔ wf; solve ≔ none;
}

// φ ⊨ ψ  is just  conjD(can φ)(can ψ) ≡ can φ  — decided by the Face theory.
symbol ⊨ : F → F → Prop; notation ⊨ infix 4;
rule ($φ ⊨ $ψ) ↪ Eq Bool (eqDnf (conjD (canF $φ) (canF $ψ)) (canF $φ)) true;

// composition's validity side-condition is a `when` whose GUARD calls the
// decision procedure (f in the guard = fine; f in the head = category error):
symbol comp : Π (T : I → TYPE) (φ : F)
                (sys : I → T i0)        // partial element on φ …
                (a0 : T i0), T i1;
when f1 ⊨ φ                              // total ⟹ comp computes to its tube on i1
   ⊢ comp T φ sys a0 ≡ sys i1;          // FIX: "φ total" is  f1 ⊨ φ (φ=⊤), NOT
                                        // φ ⊨ f1 (= φ≤⊤, trivially true ⇒ unsound).
                                        // General guard is Φ_Γ ⊨ φ — see PART II
                                        // header & proposal.md §"Metatheory" 2.

///////////////////////////////////////////////////////////////////////////////
// 5.  Demonstrations — all hold BY CONVERSION (≡), nothing invoked by hand
///////////////////////////////////////////////////////////////////////////////
symbol i j k : I;                        // opaque interval atoms (generators)

// interval De Morgan algebra, decided by the registered theory:
assert ⊢ (i ∨ j) ∧ i ≡ i;                // absorption
assert ⊢ ~ (~ i)    ≡ i;                 // involution
assert ⊢ i ∧ i1     ≡ i;                 // unit
assert ⊢ i ∧ j      ≡ j ∧ i;             // commutativity (free in the value)
assert ⊢ ~ (i ∧ j)  ≡ (~ i) ∨ (~ j);     // De Morgan
assert ⊢ i ∧ (j ∨ k) ≡ (i ∧ j) ∨ (i ∧ k);// distributivity

// De Morgan ≠ Boolean — excluded middle must NOT hold:
assertnot ⊢ i ∧ (~ i) ≡ i0;
assertnot ⊢ i ∨ (~ i) ≡ i1;

// paths, by the `when` constraints:
symbol A : TYPE; symbol t u : A; symbol p : Path A t u;
assert ⊢ p @ i0 ≡ t;                     // boundary
assert ⊢ p @ i1 ≡ u;                     // boundary
assert ⊢ pabs A (λ i, p @ i) ≡ p;        // η

// the interval theory fires UNDER paths too — same e-class, so the path agrees:
assert ⊢ p @ ((i ∨ j) ∧ i) ≡ p @ i;      // because (i∨j)∧i ≡ i is decided by Interval

// --- function extensionality: PROVABLE, and a clean stress of the boundary
//     `when` firing UNDER a binder (λ x) + function-η.  The two together ARE
//     funext — no axiom, it computes. -------------------------------------------
symbol f g : A → A;                       // two functions on A (reuse A,t from above)
symbol hpt : Π (x : A), Path A (f x) (g x);// a POINTWISE path  f x ∼ g x

// funext h ≔ ⟨i⟩ λ x, (h x) @ i.  Its type is FORCED by `pabs`, no annotation:
//   pabs (A→A) (λ i, λ x, (h x) @ i) : Path (A→A) (λ x,(h x)@i0) (λ x,(h x)@i1)
// and conversion reduces those endpoints to f, g — see the asserts below.
symbol funext : (Π (x : A), Path A (f x) (g x)) → Path (A → A) f g;
rule funext $h ↪ pabs (A → A) (λ i, λ x, ($h x) @ i);

// pointwise computation rule  (funext h) @ i  x  ≡  h x @ i   (pure β, type-erased):
assert ⊢ ((funext hpt) @ i) t ≡ hpt t @ i;

// the two boundary obligations of funext — each fires the §3 boundary `when`
// UNDER (λ x)  (hpt x : Path A (f x) (g x)  ⟹  hpt x @ i0 ≡ f x), then η:
assert ⊢ (funext hpt) @ i0 ≡ f;          // λ x,(hpt x)@i0 ≡ λ x, f x ≡ f
assert ⊢ (funext hpt) @ i1 ≡ g;          // λ x,(hpt x)@i1 ≡ λ x, g x ≡ g
// NB: this is exactly where TYPE-DIRECTED conversion earns its keep — the guard
// must read `hpt x`'s type under the λ to know the endpoints; an untyped engine
// could not fire the boundary here.  (cf. proposal.md §"Metatheory" 3.)

// face entailment in a guard (composition collapses on a total face):
symbol Tf : I → TYPE; symbol sy : I → Tf i0; symbol a0 : Tf i0;
assert ⊢ comp Tf ((i =0) ⊔ (i =1)) sy a0 ≡ sy i1;   // (i=0)⊔(i=1) ⊨ f1 in dim i
// CAVEAT (see PART II + proposal.md §"Metatheory" 2): under the corrected guard
// f1 ⊨ φ this is NOT a closed equality — (i=0)⊔(i=1) ≠ f1 (no excluded middle on
// faces, cf. `assertnot i ∨ ~i ≡ i1`).  It holds only as a *restriction*, in a
// context whose face assumptions entail (i=0)⊔(i=1).  Left as-is to mark the slip.


///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//  PART II — EXTENSION                                                       //
//  Added: partial elements, primPOr + overlap-agreement, hcomp, and the     //
//  associativity-of-composition stressor that EXERCISES the one open        //
//  question — does overlap-agreement saturation terminate & stay decided?   //
//                                                                           //
//  Two guard fixes were applied above:                                      //
//    (1) comp's total-face guard is  f1 ⊨ φ  (φ=⊤), not φ ⊨ f1 (trivial);   //
//    (2) every "on φ" guard reads the AMBIENT face context Φ_Γ, i.e.        //
//        Φ_Γ ⊨ φ.  Φ_Γ is supplied by the kernel (the conjunction of faces  //
//        conversion has entered), NOT a pattern variable — this threading   //
//        of a face context is the type/context-directed cost named in       //
//        proposal.md §"Metatheory" 3.                                       //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

// `_=0`/`_=1` must actually COMPUTE on endpoints (these are among canF's
// "omitted" cases at line 93; the demonstrations below do not converge without
// them, so we make the endpoint cases explicit):
rule (i0 =0) ↪ f1  with (i0 =1) ↪ f0
with (i1 =0) ↪ f0  with (i1 =1) ↪ f1;

///////////////////////////////////////////////////////////////////////////////
// 5.  Partial elements and primPOr — gluing over a join, agreeing on overlap
///////////////////////////////////////////////////////////////////////////////
// A partial element of A defined where the face φ holds.  (Dependent PartialP
// over a Partial-of-TYPE is the same construction one universe up; elided.)
symbol Partial : F → TYPE → TYPE;

// The ONE consumer: where the ambient face Φ_Γ entails φ, a partial element
// denotes a real one.  Write ⌊u⌋ for "u forced on the ambient face"; it
// computes ONLY under a  Φ_Γ ⊨ φ  guard.  This is the IsOne-elimination of
// CCHM with the witness supplied by the context instead of a proof term — see
// proposal.md §"Metatheory" 4 on why that reformulation is conservative.
symbol ⌊_⌋ : Π (φ : F) (A : TYPE), Partial φ A → A;

// Constant partial: any value, forgetting the face.
symbol pcst : Π (φ : F) (A : TYPE), A → Partial φ A;
when Φ_Γ ⊨ φ  ⊢  ⌊ pcst φ A a ⌋ ≡ a ;

// primPOr: glue u-on-φ and v-on-ψ into a partial on φ⊔ψ.  Per the soundness
// boundary, the join is CONSUMED in guards, never produced in a head.
symbol primPOr : Π (φ ψ : F) (A : TYPE), Partial φ A → Partial ψ A → Partial (φ ⊔ ψ) A;

// (i) restriction = the join's elimination, as two boundary `when`s:
when Φ_Γ ⊨ φ  ⊢  ⌊ primPOr φ ψ A u v ⌋ ≡ ⌊ u ⌋ ;   // on φ, the glue is u
when Φ_Γ ⊨ ψ  ⊢  ⌊ primPOr φ ψ A u v ⌋ ≡ ⌊ v ⌋ ;   // on ψ, the glue is v

// (ii) the OVERLAP-AGREEMENT coherence the proposal flagged as missing.
//      GUARD = ambient entails the overlap (decided by the Face theory);
//      HEAD  = the agreement equation.  or-ELIMINATION (conjunctive, decidable),
//      NOT construction over a disjunction.  Scoped to an actual primPOr by the
//      typing premise, exactly like the path-boundary `when`:
when  primPOr φ ψ A u v : Partial (φ ⊔ ψ) A,   Φ_Γ ⊨ (φ ⊓ ψ)
   ⊢  ⌊ u ⌋ ≡ ⌊ v ⌋ ;
// NB: (ii) is not independent — under Φ_Γ ⊨ φ⊓ψ the two rules in (i) already
// give ⌊u⌋ ≡ ⌊primPOr…⌋ ≡ ⌊v⌋ by transitivity in the e-graph.  So a FAILURE of
// (ii) is a real merge clash, and (ii) is exactly the constraint whose
// saturation is THE open question.  Termination must hold even when φ,ψ,u,v
// carry metavariables — then (i)+(ii) interleave with unification (proposal.md
// §"Metatheory" 3).

///////////////////////////////////////////////////////////////////////////////
// 6.  Kan operations — hcomp.  Its computational content splits cleanly:
//       • the FACE laws (total-face top, cap agreement) are face-guarded `when`s
//         decided by the Face theory — the same machinery as §5;
//       • the STRUCTURAL laws (hcomp in Π, Σ, Path, …) are ordinary orientable
//         rewrites, type-erased like β — NOT where the difficulty lives.
//     We give the two face laws; the structural laws mirror CCHM and are elided.
///////////////////////////////////////////////////////////////////////////////
symbol hcomp : Π (A : TYPE) (φ : F), (I → Partial φ A) → A → A;  // u0:A, really A[φ↦u i0]

when f1 ⊨ φ    ⊢  hcomp A φ u u0 ≡ ⌊ u i1 ⌋ ;   // φ total ⇒ top of the tube
when Φ_Γ ⊨ φ   ⊢  u0 ≡ ⌊ u i0 ⌋ ;               // cap agrees with the tube base on φ
//   (comp from §4 is the heterogeneous hcomp; its total-face collapse is the
//    f1 ⊨ φ law transported along T.  We reuse the §4 `comp`.)

///////////////////////////////////////////////////////////////////////////////
// 7.  (was §5)  Further demonstrations — all hold BY CONVERSION (≡)
///////////////////////////////////////////////////////////////////////////////

// --- 7a.  Path composition via hcomp; endpoints COMPUTE -----------------------
symbol ∙ : Π (A : TYPE) (x y z : A), Path A x y → Path A y z → Path A x z;
notation ∙ infix left 5;
// (p ∙ q) @ i  ≔  hcompʲ [ (i=0) ↦ x , (i=1) ↦ q@j ] (p@i)   — faces DISJOINT,
// so the overlap (i=0)⊓(i=1) = f0 (Fdiscr) and agreement (ii) is vacuous here:
rule papp $A $x $z (∙ $A $x $y $z $p $q) $i
   ↪ hcomp $A (($i =0) ⊔ ($i =1))
        (λ j, primPOr ($i =0) ($i =1) $A (pcst ($i =0) $A $x) (pcst ($i =1) $A ($q @ j)))
        ($p @ $i);

symbol B : TYPE; symbol b0 b1 b2 : B;
symbol pp : Path B b0 b1;  symbol qq : Path B b1 b2;
// endpoints reduce: at i:=i0 the face (i0=0)⊔(i0=1) = f1⊔f0 = f1 (total ⇒ collapse
// to the (i=0) tube = b0); dually at i1 to b2:
assert ⊢ (∙ B b0 b1 b2 pp qq) @ i0 ≡ b0;
assert ⊢ (∙ B b0 b1 b2 pp qq) @ i1 ≡ b2;

// --- 7b.  A square: the MINIMAL genuine overlap-agreement exerciser ----------
// Four edges of a square, corners x⟨ij⟩.  Gluing the whole boundary with nested
// primPOr makes the overlaps (i=ε)⊓(j=ε') REAL faces (not f0) — so agreement (ii)
// actually fires at all four corners:
symbol x00 x01 x10 x11 : B;
symbol le : Path B x00 x01;   // left   (i=0), along j
symbol ri : Path B x10 x11;   // right  (i=1), along j
symbol bo : Path B x00 x10;   // bottom (j=0), along i
symbol to : Path B x01 x11;   // top    (j=1), along i
//   bdy i j ≔ primPOr ((i=0)⊔(i=1)) ((j=0)⊔(j=1)) B
//               (primPOr (i=0) (i=1) B (pcst _ _ (le@j)) (pcst _ _ (ri@j)))
//               (primPOr (j=0) (j=1) B (pcst _ _ (bo@i)) (pcst _ _ (to@i)))
// Well-formedness of `bdy` invokes (ii) on the outer overlap
//   ((i=0)⊔(i=1)) ⊓ ((j=0)⊔(j=1))  =  ⊔ of the four corners (i=ε)⊓(j=ε'),
// discharging precisely these four — each a Face-entailment guard feeding the
// path-boundary `when`s, i.e. CROSS-THEORY saturation (Face ⨯ Path):
assert ⊢ le @ i0 ≡ bo @ i0;   // corner (i=0)⊓(j=0):  both ≡ x00
assert ⊢ le @ i1 ≡ to @ i0;   // corner (i=0)⊓(j=1):  both ≡ x01
assert ⊢ ri @ i0 ≡ bo @ i1;   // corner (i=1)⊓(j=0):  both ≡ x10
assert ⊢ ri @ i1 ≡ to @ i1;   // corner (i=1)⊓(j=1):  both ≡ x11
// each holds because the Face theory decides the corner face and the path-
// boundary `when` reduces both sides to the shared corner.  Agreement (ii) is
// the conjunction of these — DECIDED, not assumed.

// --- 7c.  The headline: associativity of composition -------------------------
// Double composition  p ∙∙ q ∙∙ r  (faces (i=0)↦p@~j, (i=1)↦r@j; base q@i):
symbol ∙∙∙ : Π (A:TYPE)(w x y z:A), Path A w x → Path A x y → Path A y z → Path A w z;
rule papp $A $w $z (∙∙∙ $A $w $x $y $z $p $q $r) $i
   ↪ hcomp $A (($i =0) ⊔ ($i =1))
        (λ j, primPOr ($i =0) ($i =1) $A (pcst ($i =0) $A ($p @ (~ j))) (pcst ($i =1) $A ($r @ j)))
        ($q @ $i);
symbol cc : Path B b2 b0;   // third edge, to compose three with matching ends
// Associativity holds because BOTH (pp∙qq)∙cc and pp∙(qq∙cc) convert to the
// double composite pp ∙∙ qq ∙∙ cc, via squares whose boundary is a four-corner
// primPOr exactly like 7b.  Hence (both sides : Path B b0 b0):
assert ⊢ ∙ B b0 b2 b0 (∙ B b0 b1 b2 pp qq) cc
       ≡ ∙ B b0 b1 b0 pp (∙ B b1 b2 b0 qq cc);
//        └────────── (pp ∙ qq) ∙ cc ──────────┘   └──────── pp ∙ (qq ∙ cc) ───────┘
//
// THIS `assert` is the open question made concrete.  It converts iff the
// overlap-agreement saturation at the squares' corners (7b-style) reaches a
// fixpoint and the Face theory decides each corner — and, when pp/qq/cc or the
// faces carry metavariables, iff that saturation still terminates while
// interleaving with unification (proposal.md §"Metatheory" 3).  Everything else
// in this file is dispatched; this is the one thing the thesis must prove.


///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//  PART III — CASE-TREE ELABORATION IN THE FRAMEWORK                         //
//  Representing  CtIntRoPath  and  CtDone  (Vezzosi–Mörtberg–Abel, "Cubical  //
//  Agda", ICFP 2019, §4.3 / Fig. 3, "the typing rules for case trees").      //
//                                                                           //
//  The case-tree judgment is   Σ; Γ ⊢ f q̄ := Q : C | Θ ⤳ Σ′ ,             //
//  where  Θ = α₁;…;αₙ  is a list of BOUNDARY ASSIGNMENTS — each αᵢ sends    //
//  some interval vars to i0/i1 — accumulated while elaborating a definition //
//  by copatterns/clauses.                                                   //
//                                                                           //
//  ┌─ CORRESPONDENCE ───────────────────────────────────────────────────┐  //
//  │   the paper's  Θ   IS   our ambient face context  Φ_Γ  (PART II).   │  //
//  │     • CtIntRoPath PUSHES endpoint faces (i=0),(i=1) onto Θ ;        │  //
//  │     • CtDone DISCHARGES every face of Θ by a face-restricted  ≡ .   │  //
//  │   So the framework already implements the CHECKING half: the §3     │  //
//  │   boundary `when` is CtDone restricted to the faces CtIntRoPath     │  //
//  │   pushes.  PART III makes the ELABORATION half explicit.            │  //
//  └─────────────────────────────────────────────────────────────────────┘ //
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

// ── CtIntRoPath ──────────────────────────────────────────────────────────────
//   Σ; Γ ⊢ C = PathP B u₀ u₁ : Setₙ        Θ′ = (i=0);(i=1);Θ
//   Σ; Γ(i:I) ⊢ f q̄ @u₀,u₁ i := Q : B i | Θ′ ⤳ Σ′
//   ─────────────────────────────────────────────────────────  CtIntRoPath
//   Σ; Γ ⊢ f q̄ := λi. Q : C | Θ ⤳ Σ′
//
// To elaborate a clause whose target is a path type: introduce an interval var
// i, turn the goal  f q̄ : Path B u₀ u₁  into  f q̄ @ i : B i  (path application),
// and PUSH (i=0),(i=1) onto Φ_Γ.  (Here `Path` = `PathP` at constant B, so the
// dependent `B i` collapses to the carrier T of §3.)
//
//   CONTRAST (proposal.md line 4, now concrete): the paper ANNOTATES the path
//   application — `@u₀,u₁`.  In THIS framework papp's endpoints are the inferred
//   `_ _` of  papp _ _ _ p i , read off the TYPE Path T u v by the §3 boundary
//   `when`, so the term stays UNANNOTATED.  CtIntRoPath is precisely the
//   @u₀,u₁-annotated rule our `when` improves on.

// ── CtDone ───────────────────────────────────────────────────────────────────
//   Σ; Γ ⊢ v : C        Θ = α₁;…;αₙ
//   (Σ; Γαᵢ ⊢ f q̄[αᵢ] = v[αᵢ] : C[αᵢ])ᵢ₌₁…ₙ
//   ──────────────────────────────────────────────────────────  CtDone
//   Σ; Γ ⊢ f q̄ := v : C | Θ ⤳ Σ, (clause Γ ⊢ f q̄ ↩→ v : C)
//
// A leaf is a body v of the expected type.  For EVERY face αᵢ ∈ Θ it must agree
// with the head:  f q̄[αᵢ] ≡ v[αᵢ].  In the framework this is one conversion goal
// per face — restrict to αᵢ (decided by the Face theory) and decide ≡ with the
// cubical `when`s.  The paper's subtlety — "checked in Σ BEFORE the clause
// f q̄ ↩→ v is added" — is what keeps it non-circular: the goal uses the HEAD
// f q̄, not the new rewrite, so PART II's `⌊_⌋`/Φ_Γ guards never assume what they
// are proving.

// ── Worked elaboration: path inversion `sym`, one CtIntRoPath + CtDone clause ─
symbol sym : Π (A:TYPE) (a b:A), Path A a b → Path A b a;
// clause   sym A a b p := λ i. p @ (~ i)   : Path A b a
//   CtIntRoPath:  C = Path A b a  ⇒  intro i:I, endpoints u₀=b, u₁=a,
//                 Θ := (i=0);(i=1).   New goal:
//                 sym A a b p @ i := Q : A | (i=0);(i=1)
//   CtDone:       leaf  Q = p @ (~ i).
rule papp $A $b $a (sym $A $a $b $p) $i  ↪  $p @ (~ $i);   // the elaborated clause (β)

// The two CtDone premises  Σ; Γα ⊢ (sym…)[α] = (p @ ~i)[α]  for α ∈ Θ={(i=0),(i=1)}.
// With  p : Path A t u  (§3),  sym A t u p : Path A u t  (endpoints u, t):
assert ⊢ (sym A t u p) @ i0 ≡ u;   // face (i=0):  p @ ~i0 ≡ p @ i1 ≡ u   (= u₀)
assert ⊢ (sym A t u p) @ i1 ≡ t;   // face (i=1):  p @ ~i1 ≡ p @ i0 ≡ t   (= u₁)
// each discharges by  Interval theory ( ~i0 ≡ i1 , ~i1 ≡ i0 )  THEN the §3
// boundary `when` ( p @ i1 ≡ u , p @ i0 ≡ t ): CtDone here is decided by the
// registered theory composed with one `when` — no proof term, no annotation.

// ── The rest of Fig. 3's Ct* family maps onto machinery already built: ────────
//   CtIntRo        ordinary λ-intro — the §3 papp/β layer, no faces.
//   CtSplitPaRtial split a face system r = ⋁ᵢ⋀αᵢ; "the Qᵢ must agree on the
//                  intersections" is VERBATIM the OVERLAP-AGREEMENT `when` of §5
//                  (primPOr), and "extend Θ with the previous cases" is our
//                  Φ_Γ ⊨ φ⊓ψ guard.
//   CtSplitConHIT  the hcomp-constructor case "extends Θ with (r=i1), where
//                  hcomp r u u₀ computes to u i1 1=1" — VERBATIM the §6 hcomp
//                  total-face law.
//   CtSplitCon / CtCosplit   ordinary data/record splitting — no cubical content.
// So Fig. 3's three *cubical* rules (CtIntRoPath, CtSplitPaRtial, CtSplitConHIT)
// are exactly §3's boundary `when`, §5's overlap-agreement, and §6's hcomp law,
// with the single list Θ unified as the ambient Φ_Γ.
