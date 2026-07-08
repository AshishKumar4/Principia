# P1.1-P1.3 Spec-Review Source Dossier — Causal Structure Definitions

> This document is edited and maintained by Claude and presented as-is.
> Produced 2026-07-08 by a Fable research agent from verbatim source reading;
> preserved as the auditable evidence record for the P1.1-P1.3 spec freeze.
> Epistemic tags: [VERBATIM] read directly from source text; [3RD-PARTY] pinned
> via high-quality secondary citation; [RECONSTRUCTED] training-memory, unverified.

(Verbatim agent report follows.)

## Source inventory

| Source | Access |
|---|---|
| Minguzzi, *Lorentzian causality theory*, Living Rev. Relativ. 22:3 (2019) | full open-access PDF, verbatim |
| Minguzzi & Sánchez, *The causal hierarchy of spacetimes* (arXiv:gr-qc/0609119) | full, verbatim |
| Chruściel, *Elements of causality theory* (arXiv:1110.6706v1) | full, verbatim |
| Wald, *General Relativity* (1984) | public scan; pages read visually: 22-23, 188-189, 191-195, 200-203, 209-211. **Book p. 190 physically missing from the scan** |
| Bernal & Sánchez, CMP 243 (2003) 461 (gr-qc/0306108) | full, verbatim |
| Bernal & Sánchez, CQG 24 (2007) 745 (gr-qc/0611138) | full, verbatim |
| Sánchez, arXiv:math/0604265 | full, verbatim |
| Galloway, *Notes on Lorentzian causality* (ESI notes) | full, verbatim |
| Ringström, KTH notes (reproduces O'Neill ch. 2/3/5 definitions) | full, verbatim |
| O'Neill (1983) | book NOT directly accessible; content triple-pinned via Minguzzi-Sánchez footnote, BS2003 quoting Lemma 14.29, arXiv:1204.4080, Galloway page-cites, Ringström |

## 1. Metric, index, Lorentzian manifold

- O'Neill [3RD-PARTY via Ringström]: index = largest dim of a negative-definite
  subspace (p. 47); metric tensor = symmetric nondegenerate (0,2) field of constant
  index (p. 54); Lorentz manifold = index 1 AND dim ≥ 2 (p. 55). Mostly-plus.
- Wald §2.3 pp. 22-23 [VERBATIM] (metric is §2.3, not §2.2): symmetric nondegenerate
  (0,2); signature via orthonormal-basis sign counts; "one minus and the remainder
  plus) are called Lorentzian".
- Minguzzi LRR Def. 1.6 [VERBATIM]: spacetime = connected NON-COMPACT time-oriented
  Lorentzian manifold (non-compactness is his idiosyncrasy — do not bake in).
- M-S Def. 2.1/2.5 [VERBATIM]: dim ≥ 2, Hausdorff, C^{r0} r0∈{3..∞} (2 suffices);
  spacetime = time-oriented connected. Chruściel Def. 2.1.1 omits connectedness.
- Spec verdicts: signature-generic metric + IsLorentzian=index-1 matches O'Neill/
  Sylvester; dimension hypotheses explicit at theorem sites; no non-compactness.

## 2. Causal character of vectors — the convention registry

- O'Neill [3RD-PARTY, double-pinned]: timelike g<0; null g=0 ∧ v≠0; spacelike g>0 ∨
  v=0; causal = timelike ∨ null. ZERO VECTOR IS SPACELIKE.
- Minguzzi LRR §1.3 [VERBATIM]: causal g≤0 ∧ v≠0; lightlike g=0 ∧ v≠0; null g=0
  (INCLUDES 0); spacelike g>0 ∨ v=0. Footnote: excluding 0 makes causal curves regular.
- M-S Def. 2.2 [VERBATIM]: spacelike g>0 (zero NOT spacelike here); null includes 0.
- Wald p. 189 [VERBATIM]: labels via isomorphism to Minkowski space; never explicitly
  classifies the zero vector; p. 190 wording [RECONSTRUCTED — missing page].
- Key: "causal" excludes 0 in every source that defines it → curve regularity free.
  "null" O'Neill-sense (∌0) vs Minguzzi-sense (∋0) must not drift.

## 3. Time orientation

- O'Neill pp. 143-145: timecone C(u); timelike v,w same cone iff ⟨v,w⟩<0 (reverse
  Cauchy-Schwarz; Ringström Lemma 20 reproduces). Lemma 5.32 [3RD-PARTY]:
  time-orientable ⟺ ∃ global timelike vector field.
- Wald p. 189 [VERBATIM] + Lemma 8.1.1 [VERBATIM]: time-orientable → ∃ smooth
  nonvanishing timelike field (Riemannian-minimization proof).
- Minguzzi LRR §1.7 [VERBATIM]: continuous cone choice ⟺ continuous global timelike
  field ("call future that half ... which contains v").
- M-S §2.1 [VERBATIM] Prop 2.3: ⟺ global timelike X (choosable complete); smooth/
  C^r/continuous choices coincide; causal v future-directed iff g(v,X)<0.
- Chruściel §2.1 [VERBATIM]: same orientation iff g(X,Y)<0; exactly two orientations.
- Spec verdicts: timelike-vector-field-as-data is standard-equivalent; FutureDirected
  v ↔ g(v,T)<0 valid only under causal hypothesis; same-cone ⟺ g<0 needs reverse
  Cauchy-Schwarz (Minguzzi Thm 1.2 has a formalizable proof); exactly-two-orientations
  a later lemma.

## 4. Curves — regularity classes

- Wald p. 193 [VERBATIM]: continuous causal curves via convex-normal-neighborhood
  local reachability; identification up to continuous reparametrization; continuous
  class needed ONLY for limit arguments (p. 192 [VERBATIM]). Differentiable-curve
  definition is on the missing p. 190 [RECONSTRUCTED].
- M-S §2.1 [VERBATIM]: piecewise smooth, lateral tangents at breaks in same cone.
- Minguzzi LRR §1.11 [VERBATIM]: piecewise C¹, future character at every point,
  causal curves regular (ẋ≠0 automatic); concatenation closes. Remark 2.14
  [VERBATIM]: J from piecewise-C¹ = J from continuous causal (corner smoothing).
  Remark 2.15 [VERBATIM]: Hawking-Ellis "continuous timelike" is defective — do not
  formalize.
- Chruściel §2.3 [VERBATIM]: locally Lipschitz, a.e.-causal (modern class).
- All classes induce the same I, J. Nonvanishing velocity must NOT be a separate
  axiom (redundant given causal ∌ 0). TransGen-of-C¹-segments = O'Neill/Minguzzi
  piecewise convention with cone-matching subsumed by per-segment future-direction.

## 5. Relations ≪, ≤; I±, J±

- Minguzzi LRR §1.11 [VERBATIM]: J includes diagonal by fiat ("or p = q"); Prop 1.16:
  J transitive reflexive; I transitive open. Set-level trap: E⁺(S):=J⁺(S)∖I⁺(S) ≠
  ∪ₚE⁺(p) in general (Lemma 1.15).
- M-S §2.3 [VERBATIM]: p ≤ q via "causal or constant" curve.
- O'Neill p. 402 [RECONSTRUCTED, corroborated by Galloway Def. 2.1]: p ≤ q iff p < q
  or p = q.
- Chruściel §2.4 [VERBATIM]: J⁺(U;O) := {reachable} ∪ U, explicitly refusing constant
  causal paths (fn. 6).
- Wald: p. 190 definition [RECONSTRUCTED]; p. 200 [VERBATIM] "S ⊂ D⁺(S) ⊂ J⁺(S)"
  REQUIRES reflexive J⁺ — Wald uses the reflexive convention.
- Universal: ≤ preorder; ≪ transitive open non-reflexive (p ≪ p ⟺ CTC); push-up
  lemmas are convex-neighborhood-gated (P1.4), not P1.2 claims.

## 6. Achronal sets

- Wald p. 192 [VERBATIM] (COMMONLY MISCITED AS p. 190/194): achronal iff no p,q ∈ S
  with q ∈ I⁺(p), i.e. I⁺(S) ∩ S = ∅.
- Minguzzi Def. 2.19 [VERBATIM] same; Def. 2.95 [VERBATIM] acausal = no causal curve
  starts and ends at S. M-S: "not crossed twice by any timelike (resp. causal) curve".
- Chruściel §2.9 acausal formula J⁺(U)∩J⁻(U)=∅ is INCONSISTENT with his own reflexive
  J⁺ (as printed, no nonempty set is acausal) — a real published convention-interaction
  bug; the exact bug class to hunt in our Lean. Never define acausal via reflexive-J
  intersections or `p ⤳ q → p = q`.

## 7. Endpoints and inextendibility

- Wald p. 193 [VERBATIM]: future endpoint = ∀ nbhd O ∃ t₀, λ(t) ∈ O ∀ t > t₀; at most
  one by Hausdorff; endpoint need not lie on curve; future inextendible = no future
  endpoint. Caution [VERBATIM]: differentiable causal curve with endpoint may not
  extend differentiably but always extends continuously — hence inextendibility must
  NOT be spec'd as "no extension within the smoothness class".
- Minguzzi Def. 2.16 + Lemma 2.17 [VERBATIM]: convergence form; h-arclength
  parametrized ⟹ inextendible iff domain unbounded.
- Chruściel §2.5 [VERBATIM]: endpoint vs in-class extendibility distinguished;
  equivalent under Lipschitz parametrization (Lemma 2.5.4, Thm 2.5.5).
- Limit point ≠ endpoint (imprisoned curves accumulate without converging).
- Minguzzi Prop. 3.3/Cor. 3.4 [VERBATIM]: for S closed or achronal, D⁺(S) is the same
  for C¹ / piecewise-C¹ / continuous causal curve classes — the load-bearing
  justification that a piecewise-C¹-only Phase-1 spec is not a wrong definition.

## 8. Cauchy surfaces (highest-risk item) — THREE inequivalent conventions

1. Achronal school (Wald p. 201 [VERBATIM]: closed achronal, D(Σ)=M; O'Neill p. 415
   [3RD-PARTY]: "met exactly once by every inextendible timelike curve"; Geroch 1970
   same): timelike exactly once; causal curves meet at least once, POSSIBLY IN A NULL
   SEGMENT (BS2003 quoting O'Neill Lemma 14.29 [VERBATIM]; M-S Def. 3.74 [VERBATIM]
   with explicit null-portioned example).
2. Acausal school (Minguzzi LRR Def. 3.35 [VERBATIM]): closed acausal, D(S)=M; causal
   curves meet EXACTLY once. Strictly narrower.
3. Chruściel §2.11 [VERBATIM]: achronal topological hypersurface + D_J(S)=M
   (hypersurface-ness definitional).
- All agree on spacelike/acausal surfaces; {t=0} ⊂ Minkowski is Cauchy on all three.
- Wald Prop. 8.3.4 [VERBATIM]: inextendible causal curve meets Σ, I⁺(Σ), and I⁻(Σ).
- Minguzzi Thm 3.40 [VERBATIM]: closed achronal S is Cauchy iff every inextendible
  lightlike geodesic meets S exactly once (Penrose 1972 Prop 5.14 / Geroch Prop 6).
- VERDICT for the spec: O'Neill/Geroch timelike-exactly-once form; causal-at-least-
  once becomes a separate theorem node (O'Neill Lemma 14.29 / Wald Prop. 8.3.4);
  NOT causal-exactly-once (Minguzzi acausal convention — nonstandard hypothesis for
  Wald Thm 9.5.1). Expected-false witnesses: null hyperplane {x⁰=x¹} (Chruściel Ex.
  2.9.3), past hyperboloid {t²−|x|²=1, t<0} (Chruściel Ex. 2.9.6; Galloway §5).

## 9. D±, global hyperbolicity

- Wald p. 200 eq. 8.3.1 [VERBATIM]: D⁺(S) via past-inextendible CAUSAL curves (S
  closed achronal in his usage); notes Geroch/Penrose use timelike ("differs
  slightly"); Prop. 8.3.2 [VERBATIM]: timelike version = closure of causal version.
- Minguzzi Def. 3.1 [VERBATIM]: both versions for ARBITRARY S; prefers causal (limit
  curve behavior); Rem. 3.30: D(S) = {p : every inextendible causal curve through p
  meets S} (concatenation). Cor. 3.34 [VERBATIM]: for S closed achronal, D̃(S)=M ⟺
  D(S)=M ⟺ H(S)=∅.
- GH definitional landscape (all [VERBATIM]): Wald p. 201 (∃ Cauchy surface); Leray
  (curve-space compactness); Hawking-Ellis/Chruściel (strong causality + compact
  diamonds); Bernal-Sánchez 2007 (causality suffices); Minguzzi (non-total-
  imprisonment version); Hounnonkpe-Minguzzi 2019 (dim ≥ 3 non-compact: diamonds
  alone) [abstract-level only]. All equivalent for smooth spacetimes — theorems
  apart, not interchangeable spellings.
- Geroch splitting: Thm 4.119 [VERBATIM] (homeomorphism ℝ×S, continuous time
  function); smooth/steep splitting = Bernal-Sánchez 2003/2005/2007 + Müller-Sánchez
  (Seifert 1977 proof incorrect) — smooth splitting NOT needed for Penrose.
- VERDICT: D± with causal curves over arbitrary S (hypotheses live on theorems);
  GH := ∃ Cauchy surface (Wald p. 201); diamond characterization in the
  Bernal-Sánchez-2007 form as a stated equivalence theorem node, both directions deep.

## Unresolved / could-not-verify (freeze-relevant)

1. Wald p. 190 exact wording (differentiable-curve defs, I±/J± defs) — missing from
   the only public scan; soften citations to "Wald §8.1"; mathematical content not in
   doubt; whether J⁺-reflexivity is definitional on p. 190 unverified (p. 200 usage
   requires it).
2. O'Neill definition NUMBERING unverified except Lemma 14.29 and Cor. 14.39 (safe);
   cite O'Neill by page (pp. 47, 54-55, 143-145, 402-403, 415).
3. Chruściel v1 acausal-set formula is self-inconsistent as printed; OUP 2020 book
   version unchecked; do not inherit.
4. Hawking & Ellis not directly consulted (restricted); all H&E claims via verbatim-
   verified secondaries (Wald p. 209 Remark, Minguzzi fn. 4, Chruściel §2.9).
5. Hounnonkpe-Minguzzi 2019 verified at abstract level only.

## Primary links

Minguzzi LRR: doi.org/10.1007/s41114-019-0019-x · M-S: arXiv:gr-qc/0609119 ·
Chruściel: arXiv:1110.6706 · BS2003: arXiv:gr-qc/0306108 · BS2007: arXiv:gr-qc/0611138 ·
Sánchez: arXiv:math/0604265 · Galloway: math.miami.edu/~galloway/vienna-course-notes.pdf ·
arXiv:1204.4080 · Witten arXiv:1901.03928 · Hounnonkpe-Minguzzi arXiv:1908.11701
