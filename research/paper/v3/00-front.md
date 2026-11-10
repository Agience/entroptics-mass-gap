# The Mass Gap of $SU(N)$ Gauge Theory Seen by an Observer of Fixed Physical Resolution

### A reduction of the formalized target to three open statements: the gap side derived from (S) and (M), and the doubling defect proved to vanish on regions off the isotropic line

Ikailo John Sessford, Ikailo Inc., `john@ikailo.com`
ORCID [0009-0002-0150-4027](https://orcid.org/0009-0002-0150-4027)

*Pre-print. 2026-11-10.*

Text CC BY 4.0; code Apache-2.0.

---

> Companion paper to *Entroptics: reading a 2-D signal as a finite optical aperture at its own entropy-matched resolution* [Entroptics]; references of the form §E-3.2 are to that paper. Its frame (an observer is a finite aperture, and what the aperture holds is a count of modes read from the signal's own spectrum) chose which objects are built and which statements are proved; it is a hypothesis of no theorem. Two results are the frame's own: the count of section 3 and the window of sections 4 and 5. For the Wilson field the count bound is reduced (section 3.7) to one fine-scale inequality, whose proof needs renormalization-group control and is open. The reading of the doubling defect as a sum of Rényi-2 entropies is argued, not proved. Every numbered theorem is a declaration of the Lean library `MassGap` (section 11), except Theorem 3.15, which is a declaration of the Lean development of the Entroptics library [S]. The Monte Carlo reads of section 10 are validation only. The mass gap is not proved.

---

## Abstract

We take the frame of the Entroptics paper, an observer as a finite aperture whose mode count is read from the signal's spectrum, as the method for the continuum limit of four-dimensional $SU(N)$ Wilson lattice gauge theory, and use it in two places. On the gap side the theory is read at a window it sets: the doubling defect $D_\beta(w)=16\log Z_\beta(2^w)-\log Z_\beta(2^{w+1})$ of the periodic torus, a finite-size free energy with the bulk cancelled exactly (read, as an argued interpretation, as a weighted sum of Rényi-2 entropies of transfer operators), is held at a fixed value $u_0$ along a coupling tower while the window doubles. On the existence side the observer's screen in a box of fixed physical side is a finite family of modes, and one variance bound with per-mode hypercontractivity gives every even moment through the Rényi count of order ½, with constants free of the box and the zoom, and ½ is the sharp order for the single-reading closure. For the Wilson field itself the count bound is reduced to one fine-scale inequality, which is open.

For $N\ge2$ we prove that the formalized target $\mathrm{CS}(N)$, an Osterwalder–Schrader form of the existence-and-gap statement (separated test functions, a limit along a fixed ultrafilter, no Wightman reconstruction), follows from three open statements: (S), that the defect tends to $0$ along the windows at arbitrarily large $\beta$; (M), that at window couplings arbitrarily close to $0$, along every coupling tower, the measured tensor mass stays in a band of ratio $2$ at a level chosen per tower; and (E), the existence clauses restated along towers. A fixed-level form of (M) is refuted under (S). Without hypotheses we prove the doubling bootstrap, in which one window with $D\le1/1000$ forces $D(w+1)\le250\,D(w)^2$ and a transfer gap uniform in the torus size (a four-dimensional form of the purity bootstrap of OpenAI's $O(3)$ work, of OpenAI's proof of the Haldane gap and of Grover's extensions of it); vanishing on an interval of small $\beta$, at the decoupled end of the anisotropic family and on an explicit strip of mixed couplings that shrinks with $\beta$; box gaps for $SU(2)$ and $SU(3)$ at small coupling; and a list of properties that do not separate $SU(N)$ from $U(1)$. The theorems are formalized in Lean 4. The mass gap is not proved.

## Keywords

lattice gauge theory; Wilson action; Yang–Mills mass gap; finite aperture; Entroptics; Rényi entropy; effective mode count; hypercontractivity; doubling defect; purity bootstrap; transfer operator; reflection positivity; anisotropic lattice; Osterwalder–Schrader axioms; formal verification; Lean

## Mathematics Subject Classification (2020)

Primary 81T25, 81T13. Secondary 82B20, 81T08, 94A17, 60E15, 60B15, 47A10, 68V20.
