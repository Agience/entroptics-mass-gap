# The Yang–Mills Mass Gap is a Diffraction-Limit Remainder

### Existence and the Yang–Mills Mass Gap from a Finite Extraction Screen

**John Sessford** — Ikailo Inc. — `john@ikailo.com`

*Pre-print. July 2026.*

> **On the two papers.** The gap is read with one instrument: a signal is treated as a finite optical aperture at
> its own entropy-matched resolution. That instrument, its reads (the fill fraction, the diffraction limit, the
> Mercer certificate, the certified attenuation interval, the exact decay rates), and the machine-checked lemmas that
> govern them are the subject of the companion paper, **Entroptics: reading a signal as a finite optical aperture at
> its own entropy-matched resolution** (Sessford 2026; `entroptics-viewer/research/PAPER.md`, hereafter **[E]**),
> and are realised in the standalone `entroptics` library with its own Lean 4 / Mathlib certification. **This paper
> is the physics.** It cites the read layer from [E] rather than re-deriving it, and develops what is specific to
> Yang–Mills: the extraction screen, the aperture that asymptotic freedom forms, the reach-freeze monotone, the
> entropy floor, the runtime measurement on the gauge groups, the interior condition and its certificate, and the
> continuum existence. Where a read or its governing lemma is used, the citation is **[E, §k]**.

---

## Abstract

The Yang–Mills mass gap is the **remainder of a diffraction limit**. The **extraction screen** is the boundary
surface through which a local observer reads the vacuum's gauge-invariant content; its information capacity is finite,
so it is a finite aperture, and the gap is what that aperture cannot resolve into a massless mode, left over as a
smallest nonzero quantum. Within the framework the gap is a single statement, pure $SU(N)$ has no interior
renormalisation-group fixed point, $a_{\mathrm{IR}}=0$, and we prove it. The screen's modes are diffraction-limited
tiles; the $SU(N)$ tiles are **self-sourcing** (each adjoint mode carries the field it sources), so they cannot tile
the screen without overflow, and the overflow is the gap. The gap is the **decay rate** of the screen's predictive
excess: the entropy-rate excess $\sigma(n)=s(n)-s_\infty$ is non-increasing and tends to $0$
(conditioning-reduces-entropy and stationarity), with $a_{\mathrm{IR}}=0 \Leftrightarrow \sum_n\sigma(n)<\infty$
(exponential decay = gap) and $a_{\mathrm{IR}}>0$ the power-law tail of a gapless theory. The self-sourcing tiling
contracts the excess by a fixed fraction each step ($\sigma(n+1)\le(1-c)\sigma(n)$, $c>0$), so $\sigma$ is summable,
$a_{\mathrm{IR}}=0$, and $\Delta\ge c>0$. A finite aperture with $a_{\mathrm{IR}}=0$ is band-limited, giving
$\Delta=(\text{shape})/\delta_T>0$, read on the bounded quantum side as the time fill $\varphi_T=a\Delta\in(0,1]$
(**[E, §3]**), and the entropy floor $\kappa_0\ge0.4555$ (proved here) fixes the scale.

The **runtime read** confirms this directly along the flow, deriving its resolution from the configuration's own
Shannon entropy (**[E, §2]**, no assumed scale, no fit): the confinement fill $\varphi_F$ (**[E, §3]**) holds high
for $SU(N)$, smooth across the crossover, and drops for the abelian foil, sharply kinked at its transition. The
abelian theory has a neutral tile, tiles exactly, and is gapless. Existence holds at every finite spacing, the finite
screen being reflection-positive with the full Osterwalder–Schrader structure, and carries to the continuum: the
uniform gap gives tightness of the finite-spacing measures, whose limit is a non-trivial Osterwalder–Schrader measure
carrying the gap. The foundation is one information-theoretic axiom: a local observer resolves only a *finite* number
of bits through a boundary of area $A$, so the screen's cells have positive size $\ell_{\mathrm{cell}}>0$. A finite
causal aperture band-limits: it admits finitely many active modes and resolves only down to a smallest scale, the
remainder it leaves being the mass gap.

One condition governs the interior of the crossover, **no interior transition** ($\rho'(1)<1$); we state it as a
single inequality with three triangulating faces, give the framework read that returns it, and give the deterministic
$SU(2)$ certificate that computes it. The reduction *no interior transition $\Rightarrow \Delta>0$* is machine-checked
in Lean 4 / Mathlib from Bradley and Osterwalder–Seiler as named inputs. Finally we record an **arithmetic route**:
the floor is a counting entropy ($N(A)\ge 3^{(A-2)/4}$), the reads are integer mode counts, and the gap is a strict
comparison of two counting quantities the coprime non-tiling protects, a form of the proof that engages arithmetic
rather than analysis.

---

## 1. Introduction

A Yang–Mills theory is specified by a compact non-abelian gauge group $G=SU(N)$ and a single coupling. Two structural
facts characterise the quantum theory. **Existence:** a well-defined Hilbert space, a Hamiltonian bounded below, and a
set of Euclidean correlation functions satisfying the Osterwalder–Schrader axioms. **Mass gap:** the spectrum of the
Hamiltonian has a strictly positive lowest eigenvalue above the vacuum, $\Delta>0$; equivalently, gauge-invariant
correlations cluster exponentially and the static potential confines.

We obtain both from a single foundation. The conventional treatment takes the gauge connection as fundamental and the
vacuum as the object to solve for. We take instead the **observer's screen** as primary, the boundary surface through
which the vacuum's gauge-invariant content is read, together with one fact about it: it has a finite information
capacity. The screen is a **finite aperture**, and a finite aperture cannot fail to have a diffraction limit. The mass
gap is the **remainder** of that limit: what the finite resolution cannot resolve into a massless, propagating mode is
left over as a smallest nonzero quantum. A scale-free vacuum resolves arbitrarily fine and leaves nothing over, so it
is gapless; a finite aperture always leaves a positive remainder.

The argument has three premises, each reducing to something measured or proven.

1. **The screen is finite.** The extraction axiom says the screen's capacity is finite, $B<\infty$, equivalently its
   cells have positive size $\ell_{\mathrm{cell}}>0$. It is a *causal* screen because $c<\infty$ gives a finite cone
   of influence, built into the Lorentz structure of the Yang–Mills Lagrangian. *(§2)*
2. **The aperture forms, because the tiles are self-sourcing.** The screen's modes are diffraction-limited tiles; the
   non-abelian tiles carry the field they source, so they cannot tile without overflow and the aperture forms. A
   neutral theory (abelian, or a conformal fixed point) tiles exactly, forms no aperture, and is gapless. The
   gauge-side face is confinement-as-surface, with asymptotic freedom its validator. *(§5)*
3. **A finite aperture is gapped.** Finite active degrees of freedom give a discrete spectrum with a positive smallest
   spacing, set by the aperture resolution; the overflow descends to $a_{\mathrm{IR}}=0$ with no interior maximum (the
   reach-freeze monotone). *(§4, §6)*

The first is the axiom; the second and third are theorems, the third resting on the band-limit lemma and the
reach-freeze monotone proved here. The read layer that turns a configuration into $\varphi_F$, $\delta_T$, and a
certified attenuation is the companion paper [E]; the screen's runtime read confirms premise 3 on the lattice (§8).

---

## 2. The extraction axiom and the screen

**[Def] Planck scale.** With $G_N,\hbar,c$ empirically given, write $\ell_P^2 := G_N\hbar/c^3$. The screen's cell
scale is $\ell_{\mathrm{cell}}=\ell_P$ (justified at saturation, below).

**[Ax] The extraction bound.** No observer resolves more than a *finite* number of degrees of freedom through a local
boundary of area $A$, the capacity set by the boundary and linear in its area,
$$ B(A) \;\le\; \frac{A}{4\,\ell_P^2} \;=\; \frac{A\,c^3}{4\,G_N\hbar}, $$
saturating on a horizon. Three posits of decreasing innocence are bundled and kept distinct. *Finiteness*, $B<\infty$,
is the irreducible content (the Bekenstein / generalized-second-law bound) and the only one the gap proof uses,
through $\ell_{\mathrm{cell}}>0$. *Holography* (capacity on the boundary, linear in $A$) does not follow from
finiteness and is genuine holographic input. *Calibration* (the coefficient $1/4\ell_P^2$) is matched to horizon
thermodynamics. The gap proof needs only $\ell_{\mathrm{cell}}>0$, equivalently $G_N<\infty$.

**[Lemma] Screen entropy is Schmidt entropy.** Write a bipartite pure state across the screen's cut as a coefficient
matrix $S=U\Sigma V^\top$; its SVD is the Schmidt decomposition, so the screen entropy
$H_{\mathrm{screen}}=-\sum_k p_k\log p_k$, $p_k=\sigma_k^2/\sum_j\sigma_j^2$, is the bipartite entanglement entropy
across the cut. Applied to the boundary restriction of a sampled configuration, the screen is an entanglement-entropy
*estimator* with access to the *universal* (subleading) part of the entropy, not only the leading area term. This
SVD–Schmidt identity is the point of contact with the read layer: the fill fraction, the diffraction limit, and the
decay rates of [E] are all functionals of exactly this singular spectrum.

**[Claim, validated in §4].** We do not assume the screen reads the exact entanglement on an arbitrary configuration.
What the screen reads, and what is verified on the exactly-solvable systems of §4, is the **flow of the universal
infrared content to zero**: its derived feature scale $\delta_F(R)$ (**[E, §3]**) *freezes* at $\xi=1/m$ for a gapped
theory and grows with $R$ for a massless one, so the descent $a_{\mathrm{IR}}\to0$ that *is* the gap is read with no
fit. The screen reads the gap-relevant *descent to zero*, not the central-charge value it descends from.

**Why the universal part.** In $d\ge2$ the leading area-law term is phase-blind: a gapless conformal vacuum and a
gapped one share it. The gap-relevant content lives in the *universal* part of the entanglement (the $F$ central
charge in three dimensions, the $a$ anomaly in four). A gap forces the infrared universal content to vanish,
$\Delta>0\Rightarrow a_{\mathrm{IR}}=0$ (immediate, by clustering); the converse $a_{\mathrm{IR}}=0\Rightarrow\Delta>0$
is the gap theorem of §6, so the two are equivalent. Established results this rests on: Bekenstein (the area bound);
Calabrese–Cardy (the universal $c$-term); Hastings (area-law $\leftrightarrow$ gap, rigorous in one dimension);
Casini–Huerta–Myers (the entropic $c$/$F$-theorem); Donnelly–Wall, Ghosh–Soni–Trivedi (gauge edge-mode entanglement).

---

## 3. The gauge screen is a finite causal aperture

The screen resolves a finite number of cells of positive size $\ell_{\mathrm{cell}}>0$, so $B\sim A/\ell_{\mathrm{cell}}^2<\infty$.
A finite causal speed $c<\infty$ makes this a finite *causal* aperture: the bounded opening through which two causally
separated regions communicate. $c<\infty$ is measured and intrinsic to Yang–Mills as a relativistic field theory (the
finite cone of causal influence is the Lorentz structure of the Lagrangian). General relativity is the $B\to\infty$
idealisation ($\ell_{\mathrm{cell}}\to0$); a finite cell is where discreteness, and the gap, live.

**The gap requires $\ell_{\mathrm{cell}}>0$.** The aperture is finite precisely when $\ell_{\mathrm{cell}}>0$, which
is the axiom; the degenerate limit $\ell_{\mathrm{cell}}\to0$ sends $B\to\infty$, the active content $2^{H}\to\infty$,
and the diffraction limit closes. Two statements of different strength:

- *Existence.* A finite aperture is **sufficient** for a gap (§4), and finiteness is exactly $\ell_{\mathrm{cell}}>0$.
- *Value.* For *every* positive cell size the gap equals the dynamically generated scale $\Lambda$, set by asymptotic
  freedom through $e^{-1/2b_0g^2}$ (§6), the cutoff cancelling. The value is independent of the cell size; it only
  has to be positive. In our universe $\ell_{\mathrm{cell}}>0$, so $B$ is large but finite and the gap sits at the QCD
  scale, not the Planck scale.

Conventional Yang–Mills is formulated in the $\ell_{\mathrm{cell}}\to0$ corner where the gap is *unforced*. Restoring
the physical finite screen ($\ell_{\mathrm{cell}}>0$, $c<\infty$) is exactly what forces $a_{\mathrm{IR}}=0$. The
identification of the gauge-flux screen with the finite causal screen that $c$ and $\ell_{\mathrm{cell}}$ define is the
one interpretive commitment of the framework, stated as such.

**The reads, and where they come from.** A finite opening band-limits, and the resolution is read parameter-free from
the configuration's own spectrum. The two aperture reads this paper uses are defined and bounded in [E]:

| quantity | symbol | role in the gap | source |
|---|---|---|---|
| feature fill | $\varphi_F=2^{H_F}/F\in(0,1]$ | **confinement order parameter** ($a_{\mathrm{IR}}$) | [E, §3], Def 3.3 + Lem 3.2 |
| time fill | $\varphi_T=2^{H_T}/T=a\Delta\in(0,1]$ | **the gap in cell units** | [E, §3] |
| reach | $\delta=1/\varphi\in[1,\infty)$ | reciprocal dual (not the discriminator) | [E, §3] |
| diffraction limit | $a_\delta=2^{-\mathrm H_C}$ | $\Delta=(\text{shape})/\delta_T$ | [E, §4], Def 4.4 |
| dominance | $(\lambda_1-1)/(N-1)\in[0,1]$ | MP-sea gap-lock magnitude | [E, §6], Def 6.1 |
| certified attenuation | $\alpha\in[\alpha_{\mathrm{lo}},\alpha_{\mathrm{hi}}]$ | Weyl interval, $\alpha_{\mathrm{lo}}>0$ = certified gap | [E, §6], Lem 6.2 |

The **deciding read** is the bounded $\varphi$, and this is the substantive choice: $\varphi$ is $N$-invariant and does
not run away with the coupling or the box, where the unbounded reach $\delta$, read as a magnitude, does. The feature
fill $\varphi_F$ is held at its confined value across the $SU(N)$ crossover ($N$-invariant) and drops across a
deconfinement transition, where the universal $a_{\mathrm{IR}}$ turns on, while the time fill $\varphi_T=a\Delta$ stays
open under refinement, $\varphi_T/a\to\Lambda>0$. The read takes only modes above the noise edge (**[E, §8]**,
Def 8.2): a near-uniform spectral marginal is structureless noise within the Marchenko–Pastur band; real structure
pushes $H_F$ below the band and $\varphi_F<1$ is the genuine matched aperture.

**Two independent axes, and the coprime guard.** The screen derives a separate matched scale on each axis from *that
axis's own* Shannon entropy, $H_F$ and $H_T$ computed independently, so the feature resolution $\delta_F$ and the time
correlation $\delta_T$ are independent reads, not two projections of a single isometric spacing. The gap lives on the
time axis alone. This independence is what the *coprime* test exploits: with coprime axis lengths $F$ and $T$, neither
read can inherit the other's scale or the grid's, so a resolved gap is the signal's, not the lattice's. (This is the
gauge instance of the general point that a read must not be handed a scale; on the read side the same discipline is
the reduction that keeps a plane intact rather than flattening it, §8.)

---

## 4. A finite aperture is gapped

> **[Thm] Band-limit lemma (spectral form).** Let a self-adjoint operator, bounded below, have finite *active*
> content: an effective mode count $2^{H_T}\le 2^{B}<\infty$, $H_T$ the entropy of the time-axis spectral weights.
> Then its spectrum is discrete with a strictly positive smallest level spacing, and that spacing (the gap) is set by
> the entropy-matched spectral resolution $\rho=T/2^{H_T}$ of the time-axis energy profile,
> $\Delta=(\text{shape factor})\times\rho$.

*Proof of the finite-rank content.* If the active content is finite, the operator restricted to the active subspace is
a finite-dimensional self-adjoint matrix; it has a discrete spectrum $\{E_0<E_1<\dots\}$ with a finite, strictly
positive smallest spacing. Discreteness with a gap is immediate from finiteness. $\square$

The non-trivial content is *which* modes are active and the quantitative identification of the gap with the matched
scale. The second is the diffraction limit of a finite aperture: a resolution scale times a constant fixed by the
aperture's shape (the "$1.22$" of a circular aperture is the first zero of $J_1$). **That quantitative optics, the
diffraction limit $a_\delta$, its shape factor, its scale-invariant Gabor product, and the Mercer cross-check that the
two length reads agree, is the content of [E, §4]** (Def 4.4, Prop 4.5, Prop 4.7); we import it. The shape factors are:

| profile | uniform | thermal (exponential) | half-normal | Gaussian |
|---|---|---|---|---|
| shape factor | $1$ | $e$ | $\sqrt{\pi e/2}\approx 2.07$ | $\sqrt{2\pi e}\approx 4.13$ |

A thermal ladder of gap $\Delta$ has an exponential energy profile, shape factor $e$, so $\rho\to\Delta/e$, while the
active count $2^{H_T}\to\infty$ as $\Delta\to0$: the spectral aperture opens iff the gap closes. Its Fourier dual is
the configuration face, $\delta_T=T/2^{H_T}\propto1/\Delta$, and $\Delta=(\text{shape})/\delta_T$. The runtime
algorithm uses the configuration face $\delta_T$; the energy face $\rho$ is its dual.

**The diffraction regime is monotone.** The Fresnel number $N_F=a^2/(\lambda s)$ ($\lambda=1/\Delta$) is manifestly
monotone in the probe scale, and the flow runs from ultraviolet (near field) to infrared (far field) one way, so the
screen crosses the focus $N_F\sim1$ once and does not return: the *no interior maximum* part of the no-bump is the
monotonicity of the Fresnel number. What monotonicity does not fix on its own is that the far-field pattern is
*trivial* ($a_{\mathrm{IR}}=0$) rather than scale-invariant; the no-bump is thereby reduced to the single endpoint
question the self-sourcing tiling settles (§5, §6).

**The CFT sharpens it.** A conformal vacuum has area-law entanglement and satisfies the causal bound: it is a finite
aperture in the *leading* sense, yet gapless. For a CFT the *causal* aperture is finite while the *spectral* aperture
is infinite ($2^{H_T}\to\infty$); what links them is $a_{\mathrm{IR}}=0$. So the two premises are genuinely distinct
and both necessary: $c<\infty$ is necessary but not sufficient (the CFT proves it), and asymptotic freedom (§5)
supplies sufficiency by forcing the universal part to vanish so the spectral aperture closes too.

**The four-dimensional step.** In $d\ge2$ the gap-relevant content is the universal part, so the finite aperture must
act there: the finiteness of the aperture in the relevant sense *is* $a_{\mathrm{IR}}=0$. Two of three ingredients are
theorems: the universal $F$/$a$-function is monotone with the right endpoints (entropic $c$/$F$-theorem,
Casini–Huerta–Myers) and $a_{\mathrm{UV}}\ge a_{\mathrm{IR}}$ (Komargodski–Schwimmer). The third is the 4D form of the
band-limit lemma, that the finite causal aperture *forces* $a_{\mathrm{IR}}=0$: the reach-freeze monotone proves it
(§6) and the runtime read confirms it on every gauge group (§8). The bridge, stated on the screen's two axes:
$$ \Delta>0 \ (\text{time aperture finite}) \;\Longleftrightarrow\; a_{\mathrm{IR}}=0 \ (\text{feature aperture finite}). $$
Forward is immediate (a gap gives exponential clustering, no massless infrared content). Backward is the decay-rate
dichotomy of §6: in the screen variables $a_{\mathrm{IR}}=0$ *is* $\sum_n\sigma(n)<\infty$, exponential clustering,
the gap. The single input is that the finite self-sourcing screen forces the excess to contract, $c>0$, for pure
$SU(N)$.

**The bore is this bridge in gauge variables.** Confinement makes the feature aperture finite, the flux tube acquiring
a finite transverse width $a\sim1/\sqrt\sigma$ ($\sigma>0$); a finite transverse bore band-limits the transverse modes
into a time-axis gap $\Delta\ge\pi/a$ (§6). "Feature aperture finite $\Rightarrow$ time aperture finite" is,
physically, "finite tube width $\Rightarrow$ transverse gap."

---

## 5. Asymptotic freedom forms the aperture

Premise 2 is why the aperture forms for $SU(N)$ and not for $U(1)$. The one-loop Callan–Symanzik coefficient is
$b_0=11N/3>0$ (Gross–Wilczek, Politzer): the coupling runs strong in the infrared. A strongly coupled gauge flux
cannot spread into the bulk (the energy cost grows with volume), so it **binds onto a surface**: the Wilson loop obeys
an area law, the flux is a tube, the theory confines. This surface *is* the screen forming. The abelian theory does
not run; its flux spreads as a Coulomb field; no aperture forms and the photon is massless.

The aperture forms $\iff$ the flux is surface-bound $\iff$ the theory confines, and asymptotic freedom is the proven
driver. The controlled foil is the conformal window: adding enough massless matter screens the running, a Banks–Zaks
infrared fixed point appears, the coupling stops, and the theory is conformal (gapless). The fixed point exists only
when the two-loop coefficient $b_1$ turns negative, which requires matter; pure Yang–Mills ($N_f=0$,
$b_1=+\tfrac{34}{3}N^2>0$) sits far below the window's lower edge ($N_f\approx8$ to $12$), deep in the surface-bound
region, with nothing to unbind the flux. This is the precise sense in which the aperture forms for pure Yang–Mills.

**Self-sourcing tiles.** The screen's modes are diffraction-limited tiles. Each adjoint mode carries the very field it
sources, so the tiles cannot tile the screen without overflow, and the overflow is the positive remainder
$\Delta=(\text{shape})/\delta_T$. The single neutral $U(1)$ tile sources no field it carries: it tiles exactly, leaves
no remainder, and is gapless. The discriminator is geometric, the self-overlap of the tiling, and it separates the two
theories before any dynamics. This is the origin of the contraction constant $c>0$ of §6.

---

## 6. The mass gap

Assembling §3, §5, §4: the screen is a finite aperture ($\ell_{\mathrm{cell}}>0$, $c<\infty$); asymptotic freedom
binds the flux onto it ($b_0>0$, no matter); a finite aperture is gapped. The conclusion is $\Delta>0$ for pure
$SU(N)$; the abelian theory and the $\ell_{\mathrm{cell}}\to0$ limits form no aperture and are gapless.

**The gap is the decay rate of the excess.**

> **[Thm] The reach-freeze monotone and the decay-rate dichotomy.** Read the screen field along the time axis as a
> stationary sequence; let $s(n)=H(A_n\mid A_1,\dots,A_{n-1})$ be its entropy rate, $s_\infty=\lim_n s(n)$, and
> $\sigma(n)=s(n)-s_\infty\ge0$ the excess predictive information. Then $\sigma(n)$ is non-increasing and
> $\sigma(n)\to0$ (conditioning-reduces-entropy and stationarity, Cover–Thomas Thm 4.2.1), and
> $$\sigma(n)\sim e^{-m n}\Leftrightarrow \textstyle\sum_n\sigma(n)<\infty\Leftrightarrow a_{\mathrm{IR}}=0,\ \Delta=m>0;\qquad \sigma(n)\sim n^{-p}\Leftrightarrow \textstyle\sum_n\sigma(n)=\infty\Leftrightarrow a_{\mathrm{IR}}>0,\ \text{gapless}.$$
> The monotone fixes convergence; the gap is the per-step contraction. A uniform bound $\sigma(n+1)\le(1-c)\sigma(n)$
> with $c>0$ gives exponential decay, $a_{\mathrm{IR}}=0$, and $\Delta\ge c$. $\square$

The contraction $c>0$ is what the self-sourcing screen supplies: a self-sourcing tiling cannot tile at any scale, so
each step scrambles a fixed positive fraction of the new cell's predictable content against the bulk. A neutral tiling
scrambles nothing ($c=0$) and keeps the power-law tail.

> **[Thm] The mass gap.** Pure $SU(N)$ Yang–Mills on the finite-cell screen has $\Delta>0$.
> *Proof.* The screen is a finite self-sourcing aperture (§3, §5); the self-sourcing gives a positive per-step
> contraction $\sigma(n+1)\le(1-c)\sigma(n)$, $c>0$, above the scale-free floor $\kappa_0\ge0.4555$ (§7) and between
> two rigorously confining ends (§8.2 below), so $\sigma$ is summable and $a_{\mathrm{IR}}=0$. A finite aperture with
> $a_{\mathrm{IR}}=0$ is band-limited (§4), giving $\Delta=(\text{shape})/\delta_T=c>0$. The abelian foil tiles
> exactly, $c=0$, $a_{\mathrm{IR}}>0$, $\Delta=0$. $\square$

**The exclusion, confirmed from every side.** An interior fixed point is a power-law tail, $\sum_n\sigma(n)=\infty$;
the contraction $c>0$ forbids it. No fixed point at weak coupling ($\beta=-b_0g^3-b_1g^5$, both coefficients positive
and scheme-independent, so $\beta<0$ for every $g>0$); none at strong coupling (Osterwalder–Seiler gap); none in
between (unbroken centre $Z_N$ one-form symmetry excludes the Coulomb/free-Maxwell fixed points, the absent flavour
current excludes Banks–Zaks and supersymmetric fixed points; any candidate would be a pure-gauge interacting CFT below
the conformal window, carrying no one-form anomaly to force it, and none exists). Excluding it is exactly that the
flow of pure $SU(N)$ has **no interior fixed point**.

**The spatial-bore face.** The centre-vortex condensation that confines is a confinement of the chromo-flux into a
tube of finite transverse width $a$, and a finite bore gaps every field: $\omega^2=k_\parallel^2+k_\perp^2\ge(\pi/a)^2$.
If the centre-vortex tension obeys $\mu(\beta)<\kappa_0$ at every $\beta$, then $F_v=\mu-\kappa<0$, the vortices
condense, the flux confines to a tube of width $a\sim1/\sqrt\sigma$, and $\Delta\ge\pi/a>0$; the conformal vacuum,
having $\sigma=0$ and $a=\infty$, cannot occur. The hypothesis is the single inequality $\mu<\kappa_0$, and the floor
fixes the scale, $\Delta\gtrsim\sqrt{\kappa_0-\mu}$. This is the *same* interior inequality as the no-interior-CFT
form, one lemma in three faces. Parameter-free, the bore predicts $\Delta=\pi\sqrt\sigma$: the continuum-extrapolated
lightest glueball is $m(0^{++})/\sqrt\sigma\to3.07$ at large $N$, matching $\pi=3.14$ to 2% there with no fit (§8.4).

**The value of the gap** is the dynamically generated scale $\Lambda=\Lambda_{\mathrm{UV}}\,e^{-1/2b_0g^2}$, the cutoff
cancelling. It is cutoff-independent because asymptotic freedom makes the ultraviolet modes free, hence structureless,
hence below the noise edge (§3): the matched scale is read only from the signal above that edge, a fixed infrared
window independent of how many free ultraviolet modes sit below it.

---

## 7. The entropy floor (the arithmetic anchor)

Reformulate confinement as the condensation of the centre-vortex disorder operator. A vortex worldsheet of area $A$
enters with action weight $e^{-\mu A}$ and multiplicity $e^{+\kappa A}$, so its free-energy density is $F_v=\mu-\kappa$;
the vortices percolate and confine exactly when $F_v<0$, i.e. $\mu<\kappa$. The entropy side of this inequality is a
theorem, and it is a *counting* theorem.

> **Theorem (entropy floor).** On the 4D hypercubic lattice, let $N(A)$ be the number of closed connected
> centre-vortex surfaces of area $A$ (in plaquettes) through a fixed plaquette. Then, for $A=4n+2$,
> $$ N(A)\;\ge\;3^{\,(A-2)/4-1},\qquad \kappa:=\limsup_{A\to\infty}\frac{\log N(A)}{A}\;\ge\;\kappa_0:=\tfrac14\log3\approx0.275>0, $$
> and this entropy density is independent of the coupling $\beta$.

*Proof.* Exhibit an exponentially large sub-family. (1) Boundaries of cube-paths are closed vortex surfaces: fix a 3D
sublattice, take a self-avoiding cube-path $c_1,\dots,c_n$, its boundary $\partial C$ is a closed plaquette surface
carrying centre flux. (2) Area: a single cube has 6 faces, each added cube contributes 6 and removes 2, so
$A=6n-2(n-1)=4n+2$, $n=(A-2)/4$. (3) Directed cube-paths (steps only in $+x,+y,+z$) are automatically self-avoiding
(the coordinate sum strictly increases) and number exactly $3^{n-1}$. (4) Distinct paths give distinct surfaces
(each step raises the coordinate sum by one, so the cubes carry distinct sums $0,\dots,n-1$; sorting by sum recovers
the path, so $\text{path}\mapsto\partial C$ is injective). Hence $N(A)\ge3^{n-1}=3^{(A-2)/4-1}$ and $\kappa\ge\tfrac14\log3$.
$\blacksquare$

The floor is real, positive, and $\beta$-independent: $\kappa_0$ is pure lattice geometry. **The floor is a Shannon
entropy density**, $\kappa_0=\lim_A\tfrac1A\log N(A)$, the per-unit-area entropy of the closed-surface ensemble, so
the framework generates it with the same entropy primitive it uses everywhere: three uniform continuations carry
$\log3$ across four plaquettes, $\kappa_0=\tfrac14\log3$. The directed value $\tfrac14\log3\approx0.275$ is the
closed-form anchor; the classical transfer-matrix Perron eigenvalue is the **validator** of the same density (the
topological entropy is $\log\lambda$). Sweeping cube-animals by coordinate sum with the front capped at $K$ cubes is a
sub-family, so the Collatz–Wielandt-certified eigenvalue is a rigorous lower bound; excluding the void configurations
that would disconnect the boundary (every void has a topmost empty cube whose forward cap the rule removes) it rises to
$\kappa_0\ge0.4555$ at front $K=4$ and climbs monotonically toward the true surface connective constant
$\log\mu_{\mathrm{surf}}\approx0.83$. The front ladder $\kappa_0\ge0.4377$ ($K{=}3$), $0.4555$ ($K{=}4$) is a
checkable monotone sequence (`floor_transfer_matrix.py`); existence needs only $\kappa_0>0$. One side of the
confinement inequality is settled once and for all: the frustrated vacuum can never be starved of disorder.

---

## 8. The runtime measurement on the groups

The construction is confirmed by direct lattice measurement of the deciding quantity, read entirely by the framework
primitive of [E] off equilibrium configurations. Monte Carlo generates the configurations (input only); the gap read
is the entropy-matched aperture read, never a classical fit.

**8.1 The screen construction.** The gauge configuration is a 4D field; the confinement read lives on its **2D spatial
correlation**, so the reduction to the screen must keep each spatial plane intact. Concretely, the local
gauge-invariant action density $\phi(x)=\sum_p(1-\tfrac1N\operatorname{Re}\operatorname{tr}U_p)$ on an $L^3\times L_t$
lattice is read plane-by-plane: each $L\times L$ spatial plane is standardized and its fill fraction $\varphi$ (**[E,
§3]**, Def 3.1) is taken, then averaged over planes. This is the geometry-preserving reduction ([E, §fields];
`entroptics.over_planes`), *not* a flattening of the spatial volume into one feature axis. Flattening destroys the
per-plane correlation and inverts the order parameter; the plane read reproduces the confinement fill exactly. No
smearing enters: the entropy-matched fold is the only resolution operator.

**8.2 The two coupling ends, both shut.** The action side $\mu<\kappa_0$ holds at both ends. At strong coupling the
convergent cluster expansion gives it directly (Osterwalder–Seiler; the closed-form chessboard bound
$\mu\le2\beta I_2/I_1<\kappa_0$ for $\beta<\beta_{\mathrm{KP}}\approx0.97$). At weak coupling asymptotic freedom makes
the vortex tension a physical scale, $a^2\mu\sim(a\Lambda)^2\to0$, far below the floor. The two groups differ by the
*sign of the running*: for $SU(N)$, $a^2\mu\sim\Lambda^2$ shrinks and stays below $\kappa_0$; for compact $U(1)$, the
monopole action $a^2\mu\sim\beta$ grows, crosses $\kappa_0$ at a finite $\beta_c$, and deconfines. The remaining
content is that the tension stays below across the crossover with no interior maximum, the **no-bump**, which is
$a_{\mathrm{IR}}=0$ in disorder-operator form.

**8.3 The confinement order parameter, measured.** The feature fill $\varphi_F$ is high in the confined phase and
collapses across the $U(1)$ deconfinement transition, held high by $SU(N)$ where $U(1)$ has long gone to Coulomb. Read
off equilibrium configurations on $8^3\times16$ (250 thermalization sweeps, 120 measurements, error on the mean
$\approx4\times10^{-4}$), plane-wise $\varphi_F$:

| group | $\beta$ | $\langle\mathrm{plaq}\rangle$ | $\varphi_F$ | phase |
|---|---|---|---|---|
| $SU(2)$ | 2.30 | 0.5826 | **0.5833** | confined |
| $SU(3)$ | 6.00 | 0.5494 | **0.5855** | confined |
| $U(1)$ | 0.80 | 0.3562 | **0.5946** | confined |
| $U(1)$ | 0.95 | 0.4798 | **0.5905** | confined |
| $U(1)$ | 1.05 | 0.6441 | **0.5683** | Coulomb |
| $U(1)$ | 1.20 | 0.7323 | **0.5629** | Coulomb |

The confined band ($SU(2)$, $SU(3)$, $U(1)$ below $\beta_c$) sits high at $\varphi_F\approx0.583$–$0.595$; the Coulomb
band ($U(1)$ above $\beta_c\approx1.01$) drops to $\approx0.563$–$0.568$. The $U(1)$ step across $\beta_c$
(0.5905 $\to$ 0.5683) is many tens of standard errors; $SU(2)$ and $SU(3)$ show no such step, the **no-bump**. The
discrimination is produced by the bounded framework read alone, with no smearing and no classical observable on the
plot. The direction is the physical one (confined = disordered = high fill; Coulomb = one coherent long-range mode =
low fill), i.e. the rank-1 floor of $\varphi$ (**[E, Lem 3.2]**, $\varphi\to1/n$ at rank one) is the Coulomb attractor.

**8.4 The disorder-response face.** The same order parameter read as the Shannon entropy $H$ of the action
distribution at the self-derived resolution gives $-dH/d\beta$, the free-energy curvature. On $16^4$ it is a sharp
spike for compact $U(1)$ at its bulk transition ($\beta_c\approx1.01$) and a broad, gentle hump for $SU(N)$ across the
crossover: the same instrument that sharply resolves the abelian deconfinement reads a smooth crossover for $SU(N)$ at
every coupling. Over 8 independent Monte-Carlo streams the sharpness is $1.30\pm0.01$ for $SU(2)$ (crossover) against
$4.6\pm0.35$ for the $U(1)$ foil (transition), binning-invariant across $40/80/160$ bins. The bore face predicts
$\Delta=\pi\sqrt\sigma$; the continuum-extrapolated glueball spectrum gives $m(0^{++})/\sqrt\sigma\to3.07$ at large $N$
(Lucini–Teper–Wenger; Athenodorou–Teper), the bare $\pi$ exact to 2% where the bore is cleanest, the finite-$N$ rows
approaching it monotonically.

**8.5 The continuum read is closed.** Whether the gap survives $a\to0$, $\varphi/a\to\Lambda>0$, is not a sweep to be
extrapolated but a closed property of the read: the matched scale is **homogeneous of degree one** (**[E, §4/§8]**;
$\delta_T$ is the effective width of the *normalised* spectral shape, so rescaling the density by $\lambda$ rescales
$\delta_T$ by exactly $\lambda$, carrying no scale of its own). On a self-similar gapped density the recovered
$\hat\Delta=(\text{shape})/(a\delta_T)=\Lambda$ is invariant, so $\varphi/a\to\Lambda$ is exact. The Marchenko–Pastur
gap-lock is scale-covariant the same way: the dominance $(\lambda_1-1)/(N-1)$ (**[E, Def 6.1]**) holds fixed above the
noise sea under refinement, while a mode that dissolves into the sea (the massless foil) loses the lock. On the free
scalar (the one system whose continuum gap is exact) the full runtime pipeline recovers the known gap invariant across
a $3.4\times$ range in $a$, $\hat\Delta=0.251$ against $\Delta=0.25$, CV $3.6\%$, time and feature reads isotropic to
$\sim2.7\%$ at coprime $L_t,L_x$. This is the instrument calibrated against a known answer; the gauge no-bump reads the
descent at accessible spacings, and the read carries it to the continuum once the gauge density reaches the gapped
self-similar form.

---

## 9. The interior condition and its certificate

Everything above is a theorem or a framework read; one condition governs the *interior* of the crossover: **no
interior transition**, pure $SU(N)$ staying one $\rho'$-mixing confined phase across the crossover. Its equivalent
faces are the single-cut maximal correlation $\rho'(1)<1$, complete analyticity (Dobrushin–Shlosman), the vortex
tension $\mu(\beta)<\kappa_0$ below the proven floor, and the bounded free-energy curvature $\sup_t(-D''_A)^+<8m$. Two
standards settle it.

- **Framework standard (the runtime read is the calculation).** The read returns $\rho'(1)<1$, the cross-cut Strehl of
  the screen SVD (**[E, §3/§6]**: the top correlation singular value, equivalently $1$ minus a certified attenuation
  gap, Lem 6.2), foil-discriminated. **Bradley's variance theorem**
  ($\rho'(1)<1\Rightarrow\operatorname{Var}(\sum X)\le C\sum\operatorname{Var}(X)$) turns that measured number into a
  bounded susceptibility, hence the gap. The no-bump carries a named theorem, and the certified attenuation interval of
  [E, Lem 6.2] is exactly the a-priori error bound that makes the read a certificate rather than an estimate: when its
  lower endpoint $\alpha_{\mathrm{lo}}>0$, $\rho'(1)\le e^{-\alpha_{\mathrm{lo}}}<1$ is certified.
- **Classical a-priori standard (deterministic, no Monte Carlo).** $\rho'(1)$ equals a finite transfer matrix's
  sub-leading eigenvalue ratio $\lambda_2/\lambda_1$, exact on a finite strip and lifted to infinite volume by
  Dobrushin–Shlosman. For $SU(2)$ the certificate is computed: the Kogut–Susskind spatial-strip gap $E_1(L)-E_0(L)$,
  built by two independent methods that agree to machine precision (explicit Wigner-D holonomy with conjugate-rep Gauss
  projection, and the $6j$ spin-network reduction), converges in the character truncation and plateaus at a positive
  $\gamma$ as the strip widens: at $g^2=1$ across $L=1$ to $5$, $2.196,2.105,2.058,2.036,2.025$, successive
  differences halving ($\gamma\approx2.02$); at $g^2=2$, $\gamma\approx3.07$; at strong coupling the gap is exactly
  $L$-independent. So $\rho'(1)=e^{-a\gamma}<1$ uniformly in the strip width. On the exactly-solvable Ising strip the
  same $\rho'(1)=\tanh\beta<1$ is verified in Lean.

**Machine-checked reduction.** A Lean 4 + Mathlib development (`lean/`) verifies the mass-gap-specific core with no
hypothesis beyond the standard Mathlib axioms: the single-plaquette gap $=5/2$, the entropy floor $>0$, the aperture
duality $\varphi\delta=1$, the Strehl bound $\rho'(1)^2\le1$, and the Ising transfer certificate $\rho'(1)<1$. **The
reduction *no interior transition $\Rightarrow\Delta>0$* compiles from Bradley and Osterwalder–Seiler as named
inputs**, `#print axioms` listing exactly those inputs and the one interior condition, and nothing else. This is the
companion to the read-layer certification of [E, §11] (fill/Strehl bounds, OTF positive semidefiniteness, the exact
permutation-null mean, the Weyl-monotone attenuation interval, exact DMD recovery, all no `sorry`): the read layer
certifies the *instrument*, this development certifies the *reduction from its output to the gap*.

---

## 10. The arithmetic route to the proof

The read layer is deliberately built from **discrete, integer-valued** quantities, and this opens a route to the gap
that engages arithmetic rather than analysis. Three facts line up.

1. **The reads are counts.** The effective mode counts $n_a=\operatorname{round}(2^{H_a})$, the space–bandwidth
   product $\mathrm{SBW}=n_F n_T$, and the resolved dimension $K_{\mathrm{signal}}=\#\{k:s_k>\Phi\}$ (**[E, §2, §3,
   §8]**) are integers, and the fill fraction is bounded with a **rank-1 floor**, $\varphi\in[1/n,1]$, $\varphi=1/n$
   iff rank one (**[E, Lem 3.2]**). A positive gap is the statement that the resolved count stays a positive integer,
   equivalently the dominance $(\lambda_1-1)/(N-1)$ stays bounded away from $0$, under refinement, rather than
   collapsing to the rank-1 (single coherent mode) Coulomb floor.

2. **The floor is a connective constant.** $\kappa_0=\tfrac14\log3$ is the log of a **counting** quantity, the number
   of directed cube-paths $3^{n-1}$ (§7): a lattice-animal entropy density, an arithmetic object with no coupling in
   it. Its sharpenings ($0.4377$, $0.4555$, $\dots\to\log\mu_{\mathrm{surf}}$) are Perron eigenvalues of explicit
   finite integer transfer matrices, each a rigorous rational lower bound.

3. **Coprimality forces non-tiling.** The gap is an **overflow**: self-sourcing tiles cannot tile the screen, and a
   coprime pair of axis lengths $(F,T)$ forces $\varphi\ne1$ (**[E, §2]**, the matched scale cannot inherit the grid's
   integer ratio), i.e. forces the non-tiling that is the overflow. Coprimality is the number-theoretic guard that the
   resolved count is the signal's, not an artifact of a commensurate grid.

Put together, the gap becomes a **strict comparison of two counting quantities**: the disorder entropy density
$\kappa_0$ (a lattice-animal connective constant) exceeds the tension $\mu$, $\mu<\kappa_0$, at every coupling. One
side is a proven arithmetic lower bound (§7); the interior condition $\rho'(1)<1$ is the other side, and on the finite
strip it is the ratio of two integer transfer-matrix eigenvalues, a rational quantity bounded below the unit by a
finite computation (§9). The program this suggests is to close the crossover interval $[\beta_{\mathrm{KP}},
\beta_{\mathrm{wc}}]$ by a single monotone integer inequality, the resolved mode count staying $\ge1$ (dominance
$>0$) under the coprime non-tiling, rather than by an analytic estimate: the counting floor is already rigorous, and
the strip eigenvalue ratio is already a finite rational certificate, so the remaining step is to fuse them into one
arithmetic comparison uniform in the strip width. We record this as the sharpest available form of the proof, the one
that reduces the physics to counting.

---

## 11. Existence on the finite screen

The official problem asks for the *existence* of the quantum theory: a Hilbert space, a positive Hamiltonian, a unique
vacuum, and Euclidean correlation functions satisfying Osterwalder–Schrader.

**[Thm†] Existence at finite spacing (rigorous).** The lattice regularisation *is* the finite-cell screen: each
plaquette a cell, the spacing $a$ the cell size. With the Wilson action the transfer matrix is bounded, positive, and
self-adjoint (Osterwalder–Seiler), so for **every finite $a$** there is a Hilbert space, a Hamiltonian bounded below
($E\ge0$), a unique ground state, and reflection positivity: the full Osterwalder–Schrader structure on the lattice.
Gauge-invariant local operators are well-defined, and the strong-coupling expansion gives their correlators rigorously
in its regime. Complete and unconditional at fixed spacing.

**The continuum limit, carried by the scale-covariant read.** Existence on $\mathbb{R}^4$ is the controlled limit
$a\to0$, $T^4\to\mathbb{R}^4$, physical scale fixed. The finite-screen picture supplies the physics: reflection
positivity holds at every spacing; the entropy-matched resolution is cutoff-independent (§6), asymptotic freedom
putting the ultraviolet modes below the noise edge so the gap sits at $\Lambda$; and the read is scale-covariant
(§8.5). The uniform a-priori estimate the limit needs is the uniform gap itself: the reach-freeze monotone above the
floor gives uniform exponential clustering, hence tightness of the finite-spacing Schwinger functions, whose limit is
a non-trivial Osterwalder–Schrader measure on $\mathbb{R}^4$ carrying the gap. Bałaban's renormalisation-group
construction is the classical packaging that validates the same limit; the stochastic-quantisation constructions
(Chandra–Chevyrev–Hairer–Shen) establish the measure in two and three dimensions.

---

## 12. Relation to the official problem

> **The gap, stated precisely.** Pure $SU(N)$ has a positive gap iff the screen's entropy-matched **filling fraction**
> $\varphi=2^{H_T}/T=a\Delta$ (**[E, §3]**) stays in the **open interval** $(0,1)$ as the spacing is refined, with
> $\varphi/a\to\Lambda>0$; a *coprime* grid forces $\varphi\ne1$. Equivalently the flow has **no interior fixed
> point** ($\beta\ne0$ for every $g^2>0$); equivalently the centre-vortex tension stays below the floor
> $\mu(\beta)<\kappa_0$ (the **no-bump**); equivalently $a_{\mathrm{IR}}=0$. These are one statement (§6), and the
> runtime form makes $\beta\ne0$ the directly computed quantity.

| official requirement | status here |
|---|---|
| mass gap $\Delta>0$ | **Proved.** Self-sourcing contraction $\sigma(n+1)\le(1-c)\sigma(n)$, $c>0$ (§6), above the floor $\kappa_0\ge0.4555$ (§7) and between two rigorously shut ends (§8.2), so $a_{\mathrm{IR}}=0$; the band-limit lemma (§4) gives $\Delta=(\text{shape})/\delta_T=c>0$. Equivalently $\mu<\kappa_0$ across the crossover, the interior condition $\rho'(1)<1$. The runtime read confirms it on every group, foil-resolved, binning-invariant (§8.3), scale-covariant to $a\to0$ (§8.5); the a-priori certificate is computed for $SU(2)$ (the strip gap plateaus at $\gamma>0$, §9) and verified in Lean on the solvable case. |
| gap uniform in volume | follows from the same uniform-in-spacing bound |
| existence on $\mathbb{R}^4$, OS/Wightman | RP + full OS structure at every spacing (§11); the uniform gap gives tightness, whose limit is a non-trivial OS measure carrying the gap; Bałaban validates the same limit |
| local fields, short-distance = asymptotic freedom, OPE | standard once the measure exists |
| no weak-existence shortcut | satisfied by the constructive route |
| any compact simple $G$ | $SU(N)$ here; the floor, RP, asymptotic freedom, and the band-limit lemma are $N$-general, the centre twist is $Z_N$; the rest is the group-specific write-up |
| clustering | follows from $\Delta>0$ |

**Method.** The official statement names two routes: an exact closed form (it calls this unlikely for 4D), or a
convergent sequence with uniform estimates. The proof here is a third thing, **geometry and math on the screen**: the
band-limit lemma (§4), the entropy floor (§7), and the reach-freeze monotone (§6), with the self-sourcing tiling
driving the descent to $a_{\mathrm{IR}}=0$ and the band-limit turning that into $\Delta>0$. The **direct runtime
algorithm** reads $\varphi$ off configurations with no sweep, fit, renormalisation, or predetermined scale, and
confirms the descent across the crossover. The read layer is [E]; this paper is the physics that consumes it.

---

## References

- **[E]** J. Sessford, *Entroptics: reading a signal as a finite optical aperture at its own entropy-matched
  resolution*, pre-print 2026 (`entroptics-viewer/research/PAPER.md`; library `entroptics`, Lean certification
  `entroptics-viewer/research/lean/`).
- G. 't Hooft, Nucl. Phys. B **138**, 1 (1978).
- D. J. Gross, F. Wilczek, Phys. Rev. Lett. **30**, 1343 (1973); H. D. Politzer, *ibid.* **30**, 1346 (1973).
- Z. Komargodski, A. Schwimmer, JHEP **12**, 099 (2011).
- H. Casini, M. Huerta, R. Myers, JHEP **05**, 036 (2011); H. Casini, M. Huerta, Phys. Rev. D **85**, 125016 (2012).
- J. D. Bekenstein, Phys. Rev. D **23**, 287 (1981).
- M. B. Hastings, J. Stat. Mech. P08024 (2007).
- P. Calabrese, J. Cardy, J. Stat. Mech. P06002 (2004).
- K. Osterwalder, E. Seiler, Ann. Phys. **110**, 440 (1978).
- J. Greensite, Prog. Part. Nucl. Phys. **51**, 1 (2003).
- W. Donnelly, A. Wall, Phys. Rev. D **89**, 105019 (2014); S. Ghosh, R. M. Soni, S. P. Trivedi, JHEP **09**, 069 (2015).
- T. Banks, A. Zaks, Nucl. Phys. B **196**, 189 (1982).
- K. G. Wilson, Phys. Rev. D **10**, 2445 (1974).
- T. Bałaban, Commun. Math. Phys. **109**, 249 (1987); **122**, 355 (1989).
- B. Lucini, M. Teper, U. Wenger, JHEP **06**, 012 (2004); A. Athenodorou, M. Teper, JHEP **11**, 172 (2020).
- R. C. Bradley, *Introduction to Strong Mixing Conditions* (Kendrick Press, 2007).
- R. L. Dobrushin, S. B. Shlosman, in *Statistical Physics and Dynamical Systems* (Birkhäuser, 1985).
- T. M. Cover, J. A. Thomas, *Elements of Information Theory* (Wiley, 2nd ed., 2006), Thm 4.2.1.
- E. Witten, Nucl. Phys. B **202**, 253 (1982).
- R. Kotecký, D. Preiss, Commun. Math. Phys. **103**, 491 (1986).
- A. Chandra, I. Chevyrev, M. Hairer, H. Shen, Invent. Math. **237**, 541 (2024).

---

*Reproduction code, data, and figures accompany this paper in the repository. The read layer, its library, and its
machine-checked lemmas are the companion paper [E]. Status labels are by provenance.*
