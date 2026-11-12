# 4. Clustering on their tori

> Theorem D ([MG, Theorem 4.47]). Under the hypotheses of Theorem C, for all large $m$ and all $p$:
>
> (i) on the torus of side $L_{m,p}$ the transfer $K$ has a unit eigenvector $\psi$ with eigenvalue $c$, $\lvert c\rvert=\lVert K\rVert\ne0$, with $\lvert\langle u,K^tw\rangle/c^t-\langle u,\psi\rangle\langle w,\psi\rangle\rvert\le2e^{-(\log2/\ell)\,t\,a_m}\lVert u\rVert\lVert w\rVert$ for every lag $t$;
>
> (ii) for bounded measurable functions $a,b$ of the spatial links of one time slice, with bounds $A,B$, $\lvert\langle a_0b_t\rangle-\langle a_0\rangle\langle b_t\rangle\rvert\le6AB\,(2^{-\lfloor t/n_m\rfloor}+2^{-\lfloor(L_{m,p}-t)/n_m\rfloor})$; the same bound, with $L_{m,p}-t$ replaced by $L_{m,p}-w-w'-t$, holds for bounded measurable functions of slabs of $w+1$ and $w'+1$ consecutive slices with the time links between them ($w,w'$ even and positive), with both separations counted from the slab edges, when $4(w+w')+8n_m\le L_{m,p}$;
>
> (iii) in reflection-positivity form, the two separated terms of that correlation are at most $2^{-\lfloor (j+1)/n_m\rfloor}\sqrt{R_f R_{\theta g}}$ and $2^{-\lfloor (j'+1)/n_m\rfloor}\sqrt{R_{\theta f}R_g}$, where $R_f$ is the reflected reading of $f$ at a separation $s$ fixed in lattice units, $t=s+j+1$, $L_{m,p}-w-w'-t=s+j'+1$, and $\theta f$ is $f$ read on the time-reflected slab; the wrap-around term is at most $2^{-\lfloor (j+1)/n_m\rfloor-\lfloor (j'+1)/n_m\rfloor}\sqrt{H_fH_g}+(\lvert\alpha_f\rvert+\sqrt{H_f})(\lvert\alpha_g\rvert+\sqrt{H_g})\,2^{-\lfloor L'/n_m\rfloor/2}$, $L'=(L_{m,p}-w-w')/2$, with $H_f$ the Hilbert–Schmidt reflected reading and $\alpha_f$ the vacuum one-point reading;
>
> (iv) on the cubic torus of side $L_{m,p}\ge8n_m$ every reading in (iii) is bounded by a Wilson moment $\langle f_0\,(\theta f)_s\rangle$ of $f$ with its reflection on the same torus, times $1+\sigma_0$, $\sigma_0\le2^{-\lfloor L_{m,p}/(2n_m)\rfloor}$, except the term $\sqrt{D_L(f)D_L(g)}$, where the thermal remainder $D_L(f)\ge0$ is the part of the reflected moment of $f$ that the vacuum does not carry.

No bound on the size of $f$ or $g$ enters the constants of (iii) and (iv), which is what the renormalized insertions of [OpenAIYM] require: their size grows as the spacing decreases, while their reflected moments at a fixed physical separation are separated two-point quantities. The slabs of (ii)–(iv) have the shape of their insertions, which read the links of a finite stencil. That $D_L$ vanishes along their order of limits is not proved.

The proof works at the level of the transfer kernel. A slab observable is a kernel insertion; time reflection of the slab is the transpose of its kernel, by inversion invariance of the Haar measure; a Hölder inequality for traces of kernel products, proved directly at kernel level, controls the wrap-around; and the trace identity of the torus turns kernel traces into Wilson correlations.
