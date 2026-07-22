# Information Flow in Entangled Quantum Systems

## David Deutsch and Patrick Hayden

Centre for Quantum Computation
The Clarendon Laboratory
University of Oxford, Oxford OX1 3PU, UK

June 1999

### Abstract

All information in quantum systems is, notwithstanding Bell’s theorem, localised. Measuring or otherwise interacting with a quantum system $\mathfrak{S}$ has no effect on distant systems from which $\mathfrak{S}$ is dynamically isolated, even if they are entangled with $\mathfrak{S}$. Using the Heisenberg picture to analyse quantum information processing makes this locality explicit, and reveals that under some circumstances (in particular, in Einstein-Podolski-Rosen experiments and in quantum teleportation) quantum information is transmitted through ‘classical’ (i.e. decoherent) information channels.

### 1. Quantum information

It is widely believed (see e.g. Bennett and Shor (1998)) that in general a complete description of a composite quantum system is not deducible from complete descriptions of its subsystems unless the ‘description’ of each subsystem $\mathfrak{S}$ depends on what is going on in other subsystems from which $\mathfrak{S}$ is dynamically isolated. If this were so, then in quantum systems information would be a nonlocal quantity—that is to say, the information in a composite system would not be deducible from the information located in all its subsystems and, in particular, changes in the distribution of information in a spatially extended quantum system could not be understood wholly in terms of *information flow*, *i.e.* in terms of subsystems carrying information from one location to another. In this paper we shall show that this belief is false. It has given rise to a wide range of misconceptions, some of which we shall also address here, but our main concern will be with the analysis of information flow in quantum information-processing systems.

Any quantum ‘two-state’ system such as the spin of an electron or the polarisation of a photon can in principle be used as the physical realisation of a *qubit* (quantum bit), the basic unit of quantum information. When used to store or transmit discrete data, such as the values of integers, to an unknown destination, the capacity of a qubit is exactly one bit – in other words, it can hold one of two possible values; moreover, any observer who knows which of the qubit’s observables the value was stored in can discover the value by measuring that observable. However, the states in which the qubit ‘holds a value’ in that sense are merely an isolated pair in a continuum of possible states. Hence there is a lot more than one bit of information in a qubit, though most of it is not accessible through measurements on that qubit alone. For a variety of theoretical and practical reasons, the study of the properties of this quantum information has recently been the subject of increasing attention (for a review, see Bennett and Shor (*loc. cit.*)). The main question we are addressing here is whether it possible to characterise such information *locally, i.e.* in such a way that a complete description of a composite system can always be deduced from complete descriptions of its subsystems, where under those descriptions, ‘the real factual situation of the system $\mathfrak{S}_2$ is independent of what is done with the system $\mathfrak{S}_1$, which is spatially separated from the former’ (Einstein (1949, p85)).

Einstein originally proposed this criterion during his celebrated debate with Bohr on the foundations of quantum theory, in which they both agreed that it is not satisfied by quantum theory. Bohr drew the lesson that there can be no such thing as ‘the real factual situation of the system’ except at the instant of measurement. Einstein concluded instead that quantum theory is incomplete and needs to be completed, perhaps by what we should now call a hidden-variable theory. Subsequent developments such as Bell’s theorem (Bell (1964)) and Aspect’s experiment (Aspect *et al.* (1982)), which are *prima facie* refutations of Einstein’s conclusion, have therefore been taken as vindications of Bohr’s. In fact, both conclusions are mistaken, having been drawn from the same false premise: as we shall show in this paper, quantum physics is entirely consistent with Einstein’s criterion.

Our method is to consider a quantum system prepared in a way that depends on one or more parameters, and then to investigate where those parameters subsequently appear in descriptions of that system and others with which it interacts. Although we shall express our results in terms of the location and flow of information, we shall not require a quantitative definition of information. We require only that a system $\mathfrak{S}$ be deemed to *contain information* about a parameter $\theta$ if (though not necessarily only if) the probability of some outcome of some measurement on $\mathfrak{S}$ alone depends on $\theta$; and that $\mathfrak{S}$ be deemed to *contain no information* about $\theta$ if there exists a complete description of $\mathfrak{S}$ that satisfies Einstein’s criterion and is independent of $\theta$.

### 2. Quantum theory of computation in the Heisenberg picture

Consider a quantum computational network $\mathfrak{N}$ containing $n$ interacting qubits $\mathfrak{Q}_1,\ldots,\mathfrak{Q}_n$. Following Gottesman (1998), we may represent each qubit $\mathfrak{Q}_a$ at time $t$ in the Heisenberg picture by a triple

$$
\hat{\mathbf{q}}_a(t)
=
\left(
\hat{q}_{ax}(t),
\hat{q}_{ay}(t),
\hat{q}_{az}(t)
\right)
\tag{1}
$$

of $2^n \times 2^n$ Hermitian matrices representing observables of $\mathfrak{Q}_a$, satisfying

$$
\left.
\begin{alignedat}{2}
\bigl[\hat{\mathbf{q}}_{a}(t),\hat{\mathbf{q}}_{b}(t)\bigr]
    &= 0
    &\qquad& (a\neq b), \\[4pt]
\hat{q}_{ax}(t)\hat{q}_{ay}(t)
    &= i\hat{q}_{az}(t)
    && \text{(and cyclic permutations over }(x,y,z)\text{).} \\[4pt]
\hat{q}_{ax}(t)^2
    &= \hat{1}
    &&
\end{alignedat}
\right\}
\tag{2}
$$

Thus each $\hat{\mathbf{q}}_a(t)$ is a representation of the Pauli spin operators $\hat{\boldsymbol{\sigma}}=\left(\hat{\sigma}_x,\hat{\sigma}_y,\hat{\sigma}_z\right)$, but in terms of time-dependent $2^n \times 2^n$ matrices instead of the usual constant $2 \times 2$ ones:

$$
\hat{\sigma}_x=
\begin{pmatrix}
0 & 1 \\
1 & 0
\end{pmatrix},
\qquad
\hat{\sigma}_y=
\begin{pmatrix}
0 & -i \\
i & 0
\end{pmatrix},
\qquad
\hat{\sigma}_z=
\begin{pmatrix}
1 & 0 \\
0 & -1
\end{pmatrix}.
\tag{3}
$$

We may choose, as the computation basis at time $t$, the simultaneous eigenstates
$\left\{\lvert z_1,\ldots,z_n;t\rangle\right\}$ of the
$\left\{\hat{z}_a(t)\right\}$, where

$$
\hat{z}_a(t)
=
\frac{1}{2}
\left(
\hat{1}+\hat{q}_{az}(t)
\right).
\tag{4}
$$

Each $\hat{z}_a(t)$ has eigenvalues $0$ and $1$ (corresponding respectively to the eigenvalues $-1$ and $+1$ of $\hat{q}_{az}(t)$) and is the projector for the $a$’th qubit to hold the value $1$ at time $t$.

There is considerable freedom in the choice of matrix representations for the observables (1). It is always possible, and usually desirable, to choose the initial representation to be

$$
\hat{\mathbf{q}}_a(0)
=
\hat{1}^{\,a-1}
\otimes
\hat{\boldsymbol{\sigma}}
\otimes
\hat{1}^{\,n-a},
\tag{5}
$$

where ‘$\otimes$’ denotes the tensor product (distributed, in (5), over the three components of $\hat{\boldsymbol{\sigma}}$), and $\hat{1}^{\,k}$ is the tensor product of $k$ copies of the $2 \times 2$ unit matrix. As we shall see, once the qubits begin to interact, the observables immediately lose the form (5) in the original basis. That is because, as in classical mechanics, the value of each observable of one system becomes a function of the values of observables of other systems at previous times – though now the ‘values’ are matrices. (However, at every instant, because the conditions (2) are preserved by all quantum interactions, there exists a basis in which the observables take the form (5).)

The Heisenberg state of the network is of course constant and, in the theory of computation, it is often desirable to make it a *standard* constant $\lvert 0,\ldots,0;0\rangle$, so that the resources required to prepare the ‘initial’ state will automatically be taken into account in the analysis of computations. When studying algorithms whose intended inputs are qubits in unknown initial states, it may be convenient to work with other Heisenberg states $\lvert\Psi\rangle \neq \lvert 0,\ldots,0;0\rangle$ but note, nevertheless, that by choosing any unitary matrix $U$ with the property $\lvert\Psi\rangle=U\lvert 0,\ldots,0;0\rangle$, and setting $\hat{\mathbf{q}}_a(0)=U^\dagger\left(\hat{1}^{\,a-1}\otimes\hat{\boldsymbol{\sigma}}\otimes\hat{1}^{\,n-a}\right)U$ instead of (5), it is always *possible* to choose the Heisenberg state to be $\lvert 0,\ldots,0;0\rangle$.

The formalism presented here can be generalised to accommodate mixed states (see Deutsch *et al.* (1999)). That complication is unnecessary for present purposes, but note that even in the mixed state formalism it remains possible to choose the Heisenberg state to be $\lvert 0,\ldots,0;0\rangle$.

In what follows, we shall make that choice. For the sake of brevity, let us define

$$
\langle \hat{A} \rangle
\equiv
\langle 0,\ldots,0;0 \rvert
\hat{A}
\lvert 0,\ldots,0;0 \rangle.
\tag{6}
$$

for each observable $\hat{A}$ of $\mathfrak{N}$. Note that all predictions about the behaviour of $\mathfrak{N}$ can be expressed entirely in terms of expectation values of the form (6).

Let us assume for simplicity that each gate of $\mathfrak{N}$ performs its operation in a fixed period, and let us measure time in units of that period. The effect of a $k$-qubit gate $G$ acting between the times $t$ and $t+1$ is

$$
\hat{\mathbf{q}}_a(t+1)
=
U_G^\dagger
\left(
\hat{\mathbf{q}}_1(t),\ldots,\hat{\mathbf{q}}_k(t)
\right)
\hat{\mathbf{q}}_a(t)
U_G
\left(
\hat{\mathbf{q}}_1(t),\ldots,\hat{\mathbf{q}}_k(t)
\right),
\tag{7}
$$

where $1',\ldots,k'$ are the indices of the qubits that are acted upon by $G$, and $a'$ is any such index. Since each qubit is acted upon by exactly one gate during any one computational step (counting the ‘unit wire’ $I$, which has no effect on the computational state of a qubit, as a gate with $U_I=\hat{1}$), the dynamical evolution of any qubit of $\mathfrak{N}$ during one step is fully specified by an expression of the form (7), where $G$ is the gate acting on that qubit during that step. The form of each $U_G$ *qua* function of its arguments is fixed and characteristic of the corresponding gate $G$, and its form *qua* unitary matrix varies accordingly.

It follows that the simultaneous eigenstates of the
$\left\{\hat{z}_{a'}(t)\right\}$ evolve according to

$$
\left\lvert z_{1'},\ldots,z_{k'};t+1\right\rangle
=
U_G^\dagger
\left(
\hat{\mathbf{q}}_{1'}(t),\ldots,\hat{\mathbf{q}}_{k'}(t)
\right)
\left\lvert z_{1'},\ldots,z_{k'};t\right\rangle.
\tag{8}
$$

The computation basis evolves similarly, with $k$ replaced by the total number of qubits $n$, and with $U_G$ replaced by the product (in any order, since they must commute) of all the unitary matrices corresponding to gates acting at time $t$.

We are now in a position to verify that quantum systems have the locality properties stated in Section 1. If we always choose the state vector to be a standard constant, the term ‘state vector’ becomes a misnomer, for the vector $\lvert 0,\ldots,0;0\rangle$ contains no information about the state of $\mathfrak{N}$ or anything else. All the information is contained in the observables. Specifically, the matrix triplets $\left\{\hat{\mathbf{q}}_a(t)\right\}$, each of which constitutes a complete (indeed redundant) description of one qubit $\mathfrak{Q}_{a'}$, jointly constitute a complete description of the composite system $\mathfrak{N}$ – as promised.

As for Einstein’s criterion about the effect of one subsystem upon another, consider a particular qubit $\mathfrak{Q}_a$ and let $F$ be a gate that acts only on one or more qubits *other than* $\mathfrak{Q}_a$ (so that $\mathfrak{Q}_a$ is dynamically isolated from those qubits) during the period between $t$ and $t+1$. According to (7), the complete description of $\mathfrak{Q}_a$ during *that* period would be unchanged if $F$ were replaced by any other gate. Hence it is a general feature of this formalism that when a gate acts on any set of qubits, the descriptions of all other qubits remain unaffected – even qubits that are entangled with those that the gate acts on. This is, again, as promised.

A quantum computational network is not a general quantum system: for instance, its interactions all take place in discrete computational steps of fixed duration, and during any computational step each of its qubits interacts only with the other qubits that are acted upon by the same gate. Nevertheless, since every quantum system can be simulated with arbitrary accuracy by quantum computational networks (Deutsch 1989), the above conclusions about locality are true for general quantum systems too.

### 3. Some specific quantum gates

We often define gates according to the effect they are to have on the computation basis. In such cases we can use (8) to determine the form of the function $U_G$ associated with a given gate $G$. For example, a $\mathbf{not}$ gate acting on a network consisting of a single qubit at time $t$ must have the effect

$$
\left.
\begin{aligned}
\lvert 0;t\rangle
&=
\lvert 1;t+1\rangle
=
U_{\mathrm{not}}^\dagger
\left(\hat{\mathbf{q}}(t)\right)
\lvert 1;t\rangle,
\\[4pt]
\lvert 1;t\rangle
&=
\lvert 0;t+1\rangle
=
U_{\mathrm{not}}^\dagger
\left(\hat{\mathbf{q}}(t)\right)
\lvert 0;t\rangle
\end{aligned}
\right\}.
\tag{9}
$$

(Recall that the kets here are not Schrödinger states but eigenstates of Heisenberg observables. So, for instance, $\lvert 0;t\rangle$ in (9) is the zero-eigenvalue eigenstate of $\hat{z}(t)=\frac{1}{2}\left(\hat{1}+\hat{q}_z(t)\right)$.) Hence at $t=0$,

$$
\langle r;0\rvert
U_{\mathrm{not}}^\dagger
\left(\hat{\mathbf{q}}(0)\right)
\lvert s;0\rangle
=
\delta(r,1-s).
\tag{10}
$$

The Pauli matrices (3), together with the unit matrix, form a basis in the vector space of all $2 \times 2$ matrices, so we may express (10) as an expansion in this basis to obtain

$$
U_{\mathrm{not}}
\left(\hat{\mathbf{q}}(0)\right)
=
\hat{\sigma}_x.
\tag{11}
$$

Using (5), (11), and the fact that the functional form of $U_{\mathrm{not}}$ is constant, we infer that for a general network at a general time $t$, the unitary matrix associated with a $\mathbf{not}$ gate acting on the $k$'th qubit is

$$
U_{\mathrm{not},k}
\left(
\hat{\mathbf{q}}_1(t),\ldots,\hat{\mathbf{q}}_n(t)
\right)
=
\hat{q}_{kx}(t).
\tag{12}
$$

From (12) and (2), it follows that the effect of the $\mathbf{not}$ gate on the $k$'th qubit is:

$$
\text{‘}\mathbf{not}\text{’}:\qquad
\hat{\mathbf{q}}_k(t+1)
\equiv
\left(
\hat{q}_{kx}(t+1),
\hat{q}_{ky}(t+1),
\hat{q}_{kz}(t+1)
\right)
=
\left(
\hat{q}_{kx}(t),
-\hat{q}_{ky}(t),
-\hat{q}_{kz}(t)
\right).
\tag{13}
$$

All other qubits remain unchanged. From this, we can immediately verify that the following operation on $\mathfrak{Q}_k$ is a $\sqrt{\mathbf{not}}$ operation (Deutsch (1987)):

$$
\text{‘}\sqrt{\mathbf{not}}\text{’}:\qquad
\hat{\mathbf{q}}_k(t+1)
=
\left(
\hat{q}_{kx}(t),
\hat{q}_{kz}(t),
-\hat{q}_{ky}(t)
\right).
\tag{14}
$$

Consider next the ‘perfect-measurement’ or *controlled-not* operation, $\mathbf{cnot}$ (Barenco *et al.* (1995)). This is an operation on two qubits, designated the *control* qubit and the *target* qubit. Its effect is that if the control qubit takes the value $0$, then the target qubit is unaltered, and if the control qubit takes the value $1$, then the target qubit is toggled. Given (12), this means that

$$
U_{\mathrm{cnot}}
\left(
\hat{\mathbf{q}}_k,
\hat{\mathbf{q}}_l
\right)
=
\hat{1}_k
\otimes
\frac{\hat{1}_l-\hat{q}_{lz}}{2}
+
\hat{q}_{kx}
\otimes
\frac{\hat{1}_l+\hat{q}_{lz}}{2}.
\tag{15}
$$

Here the $k$'th and $l$'th qubits are the ‘target’ and ‘control’ qubits, respectively. Substituting (15) into (7), we obtain

$$
\text{‘}\mathbf{cnot}\text{’}:\qquad
\left\{
\begin{array}{c}
\hat{\mathbf{q}}_k(t+1) \\[4pt]
\hat{\mathbf{q}}_l(t+1)
\end{array}
\right\}
=
\left\{
\begin{array}{c}
\left(
\hat{q}_{kx}(t),
-\hat{q}_{ky}(t)\hat{q}_{lz}(t),
-\hat{q}_{kz}(t)\hat{q}_{lz}(t)
\right) \\[6pt]
\left(
\hat{q}_{kx}(t)\hat{q}_{lx}(t),
\hat{q}_{kx}(t)\hat{q}_{ly}(t),
\hat{q}_{lz}(t)
\right)
\end{array}
\right\}.
\tag{16}
$$

Let $\mathbf{R}_{\mathbf{n}}(\theta)$ be the single-qubit gate that would, if the $k$'th qubit were a spin-$\frac{1}{2}$ particle, rotate it through an angle $\theta$ about the unit $3$-vector $\mathbf{n}$. The matrices $\hat{\mathbf{q}}_k$ must transform under this rotation in the same way as Pauli matrices do:

$$
\text{‘}\mathbf{R}_{\mathbf{n}}(\theta)\text{’}:\qquad
\hat{\mathbf{q}}_k(t+1)
=
e^{\,i\frac{\theta}{2}\mathbf{n}\cdot\hat{\mathbf{q}}_k(t)}
\hat{\mathbf{q}}_k(t)
e^{-i\frac{\theta}{2}\mathbf{n}\cdot\hat{\mathbf{q}}_k(t)}.
\tag{17}
$$

Hence, in particular, the effect of rotating the $k$'th qubit through an angle $\theta$ about the $x$-axis is:

$$
\text{‘}\mathbf{R}_x(\theta)\text{’}:\qquad
\hat{\mathbf{q}}_k(t+1)
=
\left(
\hat{q}_{kx}(t),
\hat{q}_{ky}(t)\cos\theta+\hat{q}_{kz}(t)\sin\theta,
\hat{q}_{kz}(t)\cos\theta-\hat{q}_{ky}(t)\sin\theta
\right).
\tag{18}
$$

Another useful gate, the Hadamard gate $\mathbf{H}$, is also a special case of (17), with $\theta=\pi$ and $\mathbf{n}$ bisecting the angle between the $x$- and $z$-axes:

$$
\text{‘}\mathbf{H}\text{’}:\qquad
\hat{\mathbf{q}}_k(t+1)
=
\left(
\hat{q}_{kz}(t),
-\hat{q}_{ky}(t),
\hat{q}_{kx}(t)
\right).
\tag{19}
$$

In general, since the $\mathbf{cnot}$ gate together with gates of the type $\mathbf{R}_{\mathbf{n}}(\theta)$ constitute a universal set, the effect of any gate can be calculated by considering a computationally equivalent network containing only those gates, and then using (16) and (17).

For example, the gate that performs the so-called Bell transformation on two qubits (Braunstein *et al.* (1992)) is equivalent to the network shown on the right of the equals sign in Fig. 1. (Gates other than $\mathbf{cnot}$ are represented by rectangles, the vertical lines represent the paths of qubits, and the arrows at the top indicate their direction of motion.) Since both $\mathbf{cnot}$ and $\mathbf{H}$ are their own inverses, the same network upside-down (*i.e.* with $\mathbf{H}$ preceding $\mathbf{cnot}$) performs the inverse of the Bell transformation. It follows that the effect of the $\mathbf{Bell}$ gate is

$$
\text{‘}\mathbf{Bell}\text{’}:\qquad
\left\{
\begin{array}{c}
\hat{\mathbf{q}}_k(t+1) \\[4pt]
\hat{\mathbf{q}}_l(t+1)
\end{array}
\right\}
=
\left\{
\begin{array}{c}
\left(
\hat{q}_{kx}(t),
-\hat{q}_{ky}(t)\hat{q}_{lz}(t),
-\hat{q}_{kz}(t)\hat{q}_{lz}(t)
\right) \\[6pt]
\left(
\hat{q}_{lz}(t),
-\hat{q}_{kx}(t)\hat{q}_{ly}(t),
\hat{q}_{kx}(t)\hat{q}_{lx}(t)
\right)
\end{array}
\right\},
\tag{20}
$$

and the effect of its inverse is

$$
\text{‘}\mathbf{Bell}^{-1}\text{’}:\qquad
\left\{
\begin{array}{c}
\hat{\mathbf{q}}_k(t+1) \\[4pt]
\hat{\mathbf{q}}_l(t+1)
\end{array}
\right\}
=
\left\{
\begin{array}{c}
\left(
\hat{q}_{kx}(t),
-\hat{q}_{ky}(t)\hat{q}_{lx}(t),
-\hat{q}_{kz}(t)\hat{q}_{lx}(t)
\right) \\[6pt]
\left(
\hat{q}_{kx}(t)\hat{q}_{lz}(t),
-\hat{q}_{kx}(t)\hat{q}_{ly}(t),
\hat{q}_{lx}(t)
\right)
\end{array}
\right\}.
\tag{21}
$$


### 4. Information flow in Einstein-Podolski-Rosen experiments