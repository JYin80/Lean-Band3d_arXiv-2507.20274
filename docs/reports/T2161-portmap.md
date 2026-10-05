# T2161 portmap (BA-D1, block Anderson chain design): inventory, pins, bulk decision, constants, instances, routes, citations, split, scripts
Written Sun Oct  4 23:21:51 UTC 2026 (`date -u`).  Probe `RBM3D/Probe/T2161Pins.lean` on branch `t/T2161`, commit `82e72b3`, base `275e275`, 2730 lines.  Companion of `docs/reports/T2161-prove.md` (section (b) points here as P.1-P.12).  The outputs below are the cached outputs of the displayed commands (`$S/final_run.sh` regenerates them; the scripts are in P.12); RBM2D is read at `c9a24cf` (T2002 O1), kept lines at `0c1330a`.  `S` = /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2161, `W` = /Users/junyin/Lean_proof/RBM3D-wt/T2161.

## P.1 Inventory (item 1)
### P.1a the statements of the paper that name the BA model (class: new / shared = BA by substitution / cited = cited-to-be-proved / band; part 3: text that is not a statement environment)
    $ python3 $S/inv_paper.py
    PART 1: statement environments (with their proof) that name the BA model
    #   file                       kind        stmt       label                    cites(stmt|proof)                  class    pin / ticket
    1   1_2_Intro_model_result     theorem     644-669    MR:decol_BA              |                                  new      Thm 2.7: BAEnd_*, BAThm27
    2   1_2_Intro_model_result     definition  714-734    def_flow                 |                                  shared   m(E+i0,g), M(E,g) at BA: BAm, BAMB
    3   1_2_Intro_model_result     lemma       949-979    lem:SE_basic             |                                  shared   S^(B)(0)=I: FlowFM.S := 1
    4   1_2_Intro_model_result     lemma       1034-1044  lem_WI_K                 |RBSO1D,YY_25                      cited    [RBSO1D L3.17]: BA-K5
    5   1_2_Intro_model_result     definition  1068-1090  def_Theta                |                                  shared   M^(s1,s2)_ab = M_ba(s1) M_ab(s2): BAMss, BATheta
    6   1_2_Intro_model_result     lemma       1119-1170  lem_propTH               |                                  shared   consts depend on g^-1, 1<=g<=d^-1 (1150): BAProp5..8
    7   3_5_Loop_Hierarchy         lemma       14-35      lem_GbEXP                |YY_25,erdHos2012rigidity,erdos201 band     no BA claim (line 14 is a notation footnote); twin lem_GbEXP_BA
    8   7_8_light_weight           lemma       1796-1808  zztE_BA                  RBSO1D|                            cited    [RBSO1D L3.3]: proved here BAzztE_*
    9   7_8_light_weight           theorem     1825-1828  lem:main_ind_BA          |                                  new      BAMainInd
    10  7_8_light_weight           lemma       1846-1906  lem:propM                |Aizenman_book,LeeSchSteYau2015    cited    [LSY15 L3.5],[Aizenman 10.5]: BAPropM
    11  7_8_light_weight           lemma       1916-1946  lem_GbEXP_BA             |RBSO1D                            cited    [RBSO1D L6.1]: BAGbEXP
    12  7_8_light_weight           lemma       1956-1985  lem_ConArg_BA            |RBSO1D                            cited    [RBSO1D L7.1]: BAConArg
    13  A_deterministic_estimates  lemma       592-598    tree-representation_BA   RBSO1D|                            cited    [RBSO1D L4.16]: BA-K2
    14  A_deterministic_estimates  lemma       643-648    lem_pureloop             |                                  shared   BA proof uses Mbound_AO(2) (A:690): BA-K3
    15  B_graphical_lemmas         definition  345-356    def scalingBA            |                                  new      BA-L1
    16  B_graphical_lemmas         lemma       359-372    lanlw                    yang2024Del|                       cited    [yang2024Del B.9]: BAlanlw
    17  B_graphical_lemmas         lemma       376-387    lem_lweight              yang2024Del|                       cited    [B.10]: BAlweight
    18  B_graphical_lemmas         lemma       393-405    GGGamma                  yang2024Del|                       cited    [B.11]: BAGGGamma; delta T2161a
    units 18  unclassified: []
    PART 2: BA-mention lines outside every statement environment (file: line numbers)
    1_2_Intro_model_result     27 lines: 4 5 8 10 11 37 39 40 45 67 253 254 342 373 599 600 604 609 613 617 620 672 688 784 1051 1100 1190
    3_5_Loop_Hierarchy         3 lines: 5 6 71
    7_8_light_weight           40 lines: 5 1792 1794 1820 1822 1832 1834 1835 1841 1914 1953 1954 1990 1993 1994 1999 2002 2004 2009 2013 2016 2017 2022 2025 2026 2029 2032 2033 2034 2036 2037 2041 2061 2075 2085 2088 2090 2095 2100 2101
    A_deterministic_estimates  15 lines: 14 20 25 58 59 88 101 114 177 215 319 376 589 690 734
    B_graphical_lemmas         20 lines: 118 286 288 289 298 321 322 357 407 408 415 416 428 431 488 489 492 496 497 522
    PART 3: BA text that is not a statement environment (definitions in text, modified proofs); the start line is printed to check the range
    1_2_Intro_model_result     599-636   new      model: H=V+g Psi, (self_m) 626, (def_G0) 631, e_lambda, supp BASelf, BAm, BAMB; bulk decisi | \subsection{Main results for the block Anderson mo
    1_2_Intro_model_result     658-666   new      def:Theta_BA, (Theta M)_ab in the quantum diffusion          BATheta, BAprof, BAqdConcl     | \be \label{def:Theta_BA}
    7_8_light_weight           1817-1819 change   spectral_domainBA: |Ehat| <= e_g - kappa                     BAendDom, BAdom (rho-form)     | \be\label{eq:spectral_domainBA}
    7_8_light_weight           1999-2096 change   (eq:MG_conclusion3_BA), EMn2 for BA (deterministic J)        BAEMn2Exp                      | \be\label{eq:MG_conclusion3_BA}
    7_8_light_weight           2100-2105 change   Steps 3-6 verbatim except sec:Step5_larget and LWterm_EXP    ST pins over baFM; BAGbEXP in  | \noindent{\bf Proof of Steps 3--6 for \Cref{lem:ma
    A_deterministic_estimates  12-70     change   proof of lem_propTH 5-8: BA mentions at 14,20,25,58,59       BAProp5..8, BA-P1..P8          | 
    A_deterministic_estimates  584-598   cited    K-loop tree representation with M-entries (A:376)            [RBSO1D L4.16, S4]: BA-K2      | \Gamma^{(n)}_{M;t,\bsig,\ba} := \sum_{b_{i,j} \in 
    A_deterministic_estimates  690-740   cited    (eq:Sigma-empty-sum-zero) for BA [RBSO1D L4.29, Claim 4.30]  BA-K3, BAKbound                | have constant size and fast exponential decay outs
    B_graphical_lemmas         286-344   new      Psi-dotted / M-dotted edges, atoms (def_atom)                BA-L1                          | \subsection{Proof of \texorpdfstring{\Cref{lem:LWt
    B_graphical_lemmas         407-523   change   BA lvl1, atomic reduction, auxiliary graph, G_by_auxG_BA     BA-L3                          | As explained in \cite[Appendix B]{yang2024Del}, re
    B_graphical_lemmas         118-118   change   LWterm_EXP with GGGamma for BA ("omit")                      BA-L4                          | The proof of \Cref{lem:LWterm_EXP} for the block A
### P.1b every `\cite` of the BA part, active or commented out in the TeX
    $ python3 $S/inv_cites.py
    file                       line  status    key                        optarg       context(45 chars before)
    1_2_Intro_model_result     624   active    Biane                                   uous probability density $\rho_N(x)$ on $\R$ 
    1_2_Intro_model_result     634   active    LeeSchSteYau2015,knowles20              e random matrix theory literature (see e.g., 
    1_2_Intro_model_result     672   active    PelSchShaSod                            ck Anderson model is localized, as proven in 
    7_8_light_weight           1796  active    RBSO1D                                  \begin{lemma}[Lemma 3.3 of 
    7_8_light_weight           1844  COMMENTED RBSO1D                     Lemma~3.9     \Cref{lem:propM}, which were established in 
    7_8_light_weight           1846  COMMENTED RBSO1D                                  %[Lemma 3.9 of 
    7_8_light_weight           1908  active    LeeSchSteYau2015           Lemma 3.5     bound $\im m \gtrsim 1$ is a consequence of 
    7_8_light_weight           1911  active    Aizenman_book              Theorem 10.5 lassical Combes--Thomas estimate (see, e.g., 
    7_8_light_weight           1948  active    RBSO1D                                  This lemma was proved as Lemma 6.1 in 
    7_8_light_weight           1987  active    RBSO1D                                  ly the same argument as that of Lemma 7.1 in 
    7_8_light_weight           1990  active    RBSO1D                     Section 7.1  1} and \eqref{Gtmwc}) is the same as that in 
    7_8_light_weight           2101  active    YY_25                      Section 5.3  \Cref{lem_GbEXP} and follows the approach of 
    7_8_light_weight           2101  active    RBSO1D                     Section 7.3  on \Cref{lem_GbEXP_BA} and parallel those in 
    7_8_light_weight           2104  COMMENTED YY_25                      Section 5.3  _GbEXP} and follow similar lines to those in 
    7_8_light_weight           2104  COMMENTED RBSO1D                     Section 7.3  on \Cref{lem_GbEXP_BA} and resemble those in 
    B_graphical_lemmas         357   active    yang2024Del                             es for the block Anderson model, as given in 
    B_graphical_lemmas         359   active    yang2024Del                             \begin{lemma}[Basic expansion, Lemma B.9 of 
    B_graphical_lemmas         376   active    yang2024Del                             egin{lemma} [Weight expansion, Lemma B.10 of 
    B_graphical_lemmas         393   active    yang2024Del                             \begin{lemma}[$GG$ expansion, Lemma B.11 of 
    B_graphical_lemmas         407   active    yang2024Del                Appendix B   As explained in 
    A_deterministic_estimates  25    active    bourgade2019random         Lemma 4.2    e $\e>0$ is a positive constant. As shown in 
    A_deterministic_estimates  48    COMMENTED yang2024Del                             C0} and \eqref{prop:BD2} were established in 
    A_deterministic_estimates  48    COMMENTED yang2024Del                             ard summation-by-parts argument.\footnote{In 
    A_deterministic_estimates  50    active    yang2024Del                             ThfadC0} and \eqref{prop:BD2} were proved in 
    A_deterministic_estimates  50    active    yang2024Del                             ard summation-by-parts argument.\footnote{In 
    A_deterministic_estimates  51    active    yang2024Del                             qref{prop:ThfadC0} is proved in Lemma 3.1 of 
    A_deterministic_estimates  51    active    yang2024Del                             \eqref{prop:BD1} is not stated explicitly in 
    A_deterministic_estimates  52    active    RBSO1D                     Lemma 3.10   ave also been derived for dimension $d=2$ in 
    A_deterministic_estimates  55    COMMENTED yang2024Del                             qref{prop:ThfadC0} is proved in Lemma 3.1 of 
    A_deterministic_estimates  55    COMMENTED yang2024Del                             hile \eqref{prop:BD2} is proved as (E.19) in 
    A_deterministic_estimates  55    COMMENTED yang2024Del                             qref{prop:BD1} does not appear explicitly in 
    A_deterministic_estimates  58    active    DYYY25                     Lemma 2.14   \ne \sig_2$. Its proof is similar to that of 
    A_deterministic_estimates  62    active    Lawler_book                Section 2    nd, using the local CLT for $X_k$ (see e.g., 
    A_deterministic_estimates  64    active    DYYY25                                  d using the argument below equation (8.3) of 
    A_deterministic_estimates  67    active    DYYY25                     Section 8    Since the argument closely follows that in 
    A_deterministic_estimates  67    active    DYYY25                                  , the proof here is somewhat simpler than in 
    A_deterministic_estimates  376   active    RBSO1D                     Section 4    ocedure for this replacement is described in 
    A_deterministic_estimates  592   active    RBSO1D                                  \begin{lemma}[Lemma 4.16 of 
    A_deterministic_estimates  650   COMMENTED YY_25                                   % We follow the proof of Corollary 3.5 in 
    A_deterministic_estimates  650   COMMENTED YY_25                                   on of the tree terms into sums from (3.6) of 
    A_deterministic_estimates  661   active    YY_25                                    proof is analogous to that of Lemma 3.11 in 
    A_deterministic_estimates  734   active    YY_25                      Lemma 3.10   The first estimate was established in 
    A_deterministic_estimates  734   active    RBSO1D                     Lemma 4.29   0]{YY_25} for 1D random band matrices and in 
    A_deterministic_estimates  734   active    RBSO1D                     Claim 4.30   els, while the second estimate was proved in 
    1_2_Intro_model_result     1032  active    YY_25,RBSO1D                            e also refer to as a ``Ward's identity''. In 
    1_2_Intro_model_result     1046  active    YY_25                                   and matrix, this corresponds to Lemma 3.6 in 
    1_2_Intro_model_result     1046  active    RBSO1D                                  erson model, it corresponds to Lemma 3.17 in 
    1_2_Intro_model_result     1050  COMMENTED DYYY25_d3                               %cite 
    1_2_Intro_model_result     1051  active    YY_25                                   or the $\cK$-loops, originally discovered in 
    1_2_Intro_model_result     1051  active    RBSO1D                                  _25} for the random band matrix model and in 
    1_2_Intro_model_result     1051  active    YY_25,RBSO1D                            -loops. The proof, being similar to those in 
    1_2_Intro_model_result     1174  active    YY_25,RBSO1D                            As shown in 
    3_5_Loop_Hierarchy         2213  active    DYYY25                     Section 7    explore the CLT cancellation within it as in 
    3_5_Loop_Hierarchy         2213  active    RBSO1D                     Appendix A.1 within it as in \cite[Section 7]{DYYY25} and 
    3_5_Loop_Hierarchy         2248  active    DYYY25                     equation (7. f this bound is exactly the same as that for 
    3_5_Loop_Hierarchy         2248  active    RBSO1D                     equation (A.  that for \cite[equation (7.39)]{DYYY25} and 
    distinct (key,status): 16  active cites: 44  commented cites: 12
### P.1c the merged RBM3D declarations that cover a piece of the BA chain (file:line in the worktree of `t/T2161`)
    $ python3 $S/inv_merged_ba.py
    merged declaration                 file:line                      class            covers
    PsiB                               RBM3D/Gauss/BlockAnderson.lean:45 covers  Psi^(B) = adjacency of the block torus (eq:Psi3D)
    PsiV                               RBM3D/Gauss/BlockAnderson.lean:48 covers  Psi = Psi^(B) (x) I_{W^d} on Vtx
    PsiI                               RBM3D/Gauss/BlockAnderson.lean:52 covers  Psi on the fine lattice
    PsiB_isHermitian                   RBM3D/Gauss/BlockAnderson.lean:55 covers  Hermitian
    seqHflowBA                         RBM3D/Gauss/BlockAnderson.lean:83 covers  flow H_u = lam0 Psi + sqrt(u) V (MBM, S(0)=I)
    seqHBA                             RBM3D/Gauss/BlockAnderson.lean:96 covers  H = V + lam Psi (eq:H_blocka)
    Gt_BA                              RBM3D/Gauss/BlockAnderson.lean:112 covers  zztE_BA third clause, pointwise
    Mres                               RBM3D/Loop/GLoopFlow.lean:81   covers  M = (H0 - z - m)^{-1} with M != mI (def_G0)
    Gres                               RBM3D/Loop/GLoopFlow.lean:74   covers  G(sigma) = (H-z)^{-1}, G(-) = G(+)^*
    ztOf                               RBM3D/Loop/GLoopFlow.lean:55   covers  z_t = E + (1-t) m with m data
    etaOf                              RBM3D/Loop/GLoopFlow.lean:58   covers  eta_t = (1-t) Im m
    loopM                              RBM3D/Loop/GLoopFlow.lean:92   covers  G-loops of any Hermitian matrix
    norm_loopM_le                      RBM3D/Loop/GLoopFlow.lean:642  covers  envelope |L^(n)| <= eta^{-n} for any Hermitian H
    PropThetaQ                         RBM3D/Propagator/Pins.lean:214 shape   Theta = (1 - t Q)^{-1} for a transition matrix Q = M^(s1,s2) S
    Prop5DecayQ                        RBM3D/Propagator/Pins.lean:225 shape   property 5 for a model family Q
    isUnit_sub_smul_of_isHermitian     RBM3D/Analysis/Resolvent.lean:132 covers  H - z invertible off the real axis
    norm_inverse_entry_le              RBM3D/Analysis/Resolvent.lean:153 covers  |((H-z)^{-1})_{xy}| <= |Im z|^{-1}
    IsKLoopS                           RBM3D/Loop/KLTree.lean:828     covers  K-loop equations with a kernel S and initial data M (kernel-generic)
    treeEqRhsS                         RBM3D/Loop/KLTree.lean:809     covers  RHS of (pro_dyncalK) with kernel S
    MLoopM                             RBM3D/Loop/KLTree.lean:818     shape   M-loop data with free label profile
    KLtreeValW                         RBM3D/Loop/KLTree.lean:114     shape   tree value with generic leaf/edge weights (Gamma_M)
    LWPins_dH                          RBM3D/Graph/LWPins.lean:62     covers  Wirtinger derivative of a resolvent polynomial
    LWPins_resPoly                     RBM3D/Graph/LWPins.lean:73     covers  f(G) as a polynomial in resolvent entries
    LData                              RBM3D/Graph/LWVocab.lean:73    shape   graph vocabulary with a general matrix M
    Prec                               RBM3D/Defs/StochDomAt.lean:121 covers  stochastic domination at the scale N
    Whp                                RBM3D/Defs/StochDomAt.lean:128 covers  w.h.p. at the scale N
    Sizes                              RBM3D/Defs/Sizes.lean:138      covers  size data (L,W,lam sequences)
    Bparam                             RBM3D/Defs/Params.lean:36      covers  B_{t,K} (g = model coupling)
    ellT                               RBM3D/Defs/Params.lean:32      covers  ell_t
    STMainInd                          RBM3D/Induction/Defs.lean:294  band    lem:main_ind (band): BA = same pin at the BA carrier (probe: STMainIndG)
    STKbound                           RBM3D/Induction/Defs.lean:174  band    ML:Kbound (band)
    STGbEXP                            RBM3D/Induction/Defs.lean:329  band    lem_GbEXP (band; BA statement differs, 7_8:1916)
    prop5to8_holds                     RBM3D/Propagator/Prop6Hold.lean:433 band    properties 5-8 for the band S^(B)(g) (not for K = |M|^2)
    declarations not found: 0  of 33
    files read from the worktree of t/T2161, base (merge-base with main) 275e275; main is now 04aedec; .lean files changed on main since the base: ['RBM3D.lean', 'RBM3D/Evolution/MeanFar.lean', 'RBM3D/Induction/AzumaProxyN.lean', 'RBM3D/Induction/AzumaProxyN2.lean', 'RBM3D/Induction/IniTermII.lean', 'RBM3D/Path/LemDecCalE.lean', 'RBM3D/Test/Axioms.lean']
    inventory declarations among them: []
### P.1d RBM2D files that can be ported (lines at `c9a24cf`, kept lines at `0c1330a`, `d = 2` tokens)
    $ python3 $S/inv_rbm2d.py
    RBM2D file (c9a24cf)                                 BA ticket         lines   kept d=2tok  use
    RBM2D/Propagator/CombesThomasConjugation.lean        BA-D4                78     -1     0  lem:propM(3): weight conjugation (SB -> gΨ-w)
    RBM2D/Propagator/CombesThomasDistanceWeight.lean     BA-D4               101     -1     0  distance weight, edge ratio
    RBM2D/Propagator/CombesThomasExponentialWeight.lean  BA-D4                79     -1     0  exponential weight e^{t dist}, ratio <= e^t-1
    RBM2D/Propagator/CombesThomasPerturbation.lean       BA-D4                74     -1     0  Neumann perturbation of the weighted inverse
    RBM2D/Propagator/CombesThomasWeightedInverse.lean    BA-D4               136     -1     0  weighted inverse bound
    RBM2D/Propagator/CombesThomasGapParameter.lean       BA-D4                64     -1     0  gap parameter
    RBM2D/Propagator/CombesThomasKernelDecay.lean        BA-D4                78     -1     0  kernel decay from the weighted bound
    RBM2D/Propagator/CombesThomasFixedGap.lean           BA-D4                59     -1     0  fixed-gap geometric decay
    RBM2D/Universality/FreeConv.lean                     BA-D2               719    667     0  (self_m): existence/uniqueness, Stieltjes of the free convolution
    RBM2D/Universality/FreeConvStability.lean            BA-D6 (partial)     835    788     0  continuity up to the real axis; stability near semicircle (BA: no)
    RBM2D/Universality/Step1Band.lean                    UN-D1 (T2162)      1259   1163     2  Step 1 comparison with LSY; BA needs the rho_N-dilated form
    RBM2D/Main/DecolFromLocal.lean                       MA-BA               361    341     3  delocalization from the local law
    RBM2D/Main/QUEFromQDiff.lean                         MA-BA              1084   1069    26  QUE from quantum diffusion
    RBM2D/Main/RegionUnif.lean                           MA-BA               950     -1    27  net lemma, uniform in z
    RBM2D/Endpoints.lean                                 probe 11 (done)     268    268     2  endpoint pins decol/locSC/QUE/BUniv; IsOrthoEigenbasis :56-59 is ported (BAIsOrthoEigenbasis)
    RBM2D/Main/Endpoints.lean                            MA-BA                71     62     0  assembly locSC_holds, decol_holds, QUE_holds, QDiff_holds from STOAll (the glue pins of probe 12.1)
    RBM2D/Main/BUnivHolds.lean                           UN-D1 (T2162)        76     62     0  Thm 2.4 assembly (L32)
    total                                                                   6292   4420    60
    group totals (files, lines at c9a24cf, kept lines at 0c1330a (0 = deleted by RBM2D T2274), d=2 tokens):
      CombesThomas* (BA-D4)                            8 files   669 lines     0 kept   0 tokens
      FreeConv* (BA-D2, D6)                            2 files  1554 lines  1455 kept   0 tokens
      Step1Band + BUnivHolds (UN-D1/T2162)             2 files  1335 lines  1225 kept   2 tokens
      Main/{Decol,QUE,RegionUnif,Endpoints} (MA-BA)    4 files  2466 lines  1472 kept  56 tokens
      Endpoints.lean (probe 11, ported pins)           1 files   268 lines   268 kept   2 tokens
    files mentioning "anderson" at c9a24cf (git grep -il): 0
    git -C ../RBM2D log -1 --format=%h c9a24cf: c9a24cf
    $ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Propagator/CombesThomasConjugation.lean RBM2D/Propagator/CombesThomasDistanceWeight.lean RBM2D/Propagator/CombesThomasExponentialWeight.lean RBM2D/Propagator/CombesThomasPerturbation.lean RBM2D/Propagator/CombesThomasWeightedInverse.lean RBM2D/Propagator/CombesThomasGapParameter.lean RBM2D/Propagator/CombesThomasKernelDecay.lean RBM2D/Propagator/CombesThomasFixedGap.lean RBM2D/Universality/FreeConv.lean RBM2D/Universality/FreeConvStability.lean RBM2D/Universality/Step1Band.lean RBM2D/Main/DecolFromLocal.lean RBM2D/Main/QUEFromQDiff.lean RBM2D/Main/RegionUnif.lean RBM2D/Endpoints.lean RBM2D/Main/Endpoints.lean RBM2D/Main/BUnivHolds.lean | tail -20   # the sources of the candidates, c9a24cf -> RBM2D HEAD
     RBM2D/Endpoints.lean                               |  66 +-
     RBM2D/Main/BUnivHolds.lean                         |  39 +-
     RBM2D/Main/DecolFromLocal.lean                     |  43 +-
     RBM2D/Main/Endpoints.lean                          |  34 +-
     RBM2D/Main/QUEFromQDiff.lean                       |  37 +-
     RBM2D/Main/RegionUnif.lean                         | 950 ---------------------
     RBM2D/Propagator/CombesThomasConjugation.lean      |  78 --
     RBM2D/Propagator/CombesThomasDistanceWeight.lean   | 101 ---
     .../Propagator/CombesThomasExponentialWeight.lean  |  79 --
     RBM2D/Propagator/CombesThomasFixedGap.lean         |  59 --
     RBM2D/Propagator/CombesThomasGapParameter.lean     |  64 --
     RBM2D/Propagator/CombesThomasKernelDecay.lean      |  78 --
     RBM2D/Propagator/CombesThomasPerturbation.lean     |  74 --
     RBM2D/Propagator/CombesThomasWeightedInverse.lean  | 136 ---
     RBM2D/Universality/FreeConv.lean                   |  79 +-
     RBM2D/Universality/FreeConvStability.lean          | 106 +--
     RBM2D/Universality/Step1Band.lean                  | 154 +---
     17 files changed, 129 insertions(+), 2048 deletions(-)
### P.1e cost structure of the merged chain (statements that hardwire the band model)
    $ python3 $S/decl_inv.py
    gate-dir      decls   lines |  decls   lines (signature mentions a band token) |  decls   lines (only the proof does)
    Analysis          8     121 |      0       0 |      0       0
    Defs            358    3219 |     49     390 |      4      75
    Evolution       489    9194 |     42    1731 |     49    1486
    Gauss           454    6214 |    114    1552 |     40     502
    Graph          1577   18646 |     86    1089 |    102    1387
    Green          1934   24124 |    378    6538 |    155    3144
    Hierarchy       146    2121 |     14     302 |     16     491
    Induction      3500   57206 |    458   13706 |    388    9509
    Kernel           91    2187 |      7      83 |      7     347
    Loop            975   15981 |    306    6919 |     74    2246
    Path            893   13995 |    166    3701 |     94    2296
    Propagator      474    8072 |     90    1183 |     28     858
    Test             19     783 |      5     189 |      4     241
    TOTAL         10918  161863 |   1715   37383 |    961   22582
    $ python3 $S/file_gate.py
    gate         lines  sig-hw body-hw
    EK            5851     498     788
    F0             904     189     241
    KL           14993    6627    2042
    LW           18646    1089    1387
    MD            6802    1232     751
    MD/F0         2054     390      59
    PT            8072    1183     858
    ST-1         38890    8989    5682
    ST-2         37334   10435    5581
    ST-3         18712    4320    3229
    ST-4          9605    2431    1964
    TOTAL       161863   37383   22582
    $ python3 $S/pin_subst2.py
    transitive closure over all 1326 merged defs: 1272 band-dependent
    group                                                                     pins band-dep.  pins independent of the band objects (even transitively)
    Step 1 (Induction/Defs)                                                     27        27  
    Step 2 (Step2*, NewKLK*, Contract*, Grid*, Azuma*)                          48        47  STPsiClass
    Steps 3-4 (Step34Pins, KDecay, DecayLoop*, SEforLn*, Q*, B45)               60        57  STAny STAlternating STEKWin
    Step 5 (Step5*, TailtoTail, WardII, Evolution/Clt*, FarEntry, ExpInv)       71        66  STReg5I STReg5Mid STReg5III STSigSame STSigMixed
    Green chain (Green/Pins, GbEXP)                                             15        15  
    LW layer (Graph/LWPins)                                                     24        24  
    K-loop layer (Loop/KBound, KLFinal, KLTree)                                 10        10  
    EK layer (Evolution/Pins, XiPins, SumDecay*, Nonzero, Prec)                 12        12  
    total                                                                      267       258

## P.2 The pins (item 2)
### P.2a registry class of every Prop-valued definition (DECISIONS §16, §20) and the index of the probe
    $ python3 $S/registry.py
    Prop-valued definitions of the probe: 74; classified: 74; unclassified: []; classified but absent: []
    owed       36: BAmExists BAmUniqReal BAmBoundary BAWard BAPropM BAoffDiag BAImmLower BAProp5 BAProp5s BAProp6 BAProp7 BAProp8 BAProp5to8 BAMainInd BAGbEXP BAConArg BAStep1 BAStep2 BAEMn2Exp BAKsolve BAKbound BAlanlw BAlweight BAGGGamma BAEnd_locSC BAEnd_QDiff BAEnd_decol BAEnd_QUE BAEnd_BUniv BAThm27 BAGlueLoc BAGlueQDiff BAGlueDecol BAGlueQUE BAGlueUniv BAGlueChain
    structural 13: BASelf BAedgeBulk BAdistBulk BAbulk BAReal BAdom BAFlow BAGbEXPpre BAendDom BAIsOrthoEigenbasis BAqueWindow BAqueBad BAque2Bad
    shape       9: BAGbEXPconcl BAConArgLoop BAConArgVec BAlocSCConcl BAqdConcl BAdecolConcl BAqueConcl BAunivConcl Thm27At
    carrier    16: STLKg STLmaxg STDecayg STDecayStrongg STLocalMaxg STLocalEntryg STExp2g STInitialGT2g STKboundg STStep1Loopg STStep1Weakg STLWassmExpg STMainIndG STStep2Localg STStep2Avgg STStep2Decayg
    borrowed    0: -
    borrowed = 0: the only external input of the BA chain is LSY Thm 2.2 (DECISIONS 5), used inside the proof of the owed pin BAEnd_BUniv; no pin states it.
    $ python3 $S/pin_index.py
    Prop-valued def        line  kind      registry    ticket/route
    BASelf                 191   def       -           
    BAedgeBulk             442   def       -           
    BAdistBulk             448   def       -           
    BAbulk                 451   def       -           
    BAReal                 455   def       -           
    BAdom                  459   def       -           
    BAmExists              571   def       owed        BA-1
    BAmUniqReal            578   def       owed        BA-1
    BAmBoundary            585   def       owed        BA-2
    BAWard                 597   def       owed        BA-1
    BAPropM                612   def       owed        BA-4: port of RBM2D `Propagator/CombesThomas*.lean`, 669 lines, retarg
    BAoffDiag              631   def       owed        BA-4
    BAImmLower             645   def       owed        BA-2; route: uniform Hölder continuity of `ρ_N` + Poisson smoothing
    BAProp5                676   def       -           
    BAProp5s               687   def       -           
    BAProp6                697   def       -           
    BAProp7                708   def       -           
    BAProp8                720   def       -           
    BAProp5to8             729   structure -           
    STLKg                  854   def       -           
    STLmaxg                861   def       -           
    STDecayg               868   def       -           
    STDecayStrongg         879   def       -           
    STLocalMaxg            889   def       -           
    STLocalEntryg          895   def       -           
    STExp2g                901   def       -           
    STInitialGT2g          914   def       -           
    STKboundg              921   def       -           
    STStep1Loopg           928   def       -           
    STStep1Weakg           935   def       -           
    STLWassmExpg           947   def       -           
    BAFlow                 1037  def       -           
    STMainIndG             1050  def       -           
    BAMainInd              1071  def       owed        BA-ST6, the chain induction for `BA`
    BAGbEXPpre             1084  def       -           
    BAGbEXPconcl           1093  def       -           
    BAGbEXP                1115  def       owed        BA-ST1
    BAConArgLoop           1133  def       -           
    BAConArgVec            1143  def       -           
    BAConArg               1160  def       owed        BA-ST1
    BAStep1                1170  def       owed        BA-ST1
    STStep2Localg          1212  def       -           
    STStep2Avgg            1218  def       -           
    STStep2Decayg          1224  def       -           
    BAStep2                1246  def       owed        BA-ST2
    BAEMn2Exp              1262  def       owed        BA-ST2
    BAKsolve               1295  def       owed        BA-KL2
    BAKbound               1313  def       owed        BA-KL3
    BAlanlw                1429  def       owed        BA-L2
    BAlweight              1436  def       owed        BA-L2
    BAGGGamma              1445  def       owed        BA-L2
    BAendDom               1489  def       -           
    BAlocSCConcl           1503  def       -           
    BAqdConcl              1516  def       -           
    BAEnd_locSC            1543  def       owed        MA-BA; from `BAMainInd` at `t₀`, the net lemma `[net]`, `zztE_BA`
    BAEnd_QDiff            1548  def       owed        MA-BA
    BAIsOrthoEigenbasis    1552  def       -           
    BAdecolConcl           1558  def       -           
    BAEnd_decol            1565  def       -           
    BAqueWindow            1570  def       -           
    BAqueBad               1574  def       -           
    BAque2Bad              1582  def       -           
    BAqueConcl             1592  def       -           
    BAEnd_QUE              1602  def       -           
    BAunivConcl            1642  def       -           
    BAEnd_BUniv            1652  def       -           
    BAThm27                1659  def       -           
    BAGlueLoc              1833  def       -           
    BAGlueQDiff            1837  def       -           
    BAGlueDecol            1841  def       -           
    BAGlueQUE              1844  def       -           
    BAGlueUniv             1847  def       -           
    BAGlueChain            1862  def       -           
    Thm27At                2547  def       -           
    Prop-valued defs/structures: 74 {'-': 54, 'owed': 20}
### P.2b pin -> paper map (the first paper line cited is printed to check the reference)
    $ python3 $S/pin_map.py
    pin           line  paper     paper line starts with                                                   what the pin states / scale
    BAmExists     571   1_2:626   \be\label{self_m}                                                        (self_m): unique m in C_+ for every L>=3, g>0, Im z>0 [Biane]; constants none
    BAmUniqReal   578   1_2:626   \be\label{self_m}                                                        uniqueness at real E (Schwarz-Pick); makes rho_N the Im of the real-axis solution
    BAmBoundary   585   1_2:715   For any $E \in \mathbb R$ and $\ilambda>0$, we denote $m(E,\ilambda)\e   m(E,g) = m(E+i0,g); Im m(E+i eta) -> 0 in a gap
    BAWard        597   7_8:1869  \be\label{eq:WardM}                                                      Ward sum_b |M_ab|^2 = Im m/(Im m+Im z); translation invariance 7_8:1859; M_aa = m
    BAPropM       612   7_8:1846  \begin{lemma}%[Lemma 3.9 of \cite{RBSO1D}]                               lem:propM (1)-(3) in the rho-bulk; constants (d,Lambda,kappa) before L,g,E,m
    BAoffDiag     631   A:32      \be\label{eq:off_diagM}                                                  (eq:off_diagM): |1-t m^2| >= eps, ||M'||_{inf->inf} <= (1-eps)|1-t m^2|, t in [0,1]
    BAImmLower    645   7_8:1908  Property (1) follows directly from the translation invariance of the m   Im m >~ 1 [LSY15 L3.5], now a bridge from the rho-bulk: Im m(E+i eta) >= c, eta in (0,1]
    BAProp5       676   1_2:1119  \begin{lemma}\label{lem_propTH}                                          lem_propTH 5 for Theta^(+,-): exponential decay, B_{t,|a|}
    BAProp5s      687   1_2:1119  \begin{lemma}\label{lem_propTH}                                          lem_propTH 5s for (sigma,sigma): 1_{a=0} + g^2 e^{-|a|/2}
    BAProp6       697   1_2:1119  \begin{lemma}\label{lem_propTH}                                          lem_propTH 6: unit first differences
    BAProp7       708   1_2:1119  \begin{lemma}\label{lem_propTH}                                          lem_propTH 7: unit second differences
    BAProp8       720   1_2:1119  \begin{lemma}\label{lem_propTH}                                          lem_propTH 8: zero mode
    BAProp5to8    729   1_2:1119  \begin{lemma}\label{lem_propTH}                                          bundle of 5-8 (constants (d,Lambda,kappa))
    BAMainInd     1071  7_8:1825  \begin{theorem}\label{lem:main_ind_BA}                                   lem:main_ind_BA: kappa,eps,d first, then c_d <= 10^-2, then the sequence; flow of zztE_BA
    BAGbEXP       1115  7_8:1916  \begin{lemma}\label{lem_GbEXP_BA}                                        lem_GbEXP_BA: (GiiGEX_BA), (GijGEX_BA), (GavLGEX_BA) [RBSO1D L6.1]
    BAConArg      1160  7_8:1956  \begin{lemma}\label{lem_ConArg_BA}                                       lem_ConArg_BA parts 1, 2 [RBSO1D L7.1]; g_s = g sqrt(s/t)
    BAStep1       1170  7_8:1990  With \Cref{lem_GbEXP_BA,lem_ConArg_BA}, Step 1 of the proof of \Cref{l   Step 1 for BA (lRB1), (Gtmwc)
    BAStep2       1246  7_8:1993  \noindent{\bf Proof of Step 2 for \Cref{lem:main_ind_BA}.}               Step 2 for BA: (Gt_bound_flow), (Gt_avgbound_flow), (Eq:Gdecay_w)
    BAEMn2Exp     1262  7_8:1999  \be\label{eq:MG_conclusion3_BA}                                          (eq:MG_conclusion3_BA) with a deterministic J >= W^-d
    BAKsolve      1295  1_2:1175  \begin{align}\label{Kn2sol}\cK^{(2)}_{t,\bsig,\ba}&= \sum_{b}\Theta_{t   (Kn2sol), (Kn3sol); IsKLoopS with M-loops
    BAKbound      1313  1_2:1056  \begin{equation}\label{eq:bcal_k}                                        ML:Kbound for BA (proof A:600-740)
    BAlanlw       1429  B:359     \begin{lemma}[Basic expansion, Lemma B.9 of \cite{yang2024Del}]\label{   lanlw [yang2024Del B.9]
    BAlweight     1436  B:376     \begin{lemma} [Weight expansion, Lemma B.10 of \cite{yang2024Del}]\lab   lem_lweight [B.10]
    BAGGGamma     1445  B:393     \begin{lemma}[$GG$ expansion, Lemma B.11 of \cite{yang2024Del}]          GG expansion [B.11] with the corrected coefficient (T2161a)
    BAEnd_decol   1565  1_2:651   \item The delocalization estimate \eqref{eq:psikLinfty} holds.           MR:decol_BA bullet 1: (eq:psikLinfty) 1_2:366, energies in the rho-bulk
    BAEnd_locSC   1543  1_2:653   \item The local laws \eqref{G_bound} and \eqref{G_bound_ave} hold for    bullet 2: (G_bound), (G_bound_ave) 1_2:388-393 on D^BA
    BAEnd_QUE     1602  1_2:655   \item The QUE estimates \eqref{Meq:QUE} and \eqref{Meq:QUE2} hold, and   bullet 3: (Meq:QUE), (Meq:QUE2) with E in the rho-bulk
    BAEnd_BUniv   1652  1_2:454   \begin{equation}\label{eq:universality}                                  bullet 3: (eq:universality), density-normalised (DECISIONS 11)
    BAEnd_QDiff   1548  1_2:657   \item Recall the variance matrix \(S\) from \eqref{bandcwV} and the ma   bullet 4: (eq:diffu1)-(Meq:QdS2) with (Theta M), def:Theta_BA 1_2:658
    BAThm27       1659  1_2:644   \begin{theorem}[Main results for the block Anderson model]\label{MR:de   MR:decol_BA: the five endpoints
    BAGlueChain   1862  7_8:1832  With \Cref{lem:main_ind_BA} in hand, we can establish \Cref{MR:decol_B   chain induction in t (BA-V2): BAMainInd from the Step 1-2 pins, BAKbound, the graph expansions; Steps 3-6 verbatim (7_8:2100-2105)
    BAGlueLoc     1833  7_8:1835  Fix $z=\hat{E}+\ii \eta\in \mathbf D_{\kappa,\e}$, and choose the flow   proof of MR:decol_BA: BAMainInd + zztE_BA + (eq:BtBt) + (Kn2sol) + net lemma
    BAGlueQDiff   1837  7_8:1835  Fix $z=\hat{E}+\ii \eta\in \mathbf D_{\kappa,\e}$, and choose the flow   same, quantum diffusion
    BAGlueDecol   1841  1_2:397   \begin{proof}[\bf Proof of \Cref{MR:decol}]                              delocalization from (G_bound) via (eq:ukx)
    BAGlueQUE     1844  1_2:520   \begin{proof}[\bf Proof of Theorem \ref{MR:QUE}]                         QUE from (Meq:QdS1),(Meq:QdS2) as in [YY_25 Thm 2.5], [DYYY25 Thm 2.4]
    BAGlueUniv    1847  1_2:454   \begin{equation}\label{eq:universality}                                  universality from the local law, [DYYY25] and LSY Thm 2.2
### P.2c which steps reuse the ST pins with `M` for `m` (paper 7_8:2100-2105) and which BA statements exist
    step                    paper                       BA change                                                     pins (this probe)                         tickets
    Step 1                  7_8:1987-1990               lem_GbEXP_BA 7_8:1916, lem_ConArg_BA 7_8:1956                 BAGbEXP, BAConArg, BAStep1               BA-G1..G6, S1..S3
    Step 2                  7_8:1993-2096               (eq:MG_conclusion3_BA) with a deterministic J (7_8:1999)      BAStep2, BAEMn2Exp                       BA-T1..T8
    Steps 3, 4              7_8:2100-2101               none ("extend verbatim")                                      ST pins over baFMz (16 ST*g forms)       BA-U1..U3
    Step 5 except Step5_larget  7_8:2100-2101           none                                                          ST Step 5 pins over baFMz                BA-U4, U6
    Step 5 sec:Step5_larget 7_8:2101 (3_5:2284, 1-t >= g^2)  uses lem_GbEXP_BA ([RBSO1D S7.3] parallel)               BAGbEXP consumed                          BA-U5
    Step 6                  7_8:2100-2101, B:286-525    lem:LWterm_EXP with GGGamma; graph layer (BA-L1..L4 of T2040)   BAlanlw, BAlweight, BAGGGamma           BA-L1..L4, V1
    chain induction in t    7_8:1825-1832               lem:main_ind_BA                                               BAMainInd (carrier pin STMainIndG), BAGlueChain  BA-V2
    from t_0 to Thm 2.7     7_8:1835, 1_2:672           zztE_BA, (eq:BtBt), (Kn2sol), net lemma, corollaries           BAGlue*, BAEnd_*, BAThm27                 BA-M1..M3, N1, N2
### P.2d statements of the pins, extracted from the probe by script (`python3 $S/statements.py <names>`; docstrings stripped; they carry the paper cites)
    $ python3 $S/statements.py BAmExists BAmUniqReal BAmBoundary BAWard BAPropM BAoffDiag BAImmLower BAProp5 BAProp5s BAProp6 BAProp7 BAProp8 BAProp5to8 BAMainInd BAGbEXP BAConArg BAStep1 BAStep2 BAEMn2Exp BAKsolve BAKbound BAlanlw BAlweight BAGGGamma BAEnd_locSC BAEnd_QDiff BAEnd_decol BAEnd_QUE BAEnd_BUniv BAThm27 BAGlueChain BAGlueLoc BAGlueQDiff BAGlueDecol BAGlueQUE BAGlueUniv
    -- RBM3D/Probe/T2161Pins.lean:571
    def BAmExists : Prop :=
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ z : ℂ, 0 < z.im →
        haveI : NeZero L := ⟨by omega⟩
        ∃! m : ℂ, BASelf d L g z m
    -- RBM3D/Probe/T2161Pins.lean:578
    def BAmUniqReal : Prop :=
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ (E : ℝ) (m m' : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BASelf d L g (E : ℂ) m → BASelf d L g (E : ℂ) m' → m = m'
    -- RBM3D/Probe/T2161Pins.lean:585
    def BAmBoundary : Prop :=
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ E : ℝ,
        haveI : NeZero L := ⟨by omega⟩
        (∀ m : ℂ, BASelf d L g (E : ℂ) m →
          Tendsto (fun η : ℝ => BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 m)) ∧
        ((¬ ∃ m : ℂ, BASelf d L g (E : ℂ) m) →
          Tendsto (fun η : ℝ => (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] (0 : ℝ)) (𝓝 0))
    -- RBM3D/Probe/T2161Pins.lean:597
    def BAWard : Prop :=
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ (z m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        0 ≤ z.im → BASelf d L g z m →
          (∀ a b r : Zd d L, BAMB d L g z m (a + r) (b + r) = BAMB d L g z m a b) ∧
          (∀ a : Zd d L, BAMB d L g z m a a = m) ∧
          ∀ a : Zd d L, (m.im + z.im) * ∑ b, ‖BAMB d L g z m a b‖ ^ 2 = m.im
    -- RBM3D/Probe/T2161Pins.lean:612
    def BAPropM (Λ κ : ℝ) : Prop :=
      3 ≤ d → 0 < Λ → 0 < κ →
        ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
          ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
            haveI : NeZero L := ⟨by omega⟩
            BAReal d L g κ E m →
              (∀ a b r : Zd d L, BAMB d L g (E : ℂ) m (a + r) (b + r) = BAMB d L g (E : ℂ) m a b) ∧
              (∀ a : Zd d L, BAMB d L g (E : ℂ) m a a = m) ∧
              (∀ a : Zd d L, ∑ b, ‖BAMB d L g (E : ℂ) m a b‖ ^ 2 = 1) ∧ ‖m‖ ≤ 1 ∧
              (g < (2 * C)⁻¹ → ∀ a b : Zd d L,
                C⁻¹ * g * (if Adj d L a b then 1 else 0) ≤ ‖BAMB d L g (E : ℂ) m a b‖ ∧
                  ‖BAMB d L g (E : ℂ) m a b‖ ≤ (C * g) ^ zdistD d L (a - b)) ∧
              ((2 * C)⁻¹ ≤ g → ∀ a b : Zd d L,
                ‖BAMB d L g (E : ℂ) m a b‖ ≤ c⁻¹ * Real.exp (-c * (zdistD d L (a - b) : ℝ)))
    -- RBM3D/Probe/T2161Pins.lean:631
    def BAoffDiag (Λ κ : ℝ) : Prop :=
      3 ≤ d → 0 < Λ → 0 < κ →
        ∃ ε : ℝ, 0 < ε ∧
          ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
            haveI : NeZero L := ⟨by omega⟩
            BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
              ε ≤ ‖1 - (t : ℂ) * m ^ 2‖ ∧
              ∑ a ∈ Finset.univ.erase (0 : Zd d L), ‖BAMss d L (BAMB d L g (E : ℂ) m) true true 0 a‖
                ≤ (1 - ε) * ‖1 - (t : ℂ) * m ^ 2‖
    -- RBM3D/Probe/T2161Pins.lean:645
    def BAImmLower (Λ κ : ℝ) : Prop :=
      3 ≤ d → 0 < Λ → 0 < κ →
        ∃ c : ℝ, 0 < c ∧
          ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
            haveI : NeZero L := ⟨by omega⟩
            BAReal d L g κ E m → ∀ η : ℝ, 0 < η → η ≤ 1 →
              c ≤ (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im
    -- RBM3D/Probe/T2161Pins.lean:676
    def BAProp5 (Λ κ : ℝ) : Prop :=
      3 ≤ d → 0 < Λ → 0 < κ →
        ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
          ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
            haveI : NeZero L := ⟨by omega⟩
            BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
              ‖BATheta d L g E m t σ₁ σ₂ 0 a‖
                ≤ C * Bparam d L g t (zdistD d L a) * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t)
    -- RBM3D/Probe/T2161Pins.lean:687
    def BAProp5s (Λ κ : ℝ) : Prop :=
      3 ≤ d → 0 < Λ → 0 < κ →
        ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
          ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
            haveI : NeZero L := ⟨by omega⟩
            BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ : Bool, ∀ a : Zd d L,
              ‖BATheta d L g E m t σ σ 0 a‖
                ≤ C * ((if a = 0 then (1 : ℝ) else 0) + g ^ 2 * Real.exp (-c * (zdistD d L a : ℝ)))
    -- RBM3D/Probe/T2161Pins.lean:697
    def BAProp6 (Λ κ c : ℝ) : Prop :=
      3 ≤ d → 0 < Λ → 0 < κ → 0 < c → c < 1 →
        ∃ C : ℝ, 0 < C ∧
          ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
            haveI : NeZero L := ⟨by omega⟩
            BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, ∀ a r : Zd d L,
              (zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ) →
              ‖BATheta d L g E m t σ₁ σ₂ 0 (a + r) - BATheta d L g E m t σ₁ σ₂ 0 a‖
                ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹
    -- RBM3D/Probe/T2161Pins.lean:708
    def BAProp7 (Λ κ c : ℝ) : Prop :=
      3 ≤ d → 0 < Λ → 0 < κ → 0 < c → c < 1 →
        ∃ C : ℝ, 0 < C ∧
          ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
            haveI : NeZero L := ⟨by omega⟩
            BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, ∀ a r : Zd d L,
              (zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ) →
              ‖BATheta d L g E m t σ₁ σ₂ 0 (a + r) + BATheta d L g E m t σ₁ σ₂ 0 (a - r)
                  - 2 * BATheta d L g E m t σ₁ σ₂ 0 a‖
                ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) ^ 2 * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹
    -- RBM3D/Probe/T2161Pins.lean:720
    def BAProp8 (Λ κ : ℝ) : Prop :=
      3 ≤ d → 0 < Λ → 0 < κ →
        ∃ C : ℝ, 0 < C ∧
          ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
            haveI : NeZero L := ⟨by omega⟩
            BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
              ‖BATheta0 d L g E m t σ₁ σ₂ 0 a‖ ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹
    -- RBM3D/Probe/T2161Pins.lean:729
    structure BAProp5to8 (Λ κ c : ℝ) : Prop where
      decay : BAProp5 d Λ κ
      short : BAProp5s d Λ κ
      diffOne : BAProp6 d Λ κ c
      diffTwo : BAProp7 d Λ κ c
      zeroMode : BAProp8 d Λ κ
    -- RBM3D/Probe/T2161Pins.lean:1071
    def BAMainInd (d : ℕ) : Prop :=
      STMainIndG d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
        (fun sz z n => BAflowT0 sz z n)
    -- RBM3D/Probe/T2161Pins.lean:1115
    def BAGbEXP (d : ℕ) : Prop :=
      3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
        ∃ c : ℝ, 0 < c ∧
          ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
            ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
              ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℝ,
                (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧
                  Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
                ∀ Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ,
                  (∀ n a b, 0 < Φ n a b ∧ Φ n a b ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
                  BAGbEXPpre sz z t ε₀ Ψ Φ → BAGbEXPconcl sz z t Ψ Φ c
    -- RBM3D/Probe/T2161Pins.lean:1160
    def BAConArg (d : ℕ) : Prop :=
      ∀ κ ε 𝔡 ε₁ : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → 0 < ε₁ →
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
          ∀ s t : ℕ → ℝ, (∀ n, ε₁ ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
            STLmaxg (baFM sz (BAlamS sz z s t) (BAflowEs sz z)) s →
            (∀ k : ℕ, 2 ≤ k → BAConArgLoop sz z s t k) ∧ BAConArgVec sz z s t
    -- RBM3D/Probe/T2161Pins.lean:1170
    def BAStep1 (d : ℕ) : Prop :=
      ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
        ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 →
          ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
            ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ BAflowT0 sz z n) → (∀ n, s n < t n) →
              (∀ n, t n ≤ BAflowT0 sz z n) →
              STKboundg (baFMz sz z) → STLKg (baFMz sz z) s → STLocalMaxg (baFMz sz z) s →
              STConStInd sz 𝔠d s t →
                STStep1Loopg (baFMz sz z) s t ∧ STStep1Weakg (baFMz sz z) s t
    -- RBM3D/Probe/T2161Pins.lean:1246
    def BAStep2 (d : ℕ) : Prop :=
      3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
        ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
          ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
            ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ BAflowT0 sz z n) → (∀ n, s n < t n) →
              (∀ n, t n ≤ BAflowT0 sz z n) →
              STLKg (baFMz sz z) s → STDecayg (baFMz sz z) s → STConStInd sz 𝔠d s t →
              STStep1Loopg (baFMz sz z) s t → STStep1Weakg (baFMz sz z) s t →
                STStep2Localg (baFMz sz z) s t ∧ STStep2Avgg (baFMz sz z) s t ∧
                  STStep2Decayg (baFMz sz z) Cd s t
    -- RBM3D/Probe/T2161Pins.lean:1262
    def BAEMn2Exp (d : ℕ) : Prop :=
      ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
            ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℝ,
              (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧
                Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
              STInitialGT2g (baFMz sz z) t ε₀ Ψ →
              ∀ ℓ : ℕ → ℝ, (∀ᶠ n in atTop, 0 ≤ ℓ n ∧ ℓ n ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 *
                  ellT (sz.L n) (sz.lam n) (t n)) →
                (∀ D : ℝ, 0 < D → STLWassmExpg (baFMz sz z) t D ℓ) →
                ∀ D : ℝ, 0 < D → ∀ J : ℕ → ℝ, (∀ n, (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ J n) →
                  Prec sz (U := fun _ => Unit) (fun n _ ω => STJhatg (baFMz sz z) n D (ℓ n) (t n) ω)
                    (fun n _ _ => J n) →
                  Prec sz (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
                    (fun n p ω => ‖STEEg (baFMz sz z) n (t n) p.1 p.2.1 p.2.2 ω‖)
                    (fun n p _ => ((baFMz sz z).eta n (t n))⁻¹ *
                      ((sz.Bctl n (t n)) ^ (1 / 2 : ℝ) + (J n) ^ 3) *
                      (STprof sz n (t n) D (ℓ n) (p.2.2 0) (p.2.2 1)) ^ 2)
    -- RBM3D/Probe/T2161Pins.lean:1295
    def BAKsolve : Prop :=
      ∀ (Λ κ : ℝ), 0 < Λ → 0 < κ → ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m →
          ∃ K : ℝ → LoopIdx (Zd d L) → ℂ,
            IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
              (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1) K ∧
            (∀ K' : ℝ → LoopIdx (Zd d L) → ℂ,
              IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
                (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1) K' →
              ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ I : LoopIdx (Zd d L), I.WF → K' t I = K t I) ∧
            ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (σ : Bool × Bool) (a₁ a₂ : Zd d L),
              K t ⟨[σ.1, σ.2], [a₁, a₂]⟩ =
                (((W : ℂ) ^ d)⁻¹) * (BATheta d L g E m t σ.1 σ.2 * BAMss d L (BAMB d L g (E : ℂ) m) σ.1 σ.2) a₁ a₂
    -- RBM3D/Probe/T2161Pins.lean:1313
    def BAKbound : Prop :=
      ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → STKboundg (baFMz sz z)
    -- RBM3D/Probe/T2161Pins.lean:1429
    def BAlanlw (d : ℕ) : Prop :=
      ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), BASelf d L g0 (E : ℂ) m →
        0 ≤ t → t < 1 →
        ∀ (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (x y : Idx d L W),
          ∫ ω, BAlanlwL d L W g0 E t m P x y ω ∂(PF d L W 0) = ∫ ω, BAlanlwR d L W g0 E t m P x y ω ∂(PF d L W 0)
    -- RBM3D/Probe/T2161Pins.lean:1436
    def BAlweight (d : ℕ) : Prop :=
      ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), BASelf d L g0 (E : ℂ) m →
        0 ≤ t → t < 1 →
        ∀ (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (x : Idx d L W),
          ∫ ω, BAlweightL d L W g0 E t m P x ω ∂(PF d L W 0) = ∫ ω, BAlweightR d L W g0 E t m P x ω ∂(PF d L W 0)
    -- RBM3D/Probe/T2161Pins.lean:1445
    def BAGGGamma (d : ℕ) : Prop :=
      ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), BASelf d L g0 (E : ℂ) m →
        0 ≤ t → t < 1 →
        ∀ (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (x y y' : Idx d L W),
          ∫ ω, BAGGGammaL d L W g0 E t m P x y y' ω ∂(PF d L W 0) =
            ∫ ω, BAGGGammaR d L W g0 E t m P x y y' ω ∂(PF d L W 0)
    -- RBM3D/Probe/T2161Pins.lean:1543
    def BAEnd_locSC (d : ℕ) : Prop :=
      3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ ε : ℝ, 0 < κ → 0 < ε → BAlocSCConcl sz κ ε
    -- RBM3D/Probe/T2161Pins.lean:1548
    def BAEnd_QDiff (d : ℕ) : Prop :=
      3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ ε : ℝ, 0 < κ → 0 < ε → BAqdConcl sz κ ε
    -- RBM3D/Probe/T2161Pins.lean:1565
    def BAEnd_decol (d : ℕ) : Prop :=
      3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D →
        BAdecolConcl sz κ τ D
    -- RBM3D/Probe/T2161Pins.lean:1602
    def BAEnd_QUE (d : ℕ) : Prop :=
      3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
        ∀ κ : ℝ, 0 < κ → ∀ ε₀ c τ : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < c → c < ε₀ → c < 𝔡 / 5 → 0 < τ →
          BAqueConcl sz 𝔡 κ ε₀ c τ
    -- RBM3D/Probe/T2161Pins.lean:1652
    def BAEnd_BUniv (d : ℕ) : Prop :=
      3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ (k : ℕ), 1 ≤ k → ∀ κ : ℝ, 0 < κ →
        ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → ∀ E' : ℝ, |E'| < 2 →
          ∀ O : (Fin k → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O → HasCompactSupport O →
            BAunivConcl sz k E E' O
    -- RBM3D/Probe/T2161Pins.lean:1659
    def BAThm27 (d : ℕ) : Prop :=
      BAEnd_decol d ∧ BAEnd_locSC d ∧ BAEnd_QUE d ∧ BAEnd_BUniv d ∧ BAEnd_QDiff d
    -- RBM3D/Probe/T2161Pins.lean:1862
    def BAGlueChain (d : ℕ) : Prop :=
      BAGbEXP d → BAConArg d → BAStep1 d → BAStep2 d → BAEMn2Exp d → BAKbound d →
        BAlanlw d → BAlweight d → BAGGGamma d → BAMainInd d
    -- RBM3D/Probe/T2161Pins.lean:1833
    def BAGlueLoc (d : ℕ) : Prop :=
      BAmUniqReal d → (∀ Λ κ : ℝ, BAImmLower d Λ κ) → BAMainInd d → BAEnd_locSC d
    -- RBM3D/Probe/T2161Pins.lean:1837
    def BAGlueQDiff (d : ℕ) : Prop :=
      BAKsolve d → BAMainInd d → BAEnd_locSC d → BAEnd_QDiff d
    -- RBM3D/Probe/T2161Pins.lean:1841
    def BAGlueDecol (d : ℕ) : Prop := BAEnd_locSC d → BAEnd_decol d
    -- RBM3D/Probe/T2161Pins.lean:1844
    def BAGlueQUE (d : ℕ) : Prop := BAEnd_locSC d → BAEnd_QDiff d → BAEnd_QUE d
    -- RBM3D/Probe/T2161Pins.lean:1847
    def BAGlueUniv (d : ℕ) : Prop := BAmBoundary d → BAEnd_locSC d → BAEnd_BUniv d
### P.2e the definitions the pins use (bulk forms, carrier, flow data, `Thm27At`)
    $ python3 $S/statements.py BASelf BAedgeBulk BAdistBulk BAbulk BAReal BAdom BAFlow BAendDom FlowFM bandFM baFM BAflowT0 BAflowE Thm27At
    -- RBM3D/Probe/T2161Pins.lean:191
    def BASelf (g : ℝ) (z m : ℂ) : Prop :=
      0 < m.im ∧ m = (((L ^ d : ℕ) : ℂ))⁻¹ * (BAMB d L g z m).trace
    -- RBM3D/Probe/T2161Pins.lean:442
    def BAedgeBulk (e κ E : ℝ) : Prop := |E| ≤ e - κ
    -- RBM3D/Probe/T2161Pins.lean:448
    def BAdistBulk (g κ E : ℝ) : Prop := ∀ x : ℝ, x ∉ BAsuppSet d L g → κ ≤ |E - x|
    -- RBM3D/Probe/T2161Pins.lean:451
    def BAbulk (g κ E : ℝ) : Prop := κ ≤ BArho d L g E
    -- RBM3D/Probe/T2161Pins.lean:455
    def BAReal (g κ E : ℝ) (m : ℂ) : Prop := BASelf d L g (E : ℂ) m ∧ κ ≤ m.im
    -- RBM3D/Probe/T2161Pins.lean:459
    def BAdom (N : ℕ) (g κ ε : ℝ) (z : ℂ) : Prop :=
      κ ≤ (BAm d L g z).im ∧ (N : ℝ) ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1
    -- RBM3D/Probe/T2161Pins.lean:1037
    def BAFlow (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) : Prop :=
      sz.Admissible 𝔠 𝔡 ∧ ∀ n, BAdom d (sz.L n) (sz.size n) (sz.lam n) κ ε (z n)
    -- RBM3D/Probe/T2161Pins.lean:1489
    def BAendDom (κ ε : ℝ) (n : ℕ) (z : ℂ) : Prop :=
      BAbulk d (sz.L n) (sz.lam n) κ z.re ∧ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1
    -- RBM3D/Probe/T2161Pins.lean:829
    structure FlowFM {d : ℕ} (sz : Sizes d) where
      /-- `𝓛^{(k)}_{t,σ,a}` at size index `n` -/
      L : ∀ (n : ℕ) (t : ℝ) {k : ℕ}, (Fin k → Bool) → (Fin k → Zd d (sz.L n)) → sz.SeqΩ → ℂ
      /-- `𝒦^{(k)}_{t,σ,a}` -/
      K : ∀ (n : ℕ) (t : ℝ) {k : ℕ}, (Fin k → Bool) → (Fin k → Zd d (sz.L n)) → ℂ
      /-- the entries of `G_t` -/
      G : ∀ (n : ℕ) (t : ℝ), sz.SeqΩ → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ
      /-- the entries of `M` -/
      M : ∀ n : ℕ, Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ
      /-- the block kernel `S^{(B)}` of the variance (`S^{(B)}(g)` for the band model, `S^{(B)}(0) = I` for `BA`) -/
      S : ∀ n : ℕ, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ
      /-- `η_t` (`(eta)`, `1_2:720`) -/
      eta : ∀ (n : ℕ) (t : ℝ), ℝ
      /-- the one-loop value `m` (`𝒦^{(1)}_{+} = m(E)`, `Def_Ktza`) -/
      m : ℕ → ℂ
    -- RBM3D/Probe/T2161Pins.lean:966
    def bandFM {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) : FlowFM sz where
      L := fun n t {_k} σ a ω => Lloop sz n (E n) t σ a ω
      K := fun n t {_k} σ a => STKloop sz n (E n) t σ a
      G := fun n t ω x y => Gt sz n (E n) t true ω x y
      M := fun n x y => if x = y then mE (E n) else 0
      S := fun n => SB d (sz.L n) (sz.lam n)
      eta := fun n t => etaT (E n) t
      m := fun n => mE (E n)
    -- RBM3D/Probe/T2161Pins.lean:976
    def baFM {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) : FlowFM sz where
      L := fun n t {_k} σ a ω => BALloop sz lam0 E n t σ a ω
      K := fun n t {_k} σ a => BAKloop sz lam0 E n t σ a
      G := fun n t ω x y => BAGt sz lam0 E n t ω x y
      M := fun n x y => BAMfine sz lam0 E n x y
      S := fun n => 1
      eta := fun n t => etaOf (BAmF sz lam0 E n) t
      m := fun n => BAmF sz lam0 E n
    -- RBM3D/Probe/T2161Pins.lean:1028
    def BAflowT0 (z : ℕ → ℂ) (n : ℕ) : ℝ := BAt0 (z n) (BAm d (sz.L n) (sz.lam n) (z n))
    -- RBM3D/Probe/T2161Pins.lean:279
    def BAflowE (z m : ℂ) : ℝ := (BAt0 z m * z.re - (1 - BAt0 z m) * m.re) / Real.sqrt (BAt0 z m)
    -- RBM3D/Probe/T2161Pins.lean:2547
    def Thm27At (sz : Sizes 3) (κ E : ℝ) : Prop :=
      BAdecolConcl sz κ (1 / 50) 10 ∧ BAlocSCConcl sz κ (1 / 10) ∧
        BAqueConcl sz (1 / 10) κ (1 / 30) (1 / 100) (1 / 100) ∧ BAunivConcl sz 1 E 0 bump1 ∧ BAqdConcl sz κ (1 / 10)
### P.2f the skeleton and the class instance (signatures)
    $ python3 $S/statements.py 'BAThm27_skeleton~' 'BAThm27_skeleton_chain~' 'inst_cls_Thm27_chain~' 'inst_cls_Thm27~' 'inst_cls_gaps~' 'inst_cls_odd~' 'inst_cls_interval~' 'inst_BAThm27_skeleton~'
    -- RBM3D/Probe/T2161Pins.lean:1851
    theorem BAThm27_skeleton (d : ℕ) (hU : BAmUniqReal d) (hI : ∀ Λ κ : ℝ, BAImmLower d Λ κ) (hB : BAmBoundary d)
        (hK : BAKsolve d) (hM : BAMainInd d)
        (g1 : BAGlueLoc d) (g2 : BAGlueQDiff d) (g3 : BAGlueDecol d) (g4 : BAGlueQUE d) (g5 : BAGlueUniv d) :
        BAThm27 d := by
    -- RBM3D/Probe/T2161Pins.lean:1868
    theorem BAThm27_skeleton_chain (d : ℕ) (hU : BAmUniqReal d) (hI : ∀ Λ κ : ℝ, BAImmLower d Λ κ) (hB : BAmBoundary d)
        (hK : BAKsolve d) (hG : BAGbEXP d) (hC : BAConArg d) (h1 : BAStep1 d) (h2 : BAStep2 d) (hE : BAEMn2Exp d)
        (hKb : BAKbound d) (hl1 : BAlanlw d) (hl2 : BAlweight d) (hl3 : BAGGGamma d) (g0 : BAGlueChain d)
        (g1 : BAGlueLoc d) (g2 : BAGlueQDiff d) (g3 : BAGlueDecol d) (g4 : BAGlueQUE d) (g5 : BAGlueUniv d) :
        BAThm27 d :=
    -- RBM3D/Probe/T2161Pins.lean:2574
    theorem inst_cls_Thm27_chain (L : ℕ) [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) (hg10 : g ≤ 10)
        (huniq : BAmUniqReal 3) (hI : ∀ Λ κ : ℝ, BAImmLower 3 Λ κ) (hB : BAmBoundary 3)
        (hK : BAKsolve 3) (hG : BAGbEXP 3) (hC : BAConArg 3) (h1 : BAStep1 3) (h2 : BAStep2 3) (hE : BAEMn2Exp 3)
        (hKb : BAKbound 3) (hl1 : BAlanlw 3) (hl2 : BAlweight 3) (hl3 : BAGGGamma 3) (g0 : BAGlueChain 3)
        (g1 : BAGlueLoc 3) (g2 : BAGlueQDiff 3) (g3 : BAGlueDecol 3) (g4 : BAGlueQUE 3) (g5 : BAGlueUniv 3) :
        Thm27At (clsS L hL hg) (clsκ L hg) (fp L hg).E :=
    -- RBM3D/Probe/T2161Pins.lean:2554
    theorem inst_cls_Thm27 (L : ℕ) [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) (hg10 : g ≤ 10)
        (huniq : BAmUniqReal 3) (h : BAThm27 3) :
        Thm27At (clsS L hL hg) (clsκ L hg) (fp L hg).E := by
    -- RBM3D/Probe/T2161Pins.lean:2588
    theorem inst_cls_gaps (huniq : BAmUniqReal 3) (h : BAThm27 3) :
        Thm27At (clsS 4 (by norm_num) hg10) (clsκ 4 hg10) (fp 4 hg10).E :=
    -- RBM3D/Probe/T2161Pins.lean:2593
    theorem inst_cls_odd (huniq : BAmUniqReal 3) (h : BAThm27 3) :
        Thm27At (clsS 5 (by norm_num) hg_fifth) (clsκ 5 hg_fifth) (fp 5 hg_fifth).E :=
    -- RBM3D/Probe/T2161Pins.lean:2598
    theorem inst_cls_interval (huniq : BAmUniqReal 3) (h : BAThm27 3) :
        Thm27At (clsS 4 (by norm_num) hg_3_10) (clsκ 4 hg_3_10) (fp 4 hg_3_10).E :=
    -- RBM3D/Probe/T2161Pins.lean:2366
    theorem inst_BAThm27_skeleton (hU : BAmUniqReal 3) (hI : ∀ Λ κ : ℝ, BAImmLower 3 Λ κ) (hB : BAmBoundary 3)
        (hK : BAKsolve 3) (hM : BAMainInd 3)
        (g1 : BAGlueLoc 3) (g2 : BAGlueQDiff 3) (g3 : BAGlueDecol 3) (g4 : BAGlueQUE 3) (g5 : BAGlueUniv 3)
        (hbulk : ∀ᶠ n in atTop, BAbulk 3 (sz0.L n) (sz0.lam n) (1 / 10) 0) :
        BAdecolConcl sz0 (1 / 10) (1 / 50) 10 ∧ BAlocSCConcl sz0 (1 / 10) (1 / 10) ∧
          BAqueConcl sz0 (1 / 10) (1 / 10) (1 / 30) (1 / 100) (1 / 100) ∧ BAunivConcl sz0 1 0 0 bump1 ∧
          BAqdConcl sz0 (1 / 10) (1 / 10) :=

## P.3 The bulk condition (T2001d/l): numerics beyond section (a)
The four forms and the classes are in section (a) (scripts `ba_supp`, `ba_check`, `ba_gcL`, `ba_cusp`, `ba_vac`, `ba_det`, `ba_flow`, `ba_adm`, outputs pasted there; P.12 has their text).
    $ python3 $S/n1_immlower.py   # BAImmLower at the vacuity classes and two extremes
    d=3 rho-bulk B_k (k=0.05): min over E in B_k, eta in (0,1] of Im m(E+i eta)  [pi*k=0.1571]
    gaps  L=4 g=10         |B_k| pts= 15/241  min Im m = 0.0858 at (E,eta)=(-40.180,1)  ratio to pi*k = 0.55
    odd   L=5 g=0.2        |B_k| pts=235/241  min Im m = 0.1852 at (E,eta)=(-2.191,0.03)  ratio to pi*k = 1.18
    cusp- L=4 g=0.35422    |B_k| pts=215/241  min Im m = 0.1525 at (E,eta)=(-2.691,0.1)  ratio to pi*k = 0.97
    intvl L=4 g=0.3        |B_k| pts=229/241  min Im m = 0.1598 at (E,eta)=(-2.506,0.03)  ratio to pi*k = 1.02
    small L=6 g=0.001      |B_k| pts=237/241  min Im m = 0.1788 at (E,eta)=(1.967,0.01)  ratio to pi*k = 1.14
    large g L=6 g=3        |B_k| pts= 65/241  min Im m = 0.0385 at (E,eta)=(-15.173,1)  ratio to pi*k = 0.25
    $ python3 $S/n1_equiv.py   # rho-form against the paper form: c1(kappa) = min rho_N on |E| <= e - kappa; c2 = min{e-|E| : rho >= 0.05}
    d=3, L even, no gaps.   kappa:  c1(kappa)=min rho on |E|<=e-kappa ; sqrt(kappa)/pi (semicircle edge) ; then k'=0.05: c2(k')=min{e-|E|: rho>=k'}
    L=4 g=0.01  e=2.0006  k=0.30: 0.1676 (sc 0.1743) | k=0.10: 0.0994 (sc 0.1007) | k=0.03: 0.0549 (sc 0.0551) | k=0.01: 0.0318 (sc 0.0318) | k'=0.05: c2=0.0250
    L=4 g=0.1   e=2.0616  k=0.30: 0.1598 (sc 0.1743) | k=0.10: 0.0949 (sc 0.1007) | k=0.03: 0.0528 (sc 0.0551) | k=0.01: 0.0306 (sc 0.0318) | k'=0.05: c2=0.0292
    L=4 g=0.3   e=2.6381  k=0.30: 0.0639 (sc 0.1743) | k=0.10: 0.0468 (sc 0.1007) | k=0.03: 0.0275 (sc 0.0551) | k=0.01: 0.0167 (sc 0.0318) | k'=0.05: c2=0.1209
    L=6 g=0.01  e=2.0006  k=0.30: 0.1676 (sc 0.1743) | k=0.10: 0.0994 (sc 0.1007) | k=0.03: 0.0549 (sc 0.0551) | k=0.01: 0.0318 (sc 0.0318) | k'=0.05: c2=0.0250
    L=6 g=0.1   e=2.0609  k=0.30: 0.1601 (sc 0.1743) | k=0.10: 0.0952 (sc 0.1007) | k=0.03: 0.0530 (sc 0.0551) | k=0.01: 0.0307 (sc 0.0318) | k'=0.05: c2=0.0292
    L=6 g=0.3   e=2.5948  k=0.30: 0.0934 (sc 0.1743) | k=0.10: 0.0433 (sc 0.1007) | k=0.03: 0.0248 (sc 0.0551) | k=0.01: 0.0151 (sc 0.0318) | k'=0.05: c2=0.1297
    L=8 g=0.01  e=2.0006  k=0.30: 0.1676 (sc 0.1743) | k=0.10: 0.0994 (sc 0.1007) | k=0.03: 0.0549 (sc 0.0551) | k=0.01: 0.0318 (sc 0.0318) | k'=0.05: c2=0.0250
    L=8 g=0.1   e=2.0609  k=0.30: 0.1601 (sc 0.1743) | k=0.10: 0.0952 (sc 0.1007) | k=0.03: 0.0530 (sc 0.0551) | k=0.01: 0.0307 (sc 0.0318) | k'=0.05: c2=0.0275
    L=8 g=0.3   e=2.5836  k=0.30: 0.0956 (sc 0.1743) | k=0.10: 0.0505 (sc 0.1007) | k=0.03: 0.0253 (sc 0.0551) | k=0.01: 0.0151 (sc 0.0318) | k'=0.05: c2=0.1012

## P.4 Exponent and constant table where `M ≠ mI` (item 4)
    $ python3 $S/n2_table.py   # r = (1-|m|^2)/min_t|1-t m^2|, Dk, lam1, |M_0e|, decay rate ct (j = 1, 2, 3) at bulk points
    d=3, bulk points; r=(1-|m|^2)/min_t|1-t m^2| (A_det:32); Dk=(1/2d)sum_a K_0a|a|^2; lam1=1-Khat(2pi/L e1); nb=|M_{0 e1}|; ct=-log|M_{0,j e1}|/j (j=1,2,3)
    L   g      E       Im m    |m|     sum|M_0b|^2  r      Dk/g^2    lam1/(g^2 2(1-cos)) |M_0e|/min(g,1) ct
    5   0.05   0.000   0.9926  0.9926  0.999999999  0.015  1.005     1.002          0.978        ['3.02', '3.02', '2.01']  chk=0.0e+00
    5   0.05   1.209   0.7940  0.9926  0.999999999  0.015  1.016     1.012          0.983        ['3.01', '3.00', '2.00']  chk=0.0e+00
    5   0.3    0.000   0.8243  0.8243  0.999999999  0.321  1.156     1.040          0.594        ['1.73', '1.67', '1.11']  chk=4.4e-16
    5   0.3    1.565   0.6048  0.8007  0.999999998  0.359  1.534     1.310          0.601        ['1.71', '1.63', '1.08']  chk=6.7e-16
    5   1      0.000   0.4382  0.4538  0.999999997  0.794  0.773     0.555          0.138        ['1.98', '1.01', '0.67']  chk=0.0e+00
    5   1      3.829   0.2731  0.4805  0.999999998  0.815  0.892     0.614          0.156        ['1.86', '1.38', '0.92']  chk=1.1e-16
    7   0.05   0.000   0.9926  0.9926  0.999999999  0.015  1.005     1.003          0.978        ['3.02', '3.02', '3.02']  chk=2.2e-16
    7   0.05   1.209   0.7940  0.9926  0.999999999  0.015  1.016     1.014          0.983        ['3.01', '3.01', '3.00']  chk=4.4e-16
    7   0.3    0.000   0.8237  0.8237  0.999999999  0.321  1.200     1.111          0.595        ['1.72', '1.69', '1.68']  chk=6.7e-16
    7   0.3    1.553   0.6070  0.8011  0.999999998  0.358  1.567     1.398          0.595        ['1.72', '1.68', '1.82']  chk=4.4e-16
    7   1      0.000   0.3688  0.3690  0.999999998  0.864  1.280     0.902          0.144        ['1.94', '1.33', '0.87']  chk=0.0e+00
    7   1      3.794   0.2025  0.3072  0.999999995  0.913  1.614     1.050          0.115        ['2.17', '1.92', '0.87']  chk=1.1e-16
    7   3      10.909  0.0943  0.1663  0.999999992  0.982  0.205     0.136          0.062        ['2.78', '1.55', '0.64']  chk=0.0e+00
    9   0.05   0.000   0.9926  0.9926  0.999999999  0.015  1.005     1.004          0.978        ['3.02', '3.02', '3.02']  chk=2.2e-16
    9   0.05   1.209   0.7940  0.9926  0.999999999  0.015  1.016     1.015          0.983        ['3.01', '3.01', '3.01']  chk=2.2e-16
    9   0.3    0.000   0.8237  0.8237  0.999999999  0.321  1.205     1.145          0.595        ['1.72', '1.69', '1.68']  chk=4.4e-16
    9   0.3    1.549   0.6081  0.8009  0.999999998  0.359  1.580     1.461          0.597        ['1.72', '1.68', '1.72']  chk=4.4e-16
    9   1      0.000   0.4347  0.4349  0.999999998  0.811  1.682     1.161          0.135        ['2.00', '1.47', '1.09']  chk=0.0e+00
    9   1      3.779   0.2125  0.3457  0.999999995  0.901  2.730     1.674          0.114        ['2.17', '1.63', '0.95']  chk=2.2e-16
    9   3      0.000   0.3028  0.3031  0.999999997  0.908  0.308     0.198          0.050        ['2.99', '1.78', '0.97']  chk=0.0e+00
    9   10     0.000   0.2883  0.2883  0.999999997  0.917  0.029     0.018          0.015        ['4.18', '2.37', '0.95']  chk=2.2e-16

## P.5 Instances (item 7)
    $ python3 $S/instances_index.py
    13.0  10 theorems: wI_im:1899 one_lt_wI:1901 wI_norm:1903 selfS:1918 zS_im_pos:1920 mS_im_lower:1922 mS_im_upper:1925 zS_add_mS_im:1928 exists_flowPt:1941 fp_kappa_pos:1951
    13.1   9 theorems: hg10:1961 inst_flowPt_gaps:1964 inst_flowPt_odd:1966 inst_flowPt_cusp:1968 inst_flowPt_interval:1970 inst_self_gaps:1972 inst_self_odd:1973 inst_self_cusp:1974 inst_self_interval:1976
    13.2   8 theorems: P4_g0_le:1985 inst_BAmExists:1988 inst_BAmUniqReal:1992 inst_BAmBoundary:1996 inst_BAWard:2001 inst_BAPropM:2006 inst_BAoffDiag:2013 inst_BAImmLower:2022
          pins taken as hypotheses: BAImmLower BAPropM BAWard BAmBoundary BAmExists BAmUniqReal BAoffDiag
    13.3   8 theorems: zd_a:2032 zd_r:2033 inst_BAProp5:2035 inst_BAProp5s:2043 inst_BAProp6:2051 inst_BAProp7:2062 inst_BAProp8:2074 inst_BAKsolve:2082
          pins taken as hypotheses: BAKsolve BAProp5 BAProp5s BAProp6 BAProp7 BAProp8
    13.4  10 theorems: sz0_lam_L:2101 mS_im_half:2115 size_ge:2120 size_rpow_le:2134 sz0_lam_pos:2149 BAm_zSeq:2154 zSeq_im_le:2161 zSeq_im_ge:2168 flow_sz0:2177 t0_sz0:2188
          pins taken as hypotheses: BAmExists
    13.5   7 theorems: inst_BAMainInd:2209 inst_BAGbEXP:2226 inst_BAConArg:2247 inst_BAStep1:2257 inst_BAStep2:2267 inst_BAEMn2Exp:2279 inst_BAKbound:2309
          pins taken as hypotheses: BAConArg BAEMn2Exp BAGbEXP BAKbound BAMainInd BAStep1 BAStep2 BAmExists
    13.6  10 theorems: inst_BAEnd_locSC:2314 inst_BAEnd_QDiff:2317 inst_BAEnd_decol:2320 inst_BAEnd_QUE:2324 bump1_smooth:2334 bump1_supp:2337 bump1_zero:2340 inst_BAEnd_BUniv:2349 inst_BAThm27:2357 inst_BAThm27_skeleton:2366
          pins taken as hypotheses: BAEnd_BUniv BAEnd_QDiff BAEnd_QUE BAEnd_decol BAEnd_locSC BAGlueDecol BAGlueLoc BAGlueQDiff BAGlueQUE BAGlueUniv BAKsolve BAMainInd BAThm27 BAmBoundary BAmUniqReal
    13.7   4 theorems: hg_half:2386 inst_BAlanlw:2390 inst_BAlweight:2397 inst_BAGGGamma:2404
          pins taken as hypotheses: BAGGGamma BAlanlw BAlweight
    13.8   1 theorems: inst_BAlocalEntry_of_flow:2416
          pins taken as hypotheses: BAmExists BAmUniqReal
    13.9  15 theorems: clsSz_L_le_W:2452 clsSz_tendsto:2458 clsSz_bandwidth:2468 clsSz_WO:2486 clsSz_admissible:2510 clsκ_pos:2521 cls_bulk:2525 cls_domain:2534 inst_cls_Thm27:2554 inst_cls_Thm27_chain:2574 hg_fifth:2583 hg_3_10:2585 inst_cls_gaps:2588 inst_cls_odd:2593 inst_cls_interval:2598
          pins taken as hypotheses: BAConArg BAEMn2Exp BAGGGamma BAGbEXP BAGlueChain BAGlueDecol BAGlueLoc BAGlueQDiff BAGlueQUE BAGlueUniv BAKbound BAKsolve BAStep1 BAStep2 BAThm27 BAlanlw BAlweight BAmBoundary BAmUniqReal
    theorems in section 13: 82
    $ python3 $S/cls_numerics.py   # the classes of 13.9: same formulas as `fp` / `exists_flowPt`
    subordination point w = 6i/5, d = 3: flow point (g0 = sqrt(t0) g_raw, E_*, m0 = m_w/sqrt(t0)); lower bound of the probe: t0 >= 1/(|w|^2+g_raw^2 L^3)
    L   g_raw    t0        t0 bound  g0        E_*        Im m0     residual  Re m0         | support at g0: e_-, e_+, #gaps, rho_N(E_*), pi*kappa=Im m0 | class
    4   10       0.2183    0.000156  4.6723    -0.00000   0.56068   1.1e-16   2.20e-18      | 28.3260 28.3260 6 0.17847 0.56068 | gaps (6 interior gaps, first (-27.827,-19.352))
    5   0.2      0.6101    0.155     0.1562    -0.00015   0.93728   3.1e-17   1.51e-04      | 2.1503 2.1527 0 0.29835 0.93728 | odd L (e_+ != e_-: 2.1527 vs 2.1503)
    4   0.3      0.5492    0.139     0.2223    0.00000    0.88931   2.2e-16   -9.36e-18     | 2.3389 2.3389 0 0.28307 0.88931 | interval (g0 < g_c(4)=0.3542)
    $ python3 $S/n5_flow_matrix.py   # zztE_BA: the clauses of (eq:zztE_BA) and Ward at (g, z), L = 7
    d=3 L=7: model (g,z) -> flow (g0, E, m0=m/sqrt t0);  residuals of the three clauses of (eq:zztE_BA) and of Ward at z
    g      z                      t0        g0        E        |sqrt(t0) m0 - m| max|sqrt(t0)M0-M| |zt0-sqrt(t0) z| |Ward-t0| 
    0.05   (0.3+0.2j)             0.81619   0.04517   0.2981   1.1e-16            6.7e-17            5.6e-17          1.1e-12    (selfm@(E,g0) resid 4.5e-16)
    0.05   (1.2+0.001j)           0.99875   0.04997   1.2000   1.1e-16            1.1e-16            3.2e-17          1.4e-12    (selfm@(E,g0) resid 5.6e-16)
    0.05   (1.2+1e-08j)           1.00000   0.05000   1.2000   1.1e-16            2.5e-16            2.3e-16          1.4e-12    (selfm@(E,g0) resid 6.3e-16)
    0.05   (-0.5+0.7j)            0.49277   0.03510   -0.4691  2.8e-17            1.4e-16            5.6e-17          8.8e-15    (selfm@(E,g0) resid 6.2e-16)
    0.3    (0.3+0.2j)             0.78949   0.26656   0.2891   0.0e+00            5.3e-17            8.3e-17          2.3e-11    (selfm@(E,g0) resid 3.1e-16)
    0.3    (1.2+0.001j)           0.99857   0.29979   1.1997   5.6e-17            1.6e-16            2.3e-17          2.0e-11    (selfm@(E,g0) resid 1.6e-16)
    0.3    (1.2+1e-08j)           1.00000   0.30000   1.2000   0.0e+00            1.2e-16            5.0e-17          2.0e-11    (selfm@(E,g0) resid 2.0e-16)
    0.3    (-0.5+0.7j)            0.46154   0.20381   -0.4364  0.0e+00            2.2e-16            1.2e-16          9.2e-12    (selfm@(E,g0) resid 3.3e-16)
    1      (0.3+0.2j)             0.66406   0.81490   0.2476   8.7e-19            5.6e-17            6.2e-17          1.5e-10    (selfm@(E,g0) resid 2.5e-16)
    1      (1.2+0.001j)           0.99746   0.99873   1.1988   0.0e+00            5.7e-17            2.0e-17          1.2e-10    (selfm@(E,g0) resid 7.9e-17)
    1      (1.2+1e-08j)           1.00000   1.00000   1.2000   5.6e-17            1.7e-16            2.2e-16          1.2e-10    (selfm@(E,g0) resid 1.2e-16)
    1      (-0.5+0.7j)            0.33460   0.57845   -0.3270  0.0e+00            4.2e-17            5.6e-17          2.4e-11    (selfm@(E,g0) resid 3.4e-16)
    3      (0.3+0.2j)             0.22742   1.43065   0.0680   0.0e+00            2.8e-17            1.4e-17          2.1e-10    (selfm@(E,g0) resid 4.5e-16)
    3      (1.2+0.001j)           0.99628   2.99442   1.1979   0.0e+00            1.2e-16            2.2e-16          4.5e-10    (selfm@(E,g0) resid 2.9e-16)
    3      (1.2+1e-08j)           1.00000   3.00000   1.2000   0.0e+00            1.4e-16            1.2e-17          4.5e-10    (selfm@(E,g0) resid 3.9e-16)
    3      (-0.5+0.7j)            0.16043   1.20161   -0.1922  4.3e-19            1.6e-17            5.6e-17          6.7e-11    (selfm@(E,g0) resid 1.2e-16)

## P.6 Routes: the PT-BA pins and the K-loop equation at extremes
    $ python3 $S/n3_pt.py
    d=3 BA (+,-): P5=max|Th|/(B e^{-0.3|a|/l}); P8=max|Th0|(g^2+e)(|a|+1); U1,U2s unit differences (|x|>=2); (+,+): P5s=max|Th++|/(1_{a=0}+g^2 e^{-|a|/2})
    L   g     E      e         Im m    | P5     P8     U1     U2s    P5s   
    15  0.05  0.000  1.00e-09  0.9926  | 0.76   0.24   0.39   1.05   0.50  
    15  0.05  0.000  7.41e-08  0.9926  | 1.49   0.24   0.39   1.05   0.50  
    15  0.05  0.000  2.50e-04  0.9926  | 0.25   0.25   0.39   0.80   0.50  
    15  0.05  0.000  2.50e-03  0.9926  | 0.35   0.35   0.45   1.07   0.50  
    15  0.05  0.000  9.99e-01  0.9926  | 1.00   1.00   0.00   0.00   1.00  
    15  0.05  1.209  1.00e-09  0.7940  | 0.67   0.24   0.38   1.03   0.63  
    15  0.05  1.209  7.41e-08  0.7940  | 1.49   0.24   0.38   1.03   0.63  
    15  0.05  1.209  2.50e-04  0.7940  | 0.25   0.25   0.39   0.79   0.63  
    15  0.05  1.209  2.50e-03  0.7940  | 0.34   0.34   0.45   1.06   0.63  
    15  0.05  1.209  9.99e-01  0.7940  | 1.00   1.00   0.00   0.00   1.00  
    15  0.3   0.000  1.00e-09  0.8237  | 0.69   0.33   0.33   0.87   0.55  
    15  0.3   0.000  2.67e-06  0.8237  | 1.51   0.33   0.33   0.87   0.55  
    15  0.3   0.000  9.00e-03  0.8237  | 0.35   0.34   0.34   0.73   0.55  
    15  0.3   0.000  9.00e-02  0.8237  | 0.50   0.50   0.36   0.89   0.57  
    15  0.3   0.000  9.99e-01  0.8237  | 1.09   1.09   0.00   0.00   0.92  
    15  0.3   1.547  1.00e-09  0.6087  | 0.58   0.28   0.26   0.66   0.72  
    15  0.3   1.547  2.67e-06  0.6087  | 1.51   0.28   0.26   0.66   0.72  
    15  0.3   1.547  9.00e-03  0.6087  | 0.31   0.30   0.27   0.59   0.72  
    15  0.3   1.547  9.00e-02  0.6087  | 0.45   0.45   0.31   0.75   0.74  
    15  0.3   1.547  9.99e-01  0.6087  | 1.09   1.09   0.00   0.00   0.92  
    15  1     0.000  1.00e-09  0.4139  | 0.46   1.22   0.26   3.73   7.62  
    15  1     0.000  2.96e-05  0.4139  | 1.51   1.22   0.26   3.73   7.62  
    15  1     0.000  1.00e-01  0.4139  | 1.31   1.31   0.24   3.53   6.97  
    15  1     0.000  9.99e-01  0.4139  | 2.00   2.00   0.00   0.01   0.50  
    15  1     0.000  9.99e-01  0.4139  | 2.00   2.00   0.00   0.01   0.50  
    15  1     3.762  1.00e-09  0.1745  | 0.25   1.12   0.52   13.81  10.10 
    15  1     3.762  2.96e-05  0.1745  | 1.51   1.12   0.52   13.81  10.10 
    15  1     3.762  1.00e-01  0.1745  | 1.21   1.21   0.50   13.33  9.07  
    15  1     3.762  9.99e-01  0.1745  | 2.00   2.00   0.00   0.02   0.50  
    15  1     3.762  9.99e-01  0.1745  | 2.00   2.00   0.00   0.02   0.50  
    15  3     0.000  1.00e-09  0.2093  | 0.26   9.42   7.90   177.51 1.31  
    15  3     0.000  2.67e-04  0.2093  | 1.77   9.42   7.90   177.45 1.31  
    15  3     0.000  9.00e-01  0.2093  | 9.91   9.94   0.72   16.25  0.13  
    15  3     0.000  9.99e-01  0.2093  | 9.97   10.00  0.01   0.16   0.10  
    15  3     0.000  9.99e-01  0.2093  | 9.97   10.00  0.01   0.16   0.10  
    15  10    0.000  1.00e-09  0.1813  | 0.23   103.57 148.23 3323.06 0.04  
    15  10    0.000  2.96e-03  0.1813  | 10.32  103.57 147.68 3310.72 0.04  
    15  10    0.000  9.99e-01  0.1813  | 98.06  100.97 0.12   2.68   0.01  
    15  10    0.000  9.99e-01  0.1813  | 98.06  100.97 0.12   2.68   0.01  
    15  10    0.000  9.99e-01  0.1813  | 98.06  100.97 0.12   2.68   0.01  
    $ python3 $S/n4_kn2.py
    d=3 L=5 g=0.3 E=0 (+,-): max |d/dt K2 - (K2*K2)| / max|d/dt K2|  (central difference, h=1e-6(1-t))
      t=0          rel residual 1.00e-10   (|K2| max 6.794e-01)
      t=0.5        rel residual 2.99e-10   (|K2| max 1.041e+00)
      t=0.99       rel residual 6.14e-09   (|K2| max 3.071e+00)
      t=0.999999   rel residual 2.21e-05   (|K2| max 7.992e+03)

## P.7 The graph-layer expansions (BA-L2)
    $ python3 $S/n6_lw.py   # W = 1 (N = 3), exact Gauss-Hermite quadrature
    m = (-0.24216842350213874+0.5044592931063798j)  self-consistency residual 1.1102230246251565e-16  M_xx==m (W=1): True
    GGGamma first two sums with coefficient S^+_{x be} (as printed, B:398)
    W=1 (exact Gauss-Hermite, 26 nodes/dim): |LHS - RHS| for (lanlw, lweight, GGGamma), and |LHS|
      f#0:  lanlw 3.06e-07 (|LHS|=0.011)   lweight 8.17e-07 (|LHS|=0.014)   GGGamma 1.24e-02 (|LHS|=0.004)
      f#1:  lanlw 7.69e-07 (|LHS|=0.018)   lweight 7.45e-07 (|LHS|=0.018)   GGGamma 2.39e-02 (|LHS|=0.011)
    GGGamma first two sums with coefficient (M^+ S^+)_{x be}
    W=1 (exact Gauss-Hermite, 26 nodes/dim): |LHS - RHS| for (lanlw, lweight, GGGamma), and |LHS|
      f#0:  lanlw 3.06e-07 (|LHS|=0.011)   lweight 8.17e-07 (|LHS|=0.014)   GGGamma 1.20e-06 (|LHS|=0.004)
      f#1:  lanlw 7.69e-07 (|LHS|=0.018)   lweight 7.45e-07 (|LHS|=0.018)   GGGamma 2.46e-06 (|LHS|=0.011)
    $ python3 $S/n6_lw_mc.py   # W = 2, N = 6, 400000 samples
    W=2, N=6, L=3, n=400000 samples; f = |G_01|^2; lanlw (x,y)=(0,0); lweight x=2; GGGamma (x,y,y')=(0,2,2)
      lanlw                          LHS=+0.00101+0.00110i  RHS=+0.00099+0.00109i  |LHS-RHS|=1.9e-05  (MC s.e. ~ 1.7e-05)
      lweight                        LHS=+0.00012+0.00099i  RHS=+0.00013+0.00098i  |LHS-RHS|=1.4e-05  (MC s.e. ~ 1.9e-05)
      GGGamma (M^+S^+ coefficient)   LHS=-0.00057-0.00010i  RHS=-0.00057-0.00010i  |LHS-RHS|=6.5e-06  (MC s.e. ~ 5.3e-06)
    W=2, N=6, L=3, n=400000 samples; f = |G_13|^2; lanlw (x,y)=(1,1); lweight x=4; GGGamma (x,y,y')=(3,1,1)
      lanlw                          LHS=+0.00441+0.00376i  RHS=+0.00430+0.00374i  |LHS-RHS|=1.1e-04  (MC s.e. ~ 7.3e-05)
      lweight                        LHS=+0.00157-0.00000i  RHS=+0.00154-0.00004i  |LHS-RHS|=5.5e-05  (MC s.e. ~ 7.1e-05)
      GGGamma (M^+S^+ coefficient)   LHS=-0.00382-0.00122i  RHS=-0.00383-0.00122i  |LHS-RHS|=9.1e-06  (MC s.e. ~ 2.7e-05)
    W=2, N=6, L=3, n=400000 samples; f = |G_02|^2; lanlw (x,y)=(2,2); lweight x=0; GGGamma (x,y,y')=(1,4,4)
      lanlw                          LHS=+0.00437+0.00373i  RHS=+0.00431+0.00375i  |LHS-RHS|=5.6e-05  (MC s.e. ~ 7.3e-05)
      lweight                        LHS=+0.00431+0.00378i  RHS=+0.00432+0.00375i  |LHS-RHS|=3.4e-05  (MC s.e. ~ 7.3e-05)
      GGGamma (M^+S^+ coefficient)   LHS=-0.00223-0.00265i  RHS=-0.00222-0.00264i  |LHS-RHS|=9.4e-06  (MC s.e. ~ 1.2e-05)
    $ python3 $S/n6_lw_mc_printed.py   # GGGamma with the coefficient as printed
    W=2, N=6, L=3, n=400000 samples; f = |G_01|^2; lanlw (x,y)=(0,0); lweight x=2; GGGamma (x,y,y')=(0,2,2)
      GGGamma with S^+ as printed    LHS=-0.00057-0.00010i  RHS=+0.00072-0.00036i  |LHS-RHS|=1.3e-03  (MC s.e. ~ 5.3e-06)
    W=2, N=6, L=3, n=400000 samples; f = |G_13|^2; lanlw (x,y)=(1,1); lweight x=4; GGGamma (x,y,y')=(3,1,1)
      GGGamma with S^+ as printed    LHS=-0.00382-0.00122i  RHS=+0.00534-0.00350i  |LHS-RHS|=9.4e-03  (MC s.e. ~ 2.7e-05)
    W=2, N=6, L=3, n=400000 samples; f = |G_02|^2; lanlw (x,y)=(2,2); lweight x=0; GGGamma (x,y,y')=(1,4,4)
      GGGamma with S^+ as printed    LHS=-0.00223-0.00265i  RHS=+0.00524-0.00257i  |LHS-RHS|=7.5e-03  (MC s.e. ~ 1.2e-05)

## P.8 External citations (item 3)
    $ python3 $S/cites_grouped.py
    #  source                                                       | cited at                   | statement                                                                | used in                | internal route                                                                                                         | items (BA-)        lines c
    1  [Biane]                                                      | 1_2:624                    | mu_N=semicircle(x)nu_L, density, m solves (self_m)                       | (self_m), rho_N        | Schwarz-Pick fixed point; RBM2D FreeConv port (719 l.); boundary values                                                | D2,D6              2100
    2  [RBSO1D] L3.3 (zztE_BA)                                      | 7_8:1796                   | sqrt(t0) m(E,g0)=m(z,g), sqrt(t0) M(E,g0)=M(z,g), G =_d sqrt(t0) G_t0    | flow, all steps        | algebra, proved in the probe (BAzztE_data/_Mres) + merged Gt_BA                                                        | D1                 1300
    3  lem:propM: [RBSO1D L3.9] (commented out), [LSY15 L3.5], [Aizenman Thm 10.5] | 7_8:1844,1846,1908,1911    | translation inv., Ward, Im m >~ 1, Mbound_AO(2)                          | Theta, Steps 1-6       | Ward proved (BAward_avg); Taylor; Combes-Thomas (RBM2D CT*, 669 l.); Im m bridge BAImmLower (Holder-1/3 + Poisson)     | D3,D4,D7           3250
    4  [RBSO1D] L6.1                                                | 7_8:1948                   | lem_GbEXP_BA: GiiGEX, GijGEX, GavLGEX (g <= W^-eps there)                | Step 1, Step 5(iii)    | RBSO1D text not in the repo; Schur/LDE rebuild, merged Green/* as the band model                                       | G1,G2,G3,G4,G5,G6  7800
    5  [RBSO1D] L7.1, S7.1, S7.3; [YY_25] S5.3                      | 7_8:1987,1990,2101         | lem_ConArg_BA; Step 1 (lRB1, Gtmwc); Step 5 large t                      | Steps 1, 5             | same arguments with (W^d l^d eta)^-1 for W^-d B; merged S1-32.., Step5*                                                | S1,S2,S3,U5        4500
    6  [RBSO1D] L3.17                                               | 1_2:1046                   | Ward identity for K-loops (lem_WI_K)                                     | Steps 2-5, Kbound      | merged KLWard.lean/KLWardIneq.lean as the model                                                                        | K5                 800
    7  [RBSO1D] L4.16, S4, L4.29, Claim 4.30; [YY_25] L3.10         | A:376,592,734              | tree representation with M-entries; molecule sum-zero                    | ML:Kbound, Kn2sol      | ODE d/dt Theta = Theta M Theta; merged KLtreeValW, KLPure                                                              | K2,K3              2800
    8  [RBSO1D] L3.10, [yang2024Del] L3.1, (E.19); [DYYY25] L2.14, S8; [Lawler] S2 | A:50-67                    | Theta(+,-) bounds by summation by parts; Gaussian tail of K^n, local CLT | lem_propTH 5-8 for K=|M|^2 | Fourier symbol of K, Esscher tilt; merged PropUnit/HeatProduct as models                                               | P4,P5,P6           3800
    9  [RBSO1D] A.10, (A.112); [DYYY25] S7                          | 3_5:2213,2248              | CLT cancellation of the far term ("does not depend on d")                | Step 5                 | merged Evolution/Clt* (S5-17..24) over the carrier                                                                     | U4                 1200
    10 [yang2024Del] L B.9-B.11, App. B                             | B:357-407                  | lanlw, lem_lweight, GGGamma; reduction to locally standard graphs        | LWterm_EXP (Step 6)    | checked numerically (b.7; delta T2161a); BAlanlw/BAlweight/BAGGGamma; BA-L2, L3                                        | L2,L3              3990
    11 LSY Thm 2.2 (authorized, DECISIONS 5)                        | 1_2 Thm B_Univ             | bulk universality of Gaussian-divisible matrices                         | UN                     | external, no proof lines; BA wrappers only                                                                             | N1,N2              2000
    12 [bourgade2019random] L4.2; [PelSchShaSod]; [LSY15, knowles20] | A:25; 1_2:39,634,672       | band properties of S^(B)(g); localization; background                    | band / remarks         | not used for BA                                                                                                        | -                  0
    $ python3 $S/cites_table.py full
    #   source                                   cited at               used in                            lines  items (central lines lo/c/hi of the carrying items)
    1   [Biane]                                  1_2:624                (self_m), rho_N, bulk set          2100   BA-D2,BA-D6 (1500/2100/3000)
    2   [RBSO1D] L3.3                            7_8:1796               flow framework, all steps          1300   BA-D1 (1000/1300/1600)
    3   [RBSO1D] L3.9                            7_8:1844, 1846 (commen Theta properties, Steps 1-6        1950   BA-D3,BA-D4 (1350/1950/2800)
    4   [LeeSchSteYau2015] L3.5                  7_8:1908               lem:propM (2), chain domain        1300   BA-D7 (800/1300/2200)
    5   [Aizenman_book] Thm 10.5                 7_8:1911               lem:propM (3), g >= (2C)^-1        1000   BA-D4 (700/1000/1400)
    6   [RBSO1D] L6.1                            7_8:1948               Step 1 (lRB1, Gtmwc), Step 5 case  7800   BA-G1,BA-G2,BA-G3,BA-G4,BA-G5,BA-G6 (5600/7800/11100)
    7   [RBSO1D] L7.1                            7_8:1987               Step 1                             1100   BA-S1 (800/1100/1500)
    8   [RBSO1D] S7.1                            7_8:1990               Step 1                             2100   BA-S2,BA-S3 (1500/2100/3100)
    9   [RBSO1D] S7.3, [YY_25] S5.3              7_8:2101               Step 5 case (iii)                  1300   BA-U5 (900/1300/1900)
    10  [RBSO1D] L3.17                           1_2:1046               K-loop bounds, Steps 2-5           800    BA-K5 (600/800/1100)
    11  [RBSO1D] L4.16, S4                       A:592, A:376           ML:Kbound, Kn2sol                  1600   BA-K2 (1200/1600/2200)
    12  [RBSO1D] L4.29, Claim 4.30; [YY_25] L3.1 A:734                  ML:Kbound                          1200   BA-K3 (900/1200/1700)
    13  [RBSO1D] L3.10, [yang2024Del] L3.1, (E.1 A:50-55                lem_propTH 5-7 for K=|M|^2         2800   BA-P4,BA-P6 (2000/2800/4000)
    14  [DYYY25] L2.14, S8; [Lawler_book] S2     A:58-67                lem_propTH property 5              2400   BA-P4,BA-P5 (1700/2400/3400)
    15  [RBSO1D] A.10, (A.112); [DYYY25] S7      3_5:2213, 2248         Step 5 (band and BA)               1200   BA-U4 (800/1200/1700)
    16  [yang2024Del] L B.9-B.11, App. B         B:359-407              LWterm_EXP (Step 6)                3990   BA-L2,BA-L3 (3460/3990/5050)
    17  [bourgade2019random] L4.2                A:25                   band lem_propTH only               0      - 
    18  LSY Thm 2.2 (authorized, DECISIONS 5)    DECISIONS 5; 1_2 (Thm  bulk universality (UN)             2000   BA-N1,BA-N2 (1200/2000/3500)
    19  [PelSchShaSod], [LeeSchSteYau2015, knowl 1_2:39, 634, 672       remarks only                       0      - 
    1. [Biane] | statement: mu_N = semicircle (x) nu_L has a continuous density; m solves (self_m), Im m>0 | cited at 1_2:624 | used in: (self_m), rho_N, bulk set | route: Schwarz-Pick/Nevanlinna fixed point of m -> G_nu(E+m); RBM2D FreeConv.lean port (719 lines, 0 d=2 tokens); boundary values
    2. [RBSO1D] L3.3 | statement: zztE_BA: sqrt(t0) m(E,g0)=m(z,g), z_t0=sqrt(t0) z, sqrt(t0) M=M, G =_d sqrt(t0) G_t0 | cited at 7_8:1796 | used in: flow framework, all steps | route: algebra; proved here: BAzztE_data, BAzztE_Mres (probe), merged Gt_BA (pointwise)
    3. [RBSO1D] L3.9 | statement: lem:propM (1)-(3): translation invariance, Ward, |m|<=1, Mbound_AO(2) | cited at 7_8:1844, 1846 (commented out in the TeX) | used in: Theta properties, Steps 1-6 | route: Ward row by row (BAward_avg proved), circulant structure, Combes-Thomas; the printed lemma cites only [LSY15 L3.5] and [Aizenman Thm 10.5] in its proof
    4. [LeeSchSteYau2015] L3.5 | statement: Im m >~ 1 for |E| <= e - kappa (bulk lower bound) | cited at 7_8:1908 | used in: lem:propM (2), chain domain | route: replaced by the bridge pin BAImmLower (rho-bulk => Im m(E+i eta) >= c): uniform Holder-1/3 of rho_N + Poisson smoothing
    5. [Aizenman_book] Thm 10.5 | statement: Combes-Thomas estimate (Mbound_AO2) | cited at 7_8:1911 | used in: lem:propM (3), g >= (2C)^-1 | route: conjugation by e^{t dist}, Neumann series; RBM2D CombesThomas* port (8 files, 669 lines at c9a24cf, 0 d=2 tokens)
    6. [RBSO1D] L6.1 | statement: lem_GbEXP_BA: resolvent entry bounds (GiiGEX, GijGEX, GavLGEX), proved there for g <= W^-eps | cited at 7_8:1948 | used in: Step 1 (lRB1, Gtmwc), Step 5 case (iii) | route: RBSO1D text is not in the repository; rebuild with Schur complements and large deviations; merged Green/* (24.1k lines) as the band model
    7. [RBSO1D] L7.1 | statement: lem_ConArg_BA: continuity argument for the resolvent bounds | cited at 7_8:1987 | used in: Step 1 | route: same argument with (W^d l^d eta)^-1 for W^-d B; merged S1-32 STConArg
    8. [RBSO1D] S7.1 | statement: Step 1 for BA (lRB1) and (Gtmwc): same as the paper cited | cited at 7_8:1990 | used in: Step 1 | route: bootstrap, net lift, forbidden region; merged Step1*/Continuity*
    9. [RBSO1D] S7.3, [YY_25] S5.3 | statement: sec:Step5_larget: large-t case of Step 5, via lem_GbEXP_BA | cited at 7_8:2101 | used in: Step 5 case (iii) | route: omitted in the paper; BAGbEXP and merged Step5 twins
    10. [RBSO1D] L3.17 | statement: Ward identity for G-loops / K-loops (lem_WI_K) | cited at 1_2:1046 | used in: K-loop bounds, Steps 2-5 | route: merged KLWard.lean/KLWardIneq.lean as the model
    11. [RBSO1D] L4.16, S4 | statement: tree representation of K-loops with M-entries (tree-representation_BA) | cited at A:592, A:376 | used in: ML:Kbound, Kn2sol | route: ODE d/dt Theta = Theta M Theta; merged KLtreeValW (KLTree.lean:114)
    12. [RBSO1D] L4.29, Claim 4.30; [YY_25] L3.10 | statement: molecule sum-zero (eq:Sigma-empty-sum-zero), pure loops | cited at A:734 | used in: ML:Kbound | route: A:643-734; merged KLPure
    13. [RBSO1D] L3.10, [yang2024Del] L3.1, (E.19) | statement: Theta(+,-) bounds (BD1, BD2, ThfadC0) by summation by parts | cited at A:50-55 | used in: lem_propTH 5-7 for K=|M|^2 | route: unit differences of K^n(0,.), Fourier symbol; merged PropUnit.lean as the model
    14. [DYYY25] L2.14, S8; [Lawler_book] S2 | statement: Gaussian/exponential tail of K^n, local CLT for the walk | cited at A:58-67 | used in: lem_propTH property 5 | route: Chernoff/Esscher tilt and on-diagonal bound on Z_L^d; merged HeatProduct.lean (1257 lines) as the model
    15. [RBSO1D] A.10, (A.112); [DYYY25] S7 | statement: CLT cancellation for the far term; "does not depend on d" (omitted) | cited at 3_5:2213, 2248 | used in: Step 5 (band and BA) | route: merged Evolution/Clt*.lean (S5-17..24) retargeted at the carrier
    16. [yang2024Del] L B.9-B.11, App. B | statement: lanlw, lem_lweight, GGGamma; reduction to locally standard graphs | cited at B:359-407 | used in: LWterm_EXP (Step 6) | route: checked numerically here (n6_lw*.py; GGGamma coefficient delta T2161a); pins BAlanlw/BAlweight/BAGGGamma; BA-L1..L4 of T2040
    17. [bourgade2019random] L4.2 | statement: properties of S^(B)(g) (band) | cited at A:25 | used in: band lem_propTH only | route: not used for BA (K = |M|^2 is a different kernel: BA-P2..P4)
    18. LSY Thm 2.2 (authorized, DECISIONS 5) | statement: bulk universality of Gaussian-divisible Hermitian matrices (Landon-Sosoe-Yau) | cited at DECISIONS 5; 1_2 (Thm B_Univ) | used in: bulk universality (UN) | route: the only external input; UN-D1 (T2162) and the BA part BA-N1/N2
    19. [PelSchShaSod], [LeeSchSteYau2015, knowles20] | statement: localization for g << W^{-d/2}; random matrix theory background | cited at 1_2:39, 634, 672 | used in: remarks only | route: not used in any proof

## P.9 The split table (item 6)
    $ python3 $S/ba_split2.py
        group                        items | lines lo / central / hi 
    D   deterministic layer              6 |   4650   6650   9600
    P   propagator (PT-BA)               8 |   5500   7600  10800
    K   K-loops (KL-BA)                  5 |   4600   6100   8400
    E   evolution kernels (EK-BA)        3 |   2200   3200   4500
    G   lem_GbEXP_BA chain               6 |   5600   7800  11100
    S   Step 1                           3 |   2300   3200   4600
    T   Step 2                           8 |   7800  10900  15400
    U   Steps 3-5                        6 |   4600   6800   9800
    V   Step 6 and chain                 3 |   2200   3200   4700
    L   graph layer (T2040 rows)         4 |   5833   6363   8296
    M   MA-BA                            3 |   2300   3300   4900
    N   UN-BA                            2 |   1200   2000   3500
        TOTAL                           57 |  48783  67113  95596
    lines/1000 (all groups): lo 48.8  central 67.1  hi 95.6 ; items 57
    graph layer BA-L1..L4 (T2040 rows, in ROUTES BA 33): items 4, lines 5833/6363/8296 ; without it: items 53, lines/1000 43.0 / 60.8 / 87.3
    items with central > 1500 lines (600-1500 rule): [('BA-K2', 1600), ('BA-K4', 1600), ('BA-T2', 1700), ('BA-L2', 2400), ('BA-L3', 1590)] ; tickets if every item is cut at 1500 central lines: 62
    roles: {'prover': 14, 'prover-hard': 31, 'prover-max': 12}
    DECISIONS 9 O2 (25/40/50): items 57, lines/1000 central 67.1 -> OVER 50
    owed pins to discharge: 36; discharged by some item: 36; missing: []; discharged twice: []
    adaptation rule: (sig-hw + 0.5 body-only) lines: ST-1..4 34403, KL 7648, EK 892 ; x alpha 0.5/0.7/1.0 -> ST-1..4 17.2/24.1/34.4, KL 3.8/5.4/7.6, EK 0.4/0.6/0.9 (lines/1000)
    items S,T,U,V (Steps 1-6 twins): 20 items, lines/1000 16.9 / 24.1 / 34.5   (to compare with ST-1..4 above)
    $ python3 $S/ba_split2.py full
    id     file (RBM3D/...)                             role         proves (pins)              lo    central hi      depends on
    BA-D1  BA/Defs + BA/Pins (+ registry lines in Test/ prover       (defs, proved base, the pi 1000  1300   1600    T2013 merged
    BA-D2  BA/SelfM                                     prover-hard  BAmExists,BAmUniqReal      700   900    1200    BA-D1
    BA-D3  BA/Ward + BA/OffDiag                         prover       BAWard,BAoffDiag           650   950    1400    BA-D1, D2
    BA-D4  BA/CombesThomas                              prover-hard  BAPropM                    700   1000   1400    BA-D1, D3
    BA-D6  BA/Boundary                                  prover-hard  BAmBoundary                800   1200   1800    BA-D2
    BA-D7  BA/ImmLower                                  prover-max   BAImmLower                 800   1300   2200    BA-D2, D6
    BA-P1  BA/Prop5Short                                prover-hard  BAProp5s                   500   700    1000    BA-D3, D4
    BA-P2  BA/KKernel                                   prover       -                          500   700    1000    BA-D3, D4
    BA-P3  BA/KSymbol                                   prover-hard  -                          700   900    1300    BA-P2
    BA-P4  BA/KHeat                                     prover-max   -                          1000  1400   2000    BA-P3
    BA-P5  BA/Prop5                                     prover-hard  BAProp5                    700   1000   1400    BA-P4
    BA-P6  BA/PropUnit                                  prover-max   BAProp6,BAProp7            1000  1400   2000    BA-P4, P5
    BA-P7  BA/Prop8                                     prover-hard  BAProp8                    500   700    1000    BA-P5
    BA-P8  BA/Prop6Path                                 prover       BAProp5to8                 600   800    1100    BA-P6, P7
    BA-K1  BA/KSolve                                    prover-hard  BAKsolve                   700   900    1200    BA-D1, P8
    BA-K2  BA/KTree                                     prover-max   -                          1200  1600   2200    BA-K1
    BA-K3  BA/KPure                                     prover-hard  -                          900   1200   1700    BA-K2
    BA-K4  BA/KBound                                    prover-max   BAKbound                   1200  1600   2200    BA-K3, P8
    BA-K5  BA/KWard                                     prover       -                          600   800    1100    BA-K1
    BA-E1  BA/EKPins                                    prover-hard  -                          700   1000   1400    BA-P8
    BA-E2  BA/EKSum                                     prover-hard  -                          1000  1500   2100    BA-E1, K3
    BA-E3  BA/EKPrec                                    prover       -                          500   700    1000    BA-E2
    BA-G1  BA/GreenSchur                                prover-max   -                          1000  1400   2000    BA-D4, D7
    BA-G2  BA/GreenLDE                                  prover-hard  -                          1000  1400   2000    BA-G1
    BA-G3  BA/GbEXPDiag                                 prover-hard  -                          1000  1400   2000    BA-G2
    BA-G4  BA/GbEXPOff                                  prover-hard  -                          1000  1400   2000    BA-G3
    BA-G5  BA/GbEXPAvg                                  prover-hard  -                          1000  1400   2000    BA-G3
    BA-G6  BA/GbEXP                                     prover       BAGbEXP                    600   800    1100    BA-G4, G5
    BA-S1  BA/ConArg                                    prover-hard  BAConArg                   800   1100   1500    BA-G6, K4
    BA-S2  BA/Step1Boot                                 prover-hard  -                          800   1100   1600    BA-S1
    BA-S3  BA/Step1                                     prover       BAStep1                    700   1000   1500    BA-S2
    BA-T1  BA/Step2Gronwall                             prover-max   -                          1100  1500   2100    BA-S3, K4
    BA-T2  BA/EMn2                                      prover-max   BAEMn2Exp                  1200  1700   2400    BA-T1, G6
    BA-T3  BA/NewKLK                                    prover-hard  -                          900   1200   1700    BA-D4, E3
    BA-T4  BA/Step2PathA                                prover-hard  -                          1000  1400   2000    BA-T1
    BA-T5  BA/Step2PathB                                prover-hard  -                          1000  1400   2000    BA-T4
    BA-T6  BA/Step2Contract                             prover-hard  -                          1000  1400   2000    BA-T2, T3
    BA-T7  BA/Step2Events                               prover-hard  -                          900   1200   1700    BA-T6
    BA-T8  BA/Step2                                     prover       BAStep2                    700   1100   1500    BA-T7
    BA-U1  BA/Step34A                                   prover-hard  -                          800   1200   1700    BA-T8, E3
    BA-U2  BA/Step34B                                   prover-hard  -                          800   1200   1700    BA-U1
    BA-U3  BA/Step34                                    prover       -                          700   1000   1500    BA-U2
    BA-U4  BA/Step5A                                    prover-hard  -                          800   1200   1700    BA-U3
    BA-U5  BA/Step5Larget                               prover-max   -                          900   1300   1900    BA-G6, U4
    BA-U6  BA/Step5                                     prover       -                          600   900    1300    BA-U4, U5
    BA-V1  BA/Step6                                     prover-hard  -                          700   1000   1500    BA-L4, U6
    BA-V2  BA/MainInd                                   prover-max   BAMainInd,BAGlueChain      1000  1500   2200    BA-V1, T8, U3, U6
    BA-V3  BA/GLoopAtT0                                 prover       -                          500   700    1000    BA-V2
    BA-L1  Graph/BAVocab (T2040)                        prover       -                          873   873    1746    LW-03, MD
    BA-L2  Graph/BAExpand (T2040)                       prover-hard  BAlanlw,BAlweight,BAGGGamm 2400  2400   2400    BA-L1, LW-04
    BA-L3  Graph/BALvl1 (T2040)                         prover-max   -                          1060  1590   2650    BA-L2, LW-08, 11, 12
    BA-L4  Graph/BALWterm (T2040)                       prover-max   -                          1500  1500   1500    BA-L2, LW-14
    BA-M1  BA/MALocal                                   prover-hard  BAGlueLoc,BAEnd_locSC      700   1000   1500    BA-V3, D7
    BA-M2  BA/MAQDiff                                   prover-hard  BAGlueQDiff,BAEnd_QDiff    700   1000   1500    BA-M1, K1
    BA-M3  BA/MADecolQUE                                prover-hard  BAGlueDecol,BAGlueQUE,BAEn 900   1300   1900    BA-M1, M2
    BA-N1  BA/UNStep1                                   prover-hard  -                          700   1200   2000    BA-D6, M1, UN-D1
    BA-N2  BA/UNBUniv                                   prover       BAGlueUniv,BAEnd_BUniv,BAT 500   800    1500    BA-N1
    
    BA-D1 [D] Defs + proved base: BASelf/BAm/BAMB/bulk forms/BAReal/BAMss/BATheta/FlowFM carrier, subordination lemma, zztE_BA data, averaged Ward; pins as Props; Axioms.lean | sources: probe sections 0-3,5-7 (T2161Pins); 1_2:626-633, 7_8:1796-1801
    BA-D2 [D] (self_m): existence/uniqueness of m(z,g) in C+, spectral bridge tr(Mres)=sum 1/(lam_i-w) (BAmExists, BAmUniqReal) | sources: RBM2D Universality/FreeConv.lean 719 (0 d=2 tokens); 1_2:624-629 [Biane]
    BA-D3 [D] Ward row by row, translation invariance, M_aa=m, |m|<=1, M symmetric (BAWard); (eq:off_diagM): eps(kappa,Lambda) with |1-tm^2|^2=(1-t|m|^2)^2+4t(Im m)^2 (BAoffDiag) | sources: probe BAward_avg + circulant structure; 7_8:1859-1869; A:32-34 (probe b.4: identity checked to 4e-16)
    BA-D4 [D] lem:propM (3): (Mbound_AO) by Taylor, (Mbound_AO2) by weighted resolvent (BAPropM) | sources: RBM2D Propagator/CombesThomas*.lean 669 (8 files, 0 tokens), retargeted at (g Psi - w)^-1; 7_8:1891-1912 [Aizenman Thm 10.5]
    BA-D6 [D] boundary values m(E+i0), rho_N continuity in E, bulk-set openness (BAmBoundary) | sources: 1_2:624, 715 [Biane]; RBM2D FreeConvStability.lean 835 (partial: limit eta->0)
    BA-D7 [D] Im m(z,g) >= c(kappa) in the rho-bulk, eta<=1 ([LSY15 L3.5] internal; BAImmLower) | sources: 7_8:1908; uniform Holder-1/3 of rho_N + Poisson smoothing (route, no source)
    BA-P1 [P] property 5s for (sigma,sigma): Taylor + BAoffDiag + CT decay (BAProp5s) | sources: A:34-48; merged Propagator/Prop5Short.lean 506
    BA-P2 [P] kernel K=M^(+,-): symmetric, doubly stochastic, exponential tails, neighbour lower bound, laziness |m|^2 | sources: A:58-67; 7_8:1869-1912
    BA-P3 [P] Fourier symbol of K: gap 1-Khat >= c (g^1)^2 |theta|^2, analytic strip (Esscher tilt) | sources: route of T2003 b9 (symbol of M^(+,-)); no source
    BA-P4 [P] Gaussian/exponential bound for K^n(0,a) on Z_L^d (Chernoff/Esscher + on-diagonal bound) | sources: A:58-67 (Bernstein + local CLT [Lawler S2]); merged HeatProduct.lean 1257 as model
    BA-P5 [P] assemble property 5 (BAProp5): Laplace-Gauss integrals + zero-mode gap n>=L^2 | sources: merged Propagator/LaplaceGauss.lean 895 (Theta-free), Prop5Hold.lean 1399 as model
    BA-P6 [P] unit first/second differences of K^n(0,.) (BAProp6/7 unit forms) | sources: A:50-56 (summation by parts); merged PropUnit.lean 1008 as model
    BA-P7 [P] property 8, zero mode (BAProp8) | sources: merged Prop5Hold.lean (zero-mode part) as model
    BA-P8 [P] path lemma (|r|<=c|a|) -> BAProp6/7; bundle BAProp5to8; charge bookkeeping | sources: merged Propagator/Prop6Hold.lean 560 (private path lemma: copied)
    BA-K1 [K] BAKsolve: K-loop existence/uniqueness for S=I and BA initial data; (Kn2sol), (Kn3sol) | sources: merged IsKLoopS (KLTree.lean:828), KL4 uniqueness; 1_2:1175
    BA-K2 [K] m-loop-tsp, Gamma_M values, tree representation tree-representation_BA (ODE proof d/dt Theta = Theta M Theta) | sources: A:380-594 [RBSO1D L4.16]; merged KLtreeValW (KLTree.lean:114)
    BA-K3 [K] pure loops BA, molecule decay, sum-zero (eq:Sigma-empty-sum-zero) | sources: A:643-654, 690, 728-734 [RBSO1D L4.29, Claim 4.30]
    BA-K4 [K] BAKbound: ML:Kbound induction with M-loops | sources: 1_2:1056; merged KLindStep/KLKpiBound (T2100, T2106, T2115) as model
    BA-K5 [K] Ward identities for K (BA): lem_WI_K, lem_wardineq_K | sources: merged KLWard.lean, KLWardIneq.lean as model
    BA-E1 [E] EK pins over the BA kernel family Q; Xi bounds with Prop5DecayQ + Mbound_AO | sources: T2016 b10 (EKuKerQ); merged Evolution/XiPins.lean
    BA-E2 [E] sum_res_1, sum_res_2_NAL, sum_res_2 (sum-zero), sum_decay_nonzero for BA | sources: A:88-220; merged Evolution/SumDecay*.lean, Nonzero.lean
    BA-E3 [E] EK conclusions -> Prec at scale N (EK-6 analog) | sources: merged Evolution/Prec.lean
    BA-G1 [G] BA resolvent/Schur structure with the deterministic hopping; (eq_resolventunderpoly) inputs | sources: 7_8:1916-1950 [RBSO1D L6.1: text not in repo]
    BA-G2 [G] large-deviation estimates for the BA minors (twin of Green/LDE*, EntryCore) | sources: merged Green/LDE*.lean, EntryCore.lean (sig-hw 6.5k of 24.1k lines)
    BA-G3 [G] (GiiGEX_BA): ||G-M||_max << Psi_t | sources: 7_8:1931; merged Green/GbEXP.lean as model
    BA-G4 [G] (GijGEX_BA): entrywise decay with Phi_t and c_g | sources: 7_8:1942
    BA-G5 [G] (GavLGEX_BA): averaged law, fluctuation averaging iteration | sources: 7_8:1931; merged Green/Fluc*.lean as model
    BA-G6 [G] assembly BAGbEXP | sources: 7_8:1916-1946
    BA-S1 [S] BAConArg: lem_ConArg_BA parts 1 and 2 (g_s = g sqrt(s/t)) | sources: 7_8:1956-1987 [RBSO1D L7.1]; merged S1-32 STConArg
    BA-S2 [S] Step 1 BA: bootstrap, net lift, forbidden region | sources: 7_8:1987-1990 [RBSO1D S7.1]; merged Induction/Step1*.lean, Continuity*.lean
    BA-S3 [S] Step 1 BA assembly BAStep1 | sources: merged S1-35, S1-36
    BA-T1 [T] (eq:MG_conclusion3_BA) with deterministic J: Gronwall iteration + stopping time T | sources: 7_8:1999-2026; merged Induction/Step2Iterate.lean as model
    BA-T2 [T] lem: EMn2_N for BA: (eq_resolventunderpoly/exp), (eq_S1_bound_BA); BAEMn2Exp | sources: 7_8:2033-2092; merged EMn2Poly/Exp1/Exp2.lean
    BA-T3 [T] lem:newKLK for BA (uses Mbound_AO) | sources: 7_8:2030 ("minor modification"); merged NewKLK.lean, NewKLKL.lean
    BA-T4 [T] Step 2 path layer twins: grid Duhamel, Azuma proxy, grid good/envelope/assembly (S-hardwired part) | sources: merged Induction/Grid*.lean, AzumaProxyN.lean, Path/* (sig-hw 3.7k)
    BA-T5 [T] Step 2 path layer twins, part 2 (stopping times, Doob, continuity) | sources: as above
    BA-T6 [T] Step 2 contraction / J-Gronwall twins (STContract, STSelfImp, STScale*) | sources: merged Induction/Contract*.lean, Step2Scale.lean, Step2Core.lean
    BA-T7 [T] Step 2 events / decay-loop twins | sources: merged Induction/Step2Events.lean, DecayLoopA/B.lean
    BA-T8 [T] Step 2 assembly BAStep2 | sources: merged Induction/Step2Defs.lean pins, ST2-04
    BA-U1 [U] Steps 3-4 twins: sum-zero/zero-mode removal, new time intervals (loop-level) | sources: merged Induction/ZeroModeCalc.lean, IterationsA.lean, NewPQ.lean, QGrid*.lean (ST-3 sig-hw 4.3k)
    BA-U2 [U] Steps 3-4 twins: lem:SEforLn, lem_decayLoop, B45 | sources: merged SEforLn1/2.lean, B45.lean, KDecay.lean
    BA-U3 [U] Steps 3-4 twins: Step34Pins consumers, Step 3/4 assembly | sources: merged Induction/Step34Pins.lean
    BA-U4 [U] Step 5 twins: cases (i)-(ii) (TailtoTail, WardII, NewKLKL, CLT cancellation, ExpInv) | sources: merged Induction/Step5*.lean, TailtoTail.lean, WardII.lean, Evolution/Clt*.lean (ST-4 sig-hw 2.4k)
    BA-U5 [U] Step 5 case (iii) = sec:Step5_larget for BA ([RBSO1D S7.3], uses lem_GbEXP_BA) | sources: 3_5:2284; 7_8:2101
    BA-U6 [U] Step 5 assembly BAStep5I-IV | sources: merged Induction/Step5Pins.lean
    BA-V1 [V] Step 6 twin: lem:LWterm_EXP assembly consumers (graph part is BA-L4) | sources: 6:83-88; B:7-121
    BA-V2 [V] chain induction in t for the BA carrier: BAMainInd from Steps 1-6 (STMainIndG) | sources: 1_2:1256-1330, 7_8:1825-1832
    BA-V3 [V] Steps 1-6 -> ML:GLoop, ML:GLoop_expec, ML:GtLocal for BA at t0 | sources: 1_2:1190; 7_8:1813
    BA-L1 [L] graph vocabulary: Psi- and M-dotted edges, atoms, scalingBA (T2040 row) | sources: B:286-356; T2040-prove.md:182
    BA-L2 [L] expansions lanlw, lem_lweight, GGGamma (pins BAlanlw, BAlweight, BAGGGamma; T2161a coefficient) | sources: B:359-405 [yang2024Del B.9-B.11]; probe section 10
    BA-L3 [L] BA lvl1, atomic reduction and auxiliary graph, Anp for atoms (T2040 row) | sources: B:407-523
    BA-L4 [L] BA lem:LWterm_EXP with GGGamma (T2040 row) | sources: B:118
    BA-M1 [M] MA-BA: BAEnd_locSC from BAMainInd at t0 + zztE_BA transfer (BAlocalEntry_of_flow proved) + (eq:BtBt) + net lemma | sources: 7_8:1813-1816; RBM2D Main/RegionUnif.lean 950
    BA-M2 [M] MA-BA: BAEnd_QDiff from Kn2sol/BAprof + (eq:BtBt), expectation bounds | sources: 1_2:657-666; RBM2D Main/*
    BA-M3 [M] MA-BA: BAEnd_decol, BAEnd_QUE from the local laws / QD, rho-bulk | sources: RBM2D Main/DecolFromLocal.lean 361, QUEFromQDiff.lean 1084 (d=2 tokens 3, 26)
    BA-N1 [N] UN-BA: rho_N-dilated Step 1 comparison with LSY Thm 2.2 for BA initial data (BA part of UN-D1/T2162) | sources: RBM2D Universality/Step1Band.lean 1259 (2 tokens); DECISIONS 11
    BA-N2 [N] UN-BA: BAEnd_BUniv assembly (limit computation at fixed L,g; rho_N(E) >= kappa) | sources: 1_2:454-457

## P.10 Compiled facts and hygiene
    $ python3 $S/name_clash.py
    declarations in the probe: 269 (public 269, private 0); namespaces used: ['RBM.BA', 'RBM.BA.Inst']
    exact full-name clashes with other RBM3D files (worktree, base 275e275): 0 []
    same bare name under another namespace (not a clash): 1 [('RBM.BA.Inst.zS', 'RBM.Green.zS', 'RBM3D/Green/EntryCore.lean')]
    public BA*/inst_BA* names in the probe: 162
    RBM2D @c9a24cf: files declaring one of them: []
    RBM1D @HEAD: files declaring one of them: []
    main worktree (RBM3D/RBM3D, current files): files declaring one of them: []

## P.11 Mathlib names (`#check` / `#check_failure` in `$S/names_check.lean`, exit 0)
    $ python3 $S/oneline.py $S/names_check.out
    present Real.sqrt_le_one                   : ∀ , √x ≤ 1 ↔ x ≤ 1
    present Real.rpow_le_rpow_of_nonpos        : ∀ , 0 < x → x ≤ y → z ≤ 0 → y ^ z ≤ x ^ z
    present Matrix.nonsing_inv_eq_ringInverse  : ∀ (A : Matrix n n α), A⁻¹ = Ring.inverse A
    present Matrix.inv_smul                    : ∀ (A : Matrix n n α) (k : α) , IsUnit A.det → (k • A)⁻¹ = ⅟k • A⁻¹
    present Matrix.trace_smul                  : ∀ (r : α) (A : Matrix n n R), (r • A).trace = r • A.trace
    present Finset.sum_mul_sq_le_sq_mul_sq     : ∀ (s : Finset ι) (f g : ι → R), (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2
    present EuclideanSpace.inner_single_right  : ∀ (i : ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι), inner 𝕜 v (EuclideanSpace.single i a) = a * (starRingEnd ((fun x => 𝕜) i)) (
    present EuclideanSpace.norm_sq_eq          : ∀ (x : EuclideanSpace 𝕜 n), ‖x‖ ^ 2 = ∑ i, ‖x.ofLp i‖ ^ 2
    present Matrix.toEuclideanLin              : → → → → → → Matrix m n 𝕜 ≃ₗ EuclideanSpace 𝕜 n →ₗ EuclideanSpace 𝕜 m
    present ContDiffBump.contDiff              : ∀ (f : ContDiffBump c) , ContDiff ℝ ↑n ↑f
    present ContDiffBump.hasCompactSupport     : ∀ (f : ContDiffBump c) , HasCompactSupport ↑f
    present ContDiffBump.one_of_mem_closedBall : ∀ (f : ContDiffBump c) , x ∈ Metric.closedBall c f.rIn → ↑f x = 1
    present HasCompactSupport.comp_homeomorph  : ∀ , HasCompactSupport f → ∀ (φ : X ≃ₜ Y), HasCompactSupport (f ∘ ⇑φ)
    present EuclideanSpace.equiv               : (ι : Type u_1) → (𝕜 : Type u_2) → → EuclideanSpace 𝕜 ι ≃L ι → 𝕜
    ABSENT  Finset.inner_mul_le_norm_mul_norm
    ABSENT  Real.sqrt_lt_one
    ABSENT  Real.rpow_le_rpow_of_exponent_nonpos
    ABSENT  Nat.pos_pow_of_pos
    ABSENT  Real.sqrt_le_one_iff_le_one_of_nonneg
    $ python3 $S/names_check.py   # grep of the declarations in Mathlib; #uses = occurrences in the probe
    name                                       status   #uses  file (first)
    Real.sqrt_le_one                           present  2      Analysis/Real/Sqrt.lean
    Real.rpow_le_rpow_of_nonpos                present  1      Analysis/SpecialFunctions/Pow/NNReal.lean
    Matrix.nonsing_inv_eq_ringInverse          present  4      LinearAlgebra/Matrix/NonsingularInverse.lean
    Matrix.inv_smul                            present  2      LinearAlgebra/Matrix/NonsingularInverse.lean
    Matrix.trace_smul                          present  1      LinearAlgebra/Matrix/Trace.lean
    Finset.sum_mul_sq_le_sq_mul_sq             present  1      Algebra/Order/BigOperators/Ring/Finset.lean
    EuclideanSpace.inner_single_right          present  1      Analysis/InnerProductSpace/l2Space.lean
    EuclideanSpace.norm_sq_eq                  present  2      Analysis/InnerProductSpace/PiL2.lean
    Matrix.toEuclideanLin                      present  6      Analysis/InnerProductSpace/PiL2.lean
    ContDiffBump.contDiff                      present  2      Analysis/Complex/CauchyIntegral.lean
    ContDiffBump.hasCompactSupport             present  1      Topology/ContinuousMap/CompactlySupported.lean
    ContDiffBump.one_of_mem_closedBall         present  1      Analysis/Calculus/BumpFunction/Basic.lean
    HasCompactSupport.comp_homeomorph          present  1      Topology/Covering/Basic.lean
    EuclideanSpace.equiv                       present  4      Order/Filter/TendstoCofinite.lean
    Real.sq_sqrt                               present  2      Analysis/Real/Sqrt.lean
    Real.sqrt_pos                              present  6      Analysis/Real/Sqrt.lean
    Complex.norm_real                          present  3      Analysis/Complex/Norm.lean
    Finset.sum_ite_eq                          present  1      Algebra/SkewMonoidAlgebra/Basic.lean
    ite_eq_left_iff                            present  0      Basic/Logic/Basic.lean
    Finset.inner_mul_le_norm_mul_norm          ABSENT   -      
    Real.sqrt_lt_one                           ABSENT   -      
    Real.rpow_le_rpow_of_exponent_nonpos       ABSENT   -      
    Nat.pos_pow_of_pos                         ABSENT   -      
    Real.sqrt_le_one_iff_le_one_of_nonneg      ABSENT   -      

## P.12 Scripts (verbatim)
### final_run.sh
```bash
#!/bin/zsh
# Regenerates every script output of the T2161 report (scratchpad T2161/); order = report sections.
cd "$(dirname "$0")"
W=/Users/junyin/Lean_proof/RBM3D-wt/T2161
echo "start $(date -u)" > final_run.log
( cd $W && lake env lean RBM3D/Probe/T2161Pins.lean > $OLDPWD/final_lean.out 2>&1; echo "exit=$?" >> $OLDPWD/final_lean.out )
( cd $W && lake build RBM3D.Probe.T2161Pins > $OLDPWD/final_build.out 2>&1; echo "exit=$?" >> $OLDPWD/final_build.out )
python3 name_clash.py > name_clash.out 2>&1
python3 pin_index.py > pin_index.out 2>&1
python3 registry.py > registry.out 2>&1
python3 instances_index.py > instances_index.out 2>&1
python3 n1_immlower.py > n1_immlower.out 2>&1
python3 n1_equiv.py > n1_equiv.out 2>&1
python3 n2_table.py > n2_table.out 2>&1
python3 n3_pt.py > n3_pt.out 2>&1
python3 n4_kn2.py > n4_kn2.out 2>&1
python3 n5_flow_matrix.py > n5_flow_matrix.out 2>&1
python3 n6_lw.py > n6_lw.out 2>&1
python3 n6_lw_mc.py > n6_lw_mc_full.out 2>&1
python3 n6_lw_mc_printed.py > n6_lw_mc.out 2>&1
python3 cls_numerics.py > cls_numerics.out 2>&1
python3 inv_paper.py > inv_paper.out 2>&1
python3 inv_cites.py > inv_cites.out 2>&1
python3 inv_merged_ba.py > inv_merged_ba.out 2>&1
python3 inv_rbm2d.py > inv_rbm2d.out 2>&1
python3 decl_inv.py > decl_inv.out 2>&1
python3 file_gate.py > file_gate.out 2>&1
python3 pin_subst2.py > pin_subst2.out 2>&1
python3 ba_split2.py > ba_split2.out 2>&1
python3 ba_split2.py full > ba_split2_full.out 2>&1
python3 cites_table.py > cites_table.out 2>&1
python3 cites_table.py full > cites_table_full.out 2>&1
python3 cites_grouped.py > cites_grouped.out 2>&1
python3 pin_map.py > pin_map.out 2>&1
python3 names_check.py > names_check_grep.out 2>&1
( cd $W && lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2161/names_check.lean > $OLDPWD/names_check.out 2>&1 )
echo "end $(date -u)" >> final_run.log
```
### ba_core.py
```python
# Core numerics for the BA deterministic layer at d=3 (all FFT-based; Psi^(B) = adjacency of Z_L^3).
import itertools, math, numpy as np
from collections import Counter
D = 3
def eps_grid(L, d=D):
    k = 2*np.pi*np.arange(L)/L
    c = 2*np.cos(k)
    e = c[:, None, None] + c[None, :, None] + c[None, None, :]
    return e
def atoms_of(L, g, d=D):
    e = eps_grid(L, d).ravel()
    cnt = Counter(np.round(e, 9))
    return sorted((g*x, n/L**d) for x, n in cnt.items())
def m_of(z, A, tol=1e-15, it=3000000):
    m = 1j
    for _ in range(it):
        new = sum(w/(a - z - m) for a, w in A)
        if abs(new - m) < tol: return new
        m = 0.5*m + 0.5*new
    return m
def Mblock(L, g, E, m, eta=0.0):
    """M^(B)_{0b} for b in Z_L^3 (translation invariant): inverse FFT of 1/(g eps(k) - z - m)."""
    sym = 1.0/(g*eps_grid(L) - (E + 1j*eta) - m)
    return np.fft.ifftn(sym)          # entry [b] = M_{0b}
def sym_to_K(M0):
    return np.abs(M0)**2
def theta_row(L, K0, t):
    """Theta_t(0,.) = inverse FFT of 1/(1 - t Khat(k))  for the kernel K0 (entries K_{0b})."""
    Kh = np.fft.fftn(K0)
    return np.fft.ifftn(1.0/(1.0 - t*Kh))
def dist_l1(L):
    x = np.arange(L); d1 = np.minimum(x, L - x)
    return d1[:, None, None] + d1[None, :, None] + d1[None, None, :]
```
### ba_supp.py
```python
# Exact support of mu = semicircle (x) free conv. with empirical measure of g*Psi^(B) on Z_L^d (self_m, 1_2:626-629).
# Subordination: u=z+m, m=G_nu(u)=sum w/(a-u); z(u)=u-G(u); gaps of supp mu = z(interval where f(u)=sum w/(a-u)^2 <1, u real off atoms).
import itertools, math
from collections import Counter
from scipy.optimize import brentq
def atoms(d,L,g):
    c=Counter()
    for k in itertools.product(range(L),repeat=d):
        c[round(sum(2*math.cos(2*math.pi*ki/L) for ki in k),9)]+=1
    return sorted((g*x,n/L**d) for x,n in c.items())
def G(u,A): return sum(w/(a-u) for a,w in A)
def f(u,A): return sum(w/(a-u)**2 for a,w in A)
def fp(u,A): return sum(2*w/(a-u)**3 for a,w in A)
def z(u,A): return u-G(u,A)
def support(d,L,g):
    A=atoms(d,L,g); amax=A[-1][0]; amin=A[0][0]
    up=brentq(lambda u:f(u,A)-1,amax+1e-12,amax+1e6) # f>1 near atom, decreasing
    um=brentq(lambda u:f(u,A)-1,amin-1e6,amin-1e-12)
    ep=z(up,A); em=-z(um,A); gaps=[]
    for (a0,_),(a1,_) in zip(A,A[1:]):
        h=(a1-a0); lo,hi=a0+1e-9*h,a1-1e-9*h
        if hi<=lo: continue
        if fp(lo,A)>=0 or fp(hi,A)<=0: continue
        u0=brentq(lambda u:fp(u,A),lo,hi)
        if f(u0,A)<1:
            u1=brentq(lambda u:f(u,A)-1,lo,u0); u2=brentq(lambda u:f(u,A)-1,u0,hi)
            gaps.append((z(u1,A),z(u2,A)))
    return em,ep,gaps,A
if __name__=="__main__":
    d=3
    print("d=3: exact support of mu_N: left edge -e_-, right edge e_+, interior gaps of supp mu (z(u1),z(u2))")
    for L in (4,5,6):
        for g in (0.5,1.0,10.0):
            em,ep,gaps,A=support(d,L,g)
            print("L=%d g=%-4g e_-=%.4f e_+=%.4f #gaps=%d first gap=%s"%(L,g,em,ep,len(gaps),"(%.3f,%.3f)"%gaps[0] if gaps else "-"))
```
### ba_det.py
```python
# deterministic layer at d=3: (self_m), Ward, gap of 1-K (K_ab=|M_ab|^2, S^(B)=I), ||M^(+,+)||, Combes-Thomas ratios
import itertools, math, numpy as np
from ba_supp import atoms, support
def m_of(z,A,it=2000000):
    m=1j
    for _ in range(it):
        new=sum(w/(a-z-m) for a,w in A)
        if abs(new-m)<1e-15: return new
        m=0.5*m+0.5*new
    return m
def adj(d,L):
    idx=list(itertools.product(range(L),repeat=d)); pos={x:i for i,x in enumerate(idx)}
    P=np.zeros((L**d,L**d))
    for x in idx:
        for k in range(d):
            for s in (1,-1):
                y=list(x); y[k]=(y[k]+s)%L; P[pos[x],pos[tuple(y)]]=1
    return idx,P
def report(L,g,kappa=0.1,eta=1e-10,d=3):
    em,ep,gaps,A=support(d,L,g)
    idx,P=adj(d,L); lam,U=np.linalg.eigh(P)
    Es=np.linspace(-em+kappa,ep-kappa,121)
    rho=[m_of(E+1j*1e-8,A).imag/math.pi for E in Es]
    print("L=%d g=%g: e_-=%.4f e_+=%.4f #gaps=%d  min rho_N on [-e_-+0.1,e_+-0.1]=%.4f"%(L,g,em,ep,len(gaps),min(rho)))
    for E in (0.0,ep-kappa):
        z=E+1j*eta; m=m_of(z,A)
        M=(U*(1/(g*lam-z-m)))@U.T                     # M^(B)=(g Psi - z - m)^{-1}
        K=np.abs(M)**2; ev=np.sort(np.linalg.eigvalsh(np.eye(len(K))-K))
        Mpp=np.min(np.abs(1-np.linalg.eigvals(M**2)))
        dist=np.array([sum(min(abs(a-b),L-abs(a-b)) for a,b in zip(x,idx[0])) for x in idx])
        ct=max((abs(M[0,j])/g**dist[j])**(1/dist[j]) for j in range(len(idx)) if 0<dist[j]<=3)
        nb=min(abs(M[0,j])/g for j in range(len(idx)) if dist[j]==1)
        print("   E=%.4f |m|=%.4f Im m=%.4f Ward=%.9f lam1(1-K)=%.3e lam1/g^2=%.3f min_k|1-M++_k|=%.3f C_eff=%.2f min_{b~0}|M_0b|/g=%.3f"%(
            E,abs(m),m.imag,np.sum(np.abs(M[0])**2),ev[1],ev[1]/g**2,Mpp,ct,nb))
if __name__=="__main__":
    for L,g in ((6,0.2),(4,0.3),(5,0.2),(6,1e-3)): report(L,g)
```
### ba_check.py
```python
import math
from ba_supp import atoms, support
def m_of(z,A,it=400000):
    m=1j
    for _ in range(it):
        new=sum(w/(a-z-m) for a,w in A)
        if abs(new-m)<1e-14: return new
        m=0.5*m+0.5*new
    return m
if __name__=="__main__":
    print("cross-check by direct (self_m) iteration, eta=1e-7: rho_N=Im m/pi at E inside/outside the exact gap")
    for L,g,gi,pts in ((4,0.5,0,(2.5,3.085,3.4)),(5,1.0,2,(0.2,0.3395,0.5))):
        em,ep,gaps,A=support(3,L,g)
        print("L=%d g=%g gap=(%.3f,%.3f) E=%s rho_N=%s"%(L,g,*gaps[gi],pts,["%.2e"%(m_of(E+1e-7j,A).imag/math.pi) for E in pts]))
```
### ba_gcL.py
```python
# g_c(L): smallest g (bisection on [0.05,1.5], gap-count>0 assumed monotone) at which supp mu_N first has an interior gap, d=3
from ba_supp import support
def gc(L):
    lo,hi=0.05,1.5
    assert not support(3,L,lo)[2] and support(3,L,hi)[2]
    for _ in range(40):
        mid=(lo+hi)/2
        if support(3,L,mid)[2]: hi=mid
        else: lo=mid
    return hi
print("d=3 g_c(L) (first interior gap opens; cusp there):",{L:round(gc(L),4) for L in (3,4,5,6,7,8,10,12)})
```
### ba_cusp.py
```python
# L=4,d=3: critical g_c where the first interior gap of supp mu_N opens (cusp); rho_N(E*) ~ eta^{1/3} there
import math
from ba_supp import support
from ba_det import m_of
lo,hi=0.3,0.5          # no gap at lo, gap at hi (see ba_gc.py)
for _ in range(60):
    mid=(lo+hi)/2
    if support(3,4,mid)[2]: hi=mid
    else: lo=mid
em,ep,gaps,A=support(3,4,hi)
Es=0.5*(gaps[-1][0]+gaps[-1][1]); print("g_c(L=4)=%.9f  gap just above g_c: (%.6f,%.6f) -> cusp E*=%.5f ; e_g=%.5f ; E* in [-e+kappa,e-kappa] for kappa=0.1: %s"%(hi,*gaps[-1],Es,ep,abs(Es)<=ep-0.1))
em,ep,gaps,A=support(3,4,lo)
for eta in (1e-3,1e-5,1e-7):
    r=m_of(Es+1j*eta,A).imag/math.pi
    print("  g=g_c-: eta=%g rho_N(E*)=%.4e  rho/eta^(1/3)=%.4f"%(eta,r,r/eta**(1/3)))
```
### ba_vac.py
```python
# rho-form bulk set B_k={E: rho_N(E)>=k}, k=0.05: non-vacuous at each vacuity class (grid, eta=1e-7)
import math, numpy as np
from ba_supp import support
from ba_det import m_of
k=0.05
for name,L,g in (("gaps: L=4,g=10",4,10.0),("odd L: L=5,g=0.2",5,0.2),("cusp: L=4,g=g_c-",4,0.3542262),("interval: L=4,g=0.3",4,0.3)):
    em,ep,gaps,A=support(3,L,g)
    Es=np.linspace(-em,ep,1201); rho=np.array([m_of(E+1e-7j,A).imag/math.pi for E in Es])
    ok=rho>=k; E0=Es[int(np.argmin(np.abs(Es-0)))]
    print("%-20s e_-=%.4f e_+=%.4f #gaps=%d |B_k|/(e_-+e_+)=%.3f nonempty=%s rho(0)=%.4f"%(name,em,ep,len(gaps),ok.mean(),ok.any(),m_of(1e-7j,A).imag/math.pi))
```
### ba_flow.py
```python
# zztE_BA (7_8:1796-1801) at d=3, L=6, g=0.2: t0, E, g0=sqrt(t0) g ; sqrt(t0) m(E,g0)=m(z,g); where does E sit in the bulk of mu_{g0}?
import math
from ba_supp import atoms, support
from ba_det import m_of
d,L,g,kappa=3,6,0.2,0.1
A=atoms(d,L,g); em,ep,_,_=support(d,L,g)
print("g=%g: e_g=%.5f ; target window |Re z|<=e_g-kappa=%.5f"%(g,ep,ep-kappa))
for Rez,eta in ((0.0,1.0),(2.1,0.1),(2.1,1e-3)):
    z=Rez+1j*eta; m=m_of(z,A); t0=m.imag/(m.imag+eta); E=(t0*Rez-(1-t0)*m.real)/math.sqrt(t0); g0=math.sqrt(t0)*g
    A0=atoms(d,L,g0); e0m,e0p,gp0,_=support(d,L,g0); m0=m_of(E+1e-13j,A0)
    print("z=%+.1f+%gi t0=%.4f E=%+.4f g0=%.4f |sqrt(t0)m0-m|=%.0e rho_g0(E)=%.4f >= Im m(z)/pi=%.4f ; e_g0-|E|=%.4f"%(
      Rez,eta,t0,E,g0,abs(math.sqrt(t0)*m0-m),m0.imag/math.pi,m.imag/math.pi,e0p-abs(E)))
```
### ba_adm.py
```python
# sequence-level admissibility (Main_DEL_COND, eq:WO) and eq:off_diagM ratio r=(1-|m|^2)/min_{t in[0,1]}|1-t m^2|  (A_det:34)
import math
from fractions import Fraction as F
from ba_supp import atoms, support
from ba_det import m_of
d=3; c=F(1,20); dd=F(1,10)
for name,L,gexp in (("L=4,g=0.3 (fixed)",4,None),("L=6,g=W^-1.3",6,F(-13,10))):
    for n in (2,8):
        W=10**n; N=(W*L)**d; g=0.3 if gexp is None else float(W)**float(gexp)
        lo=float(W)**float(F(-d,2)+dd)
        print("%-14s n=%d N=%.1e: W>=N^c %s; W^{-d/2+dd}=%.1e <= g=%.1e <= 1/dd=%g: %s"%(name,n,N,W>=N**float(c),lo,g,1/float(dd),lo<=g<=1/float(dd)))
for L,g in ((6,0.2),(4,0.3),(5,0.2)):
    em,ep,_,A=support(3,L,g)
    for E in (0.0,ep-0.1):
        m=m_of(E+1e-10j,A); m2=m*m
        tmin=min(1.0,max(0.0,m2.real/abs(m2)**2)); mn=abs(1-tmin*m2)
        print("L=%d g=%g E=%.4f: 1-|m|^2=%.4f min_t|1-t m^2|=%.4f r=%.4f"%(L,g,E,1-abs(m)**2,mn,(1-abs(m)**2)/mn))
```
### n1_immlower.py
```python
# N1d: rho-form bulk B_kappa={E: rho_N(E)>=kappa}.  Claim to test (BAImmLower): for E in B_kappa and every eta in (0,1],
#      Im m(E+i eta, g) >= c(kappa) uniformly in (L,g).  Report min over eta in (0,1], E in B_kappa of Im m / (pi*kappa).
import math, numpy as np
from ba_supp import support, atoms
def solve(z, A, m0=None, it=400000, tol=1e-13):
    m = 1j if m0 is None else m0
    for _ in range(it):
        new = sum(w/(a - z - m) for a, w in A)
        if abs(new-m) < tol: return new
        m = 0.5*m + 0.5*new
    return m
kappa = 0.05
print("d=3 rho-bulk B_k (k=%.2f): min over E in B_k, eta in (0,1] of Im m(E+i eta)  [pi*k=%.4f]" % (kappa, math.pi*kappa))
for name, L, g in (("gaps  L=4 g=10", 4, 10.0), ("odd   L=5 g=0.2", 5, 0.2), ("cusp- L=4 g=0.35422", 4, 0.3542262), ("intvl L=4 g=0.3", 4, 0.3), ("small L=6 g=0.001", 6, 1e-3), ("large g L=6 g=3", 6, 3.0)):
    em, ep, gaps, A = support(3, L, g)
    Es = np.linspace(-em, ep, 241)
    rho = np.array([solve(E+1e-9j, A).imag/math.pi for E in Es])
    B = Es[rho >= kappa]
    # eta grid: log-spaced + 1
    etas = [1e-6, 1e-4, 1e-3, 1e-2, 3e-2, 0.1, 0.3, 0.5, 1.0]
    worst = 1e9; arg = None
    for E in B[::4]:
        for eta in etas:
            v = solve(E+1j*eta, A).imag
            if v < worst: worst, arg = v, (E, eta)
    print("%-22s |B_k| pts=%3d/%d  min Im m = %.4f at (E,eta)=(%.3f,%g)  ratio to pi*k = %.2f" % (name, len(B), len(Es), worst, arg[0], arg[1], worst/(math.pi*kappa)))
```
### n1_equiv.py
```python
# N1e: on regular sequences (L even, g small: interval support, no cusp) the paper's set {|E|<=e-kappa} and the rho-set {rho>=k'} are comparable:
#   c1(kappa) = min rho on [-e+kappa, e-kappa]  (so {|E|<=e-kappa} is inside {rho>=c1})  and  c2(k') = min{e-|E| : rho(E)>=k'}  (so {rho>=k'} is inside {|E|<=e-c2}).
import math, numpy as np
from ba_supp import support
from ba_core import m_of
def rho_grid(A, em, ep, n=2401):
    Es = np.linspace(-em, ep, n)
    return Es, np.array([m_of(E+1e-10j, A).imag/math.pi for E in Es])
print("d=3, L even, no gaps.   kappa:  c1(kappa)=min rho on |E|<=e-kappa ; sqrt(kappa)/pi (semicircle edge) ; then k'=0.05: c2(k')=min{e-|E|: rho>=k'}")
for L in (4,6,8):
    for g in (0.01, 0.1, 0.3):
        em,ep,gaps,A = support(3,L,g)
        assert not gaps
        Es, rho = rho_grid(A, em, ep)
        out=[]
        for kappa in (0.3, 0.1, 0.03, 0.01):
            sel = (np.abs(Es) <= ep-kappa)
            out.append("k=%.2f: %.4f (sc %.4f)" % (kappa, rho[sel].min(), math.sqrt(kappa)/math.pi))
        kp = 0.05
        c2 = (ep - np.abs(Es[rho>=kp])).min()
        print("L=%d g=%-5g e=%.4f  %s | k'=%.2f: c2=%.4f" % (L,g,ep," | ".join(out),kp,c2))
```
### n2_table.py
```python
# N2: exponent / constant table where M != m I changes an RBM estimate (d=3).  Bulk energies E in B_k, flow coupling g.
import math, numpy as np
from ba_core import *
from ba_supp import support
def row(L, g, E, kappa_label=""):
    A = atoms_of(L, g)
    eta = 1e-9
    m = m_of(E + 1j*eta, A)
    M0 = Mblock(L, g, E, m, eta)
    K0 = sym_to_K(M0)
    dist = dist_l1(L)
    ward = K0.sum()                         # = Im m/(Im m + eta) ~ 1
    # (+,+): M'_{0a} = M_{0a}^2 (a != 0), M''=M^2 diag = m^2
    Mpp0 = M0**2
    Mp = Mpp0.copy(); Mp[0,0,0] = 0
    nM1 = np.abs(Mp).sum()                   # ||M'||_{inf->inf} = 1-|m|^2 (Ward)
    tt = np.linspace(0,1,2001)
    mn = min(abs(1 - t*m*m) for t in tt)
    r = (1-abs(m)**2)/mn
    # check |1-t m^2|^2 = (1-t|m|^2)^2 + 4 t (Im m)^2
    t_chk = 0.37; lhs = abs(1-t_chk*m*m)**2; rhs = (1 - t_chk*abs(m)**2)**2 + 4*t_chk*m.imag**2
    # diffusion constant of K: Dk = (1/2d) sum_a K_{0a}|a|^2 (l2 distance squared)
    k = 2*np.pi*np.arange(L)/L
    x = np.arange(L); x2 = np.minimum(x, L-x)**2
    r2 = x2[:,None,None] + x2[None,:,None] + x2[None,None,:]
    Dk = (K0*r2).sum()/(2*D)
    # spectral gap of 1-K at the smallest nonzero momentum
    Kh = np.fft.fftn(K0).real
    lam1 = 1 - Kh[1,0,0]
    # CT decay: -log|M_{0a}|/|a| for |a|=1,2,3 (l1), a along axis
    ct = [(-math.log(abs(M0[j,0,0]))/j) if abs(M0[j,0,0])>0 else float('nan') for j in (1,2,3) if j < L]
    nb = abs(M0[1,0,0])
    return dict(L=L,g=g,E=E,Imm=m.imag,absm=abs(m),ward=ward,r=r,Dk_over_g2=Dk/g**2,lam1_over_g2L2=lam1/(g**2*(2-2*math.cos(2*math.pi/L))),nb_over_gstar=nb/min(g,1.0),ct=ct,chk=abs(lhs-rhs))
print("d=3, bulk points; r=(1-|m|^2)/min_t|1-t m^2| (A_det:32); Dk=(1/2d)sum_a K_0a|a|^2; lam1=1-Khat(2pi/L e1); nb=|M_{0 e1}|; ct=-log|M_{0,j e1}|/j (j=1,2,3)")
print("%-3s %-6s %-7s %-7s %-7s %-12s %-6s %-9s %-14s %-12s %s" % ("L","g","E","Im m","|m|","sum|M_0b|^2","r","Dk/g^2","lam1/(g^2 2(1-cos))","|M_0e|/min(g,1)","ct"))
for L in (5,7,9):
    for g in (0.05, 0.3, 1.0, 3.0, 10.0):
        em,ep,gaps,A = support(3,L,g)
        # pick E: 0, and the point of the bulk where rho is about 0.1 near the right edge
        for E in (0.0, 0.6*ep):
            m = m_of(E+1e-9j, A)
            if m.imag/math.pi < 0.03: continue
            r = row(L,g,E)
            print("%-3d %-6g %-7.3f %-7.4f %-7.4f %-12.9f %-6.3f %-9.3f %-14.3f %-12.3f %s  chk=%.1e" % (L,g,E,r['Imm'],r['absm'],r['ward'],r['r'],r['Dk_over_g2'],r['lam1_over_g2L2'],r['nb_over_gstar'],["%.2f"%c for c in r['ct']],r['chk']))
```
### n3_pt.py
```python
# N3: the BA propagator pins at extreme inputs (d=3): t -> 1, g in {0.05,0.3,1,3,10}, L in {15,21}.
# Channels: (+,-): Theta=(1-tK)^{-1}, K_ab=|M_ab|^2 ;  (+,+): Theta=(1-tM2)^{-1}, M2_ab=M_ab^2.
import math, numpy as np
from ba_core import *
from ba_supp import support
d = 3
def stats(L, g, E, e, c5=0.3):
    A = atoms_of(L, g); m = m_of(E+1e-9j, A)
    M0 = Mblock(L, g, E, m, 1e-9)
    K0 = np.abs(M0)**2
    t = 1 - e
    Th = theta_row(L, K0, t).real          # real: K symmetric nonnegative
    dist = dist_l1(L).astype(float)
    ell = min(max(g*e**-0.5, 1.0), L)
    B = (g*g + e)**-1 / (dist+1)**(d-2) + 1/(L**d*e)
    P5 = (np.abs(Th)/(B*np.exp(-c5*dist/ell))).max()
    Th0 = Th - Th.mean()                       # zero-mode removed: L^{-d} sum_a Theta(0,a) = mean
    P8 = (np.abs(Th0)*(g*g+e)*(dist+1)**(d-2)).max()
    # unit first/second differences in direction e_1 (by roll), weights (g^2+e)(|x|+1)^{d-1} / ^d, away from the origin shell |x|>=2
    D1 = np.abs(np.roll(Th,-1,axis=0)-Th)*(g*g+e)*(dist+1)**(d-1)
    D2 = np.abs(np.roll(Th,-1,axis=0)+np.roll(Th,1,axis=0)-2*Th)*(g*g+e)*(dist+1)**d
    mask = dist >= 2
    U1 = D1[mask].max(); U2s = D2[mask].max()
    # (+,+) channel, property 5s: |Theta^{++}(0,a)| <= C (1_{a=0} + g^2 e^{-c|a|}),  c=0.5
    M2 = M0**2
    ThPP = np.fft.ifftn(1.0/(1.0 - t*np.fft.fftn(M2)))
    ref = (dist==0) + g*g*np.exp(-0.5*dist)
    P5s = (np.abs(ThPP)/ref).max()
    return m.imag, P5, P8, U1, U2s, P5s
print("d=3 BA (+,-): P5=max|Th|/(B e^{-0.3|a|/l}); P8=max|Th0|(g^2+e)(|a|+1); U1,U2s unit differences (|x|>=2); (+,+): P5s=max|Th++|/(1_{a=0}+g^2 e^{-|a|/2})")
print("%-3s %-5s %-6s %-9s %-7s | %-6s %-6s %-6s %-6s %-6s" % ("L","g","E","e","Im m","P5","P8","U1","U2s","P5s"))
worst = {}
for L in (15,):
    for g in (0.05, 0.3, 1.0, 3.0, 10.0):
        em,ep,gaps,A = support(3,L,g)
        Es = [0.0] if g>=3 else [0.0, 0.6*ep]
        for E in Es:
            for e in (1e-9, 0.1*g*g/L**3, 0.1*g*g, g*g, 1.0):
                if e >= 1 : e = 0.999
                im,P5,P8,U1,U2s,P5s = stats(L,g,E,e)
                print("%-3d %-5g %-6.3f %-9.2e %-7.4f | %-6.2f %-6.2f %-6.2f %-6.2f %-6.2f" % (L,g,E,e,im,P5,P8,U1,U2s,P5s))
```
### n4_kn2.py
```python
# N4: (Kn2sol) for BA: K2_t = W^{-d} Theta_t M^{(+,-)} solves  d/dt K2 = W^d K2 K2  (kernel S=I, n=2 equation of (pro_dyncalK)), t -> 1.
import math, numpy as np
from ba_core import *
L, g, E = 5, 0.3, 0.0
A = atoms_of(L, g); m = m_of(E + 1e-9j, A)
M0 = Mblock(L, g, E, m, 1e-9); K0 = np.abs(M0)**2
Wd = 1.0   # W^d is a global factor: K2 = W^{-d} Theta M ; the equation is homogeneous in W^d
def K2(t):
    Th = theta_row(L, K0, t)                  # Theta_t(0,.)
    return np.fft.ifftn(np.fft.fftn(Th)*np.fft.fftn(K0))      # (Theta M)_{0 .}
print("d=3 L=5 g=0.3 E=0 (+,-): max |d/dt K2 - (K2*K2)| / max|d/dt K2|  (central difference, h=1e-6(1-t))")
for t in (0.0, 0.5, 0.99, 0.999999):
    h = 1e-6*(1-t) if t > 0 else 1e-6
    der = (K2(t+h) - K2(t-h))/(2*h)
    rhs = np.fft.ifftn(np.fft.fftn(K2(t))**2)  # convolution K2*K2 on the torus (S=I: sum_a K_{a1 a}K_{a a2}); translation invariance
    print("  t=%-9g  rel residual %.2e   (|K2| max %.3e)" % (t, np.abs(der-rhs).max()/np.abs(der).max(), np.abs(K2(t)).max()))
```
### n5_flow_matrix.py
```python
# N5: zztE_BA at the level of matrices (d=3): sqrt(t0) M(E,g0) = M(z,g), z_t0(E,g0) = sqrt(t0) z, Ward at complex z: sum_b |M(z)_0b|^2 = t0.
import math, numpy as np
from ba_core import *
def Mrow(L, g, z, m):
    return Mblock(L, g, z.real, m, z.imag)           # M_{0b} = ifft of 1/(g eps - z - m)
d, L = 3, 7
print("d=3 L=%d: model (g,z) -> flow (g0, E, m0=m/sqrt t0);  residuals of the three clauses of (eq:zztE_BA) and of Ward at z" % L)
print("%-6s %-22s %-9s %-9s %-8s %-10s %-10s %-10s %-10s" % ("g", "z", "t0", "g0", "E", "|sqrt(t0) m0 - m|", "max|sqrt(t0)M0-M|", "|zt0-sqrt(t0) z|", "|Ward-t0|"))
for g in (0.05, 0.3, 1.0, 3.0):
    A = atoms_of(L, g)
    for z in (0.3 + 0.2j, 1.2 + 1e-3j, 1.2 + 1e-8j, -0.5 + 0.7j):
        m = m_of(z, A); t0 = m.imag/(m.imag + z.imag); E = (t0*z.real - (1-t0)*m.real)/math.sqrt(t0); g0 = math.sqrt(t0)*g
        A0 = atoms_of(L, g0)
        # real-axis solution at (E,g0): iterate from m/sqrt(t0)  (self_m at real E)
        m0 = m/math.sqrt(t0)
        res_self = abs(m0 - sum(w/(a - E - m0) for a, w in A0))          # (self_m) at (E, g0) with the datum m0
        M = Mrow(L, g, z, m); M0 = Mrow(L, g0, E + 0j, m0)
        ztt0 = E + (1-t0)*m0
        ward = np.sum(np.abs(M)**2)
        print("%-6g %-22s %-9.5f %-9.5f %-8.4f %-18.1e %-18.1e %-16.1e %-10.1e (selfm@(E,g0) resid %.1e)" % (g, str(z), t0, g0, E, abs(math.sqrt(t0)*m0 - m), np.abs(math.sqrt(t0)*M0 - M).max(), abs(ztt0 - math.sqrt(t0)*z), abs(ward - t0), res_self))
```
### n6_lw.py
```python
# N6: the three expansions of the BA graph layer (lanlw B:359, lem_lweight B:376, GGGamma B:393) as identities of expectations.
# Setting: L=3 blocks (triangle C_3, Psi^(B)=J-I), W=1 (Anderson: V=diag real N(0,1)) -> exact Gauss-Hermite;  W=2 -> Monte Carlo.
# H_t = g0 Psi + sqrt(t) V,  z_t = E + (1-t) m  with an ARBITRARY m in C_+ (no self-consistency is used),  M=(g0 Psi - E - m)^{-1}, S=t*S(0).
import numpy as np, itertools, math
from numpy.polynomial.hermite_e import hermegauss
rng = np.random.default_rng(1)
L = 3; g0 = 0.7; E = 0.4 + 0.25j; t = 0.35
PsiB = np.ones((L, L)) - np.eye(L)
# m = the solution of (self_m) at the (complex) energy E on the block torus:  m = L^{-1} tr (g0 PsiB - E - m)^{-1}, Im m > 0
m = 0.5j
for _ in range(2000):
    mn = np.trace(np.linalg.inv(g0*PsiB - (E + m)*np.eye(L)))/L
    m = 0.5*m + 0.5*mn
print("m =", m, " self-consistency residual", abs(m - np.trace(np.linalg.inv(g0*PsiB - (E + m)*np.eye(L)))/L), " M_xx==m (W=1):", np.allclose(np.diag(np.linalg.inv(g0*PsiB-(E+m)*np.eye(L))), m))
def setup(W):
    N = L*W
    Psi = np.kron(PsiB, np.eye(W))
    M = np.linalg.inv(g0*Psi - (E + m)*np.eye(N))
    S0 = np.kron(np.eye(L), np.ones((W, W))/W)          # S(0)_{xy} = W^{-1} 1(same block)
    S = t*S0
    Mp = M * M.T                                        # M^+_{xy} = M_xy M_yx
    Wt = np.linalg.inv(np.eye(N) - Mp @ S)              # 1 + M^+ S^+
    Sp = S @ Wt                                          # S^+ = S (1 - M^+ S)^{-1}
    return N, Psi, M, S, Mp, Wt, Sp
def Gfun(H, z): return np.linalg.inv(H - z*np.eye(H.shape[0]))
zt = E + (1-t)*m
def quantities(W, V, Psi, M, f_kind):
    N = L*W
    H = g0*Psi + np.sqrt(t)*V
    G = Gfun(H, zt); Gs = Gfun(H, np.conj(zt))       # G^*(as function of H) = (H - zbar)^{-1}
    Gc = G - M
    return H, G, Gs, Gc
# f(G) = G_{ab} * conj(G_{cd}) ; conj(G_cd) = (G^*)_{dc} at Hermitian H.  derivatives wrt H_{beta alpha}:
def f_and_df(G, Gs, a, b, c, d, N):
    f = G[a, b]*Gs[d, c]
    df = np.zeros((N, N), dtype=complex)                 # df[beta, alpha] = d f / d H_{beta alpha}
    for be in range(N):
        for al in range(N):
            df[be, al] = (-G[a, be]*G[al, b])*Gs[d, c] + G[a, b]*(-Gs[d, be]*Gs[al, c])
    return f, df
def rhs_lanlw(G, Gc, M, S, f, df, x, y, N):
    r = 0
    for al in range(N):
        for be in range(N):
            r += M[x, al]*S[al, be]*(Gc[be, be]*G[al, y]*f - G[be, y]*df[be, al])
    return r
def rhs_lweight(G, Gc, M, S, Wt, f, df, x, N):
    r = 0
    for y in range(N):
        inner = 0
        for al in range(N):
            for be in range(N):
                inner += M[y, al]*S[al, be]*(Gc[al, y]*Gc[be, be]*f - G[be, y]*df[be, al])
        r += Wt[x, y]*inner
    return r
MPSP_MODE = 'paper'
def rhs_gg(G, Gc, M, S, Wt, Sp, f, df, x, y, yp, N):
    r = 0
    Mp = M * M.T
    for be in range(N):
        coef = Sp[x, be] if MPSP_MODE == 'paper' else (Wt - np.eye(N))[x, be]      # S^+_{x be}  (as printed)  vs  (M^+ S^+)_{x be} = Wt - 1
        r += coef*M[be, y]*M[yp, be]*f
        r += coef*(Gc[be, y]*M[yp, be] + M[be, y]*Gc[yp, be])*f
    for w in range(N):
        for al in range(N):
            for be in range(N):
                r += Wt[x, w]*M[w, al]*S[al, be]*(Gc[be, be]*G[al, y]*Gc[yp, w]*f + Gc[al, w]*G[be, y]*G[yp, be]*f - G[be, y]*Gc[yp, w]*df[be, al])
    return r
def run(W, nodes=None, nsamp=None):
    N, Psi, M, S, Mp, Wt, Sp = setup(W)
    cases = [(0,1,2,0),(1,1,0,2),(2,0,1,1)]            # f = G_ab conj(G_cd)
    pts = [(1,2),(0,0),(2,1)]                           # (x,y) for lanlw / GGGamma (x,y,yp)
    acc = {k: [0j, 0j] for k in ("lan","lw","gg")}
    # collect samples
    if W == 1:
        xs, ws = hermegauss(nodes); ws = ws/ws.sum()
        samples = [(np.diag(np.array(v)), np.prod([ws[i] for i in idx])) for idx in itertools.product(range(nodes), repeat=N) for v in [[xs[i] for i in idx]]]
    else:
        samples = []
        for _ in range(nsamp):
            V = np.zeros((N, N), dtype=complex)
            for b in range(L):
                A = (rng.normal(size=(W, W)) + 1j*rng.normal(size=(W, W)))/math.sqrt(2)
                Hb = (A + A.conj().T)/math.sqrt(2)         # GUE: diag real N(0,1), offdiag complex var 1
                V[b*W:(b+1)*W, b*W:(b+1)*W] = Hb/math.sqrt(W)  # variance 1/W per entry
            samples.append((V, 1.0/nsamp))
    res = []
    out = {}
    for ci, (a,b,c,d) in enumerate(cases[:2]):
        lan_l = lan_r = lw_l = lw_r = gg_l = gg_r = 0
        x, y = pts[ci][0], pts[ci][1]
        for V, w in samples:
            H, G, Gs, Gc = quantities(W, V, Psi, M, None)
            f, df = f_and_df(G, Gs, a, b, c, d, N)
            lan_l += w*Gc[x, y]*f; lan_r += w*rhs_lanlw(G, Gc, M, S, f, df, x, y, N)
            lw_l += w*Gc[x, x]*f;  lw_r += w*rhs_lweight(G, Gc, M, S, Wt, f, df, x, N)
            yp = (y+1) % N
            gg_l += w*Gc[yp, x]*Gc[x, y]*f; gg_r += w*rhs_gg(G, Gc, M, S, Wt, Sp, f, df, x, y, yp, N)
        out[ci] = (lan_l, lan_r, lw_l, lw_r, gg_l, gg_r)
    return out
for MODE in ('paper', 'MPSP'):
  MPSP_MODE = MODE
  for W, kw in ((1, dict(nodes=26)),):
    o = run(W, **kw)
    print("GGGamma first two sums with coefficient", "S^+_{x be} (as printed, B:398)" if MODE=='paper' else "(M^+ S^+)_{x be}")
    print("W=%d (exact Gauss-Hermite, %d nodes/dim): |LHS - RHS| for (lanlw, lweight, GGGamma), and |LHS|" % (W, kw['nodes']))
    for ci, v in o.items():
        print("  f#%d:  lanlw %.2e (|LHS|=%.3f)   lweight %.2e (|LHS|=%.3f)   GGGamma %.2e (|LHS|=%.3f)" % (ci, abs(v[0]-v[1]), abs(v[0]), abs(v[2]-v[3]), abs(v[2]), abs(v[4]-v[5]), abs(v[4])))
```
### n6_lw_mc.py
```python
# N6b: the same three identities at W=2 (N=6): Monte Carlo over the block-GUE potential V (off-diagonal S_{alpha beta} != 0 inside a block).
import numpy as np, math
rng = np.random.default_rng(7)
L, W = 3, 2; N = L*W
g0 = 0.7; E = 0.4 + 0.25j; t = 0.35
PsiB = np.ones((L, L)) - np.eye(L)
m = 0.5j
for _ in range(3000):
    m = 0.5*m + 0.5*np.trace(np.linalg.inv(g0*PsiB - (E + m)*np.eye(L)))/L
Psi = np.kron(PsiB, np.eye(W))
M = np.linalg.inv(g0*Psi - (E + m)*np.eye(N))
S0 = np.kron(np.eye(L), np.ones((W, W))/W); S = t*S0
Mp = M * M.T; Wt = np.linalg.inv(np.eye(N) - Mp @ S); WtM1 = Wt - np.eye(N)
zt = E + (1-t)*m
def sample(B):
    V = np.zeros((B, N, N), dtype=complex)
    for b in range(L):
        A = (rng.normal(size=(B, W, W)) + 1j*rng.normal(size=(B, W, W)))/math.sqrt(2)
        Hb = (A + np.conj(np.swapaxes(A, 1, 2)))/math.sqrt(2)       # GUE: diag N(0,1) real, offdiag complex E|.|^2=1
        V[:, b*W:(b+1)*W, b*W:(b+1)*W] = Hb/math.sqrt(W)
    return V
def run(B, nb, A_=0,B_=1,C_=0,D_=1,XL=0,YL=0,XW=2,XG=0,YG=2,YPG=2):
    acc = np.zeros(6, dtype=complex); acc2 = np.zeros(6, dtype=float)
    a,b,c,d = A_,B_,C_,D_
    for _ in range(nb):
        V = sample(B); H = g0*Psi + math.sqrt(t)*V
        G = np.linalg.inv(H - zt*np.eye(N)); Gs = np.linalg.inv(H - np.conj(zt)*np.eye(N))
        Gc = G - M
        f = G[:, a, b]*Gs[:, d, c]                                  # f = G_ab conj(G_cd)
        # df[B, be, al] = d f / d H_{be al}
        df = (-G[:, a, :, None]*G[:, None, :, b])*Gs[:, d, c][:, None, None] + G[:, a, b][:, None, None]*(-Gs[:, d, :, None]*Gs[:, None, :, c])
        # lanlw
        x,y = XL,YL
        lan_l = Gc[:, x, y]*f
        lan_r = np.einsum('xa,ab,Bb,Ba->B', M[x:x+1, :], S, Gc.diagonal(axis1=1, axis2=2), G[:, :, y])*0
        t1 = np.einsum('a,ab,Bb,Ba,B->B', M[x, :], S, Gc.diagonal(axis1=1, axis2=2), G[:, :, y], f)
        t2 = np.einsum('a,ab,Bb,Bba->B', M[x, :], S, G[:, :, y], df)
        lan_r = t1 - t2
        # lweight
        x = XW
        lw_l = Gc[:, x, x]*f
        inner_a = np.einsum('ya,ab,Bay,Bb,B->By', M, S, Gc, Gc.diagonal(axis1=1, axis2=2), f)
        inner_b = np.einsum('ya,ab,Bby,Bba->By', M, S, G, df)
        lw_r = np.einsum('y,By->B', Wt[x, :], inner_a - inner_b)
        # GGGamma (corrected coefficient (M^+S^+) = Wt - 1)
        x,y,yp = XG,YG,YPG
        gg_l = Gc[:, yp, x]*Gc[:, x, y]*f
        r1 = np.einsum('b,b,b,B->B', WtM1[x, :], M[:, y], M[yp, :], f)
        r2 = np.einsum('b,Bb,b->B', WtM1[x, :], Gc[:, :, y], M[yp, :])*f + np.einsum('b,b,Bb->B', WtM1[x, :], M[:, y], Gc[:, yp, :])*f
        r3a = np.einsum('w,wa,ab,Bb,Ba,Bw,B->B', Wt[x, :], M, S, Gc.diagonal(axis1=1, axis2=2), G[:, :, y], Gc[:, yp, :], f)
        r3b = np.einsum('w,wa,ab,Baw,Bb,Bb,B->B', Wt[x, :], M, S, Gc, G[:, :, y], G[:, yp, :], f)
        r3c = np.einsum('w,wa,ab,Bb,Bw,Bba->B', Wt[x, :], M, S, G[:, :, y], Gc[:, yp, :], df)
        gg_r = r1 + r2 + r3a + r3b - r3c
        for i, v in enumerate((lan_l, lan_r, lw_l, lw_r, gg_l, gg_r)):
            acc[i] += v.sum(); acc2[i] += (np.abs(v)**2).sum()
    n = B*nb
    mean = acc/n; var = acc2/n - np.abs(mean)**2
    return mean, np.sqrt(var/n), n
for cfg in ((0,1,0,1, 0,0,2, 0,2,2), (1,3,1,3, 1,1,4, 3,1,1), (0,2,0,2, 2,2,0, 1,4,4)):
  mean, se, n = run(20000, 20, *cfg)
  print("W=2, N=6, L=3, n=%d samples; f = |G_%d%d|^2; lanlw (x,y)=(%d,%d); lweight x=%d; GGGamma (x,y,y')=(%d,%d,%d)" % ((n, cfg[0], cfg[1], cfg[4], cfg[5], cfg[6], cfg[7], cfg[8], cfg[9])))
  for name, (i, j) in (("lanlw", (0, 1)), ("lweight", (2, 3)), ("GGGamma (M^+S^+ coefficient)", (4, 5))):
      print("  %-30s LHS=%+.5f%+.5fi  RHS=%+.5f%+.5fi  |LHS-RHS|=%.1e  (MC s.e. ~ %.1e)" % (name, mean[i].real, mean[i].imag, mean[j].real, mean[j].imag, abs(mean[i]-mean[j]), max(se[i], se[j])))
```
### n6_lw_mc_printed.py
```python
# N6b: the same three identities at W=2 (N=6): Monte Carlo over the block-GUE potential V (off-diagonal S_{alpha beta} != 0 inside a block).
import numpy as np, math
rng = np.random.default_rng(7)
L, W = 3, 2; N = L*W
g0 = 0.7; E = 0.4 + 0.25j; t = 0.35
PsiB = np.ones((L, L)) - np.eye(L)
m = 0.5j
for _ in range(3000):
    m = 0.5*m + 0.5*np.trace(np.linalg.inv(g0*PsiB - (E + m)*np.eye(L)))/L
Psi = np.kron(PsiB, np.eye(W))
M = np.linalg.inv(g0*Psi - (E + m)*np.eye(N))
S0 = np.kron(np.eye(L), np.ones((W, W))/W); S = t*S0
Mp = M * M.T; Wt = np.linalg.inv(np.eye(N) - Mp @ S); WtM1 = S @ Wt   # S^+ as printed in B:398
zt = E + (1-t)*m
def sample(B):
    V = np.zeros((B, N, N), dtype=complex)
    for b in range(L):
        A = (rng.normal(size=(B, W, W)) + 1j*rng.normal(size=(B, W, W)))/math.sqrt(2)
        Hb = (A + np.conj(np.swapaxes(A, 1, 2)))/math.sqrt(2)       # GUE: diag N(0,1) real, offdiag complex E|.|^2=1
        V[:, b*W:(b+1)*W, b*W:(b+1)*W] = Hb/math.sqrt(W)
    return V
def run(B, nb, A_=0,B_=1,C_=0,D_=1,XL=0,YL=0,XW=2,XG=0,YG=2,YPG=2):
    acc = np.zeros(6, dtype=complex); acc2 = np.zeros(6, dtype=float)
    a,b,c,d = A_,B_,C_,D_
    for _ in range(nb):
        V = sample(B); H = g0*Psi + math.sqrt(t)*V
        G = np.linalg.inv(H - zt*np.eye(N)); Gs = np.linalg.inv(H - np.conj(zt)*np.eye(N))
        Gc = G - M
        f = G[:, a, b]*Gs[:, d, c]                                  # f = G_ab conj(G_cd)
        # df[B, be, al] = d f / d H_{be al}
        df = (-G[:, a, :, None]*G[:, None, :, b])*Gs[:, d, c][:, None, None] + G[:, a, b][:, None, None]*(-Gs[:, d, :, None]*Gs[:, None, :, c])
        # lanlw
        x,y = XL,YL
        lan_l = Gc[:, x, y]*f
        lan_r = np.einsum('xa,ab,Bb,Ba->B', M[x:x+1, :], S, Gc.diagonal(axis1=1, axis2=2), G[:, :, y])*0
        t1 = np.einsum('a,ab,Bb,Ba,B->B', M[x, :], S, Gc.diagonal(axis1=1, axis2=2), G[:, :, y], f)
        t2 = np.einsum('a,ab,Bb,Bba->B', M[x, :], S, G[:, :, y], df)
        lan_r = t1 - t2
        # lweight
        x = XW
        lw_l = Gc[:, x, x]*f
        inner_a = np.einsum('ya,ab,Bay,Bb,B->By', M, S, Gc, Gc.diagonal(axis1=1, axis2=2), f)
        inner_b = np.einsum('ya,ab,Bby,Bba->By', M, S, G, df)
        lw_r = np.einsum('y,By->B', Wt[x, :], inner_a - inner_b)
        # GGGamma (corrected coefficient (M^+S^+) = Wt - 1)
        x,y,yp = XG,YG,YPG
        gg_l = Gc[:, yp, x]*Gc[:, x, y]*f
        r1 = np.einsum('b,b,b,B->B', WtM1[x, :], M[:, y], M[yp, :], f)
        r2 = np.einsum('b,Bb,b->B', WtM1[x, :], Gc[:, :, y], M[yp, :])*f + np.einsum('b,b,Bb->B', WtM1[x, :], M[:, y], Gc[:, yp, :])*f
        r3a = np.einsum('w,wa,ab,Bb,Ba,Bw,B->B', Wt[x, :], M, S, Gc.diagonal(axis1=1, axis2=2), G[:, :, y], Gc[:, yp, :], f)
        r3b = np.einsum('w,wa,ab,Baw,Bb,Bb,B->B', Wt[x, :], M, S, Gc, G[:, :, y], G[:, yp, :], f)
        r3c = np.einsum('w,wa,ab,Bb,Bw,Bba->B', Wt[x, :], M, S, G[:, :, y], Gc[:, yp, :], df)
        gg_r = r1 + r2 + r3a + r3b - r3c
        for i, v in enumerate((lan_l, lan_r, lw_l, lw_r, gg_l, gg_r)):
            acc[i] += v.sum(); acc2[i] += (np.abs(v)**2).sum()
    n = B*nb
    mean = acc/n; var = acc2/n - np.abs(mean)**2
    return mean, np.sqrt(var/n), n
for cfg in ((0,1,0,1, 0,0,2, 0,2,2), (1,3,1,3, 1,1,4, 3,1,1), (0,2,0,2, 2,2,0, 1,4,4)):
  mean, se, n = run(20000, 20, *cfg)
  print("W=2, N=6, L=3, n=%d samples; f = |G_%d%d|^2; lanlw (x,y)=(%d,%d); lweight x=%d; GGGamma (x,y,y')=(%d,%d,%d)" % ((n, cfg[0], cfg[1], cfg[4], cfg[5], cfg[6], cfg[7], cfg[8], cfg[9])))
  for name, (i, j) in (("GGGamma with S^+ as printed", (4, 5)),):
      print("  %-30s LHS=%+.5f%+.5fi  RHS=%+.5f%+.5fi  |LHS-RHS|=%.1e  (MC s.e. ~ %.1e)" % (name, mean[i].real, mean[i].imag, mean[j].real, mean[j].imag, abs(mean[i]-mean[j]), max(se[i], se[j])))
```
### cls_numerics.py
```python
# The class sequences of the probe (section 13.9): for (L, g_raw) with w = 6i/5 the flow point (g0, E_*, m0) of zztE_BA at the
# subordination point z_S = w - m_w; the same formulas as `fp`/`exists_flowPt` in the probe; classification at the coupling g0.
import math, cmath
from ba_supp import support, atoms
W = 1.2j
def flow_point(L, graw):
    A = atoms(3, L, graw)
    mw = sum(w/(a - W) for a, w in A)                 # m_w = L^-3 tr (g Psi - w)^-1  (BAmSubord)
    zS = W - mw
    t0 = mw.imag/(mw.imag + zS.imag)                  # BAt0
    E = (t0*zS.real - (1 - t0)*mw.real)/math.sqrt(t0) # BAflowE
    g0 = math.sqrt(t0)*graw
    m0 = mw/math.sqrt(t0)
    A0 = atoms(3, L, g0)
    res = abs(m0 - sum(w/(a - E - m0) for a, w in A0))  # (self_m) at (E, g0): residual of the flow point
    return mw, zS, t0, E, g0, m0, res
print('subordination point w = 6i/5, d = 3: flow point (g0 = sqrt(t0) g_raw, E_*, m0 = m_w/sqrt(t0)); lower bound of the probe: t0 >= 1/(|w|^2+g_raw^2 L^3)')
print('%-3s %-8s %-9s %-9s %-9s %-10s %-9s %-9s %-13s | support at g0: e_-, e_+, #gaps, rho_N(E_*), pi*kappa=Im m0 | class' % ('L', 'g_raw', 't0', 't0 bound', 'g0', 'E_*', 'Im m0', 'residual', 'Re m0'))
cg = 0.354226297  # g_c(4) of (a)
for L, graw in ((4, 10.0), (5, 0.2), (4, 0.3)):
    mw, zS, t0, E, g0, m0, res = flow_point(L, graw)
    em, ep, gaps, A0 = support(3, L, g0)
    bound = 1/(abs(W)**2 + graw**2*L**3)
    cls = []
    if L % 2 == 1: cls.append('odd L (e_+ != e_-: %.4f vs %.4f)' % (ep, em))
    if gaps: cls.append('gaps (%d interior gaps, first (%.3f,%.3f))' % ((len(gaps),) + tuple(gaps[0])))
    if not gaps and L % 2 == 0: cls.append('interval (g0 %s g_c(4)=%.4f)' % ('<' if g0 < cg else '>', cg))
    print('%-3d %-8g %-9.4g %-9.3g %-9.4f %-10.5f %-9.5f %-9.1e %-13.2e | %.4f %.4f %d %.5f %.5f | %s' % (L, graw, t0, bound, g0, E, m0.imag, res, m0.real, em, ep, len(gaps), m0.imag/math.pi, m0.imag, '; '.join(cls)))
```
### inv_paper.py
```python
# Inventory of the BA statements of the paper (paper/tex).  Parsing: comments stripped; statement environments with their
# labels, line ranges, cited keys in the statement and in the proof that follows it; BA-mention counts (lines naming the BA model:
# "Anderson", "_BA", the token BA, scalingBA).  Part 1: all statement environments with >= 1 BA-mention line (statement or proof);
# part 2: the BA-mention lines outside every statement environment, grouped.
import re, collections, sys
T = '/Users/junyin/Lean_proof/RBM3D/paper/tex/'
FILES = ['1_2_Intro_model_result','3_5_Loop_Hierarchy','6_Step6_two_loop','7_8_light_weight','A_deterministic_estimates','B_graphical_lemmas']
STAT = ('lemma','theorem','proposition','corollary','definition','claim','assumption','conjecture')
PAT = re.compile(r'[Aa]nderson|_BA\b|[^A-Za-z]BA[^A-Za-z]|scalingBA|\{BA\}')
def strip(ln):
    out = []; i = 0
    while i < len(ln):
        if ln[i] == '%' and (i == 0 or ln[i-1] != '\\'): break
        out.append(ln[i]); i += 1
    return ''.join(out)
units = []
loose = collections.OrderedDict()
for f in FILES:
    L = [strip(x) for x in open(T+f+'.tex', encoding='utf-8').read().split('\n')]
    envs = []; stack = []
    for i, ln in enumerate(L, 1):
        for m in re.finditer(r'\\(begin|end)\{(\w+)\*?\}', ln):
            if m.group(1) == 'begin': stack.append((m.group(2), i))
            else:
                for j in range(len(stack)-1, -1, -1):
                    if stack[j][0] == m.group(2):
                        envs.append((m.group(2), stack[j][1], i)); del stack[j:]; break
    st = sorted([e for e in envs if e[0] in STAT], key=lambda e: e[1])
    pr = sorted([e for e in envs if e[0] == 'proof'], key=lambda e: e[1])
    def labels(a, b): return sum([re.findall(r'\\label\{([^}]*)\}', L[i]) for i in range(a-1, b)], [])
    def cites(a, b):
        out = []
        for i in range(a-1, b):
            for m in re.finditer(r'\\cite[a-z]*(?:\[[^\]]*\])?\{([^}]*)\}', L[i]): out += [x.strip() for x in m.group(1).split(',')]
        return out
    def proof_of(e):
        # proof whose begin line is within 3 lines after the statement end (no other statement between)
        for p in pr:
            if e[2] <= p[1] <= e[2] + 3: return p
        return None
    inner = set()
    for e in st:
        p = proof_of(e); rng = [(e[1], e[2])] + ([(p[1], p[2])] if p else [])
        hits = [h for h in range(1, len(L)+1) if PAT.search(L[h-1]) and any(a <= h <= b for a, b in rng)]
        if hits:
            lab = labels(e[1], e[1] + 2) or labels(e[1], e[2])
            units.append((f, e[0], e[1], e[2], p[2] if p else e[2], lab[:1], sorted(set(cites(e[1], e[2]))), sorted(set(cites(p[1], p[2]))) if p else [], len(hits)))
    covered = [(e[1], e[2]) for e in st] + [(p[1], p[2]) for e in st for p in [proof_of(e)] if p]
    for h in range(1, len(L)+1):
        if PAT.search(L[h-1]) and not any(a <= h <= b for a, b in covered):
            loose.setdefault(f, []).append(h)
print('PART 1: statement environments (with their proof) that name the BA model')
CLS = {
 'MR:decol_BA': ('new', 'Thm 2.7: BAEnd_*, BAThm27'), 'def_flow': ('shared', 'm(E+i0,g), M(E,g) at BA: BAm, BAMB'), 'lem:SE_basic': ('shared', 'S^(B)(0)=I: FlowFM.S := 1'),
 'lem_WI_K': ('cited', '[RBSO1D L3.17]: BA-K5'), 'def_Theta': ('shared', 'M^(s1,s2)_ab = M_ba(s1) M_ab(s2): BAMss, BATheta'), 'lem_propTH': ('shared', 'consts depend on g^-1, 1<=g<=d^-1 (1150): BAProp5..8'),
 'lem_GbEXP': ('band', 'no BA claim (line 14 is a notation footnote); twin lem_GbEXP_BA'), 'zztE_BA': ('cited', '[RBSO1D L3.3]: proved here BAzztE_*'), 'lem:main_ind_BA': ('new', 'BAMainInd'),
 'lem:propM': ('cited', '[LSY15 L3.5],[Aizenman 10.5]: BAPropM'), 'lem_GbEXP_BA': ('cited', '[RBSO1D L6.1]: BAGbEXP'), 'lem_ConArg_BA': ('cited', '[RBSO1D L7.1]: BAConArg'),
 'tree-representation_BA': ('cited', '[RBSO1D L4.16]: BA-K2'), 'lem_pureloop': ('shared', 'BA proof uses Mbound_AO(2) (A:690): BA-K3'), 'def scalingBA': ('new', 'BA-L1'),
 'lanlw': ('cited', '[yang2024Del B.9]: BAlanlw'), 'lem_lweight': ('cited', '[B.10]: BAlweight'), 'GGGamma': ('cited', '[B.11]: BAGGGamma; delta T2161a')}
print('%-3s %-26s %-11s %-10s %-24s %-34s %-8s %s' % ('#', 'file', 'kind', 'stmt', 'label', 'cites(stmt|proof)', 'class', 'pin / ticket'))
for k, (f, kind, a, b, pe, lab, c1, c2, n) in enumerate(units, 1):
    c = CLS.get(lab[0] if lab else '-', ('UNCLASSIFIED', ''))
    print('%-3d %-26s %-11s %-10s %-24s %-34s %-8s %s' % (k, f[:26], kind[:11], '%d-%d' % (a, b), (lab[0] if lab else '-')[:24], (','.join(c1) + '|' + ','.join(c2))[:34], c[0], c[1]))
print('units', len(units), ' unclassified:', [lab[0] if lab else '-' for (f, kind, a, b, pe, lab, c1, c2, n) in units if (lab[0] if lab else '-') not in CLS])
print('PART 2: BA-mention lines outside every statement environment (file: line numbers)')
for f, hs in loose.items():
    print('%-26s %d lines: %s' % (f, len(hs), ' '.join(map(str, hs))))

print('PART 3: BA text that is not a statement environment (definitions in text, modified proofs); the start line is printed to check the range')
EXTRA = [
 ('1_2_Intro_model_result', 599, 636, 'model: H=V+g Psi, (self_m) 626, (def_G0) 631, e_lambda, supp mu_N 624 [Biane]', 'new', 'BASelf, BAm, BAMB; bulk decision b.3'),
 ('1_2_Intro_model_result', 658, 666, 'def:Theta_BA, (Theta M)_ab in the quantum diffusion', 'new', 'BATheta, BAprof, BAqdConcl'),
 ('7_8_light_weight', 1817, 1819, 'spectral_domainBA: |Ehat| <= e_g - kappa', 'change', 'BAendDom, BAdom (rho-form)'),
 ('7_8_light_weight', 1999, 2096, '(eq:MG_conclusion3_BA), EMn2 for BA (deterministic J)', 'change', 'BAEMn2Exp'),
 ('7_8_light_weight', 2100, 2105, 'Steps 3-6 verbatim except sec:Step5_larget and LWterm_EXP', 'change', 'ST pins over baFM; BAGbEXP in 5(iii); BA-L1..L4'),
 ('A_deterministic_estimates', 12, 70, 'proof of lem_propTH 5-8: BA mentions at 14,20,25,58,59', 'change', 'BAProp5..8, BA-P1..P8'),
 ('A_deterministic_estimates', 584, 598, 'K-loop tree representation with M-entries (A:376)', 'cited', '[RBSO1D L4.16, S4]: BA-K2'),
 ('A_deterministic_estimates', 690, 740, '(eq:Sigma-empty-sum-zero) for BA [RBSO1D L4.29, Claim 4.30]', 'cited', 'BA-K3, BAKbound'),
 ('B_graphical_lemmas', 286, 344, 'Psi-dotted / M-dotted edges, atoms (def_atom)', 'new', 'BA-L1'),
 ('B_graphical_lemmas', 407, 523, 'BA lvl1, atomic reduction, auxiliary graph, G_by_auxG_BA', 'change', 'BA-L3'),
 ('B_graphical_lemmas', 118, 118, 'LWterm_EXP with GGGamma for BA ("omit")', 'change', 'BA-L4'),
]
for f, a, b, what, cl, pin in EXTRA:
    L = open(T + f + '.tex', encoding='utf-8').read().split('\n')
    print('%-26s %-9s %-8s %-60s %-30s | %s' % (f[:26], '%d-%d' % (a, b), cl, what[:60], pin[:30], re.sub(r'\s+', ' ', strip(L[a-1]))[:50]))
```
### inv_paper_summary.py
```python
# Part 1 of inv_paper.out grouped by class: label + file:lines (file prefixes 1_2, 3_5, 7_8, A, B = paper/tex/{1_2_Intro_model_result, 3_5_Loop_Hierarchy, 7_8_light_weight, A_deterministic_estimates, B_graphical_lemmas}.tex)
import re, collections
short = {'1_2_Intro_model_result': '1_2', '3_5_Loop_Hierarchy': '3_5', '7_8_light_weight': '7_8', 'A_deterministic_estimates': 'A', 'B_graphical_lemmas': 'B'}
g = collections.OrderedDict((c, []) for c in ('new', 'shared', 'cited', 'band'))
for ln in open('inv_paper.out', encoding='utf-8'):
    m = re.match(r'^(\d+)\s+(\S+)\s+(theorem|lemma|definition)\s+(\d+-\d+)\s+(.+?)\s{2,}.*?\s(new|shared|cited|band)\s', ln)
    if m: g[m.group(6)].append('%s %s:%s' % (m.group(5).strip(), short[m.group(2)], m.group(4)))
tot = sum(len(v) for v in g.values())
print('statement environments naming the BA model: %d (each with its proof; `$S/inv_paper.out` has cites and pins)' % tot)
for c, v in g.items(): print('  %-6s (%d): %s' % (c, len(v), '; '.join(v)))
```
### inv_cites.py
```python
# Every \cite in the BA part of the paper: file:line, active (printed) or commented-out, key, optional argument, context.
import re
T = '/Users/junyin/Lean_proof/RBM3D/paper/tex/'
RANGES = [('1_2_Intro_model_result', 599, 675), ('7_8_light_weight', 1792, 2108), ('B_graphical_lemmas', 286, 525),
          ('A_deterministic_estimates', 12, 70), ('A_deterministic_estimates', 370, 380), ('A_deterministic_estimates', 584, 598),
          ('A_deterministic_estimates', 640, 740), ('1_2_Intro_model_result', 1030, 1052), ('1_2_Intro_model_result', 1172, 1176),
          ('3_5_Loop_Hierarchy', 2210, 2250)]
rows = []
for f, a, b in RANGES:
    L = open(T+f+'.tex', encoding='utf-8').read().split('\n')
    for i in range(a, b+1):
        ln = L[i-1]
        # split into active / commented part
        k = None
        for j, ch in enumerate(ln):
            if ch == '%' and (j == 0 or ln[j-1] != '\\'): k = j; break
        act, com = (ln, '') if k is None else (ln[:k], ln[k:])
        for part, tag in ((act, 'active'), (com, 'COMMENTED')):
            for m in re.finditer(r'\\cite[a-z]*\s*(?:\[([^\]]*)\])?\{([^}]*)\}', part):
                opt = m.group(1) or ''
                ctx = re.sub(r'\s+', ' ', part[max(0, m.start()-45):m.start()])
                # "Lemma 3.3 of \cite" pattern: take the words before
                rows.append((f, i, tag, m.group(2).strip(), opt, ctx))
print('%-26s %-5s %-9s %-26s %-12s %s' % ('file', 'line', 'status', 'key', 'optarg', 'context(45 chars before)'))
for f, i, tag, key, opt, ctx in rows:
    print('%-26s %-5d %-9s %-26s %-12s %s' % (f[:26], i, tag, key[:26], opt[:12], ctx))
import collections
c = collections.Counter((r[3], r[2]) for r in rows)
print('distinct (key,status):', len(c), ' active cites:', sum(1 for r in rows if r[2]=='active'), ' commented cites:', sum(1 for r in rows if r[2]=='COMMENTED'))
```
### inv_merged_ba.py
```python
import subprocess, re, os
R='/Users/junyin/Lean_proof/RBM3D-wt/T2161'
rows = [
 ('PsiB','Gauss/BlockAnderson.lean','Psi^(B) = adjacency of the block torus (eq:Psi3D)','covers'),
 ('PsiV','Gauss/BlockAnderson.lean','Psi = Psi^(B) (x) I_{W^d} on Vtx','covers'),
 ('PsiI','Gauss/BlockAnderson.lean','Psi on the fine lattice','covers'),
 ('PsiB_isHermitian','Gauss/BlockAnderson.lean','Hermitian','covers'),
 ('seqHflowBA','Gauss/BlockAnderson.lean','flow H_u = lam0 Psi + sqrt(u) V (MBM, S(0)=I)','covers'),
 ('seqHBA','Gauss/BlockAnderson.lean','H = V + lam Psi (eq:H_blocka)','covers'),
 ('Gt_BA','Gauss/BlockAnderson.lean','zztE_BA third clause, pointwise','covers'),
 ('Mres','Loop/GLoopFlow.lean','M = (H0 - z - m)^{-1} with M != mI (def_G0)','covers'),
 ('Gres','Loop/GLoopFlow.lean','G(sigma) = (H-z)^{-1}, G(-) = G(+)^*','covers'),
 ('ztOf','Loop/GLoopFlow.lean','z_t = E + (1-t) m with m data','covers'),
 ('etaOf','Loop/GLoopFlow.lean','eta_t = (1-t) Im m','covers'),
 ('loopM','Loop/GLoopFlow.lean','G-loops of any Hermitian matrix','covers'),
 ('norm_loopM_le','Loop/GLoopFlow.lean','envelope |L^(n)| <= eta^{-n} for any Hermitian H','covers'),
 ('PropThetaQ','Propagator/Pins.lean','Theta = (1 - t Q)^{-1} for a transition matrix Q = M^(s1,s2) S','shape'),
 ('Prop5DecayQ','Propagator/Pins.lean','property 5 for a model family Q','shape'),
 ('isUnit_sub_smul_of_isHermitian','Analysis/Resolvent.lean','H - z invertible off the real axis','covers'),
 ('norm_inverse_entry_le','Analysis/Resolvent.lean','|((H-z)^{-1})_{xy}| <= |Im z|^{-1}','covers'),
 ('IsKLoopS','Loop/KLTree.lean','K-loop equations with a kernel S and initial data M (kernel-generic)','covers'),
 ('treeEqRhsS','Loop/KLTree.lean','RHS of (pro_dyncalK) with kernel S','covers'),
 ('MLoopM','Loop/KLTree.lean','M-loop data with free label profile','shape'),
 ('KLtreeValW','Loop/KLTree.lean','tree value with generic leaf/edge weights (Gamma_M)','shape'),
 ('LWPins_dH','Graph/LWPins.lean','Wirtinger derivative of a resolvent polynomial','covers'),
 ('LWPins_resPoly','Graph/LWPins.lean','f(G) as a polynomial in resolvent entries','covers'),
 ('LData','Graph/LWVocab.lean','graph vocabulary with a general matrix M','shape'),
 ('Prec','Defs/StochDomAt.lean','stochastic domination at the scale N','covers'),
 ('Whp','Defs/StochDomAt.lean','w.h.p. at the scale N','covers'),
 ('Sizes','Defs/Sizes.lean','size data (L,W,lam sequences)','covers'),
 ('Bparam','Defs/Params.lean','B_{t,K} (g = model coupling)','covers'),
 ('ellT','Defs/Params.lean','ell_t','covers'),
 ('STMainInd','Induction/Defs.lean','lem:main_ind (band): BA = same pin at the BA carrier (probe: STMainIndG)','band'),
 ('STKbound','Induction/Defs.lean','ML:Kbound (band)','band'),
 ('STGbEXP','Induction/Defs.lean','lem_GbEXP (band; BA statement differs, 7_8:1916)','band'),
 ('prop5to8_holds','Propagator/Prop6Hold.lean','properties 5-8 for the band S^(B)(g) (not for K = |M|^2)','band'),
]
def find(name, f):
    p = os.path.join(R,'RBM3D',f)
    for i,l in enumerate(open(p,encoding='utf-8').read().split('\n'),1):
        if re.match(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*(?:theorem|lemma|def|abbrev|structure|class)\s+(?:\S+\.)?%s\b' % re.escape(name), l):
            return i
    return -1
print('%-34s %-30s %-6s %-9s %s' % ('merged declaration','file:line','class','', 'covers'))
miss=0
for n,f,u,c in rows:
    ln = find(n,f)
    if ln<0: miss+=1
    print('%-34s %-30s %-6s  %s' % (n, 'RBM3D/%s:%d'%(f,ln), c, u))
print('declarations not found:', miss, ' of', len(rows))
def git(*a, cwd=R): return subprocess.run(['git','--no-optional-locks',*a],cwd=cwd,capture_output=True,text=True).stdout.strip()
base = git('rev-parse','--short',git('merge-base','HEAD','main')); mainh = git('log','-1','--format=%h','main')
chg = [x for x in git('diff','--name-only',base,'main','--','RBM3D','RBM3D.lean').split('\n') if x]
print('files read from the worktree of t/T2161, base (merge-base with main) %s; main is now %s; .lean files changed on main since the base: %s' % (base, mainh, chg))
print('inventory declarations among them:', [c for c in chg if any(c.endswith(f) or ('RBM3D/'+f) == c for _,f,_,_ in rows)])
```
### inv_merged_summary.py
```python
# Summary of inv_merged_ba.out: merged RBM3D declarations that cover a piece of the BA chain, by class and by file.
import re, collections
cls = collections.Counter(); fl = collections.Counter(); n = 0
for ln in open('inv_merged_ba.out', encoding='utf-8'):
    m = re.match(r'^(\S+)\s+RBM3D/(\S+?):(\d+)\s+(covers|shape|band)\s', ln)
    if m: n += 1; cls[m.group(4)] += 1; fl[m.group(2)] += 1
print('%d merged declarations found: %s; by file: %s' % (n, ', '.join('%s %d' % kv for kv in cls.items()), ', '.join('%s %d' % (k.split('/')[-1][:-5], v) for k, v in fl.items())))
print('covers = used as is (Gt_BA, Mres/Gres, IsKLoopS, Prec, Sizes ...); shape = same shape with a kernel/M parameter; band = the band pin, BA statement differs (STMainInd, STKbound, STGbEXP, prop5to8_holds)')
```
### inv_rbm2d.py
```python
import subprocess, re
R='/Users/junyin/Lean_proof/RBM2D'
def show(commit, path):
    r = subprocess.run(['git','--no-optional-locks','show','%s:%s'%(commit,path)],cwd=R,capture_output=True,text=True)
    return r.stdout if r.returncode==0 else None
tok = re.compile(r'W \^ 2|L \^ 2|\(W \* L\) \^ 2|size \^ 2|W⁻²|L²|d = 2|Z_L\^2|5⁻¹')
rows = [
 ('Propagator/CombesThomasConjugation.lean','BA-D4','lem:propM(3): weight conjugation (SB -> gΨ-w)'),
 ('Propagator/CombesThomasDistanceWeight.lean','BA-D4','distance weight, edge ratio'),
 ('Propagator/CombesThomasExponentialWeight.lean','BA-D4','exponential weight e^{t dist}, ratio <= e^t-1'),
 ('Propagator/CombesThomasPerturbation.lean','BA-D4','Neumann perturbation of the weighted inverse'),
 ('Propagator/CombesThomasWeightedInverse.lean','BA-D4','weighted inverse bound'),
 ('Propagator/CombesThomasGapParameter.lean','BA-D4','gap parameter'),
 ('Propagator/CombesThomasKernelDecay.lean','BA-D4','kernel decay from the weighted bound'),
 ('Propagator/CombesThomasFixedGap.lean','BA-D4','fixed-gap geometric decay'),
 ('Universality/FreeConv.lean','BA-D2','(self_m): existence/uniqueness, Stieltjes of the free convolution'),
 ('Universality/FreeConvStability.lean','BA-D6 (partial)','continuity up to the real axis; stability near semicircle (BA: no)'),
 ('Universality/Step1Band.lean','UN-D1 (T2162)','Step 1 comparison with LSY; BA needs the rho_N-dilated form'),
 ('Main/DecolFromLocal.lean','MA-BA','delocalization from the local law'),
 ('Main/QUEFromQDiff.lean','MA-BA','QUE from quantum diffusion'),
 ('Main/RegionUnif.lean','MA-BA','net lemma, uniform in z'),
 ('Endpoints.lean','probe 11 (done)','endpoint pins decol/locSC/QUE/BUniv; IsOrthoEigenbasis :56-59 is ported (BAIsOrthoEigenbasis)'),
 ('Main/Endpoints.lean','MA-BA','assembly locSC_holds, decol_holds, QUE_holds, QDiff_holds from STOAll (the glue pins of probe 12.1)'),
 ('Main/BUnivHolds.lean','UN-D1 (T2162)','Thm 2.4 assembly (L32)'),
]
print('%-52s %-16s %6s %6s %5s  %s' % ('RBM2D file (c9a24cf)','BA ticket','lines','kept','d=2tok','use'))
tot=[0,0,0]
for p,t,u in rows:
    a = show('c9a24cf','RBM2D/'+p); b = show('0c1330a','RBM2D/'+p)
    n = a.count('\n') if a else -1; k = b.count('\n') if b else -1
    tk = len(tok.findall(a)) if a else -1
    print('%-52s %-16s %6d %6d %5d  %s' % ('RBM2D/'+p, t, n, k, tk, u))
    if n>0: tot[0]+=n; tot[1]+=max(k,0); tot[2]+=tk
print('%-52s %-16s %6d %6d %5d' % ('total','',*tot))
import collections
grp = collections.OrderedDict()
for p,t,u in rows:
    a = show('c9a24cf','RBM2D/'+p); b = show('0c1330a','RBM2D/'+p)
    key = 'CombesThomas* (BA-D4)' if 'CombesThomas' in p else ('FreeConv* (BA-D2, D6)' if 'FreeConv' in p else ('Main/{Decol,QUE,RegionUnif,Endpoints} (MA-BA)' if p.startswith('Main/') and 'BUniv' not in p else ('Step1Band + BUnivHolds (UN-D1/T2162)' if ('Step1Band' in p or 'BUniv' in p) else 'Endpoints.lean (probe 11, ported pins)')))
    g = grp.setdefault(key, [0,0,0,0]); g[0]+=1; g[1]+=a.count('\n'); g[2]+=(b.count('\n') if b else 0); g[3]+=len(tok.findall(a))
print('group totals (files, lines at c9a24cf, kept lines at 0c1330a (0 = deleted by RBM2D T2274), d=2 tokens):')
for k,v in grp.items(): print('  %-48s %d files %5d lines %5d kept %3d tokens' % (k,*v))
r = subprocess.run(['git','--no-optional-locks','grep','-il','anderson','c9a24cf','--','RBM2D'],cwd=R,capture_output=True,text=True)
print('files mentioning "anderson" at c9a24cf (git grep -il):', len([x for x in r.stdout.split('\n') if x.strip()]))
print('git -C ../RBM2D log -1 --format=%h c9a24cf:', subprocess.run(['git','--no-optional-locks','log','-1','--format=%h','c9a24cf'],cwd=R,capture_output=True,text=True).stdout.strip())
```
### decl_inv.py
```python
# Declaration-level inventory of the merged RBM3D files: which declarations have a *statement* that hard-wires the band model.
import os, re, sys, collections, json
root = '/Users/junyin/Lean_proof/RBM3D-wt/T2161/RBM3D'
tok = re.compile(r'\b(mE|msc|mSigma|SB|SBR|svarF|seqHflow|seqXmat|Lloop|Gt|Gsig|gloop|Hmat|Hflow|zt|lemE|lemT|KLK|KLloopOf|IsKLoop|STKloop|STGM|STKI|STLI|Theta|Theta0|sbKernelR|Gn|etaT|STmsig|PsiB)\b')
decl = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |unsafe )*(theorem|lemma|def|abbrev|instance|structure|class|inductive|example)\b')
rows = []
for dp, dn, fn in sorted(os.walk(root)):
    if '/Probe' in dp: continue
    for f in sorted(fn):
        if not f.endswith('.lean'): continue
        p = os.path.join(dp, f); rel = os.path.relpath(p, root)
        lines = open(p, encoding='utf-8').read().split('\n')
        starts = [i for i, l in enumerate(lines) if decl.match(l)]
        # a docstring/comment immediately above belongs to the decl: ignore (lines counted from the decl keyword)
        bounds = starts + [len(lines)]
        for a, b in zip(bounds, bounds[1:]):
            # trim trailing blank/comment/`end` lines
            e = b
            while e > a and (lines[e-1].strip() == '' or lines[e-1].startswith('/--') or lines[e-1].startswith('/-') or lines[e-1].startswith('--') or lines[e-1].startswith('end ') or lines[e-1].startswith('namespace') or lines[e-1].startswith('section') or lines[e-1].startswith('open ') or lines[e-1].startswith('variable') or lines[e-1].startswith('set_option') or lines[e-1].startswith('omit') or lines[e-1].startswith('/-! ')):
                e -= 1
            text = '\n'.join(lines[a:e])
            m = re.search(r':=|\bwhere\b|\n\s*\|', text)
            sig = text[:m.start()] if m else text
            kind = decl.match(lines[a]).group(1)
            hw = bool(tok.search(sig))
            hwb = bool(tok.search(text))
            rows.append((rel, kind, e - a, hw, hwb))
agg = collections.defaultdict(lambda: [0,0,0,0,0,0])  # decls, lines, sig-hw decls, sig-hw lines, body-only hw decls, body-only lines
for rel, kind, n, hw, hwb in rows:
    k = rel.split('/')[0]
    a = agg[k]; a[0]+=1; a[1]+=n
    if hw: a[2]+=1; a[3]+=n
    elif hwb: a[4]+=1; a[5]+=n
print('%-12s %6s %7s | %6s %7s (signature mentions a band token) | %6s %7s (only the proof does)' % ('gate-dir','decls','lines','decls','lines','decls','lines'))
T=[0]*6
for k, a in sorted(agg.items()):
    print('%-12s %6d %7d | %6d %7d | %6d %7d' % (k, *a))
    for i in range(6): T[i]+=a[i]
print('%-12s %6d %7d | %6d %7d | %6d %7d' % ('TOTAL', *T))
json.dump(rows, open('/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2161/decl_rows.json','w'))
```
### file_gate.py
```python
import subprocess, re, json, collections
S='/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2161/'
rows = json.load(open(S+'decl_rows.json'))
out = subprocess.run(['git','log','--diff-filter=A','--format=@@%h|%s','--name-only','--','RBM3D/*.lean'],capture_output=True,text=True,cwd='/Users/junyin/Lean_proof/RBM3D-wt/T2161').stdout
sub = {}; cur=None
for l in out.split('\n'):
    if l.startswith('@@'): cur=l[2:]
    elif l.strip().endswith('.lean') and cur and 'Probe' not in l:
        sub[l.strip()[len('RBM3D/'):]] = cur
def gate(rel, s):
    m = re.search(r'\b(S1-\d+|ST2-\d+\w*|S3-\d+\w*|S5-\d+\w*|LW-\d+\w*|KL\d+\w*|EK-\d+|PT-\w+|MD-\d|F0-\d)', s or '')
    tag = m.group(1) if m else ''
    if tag.startswith('S1-'): return 'ST-1'
    if tag.startswith('ST2-'): return 'ST-2'
    if tag.startswith('S3-'): return 'ST-3'
    if tag.startswith('S5-'): return 'ST-4'
    if tag.startswith('LW-'): return 'LW'
    if tag.startswith('KL'): return 'KL'
    if tag.startswith('EK'): return 'EK'
    if tag.startswith('PT'): return 'PT'
    if tag.startswith('MD'): return 'MD'
    d = rel.split('/')[0]
    return {'Propagator':'PT','Loop':'KL','Kernel':'EK','Evolution':'EK/ST-4','Graph':'LW','Green':'ST-1','Induction':'ST-?','Path':'ST-2?','Gauss':'MD','Defs':'MD/F0','Hierarchy':'ST-3?','Analysis':'F0','Basic.lean':'F0','Test':'F0'}.get(d, d)
agg = collections.defaultdict(lambda:[0,0,0,0,0])
files = collections.defaultdict(lambda:[0,0,0,0,'',''])
for rel, kind, n, hw, hwb in rows:
    g = gate(rel, sub.get(rel))
    a = agg[g]; a[0]+=n
    if hw: a[1]+=n
    elif hwb: a[2]+=n
    f = files[rel]; f[0]+=n
    if hw: f[1]+=n
    elif hwb: f[2]+=n
    f[4]=g; f[5]=(sub.get(rel) or '')[:70]
print('%-10s %7s %7s %7s' % ('gate','lines','sig-hw','body-hw'))
tot=[0,0,0]
for g,a in sorted(agg.items()):
    print('%-10s %7d %7d %7d' % (g,a[0],a[1],a[2]))
    for i in range(3): tot[i]+=a[i]
print('%-10s %7d %7d %7d' % ('TOTAL',*tot))
json.dump({k:v for k,v in files.items()}, open(S+'file_gate.json','w'))
```
### pin_subst2.py
```python
# Transitive version: a def is band-dependent if its text mentions a band object or a band-dependent def (fixpoint over all merged files).
import re, os, collections
R='/Users/junyin/Lean_proof/RBM3D-wt/T2161/RBM3D'
band0 = re.compile(r'\b(mE|SB|SBR|seqHflow|Lloop|zt|Gt|Gsig|Hflow|lemE|lemT|KLK|STKloop|STGM|STflowE|STLM|STLKM|STmsig|Theta|Theta0|Hmat)\b')
defs = {}   # name -> (file, text, isProp)
for dp, dn, fn in os.walk(R):
    if '/Probe' in dp: continue
    for f in fn:
        if not f.endswith('.lean'): continue
        p=os.path.join(dp,f); rel=os.path.relpath(p,R)
        txt=open(p,encoding='utf-8').read()
        idx=[m.start() for m in re.finditer(r'^(?:noncomputable )?def\s', txt, re.M)]
        idx.append(len(txt))
        for a,b in zip(idx,idx[1:]):
            blk=txt[a:b]
            nm=re.match(r'(?:noncomputable )?def\s+(\w+)', blk).group(1)
            head=blk.split(':=')[0].replace('\n',' ')
            isprop = bool(re.search(r':\s*Prop\b', head))
            defs[nm]=(rel, blk, isprop)
dep = {n for n,(f,t,p) in defs.items() if band0.search(t)}
names = set(defs)
changed=True
word = re.compile(r'\b\w+\b')
while changed:
    changed=False
    for n,(f,t,p) in defs.items():
        if n in dep: continue
        if any(w in dep for w in set(word.findall(t)) if w!=n and w in names):
            dep.add(n); changed=True
groups = collections.OrderedDict([
 ('Step 1 (Induction/Defs)', ['Induction/Defs.lean']),
 ('Step 2 (Step2*, NewKLK*, Contract*, Grid*, Azuma*)', ['Induction/Step2Defs.lean','Induction/Step2Core.lean','Induction/Step2Events.lean','Induction/Step2Iterate.lean','Induction/Step2K2.lean','Induction/Step2Scale.lean','Induction/NewKLK.lean','Induction/NewKLKL.lean','Induction/GridGoodN.lean','Induction/GridEnvelopeN.lean','Induction/GridAssemblyN.lean','Induction/GridDriftN.lean','Induction/GridDuhamelN.lean','Induction/AzumaProxyN.lean']),
 ('Steps 3-4 (Step34Pins, KDecay, DecayLoop*, SEforLn*, Q*, B45)', ['Induction/Step34Pins.lean','Induction/KDecay.lean','Induction/DecayLoopA.lean','Induction/DecayLoopB.lean','Induction/SEforLn1.lean','Induction/SEforLn2.lean','Induction/QGridA.lean','Induction/QGridB.lean','Induction/B45.lean','Induction/ZeroModeCalc.lean','Induction/IterationsA.lean','Induction/NewPQ.lean']),
 ('Step 5 (Step5*, TailtoTail, WardII, Evolution/Clt*, FarEntry, ExpInv)', ['Induction/Step5Pins.lean','Induction/Step5Cases.lean','Induction/Step5Kit.lean','Induction/Step5Kernel.lean','Induction/TailtoTail.lean','Induction/WardII.lean','Evolution/CltStep.lean','Evolution/CltGood.lean','Evolution/CltSwap.lean','Evolution/CltResolvent.lean','Evolution/CltPath.lean','Evolution/FarEntry.lean','Evolution/ExpInv.lean']),
 ('Green chain (Green/Pins, GbEXP)', ['Green/Pins.lean','Green/GbEXP.lean']),
 ('LW layer (Graph/LWPins)', ['Graph/LWPins.lean']),
 ('K-loop layer (Loop/KBound, KLFinal, KLTree)', ['Loop/KBound.lean','Loop/KLFinal.lean','Loop/KLTree.lean']),
 ('EK layer (Evolution/Pins, XiPins, SumDecay*, Nonzero, Prec)', ['Evolution/Pins.lean','Evolution/XiPins.lean','Evolution/SumDecay.lean','Evolution/SumDecayZero.lean','Evolution/Nonzero.lean','Evolution/Prec.lean']),
])
print('transitive closure over all %d merged defs: %d band-dependent' % (len(defs), len(dep)))
print('%-72s %5s %9s  %s' % ('group', 'pins', 'band-dep.', 'pins independent of the band objects (even transitively)'))
tot=[0,0]
for g, files in groups.items():
    pins=[n for n,(f,t,p) in defs.items() if p and f in files]
    bd=[n for n in pins if n in dep]; ind=[n for n in pins if n not in dep]
    tot[0]+=len(pins); tot[1]+=len(bd)
    print('%-72s %5d %9d  %s' % (g, len(pins), len(bd), ' '.join(ind[:12])+(' ...' if len(ind)>12 else '')))
print('%-72s %5d %9d' % ('total', *tot))
```
### pin_index.py
```python
# Index of the Prop-valued definitions of the probe (pins, structural predicates): line, kind, registry class from the docstring.
import re
P = '/Users/junyin/Lean_proof/RBM3D-wt/T2161/RBM3D/Probe/T2161Pins.lean'
src = open(P, encoding='utf-8').read().split('\n')
text = '\n'.join(src)
# docstring blocks: '/--' ... '-/' immediately preceding a declaration
rows = []
i = 0
while i < len(src):
    ln = src[i]
    m = re.match(r'^(?:noncomputable )?(def|structure)\s+(\S+)', ln)
    if m:
        # find the end of the signature header (up to ':= ' or 'where' on same/next lines) to decide if Prop
        hdr = ' '.join(src[i:i+14])
        hdr = re.split(r':=|\bwhere\b', hdr)[0]
        isprop = bool(re.search(r':\s*Prop\s*$', hdr.strip())) or m.group(1) == 'structure' and ': Prop' in hdr
        # docstring above
        j = i - 1
        while j >= 0 and src[j].strip() == '': j -= 1
        doc = ''
        if src[j].rstrip().endswith('-/'):
            k = j
            while k >= 0 and '/--' not in src[k] and '/-!' not in src[k]: k -= 1
            doc = ' '.join(src[k:j+1])
        reg = re.search(r'Registry class:?\s*([a-z]+)(?:\s*\(([^)]*)\))?', doc)
        proved = 'Proved' in doc or 'proved' in doc[:200] and 'Iff.rfl' in doc
        if isprop:
            rows.append((m.group(2), i+1, m.group(1), reg.group(1) if reg else '-', (reg.group(2) or '') if reg else '', 'Iff.rfl' in doc))
    i += 1
print('%-22s %-5s %-9s %-11s %s' % ('Prop-valued def', 'line', 'kind', 'registry', 'ticket/route'))
for r in rows:
    print('%-22s %-5d %-9s %-11s %s' % (r[0], r[1], r[2], r[3], r[4][:70]))
import collections
c = collections.Counter(r[3] for r in rows)
print('Prop-valued defs/structures:', len(rows), dict(c))
```
### registry.py
```python
# Registry class (DECISIONS 16, 20) of every Prop-valued definition of the probe: structural (a condition on data, taken as a hypothesis
# by deterministic lemmas), owed (a conclusion the paper proves and no RBM3D theorem proves yet), borrowed (external literature; only LSY, 5),
# shape (the conclusion of a pin or of a carrier form: not a hypothesis by itself), carrier (the merged band pin restated over FlowFM; class of the band pin).
import re, subprocess, collections
rows = [l for l in subprocess.run(['python3', 'pin_index.py'], capture_output=True, text=True).stdout.split('\n') if re.match(r'^\S+\s+\d+\s+(def|structure)\s', l)]
names = [l.split()[0] for l in rows]
STRUCT = ['BASelf', 'BAedgeBulk', 'BAdistBulk', 'BAbulk', 'BAReal', 'BAdom', 'BAFlow', 'BAGbEXPpre', 'BAendDom', 'BAIsOrthoEigenbasis', 'BAqueWindow', 'BAqueBad', 'BAque2Bad']
SHAPE = ['BAGbEXPconcl', 'BAConArgLoop', 'BAConArgVec', 'BAlocSCConcl', 'BAqdConcl', 'BAdecolConcl', 'BAqueConcl', 'BAunivConcl', 'Thm27At']
CARRIER = ['STLKg', 'STLmaxg', 'STDecayg', 'STDecayStrongg', 'STLocalMaxg', 'STLocalEntryg', 'STExp2g', 'STInitialGT2g', 'STKboundg', 'STStep1Loopg', 'STStep1Weakg',
           'STLWassmExpg', 'STStep2Localg', 'STStep2Avgg', 'STStep2Decayg', 'STMainIndG']
OWED = ['BAmExists', 'BAmUniqReal', 'BAmBoundary', 'BAWard', 'BAPropM', 'BAoffDiag', 'BAImmLower', 'BAProp5', 'BAProp5s', 'BAProp6', 'BAProp7', 'BAProp8', 'BAProp5to8',
        'BAMainInd', 'BAGbEXP', 'BAConArg', 'BAStep1', 'BAStep2', 'BAEMn2Exp', 'BAKsolve', 'BAKbound', 'BAlanlw', 'BAlweight', 'BAGGGamma',
        'BAEnd_locSC', 'BAEnd_QDiff', 'BAEnd_decol', 'BAEnd_QUE', 'BAEnd_BUniv', 'BAThm27', 'BAGlueChain', 'BAGlueLoc', 'BAGlueQDiff', 'BAGlueDecol', 'BAGlueQUE', 'BAGlueUniv']
BORROWED = []
cls = {}
for k, lst in (('structural', STRUCT), ('shape', SHAPE), ('carrier', CARRIER), ('owed', OWED), ('borrowed', BORROWED)):
    for n in lst: cls[n] = k
unc = [n for n in names if n not in cls]
gone = [n for n in cls if n not in names]
print('Prop-valued definitions of the probe: %d; classified: %d; unclassified: %s; classified but absent: %s' % (len(names), len(names) - len(unc), unc, gone))
for k in ('owed', 'structural', 'shape', 'carrier', 'borrowed'):
    v = [n for n in names if cls.get(n) == k]
    print('%-10s %2d: %s' % (k, len(v), ' '.join(v) if v else '-'))
print('borrowed = 0: the only external input of the BA chain is LSY Thm 2.2 (DECISIONS 5), used inside the proof of the owed pin BAEnd_BUniv; no pin states it.')
```
### pin_map.py
```python
# Pin -> paper map (hand-written rows, checked by script: the probe line of the pin and the first 70 characters of the first paper line cited).
import re
P = '/Users/junyin/Lean_proof/RBM3D-wt/T2161/RBM3D/Probe/T2161Pins.lean'
T = '/Users/junyin/Lean_proof/RBM3D/paper/tex/'
F = {'1_2': '1_2_Intro_model_result', '3_5': '3_5_Loop_Hierarchy', '7_8': '7_8_light_weight', 'A': 'A_deterministic_estimates', 'B': 'B_graphical_lemmas'}
src = open(P, encoding='utf-8').read().split('\n')
ROWS = [
 ('BAmExists', '1_2:626', '(self_m): unique m in C_+ for every L>=3, g>0, Im z>0 [Biane]; constants none'),
 ('BAmUniqReal', '1_2:626', 'uniqueness at real E (Schwarz-Pick); makes rho_N the Im of the real-axis solution'),
 ('BAmBoundary', '1_2:715', 'm(E,g) = m(E+i0,g); Im m(E+i eta) -> 0 in a gap'),
 ('BAWard', '7_8:1869', 'Ward sum_b |M_ab|^2 = Im m/(Im m+Im z); translation invariance 7_8:1859; M_aa = m'),
 ('BAPropM', '7_8:1846', 'lem:propM (1)-(3) in the rho-bulk; constants (d,Lambda,kappa) before L,g,E,m'),
 ('BAoffDiag', 'A:32', '(eq:off_diagM): |1-t m^2| >= eps, ||M\'||_{inf->inf} <= (1-eps)|1-t m^2|, t in [0,1]'),
 ('BAImmLower', '7_8:1908', 'Im m >~ 1 [LSY15 L3.5], now a bridge from the rho-bulk: Im m(E+i eta) >= c, eta in (0,1]'),
 ('BAProp5', '1_2:1119', 'lem_propTH 5 for Theta^(+,-): exponential decay, B_{t,|a|}'),
 ('BAProp5s', '1_2:1119', 'lem_propTH 5s for (sigma,sigma): 1_{a=0} + g^2 e^{-|a|/2}'),
 ('BAProp6', '1_2:1119', 'lem_propTH 6: unit first differences'),
 ('BAProp7', '1_2:1119', 'lem_propTH 7: unit second differences'),
 ('BAProp8', '1_2:1119', 'lem_propTH 8: zero mode'),
 ('BAProp5to8', '1_2:1119', 'bundle of 5-8 (constants (d,Lambda,kappa))'),
 ('BAMainInd', '7_8:1825', 'lem:main_ind_BA: kappa,eps,d first, then c_d <= 10^-2, then the sequence; flow of zztE_BA'),
 ('BAGbEXP', '7_8:1916', 'lem_GbEXP_BA: (GiiGEX_BA), (GijGEX_BA), (GavLGEX_BA) [RBSO1D L6.1]'),
 ('BAConArg', '7_8:1956', 'lem_ConArg_BA parts 1, 2 [RBSO1D L7.1]; g_s = g sqrt(s/t)'),
 ('BAStep1', '7_8:1990', 'Step 1 for BA (lRB1), (Gtmwc)'),
 ('BAStep2', '7_8:1993', 'Step 2 for BA: (Gt_bound_flow), (Gt_avgbound_flow), (Eq:Gdecay_w)'),
 ('BAEMn2Exp', '7_8:1999', '(eq:MG_conclusion3_BA) with a deterministic J >= W^-d'),
 ('BAKsolve', '1_2:1175', '(Kn2sol), (Kn3sol); IsKLoopS with M-loops'),
 ('BAKbound', '1_2:1056', 'ML:Kbound for BA (proof A:600-740)'),
 ('BAlanlw', 'B:359', 'lanlw [yang2024Del B.9]'),
 ('BAlweight', 'B:376', 'lem_lweight [B.10]'),
 ('BAGGGamma', 'B:393', 'GG expansion [B.11] with the corrected coefficient (T2161a)'),
 ('BAEnd_decol', '1_2:651', 'MR:decol_BA bullet 1: (eq:psikLinfty) 1_2:366, energies in the rho-bulk'),
 ('BAEnd_locSC', '1_2:653', 'bullet 2: (G_bound), (G_bound_ave) 1_2:388-393 on D^BA'),
 ('BAEnd_QUE', '1_2:655', 'bullet 3: (Meq:QUE), (Meq:QUE2) with E in the rho-bulk'),
 ('BAEnd_BUniv', '1_2:454', 'bullet 3: (eq:universality), density-normalised (DECISIONS 11)'),
 ('BAEnd_QDiff', '1_2:657', 'bullet 4: (eq:diffu1)-(Meq:QdS2) with (Theta M), def:Theta_BA 1_2:658'),
 ('BAThm27', '1_2:644', 'MR:decol_BA: the five endpoints'),
 ('BAGlueChain', '7_8:1832', 'chain induction in t (BA-V2): BAMainInd from the Step 1-2 pins, BAKbound, the graph expansions; Steps 3-6 verbatim (7_8:2100-2105)'),
 ('BAGlueLoc', '7_8:1835', 'proof of MR:decol_BA: BAMainInd + zztE_BA + (eq:BtBt) + (Kn2sol) + net lemma'),
 ('BAGlueQDiff', '7_8:1835', 'same, quantum diffusion'),
 ('BAGlueDecol', '1_2:397', 'delocalization from (G_bound) via (eq:ukx)'),
 ('BAGlueQUE', '1_2:520', 'QUE from (Meq:QdS1),(Meq:QdS2) as in [YY_25 Thm 2.5], [DYYY25 Thm 2.4]'),
 ('BAGlueUniv', '1_2:454', 'universality from the local law, [DYYY25] and LSY Thm 2.2'),
]
print('%-13s %-5s %-9s %-72s %s' % ('pin', 'line', 'paper', 'paper line starts with', 'what the pin states / scale'))
for n, ref, note in ROWS:
    i = next((k for k, l in enumerate(src) if re.match(r'^(?:noncomputable )?(def|structure)\s+%s\b' % re.escape(n), l)), None)
    f, ln = ref.split(':'); L = open(T + F[f] + '.tex', encoding='utf-8').read().split('\n')
    txt = re.sub(r'\s+', ' ', L[int(ln) - 1]).strip()[:70]
    print('%-13s %-5s %-9s %-72s %s' % (n, i + 1 if i is not None else 'MISSING', ref, txt, note))
```
### statements.py
```python
# Extract the statement text (declaration without docstring) of the named declarations from the probe, with file:line.
import re, sys
P = '/Users/junyin/Lean_proof/RBM3D-wt/T2161/RBM3D/Probe/T2161Pins.lean'
src = open(P, encoding='utf-8').read().split('\n')
def extract(name, with_body=True):
    pat = re.compile(r'^(?:noncomputable )?(def|theorem|structure|abbrev)\s+' + re.escape(name) + r'(?=[\s:({\[])')
    for i, ln in enumerate(src):
        if pat.match(ln):
            j = i + 1
            while j < len(src) and not (src[j].strip() == '' and (j + 1 >= len(src) or not src[j+1].startswith(' '))):
                j += 1
            blk = src[i:j]
            if not with_body:   # signature only: up to the line containing ':='
                for k, b in enumerate(blk):
                    if ':=' in b or b.rstrip().endswith(' where'):
                        blk = blk[:k+1]; break
            return i + 1, blk
    return None, []
if __name__ == '__main__':
    names = sys.argv[1:]
    for n in names:
        sig = n.endswith('~')
        n = n.rstrip('~')
        ln, blk = extract(n, with_body=not sig)
        print('-- RBM3D/Probe/T2161Pins.lean:%s' % ln)
        print('\n'.join(blk))
```
### instances_index.py
```python
# Compiled instances of the probe (section 13): theorem names with line numbers per subsection, the pins each takes as hypotheses.
import re
P = '/Users/junyin/Lean_proof/RBM3D-wt/T2161/RBM3D/Probe/T2161Pins.lean'
src = open(P, encoding='utf-8').read().split('\n')
sec = None; rows = {}
start = next(i for i, l in enumerate(src) if l.startswith('/-! ## 13.'))
end = next(i for i, l in enumerate(src) if l.startswith('/-! ## 14.'))
for i in range(start, end):
    m = re.match(r'^/-! ### (13\.\d+)', src[i])
    if m: sec = m.group(1)
    if src[i].startswith('/-! ## 13.'): sec = '13.0'
    m = re.match(r'^(?:noncomputable )?(theorem|def|structure|abbrev)\s+(\S+)', src[i])
    if m and sec:
        hdr = ' '.join(src[i:i+8]).split(':=')[0]
        pins = sorted(set(re.findall(r'\(\w+ : (BA(?:m|Prop|Ward|off|Imm|Main|Gb|Con|Step|EM|Ksolve|Kbound|lan|lw|GG|End|Thm|Glue)\w*|Thm27At)\b', hdr)))
        rows.setdefault(sec, []).append((m.group(2), i + 1, m.group(1), pins))
tot = 0
for s in sorted(rows, key=lambda x: [int(t) for t in x.split('.')]):
    th = [r for r in rows[s] if r[2] == 'theorem']
    tot += len(th)
    print('%-5s %2d theorems: %s' % (s, len(th), ' '.join('%s:%d' % (r[0], r[1]) for r in th)))
    pins = sorted(set(p for r in th for p in r[3]))
    if pins: print('      pins taken as hypotheses: %s' % ' '.join(pins))
print('theorems in section 13:', tot)
```
### name_clash.py
```python
# New public declarations of RBM3D/Probe/T2161Pins.lean (namespaces RBM.BA, RBM.BA.Inst) against every other Lean file of RBM3D (worktree)
# and against RBM2D/RBM1D at the pinned commits (read-only `git grep`).
import re, subprocess, os, collections
W = '/Users/junyin/Lean_proof/RBM3D-wt/T2161'
P = W + '/RBM3D/Probe/T2161Pins.lean'
src = open(P, encoding='utf-8').read().split('\n')
decl = re.compile(r'^(?:@\[[^\]]*\]\s*)?(private |protected |noncomputable )*(theorem|lemma|def|abbrev|structure|instance|inductive)\s+([^\s:({\[]+)')
ns = []; names = []
for ln in src:
    m = re.match(r'^namespace\s+(\S+)', ln)
    if m: ns.append(m.group(1))
    m = re.match(r'^end\s+(\S+)', ln)
    if m and ns and ns[-1] == m.group(1): ns.pop()
    d = decl.match(ln)
    if d:
        full = ('RBM.BA.' if not ns else '') + d.group(3) if False else d.group(3)
        names.append((ns[:] , d.group(3), 'private' if d.group(1) and 'private' in d.group(1) else 'public'))
pub = [(n, nm) for n, nm, v in names if v == 'public']
print('declarations in the probe: %d (public %d, private %d); namespaces used: %s' % (len(names), len(pub), len(names)-len(pub), sorted(set('.'.join(n) for n, _ in pub))))
# collect all other RBM3D declarations: bare names and the namespace they are in
others = collections.defaultdict(list)
for dp, dn, fn in os.walk(W + '/RBM3D'):
    for f in fn:
        p = os.path.join(dp, f)
        if not f.endswith('.lean') or p == P: continue
        ns2 = []
        for ln in open(p, encoding='utf-8').read().split('\n'):
            m = re.match(r'^namespace\s+(\S+)', ln)
            if m: ns2.append(m.group(1))
            m = re.match(r'^end\s+(\S+)', ln)
            if m and ns2 and ns2[-1] == m.group(1): ns2.pop()
            d = decl.match(ln)
            if d and not (d.group(1) and 'private' in d.group(1)):
                others[d.group(3)].append(('.'.join(ns2), os.path.relpath(p, W)))
clash_full = []; clash_bare = []
for n, nm in pub:
    full = '.'.join(n) + '.' + nm if n else nm
    for (ns2, rel) in others.get(nm, []):
        full2 = (ns2 + '.' + nm) if ns2 else nm
        if full2 == full: clash_full.append((full, rel))
        else: clash_bare.append((full, full2, rel))
print('exact full-name clashes with other RBM3D files (worktree, base 275e275):', len(clash_full), clash_full[:5])
print('same bare name under another namespace (not a clash):', len(clash_bare), clash_bare[:6])
# RBM2D at c9a24cf: same bare names of the public BA* names
def gg(repo, commit, pat):
    r = subprocess.run(['git', '--no-optional-locks', 'grep', '-lE', pat, commit, '--', '*.lean'], cwd=repo, capture_output=True, text=True)
    return [x for x in r.stdout.split('\n') if x]
bare = sorted(set(nm for n, nm in pub if nm.startswith('BA') or nm.startswith('inst_BA')))
pat = r'^(private |protected |noncomputable )*(theorem|lemma|def|abbrev|structure)\s+(' + '|'.join(re.escape(b) for b in bare) + r')\b'
print('public BA*/inst_BA* names in the probe:', len(bare))
for repo, commit in (('/Users/junyin/Lean_proof/RBM2D', 'c9a24cf'), ('/Users/junyin/Lean_proof/RBM1D', 'HEAD')):
    print('%s @%s: files declaring one of them: %s' % (os.path.basename(repo), commit, gg(repo, commit, pat)[:3]))
# the main worktree (current main) too
r = subprocess.run(['grep', '-rlE', pat.replace('^', '^'), '/Users/junyin/Lean_proof/RBM3D/RBM3D', '--include=*.lean'], capture_output=True, text=True)
print('main worktree (RBM3D/RBM3D, current files): files declaring one of them:', [x for x in r.stdout.split('\n') if x][:3])
```
### names_check.py
```python
# Mathlib names used by the probe: present (declaration found in Mathlib sources, #uses in the probe) / names verified absent.
import re, subprocess
M = '/Users/junyin/Lean_proof/RBM3D/.lake/packages/mathlib/Mathlib'
P = '/Users/junyin/Lean_proof/RBM3D-wt/T2161/RBM3D/Probe/T2161Pins.lean'
probe = open(P, encoding='utf-8').read()
present = ['Real.sqrt_le_one', 'Real.rpow_le_rpow_of_nonpos', 'Matrix.nonsing_inv_eq_ringInverse', 'Matrix.inv_smul', 'Matrix.trace_smul',
           'Finset.sum_mul_sq_le_sq_mul_sq', 'EuclideanSpace.inner_single_right', 'EuclideanSpace.norm_sq_eq', 'Matrix.toEuclideanLin',
           'ContDiffBump.contDiff', 'ContDiffBump.hasCompactSupport', 'ContDiffBump.one_of_mem_closedBall', 'HasCompactSupport.comp_homeomorph',
           'EuclideanSpace.equiv', 'Real.sq_sqrt', 'Real.sqrt_pos', 'Complex.norm_real', 'Finset.sum_ite_eq', 'ite_eq_left_iff']
absent = ['Finset.inner_mul_le_norm_mul_norm', 'Real.sqrt_lt_one', 'Real.rpow_le_rpow_of_exponent_nonpos', 'Nat.pos_pow_of_pos',
          'Real.sqrt_le_one_iff_le_one_of_nonneg']
def decl_found(name):
    short = name.split('.')[-1]
    pat = r'(theorem|lemma|def|abbrev|structure|instance|alias|irreducible_def)\s+(?:[A-Za-z_.]*\.)?' + re.escape(short) + r'\b'
    r = subprocess.run(['grep', '-rEl', '--include=*.lean', pat, M], capture_output=True, text=True)
    files = [x.replace(M + '/', '') for x in r.stdout.split('\n') if x]
    return files
print('%-42s %-8s %-6s %s' % ('name', 'status', '#uses', 'file (first)'))
for n in present:
    short = n.split('.')[-1]
    uses = len(re.findall(r'\b' + re.escape(short) + r'\b', probe))
    f = decl_found(n)
    print('%-42s %-8s %-6d %s' % (n, 'present' if f else 'MISSING', uses, f[0] if f else ''))
for n in absent:
    short = n.split('.')[-1]
    f = decl_found(n)
    print('%-42s %-8s %-6s %s' % (n, 'ABSENT' if not f else 'FOUND?', '-', f[0] if f else ''))
```
### names_check.lean
```lean
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option format.width 1000
#check @Real.sqrt_le_one
#check @Real.rpow_le_rpow_of_nonpos
#check @Matrix.nonsing_inv_eq_ringInverse
#check @Matrix.inv_smul
#check @Matrix.trace_smul
#check @Finset.sum_mul_sq_le_sq_mul_sq
#check @EuclideanSpace.inner_single_right
#check @EuclideanSpace.norm_sq_eq
#check @Matrix.toEuclideanLin
#check @ContDiffBump.contDiff
#check @ContDiffBump.hasCompactSupport
#check @ContDiffBump.one_of_mem_closedBall
#check @HasCompactSupport.comp_homeomorph
#check @EuclideanSpace.equiv
#check_failure @Finset.inner_mul_le_norm_mul_norm
#check_failure @Real.sqrt_lt_one
#check_failure @Real.rpow_le_rpow_of_exponent_nonpos
#check_failure @Nat.pos_pow_of_pos
#check_failure @Real.sqrt_le_one_iff_le_one_of_nonneg
```
### oneline.py
```python
# Condense `#check`/`#check_failure` messages (names_check.out) to one line per name: `name : type` (type truncated), unknown constants as ABSENT.
import re, sys
txt = open(sys.argv[1], encoding='utf-8').read().split('\n')
msgs = []
for ln in txt:
    if re.match(r'^(@?[A-Za-z_.κ₀]+ :|Unknown constant)', ln): msgs.append(ln)
    elif msgs and ln.startswith(' '): msgs[-1] += ' ' + ln.strip()
for m in msgs:
    m = re.sub(r'\s+', ' ', m)
    if m.startswith('Unknown constant'):
        print('ABSENT  ' + m.split('`')[1])
    else:
        name, ty = m.split(' : ', 1)
        ty = re.sub(r'\{[^}]*\}|\[[^\]]*\]', '', ty)           # drop implicit/instance binders
        ty = re.sub(r'\s+', ' ', ty).strip()
        print('present %-34s : %s' % (name.lstrip('@'), ty[:120]))
```
### ba_split2.py
```python
# Split table of gate BA (design T2161) and the count against DECISIONS 9 O2 (25/40/50).
# Sizes: (lo, central, hi) lines.  Rules: (A) adaptation of merged band-hardwired declarations = script `decl_inv.py`/`file_gate.py` lines
# (signature-hardwired + 1/2 proof-only) x alpha (lo 0.5, central 0.7, hi 1.0); (N) new items from the paper span (TeX kchar x 151 lines/kchar x omitted-step
# multiplier, the T2040 rule) or from a named RBM2D/merged source with kept lines; BA-L1..L4 are the rows of T2040-prove.md:182 (reused, not re-split).
import json, collections
Z = lambda a, b, c: (a, b, c)
items = [
 # id, group, title, sources, deps, role, (lo, central, hi)
 ('BA-D1','D','Defs + proved base: BASelf/BAm/BAMB/bulk forms/BAReal/BAMss/BATheta/FlowFM carrier, subordination lemma, zztE_BA data, averaged Ward; pins as Props; Axioms.lean','probe sections 0-3,5-7 (T2161Pins); 1_2:626-633, 7_8:1796-1801','T2013 merged','prover',Z(1000,1300,1600)),
 ('BA-D2','D','(self_m): existence/uniqueness of m(z,g) in C+, spectral bridge tr(Mres)=sum 1/(lam_i-w) (BAmExists, BAmUniqReal)','RBM2D Universality/FreeConv.lean 719 (0 d=2 tokens); 1_2:624-629 [Biane]','BA-D1','prover-hard',Z(700,900,1200)),
 ('BA-D3','D','Ward row by row, translation invariance, M_aa=m, |m|<=1, M symmetric (BAWard); (eq:off_diagM): eps(kappa,Lambda) with |1-tm^2|^2=(1-t|m|^2)^2+4t(Im m)^2 (BAoffDiag)','probe BAward_avg + circulant structure; 7_8:1859-1869; A:32-34 (probe b.4: identity checked to 4e-16)','BA-D1, D2','prover',Z(650,950,1400)),
 ('BA-D4','D','lem:propM (3): (Mbound_AO) by Taylor, (Mbound_AO2) by weighted resolvent (BAPropM)','RBM2D Propagator/CombesThomas*.lean 669 (8 files, 0 tokens), retargeted at (g Psi - w)^-1; 7_8:1891-1912 [Aizenman Thm 10.5]','BA-D1, D3','prover-hard',Z(700,1000,1400)),
 ('BA-D6','D','boundary values m(E+i0), rho_N continuity in E, bulk-set openness (BAmBoundary)','1_2:624, 715 [Biane]; RBM2D FreeConvStability.lean 835 (partial: limit eta->0)','BA-D2','prover-hard',Z(800,1200,1800)),
 ('BA-D7','D','Im m(z,g) >= c(kappa) in the rho-bulk, eta<=1 ([LSY15 L3.5] internal; BAImmLower)','7_8:1908; uniform Holder-1/3 of rho_N + Poisson smoothing (route, no source)','BA-D2, D6','prover-max',Z(800,1300,2200)),
 ('BA-P1','P','property 5s for (sigma,sigma): Taylor + BAoffDiag + CT decay (BAProp5s)','A:34-48; merged Propagator/Prop5Short.lean 506','BA-D3, D4','prover-hard',Z(500,700,1000)),
 ('BA-P2','P','kernel K=M^(+,-): symmetric, doubly stochastic, exponential tails, neighbour lower bound, laziness |m|^2','A:58-67; 7_8:1869-1912','BA-D3, D4','prover',Z(500,700,1000)),
 ('BA-P3','P','Fourier symbol of K: gap 1-Khat >= c (g^1)^2 |theta|^2, analytic strip (Esscher tilt)','route of T2003 b9 (symbol of M^(+,-)); no source','BA-P2','prover-hard',Z(700,900,1300)),
 ('BA-P4','P','Gaussian/exponential bound for K^n(0,a) on Z_L^d (Chernoff/Esscher + on-diagonal bound)','A:58-67 (Bernstein + local CLT [Lawler S2]); merged HeatProduct.lean 1257 as model','BA-P3','prover-max',Z(1000,1400,2000)),
 ('BA-P5','P','assemble property 5 (BAProp5): Laplace-Gauss integrals + zero-mode gap n>=L^2','merged Propagator/LaplaceGauss.lean 895 (Theta-free), Prop5Hold.lean 1399 as model','BA-P4','prover-hard',Z(700,1000,1400)),
 ('BA-P6','P','unit first/second differences of K^n(0,.) (BAProp6/7 unit forms)','A:50-56 (summation by parts); merged PropUnit.lean 1008 as model','BA-P4, P5','prover-max',Z(1000,1400,2000)),
 ('BA-P7','P','property 8, zero mode (BAProp8)','merged Prop5Hold.lean (zero-mode part) as model','BA-P5','prover-hard',Z(500,700,1000)),
 ('BA-P8','P','path lemma (|r|<=c|a|) -> BAProp6/7; bundle BAProp5to8; charge bookkeeping','merged Propagator/Prop6Hold.lean 560 (private path lemma: copied)','BA-P6, P7','prover',Z(600,800,1100)),
 ('BA-K1','K','BAKsolve: K-loop existence/uniqueness for S=I and BA initial data; (Kn2sol), (Kn3sol)','merged IsKLoopS (KLTree.lean:828), KL4 uniqueness; 1_2:1175','BA-D1, P8','prover-hard',Z(700,900,1200)),
 ('BA-K2','K','m-loop-tsp, Gamma_M values, tree representation tree-representation_BA (ODE proof d/dt Theta = Theta M Theta)','A:380-594 [RBSO1D L4.16]; merged KLtreeValW (KLTree.lean:114)','BA-K1','prover-max',Z(1200,1600,2200)),
 ('BA-K3','K','pure loops BA, molecule decay, sum-zero (eq:Sigma-empty-sum-zero)','A:643-654, 690, 728-734 [RBSO1D L4.29, Claim 4.30]','BA-K2','prover-hard',Z(900,1200,1700)),
 ('BA-K4','K','BAKbound: ML:Kbound induction with M-loops','1_2:1056; merged KLindStep/KLKpiBound (T2100, T2106, T2115) as model','BA-K3, P8','prover-max',Z(1200,1600,2200)),
 ('BA-K5','K','Ward identities for K (BA): lem_WI_K, lem_wardineq_K','merged KLWard.lean, KLWardIneq.lean as model','BA-K1','prover',Z(600,800,1100)),
 ('BA-E1','E','EK pins over the BA kernel family Q; Xi bounds with Prop5DecayQ + Mbound_AO','T2016 b10 (EKuKerQ); merged Evolution/XiPins.lean','BA-P8','prover-hard',Z(700,1000,1400)),
 ('BA-E2','E','sum_res_1, sum_res_2_NAL, sum_res_2 (sum-zero), sum_decay_nonzero for BA','A:88-220; merged Evolution/SumDecay*.lean, Nonzero.lean','BA-E1, K3','prover-hard',Z(1000,1500,2100)),
 ('BA-E3','E','EK conclusions -> Prec at scale N (EK-6 analog)','merged Evolution/Prec.lean','BA-E2','prover',Z(500,700,1000)),
 ('BA-G1','G','BA resolvent/Schur structure with the deterministic hopping; (eq_resolventunderpoly) inputs','7_8:1916-1950 [RBSO1D L6.1: text not in repo]','BA-D4, D7','prover-max',Z(1000,1400,2000)),
 ('BA-G2','G','large-deviation estimates for the BA minors (twin of Green/LDE*, EntryCore)','merged Green/LDE*.lean, EntryCore.lean (sig-hw 6.5k of 24.1k lines)','BA-G1','prover-hard',Z(1000,1400,2000)),
 ('BA-G3','G','(GiiGEX_BA): ||G-M||_max << Psi_t','7_8:1931; merged Green/GbEXP.lean as model','BA-G2','prover-hard',Z(1000,1400,2000)),
 ('BA-G4','G','(GijGEX_BA): entrywise decay with Phi_t and c_g','7_8:1942','BA-G3','prover-hard',Z(1000,1400,2000)),
 ('BA-G5','G','(GavLGEX_BA): averaged law, fluctuation averaging iteration','7_8:1931; merged Green/Fluc*.lean as model','BA-G3','prover-hard',Z(1000,1400,2000)),
 ('BA-G6','G','assembly BAGbEXP','7_8:1916-1946','BA-G4, G5','prover',Z(600,800,1100)),
 ('BA-S1','S','BAConArg: lem_ConArg_BA parts 1 and 2 (g_s = g sqrt(s/t))','7_8:1956-1987 [RBSO1D L7.1]; merged S1-32 STConArg','BA-G6, K4','prover-hard',Z(800,1100,1500)),
 ('BA-S2','S','Step 1 BA: bootstrap, net lift, forbidden region','7_8:1987-1990 [RBSO1D S7.1]; merged Induction/Step1*.lean, Continuity*.lean','BA-S1','prover-hard',Z(800,1100,1600)),
 ('BA-S3','S','Step 1 BA assembly BAStep1','merged S1-35, S1-36','BA-S2','prover',Z(700,1000,1500)),
 ('BA-T1','T','(eq:MG_conclusion3_BA) with deterministic J: Gronwall iteration + stopping time T','7_8:1999-2026; merged Induction/Step2Iterate.lean as model','BA-S3, K4','prover-max',Z(1100,1500,2100)),
 ('BA-T2','T','lem: EMn2_N for BA: (eq_resolventunderpoly/exp), (eq_S1_bound_BA); BAEMn2Exp','7_8:2033-2092; merged EMn2Poly/Exp1/Exp2.lean','BA-T1, G6','prover-max',Z(1200,1700,2400)),
 ('BA-T3','T','lem:newKLK for BA (uses Mbound_AO)','7_8:2030 ("minor modification"); merged NewKLK.lean, NewKLKL.lean','BA-D4, E3','prover-hard',Z(900,1200,1700)),
 ('BA-T4','T','Step 2 path layer twins: grid Duhamel, Azuma proxy, grid good/envelope/assembly (S-hardwired part)','merged Induction/Grid*.lean, AzumaProxyN.lean, Path/* (sig-hw 3.7k)','BA-T1','prover-hard',Z(1000,1400,2000)),
 ('BA-T5','T','Step 2 path layer twins, part 2 (stopping times, Doob, continuity)','as above','BA-T4','prover-hard',Z(1000,1400,2000)),
 ('BA-T6','T','Step 2 contraction / J-Gronwall twins (STContract, STSelfImp, STScale*)','merged Induction/Contract*.lean, Step2Scale.lean, Step2Core.lean','BA-T2, T3','prover-hard',Z(1000,1400,2000)),
 ('BA-T7','T','Step 2 events / decay-loop twins','merged Induction/Step2Events.lean, DecayLoopA/B.lean','BA-T6','prover-hard',Z(900,1200,1700)),
 ('BA-T8','T','Step 2 assembly BAStep2','merged Induction/Step2Defs.lean pins, ST2-04','BA-T7','prover',Z(700,1100,1500)),
 ('BA-U1','U','Steps 3-4 twins: sum-zero/zero-mode removal, new time intervals (loop-level)','merged Induction/ZeroModeCalc.lean, IterationsA.lean, NewPQ.lean, QGrid*.lean (ST-3 sig-hw 4.3k)','BA-T8, E3','prover-hard',Z(800,1200,1700)),
 ('BA-U2','U','Steps 3-4 twins: lem:SEforLn, lem_decayLoop, B45','merged SEforLn1/2.lean, B45.lean, KDecay.lean','BA-U1','prover-hard',Z(800,1200,1700)),
 ('BA-U3','U','Steps 3-4 twins: Step34Pins consumers, Step 3/4 assembly','merged Induction/Step34Pins.lean','BA-U2','prover',Z(700,1000,1500)),
 ('BA-U4','U','Step 5 twins: cases (i)-(ii) (TailtoTail, WardII, NewKLKL, CLT cancellation, ExpInv)','merged Induction/Step5*.lean, TailtoTail.lean, WardII.lean, Evolution/Clt*.lean (ST-4 sig-hw 2.4k)','BA-U3','prover-hard',Z(800,1200,1700)),
 ('BA-U5','U','Step 5 case (iii) = sec:Step5_larget for BA ([RBSO1D S7.3], uses lem_GbEXP_BA)','3_5:2284; 7_8:2101','BA-G6, U4','prover-max',Z(900,1300,1900)),
 ('BA-U6','U','Step 5 assembly BAStep5I-IV','merged Induction/Step5Pins.lean','BA-U4, U5','prover',Z(600,900,1300)),
 ('BA-V1','V','Step 6 twin: lem:LWterm_EXP assembly consumers (graph part is BA-L4)','6:83-88; B:7-121','BA-L4, U6','prover-hard',Z(700,1000,1500)),
 ('BA-V2','V','chain induction in t for the BA carrier: BAMainInd from Steps 1-6 (STMainIndG)','1_2:1256-1330, 7_8:1825-1832','BA-V1, T8, U3, U6','prover-max',Z(1000,1500,2200)),
 ('BA-V3','V','Steps 1-6 -> ML:GLoop, ML:GLoop_expec, ML:GtLocal for BA at t0','1_2:1190; 7_8:1813','BA-V2','prover',Z(500,700,1000)),
 ('BA-L1','L','graph vocabulary: Psi- and M-dotted edges, atoms, scalingBA (T2040 row)','B:286-356; T2040-prove.md:182','LW-03, MD','prover',Z(873,873,1746)),
 ('BA-L2','L','expansions lanlw, lem_lweight, GGGamma (pins BAlanlw, BAlweight, BAGGGamma; T2161a coefficient)','B:359-405 [yang2024Del B.9-B.11]; probe section 10','BA-L1, LW-04','prover-hard',Z(2400,2400,2400)),
 ('BA-L3','L','BA lvl1, atomic reduction and auxiliary graph, Anp for atoms (T2040 row)','B:407-523','BA-L2, LW-08, 11, 12','prover-max',Z(1060,1590,2650)),
 ('BA-L4','L','BA lem:LWterm_EXP with GGGamma (T2040 row)','B:118','BA-L2, LW-14','prover-max',Z(1500,1500,1500)),
 ('BA-M1','M','MA-BA: BAEnd_locSC from BAMainInd at t0 + zztE_BA transfer (BAlocalEntry_of_flow proved) + (eq:BtBt) + net lemma','7_8:1813-1816; RBM2D Main/RegionUnif.lean 950','BA-V3, D7','prover-hard',Z(700,1000,1500)),
 ('BA-M2','M','MA-BA: BAEnd_QDiff from Kn2sol/BAprof + (eq:BtBt), expectation bounds','1_2:657-666; RBM2D Main/*','BA-M1, K1','prover-hard',Z(700,1000,1500)),
 ('BA-M3','M','MA-BA: BAEnd_decol, BAEnd_QUE from the local laws / QD, rho-bulk','RBM2D Main/DecolFromLocal.lean 361, QUEFromQDiff.lean 1084 (d=2 tokens 3, 26)','BA-M1, M2','prover-hard',Z(900,1300,1900)),
 ('BA-N1','N','UN-BA: rho_N-dilated Step 1 comparison with LSY Thm 2.2 for BA initial data (BA part of UN-D1/T2162)','RBM2D Universality/Step1Band.lean 1259 (2 tokens); DECISIONS 11','BA-D6, M1, UN-D1','prover-hard',Z(700,1200,2000)),
 ('BA-N2','N','UN-BA: BAEnd_BUniv assembly (limit computation at fixed L,g; rho_N(E) >= kappa)','1_2:454-457','BA-N1','prover',Z(500,800,1500)),
]

FILES = {
 'BA-D1':'BA/Defs + BA/Pins (+ registry lines in Test/Axioms.lean)', 'BA-D2':'BA/SelfM', 'BA-D3':'BA/Ward + BA/OffDiag', 'BA-D4':'BA/CombesThomas',
 'BA-D6':'BA/Boundary', 'BA-D7':'BA/ImmLower',
 'BA-P1':'BA/Prop5Short','BA-P2':'BA/KKernel','BA-P3':'BA/KSymbol','BA-P4':'BA/KHeat','BA-P5':'BA/Prop5','BA-P6':'BA/PropUnit','BA-P7':'BA/Prop8','BA-P8':'BA/Prop6Path',
 'BA-K1':'BA/KSolve','BA-K2':'BA/KTree','BA-K3':'BA/KPure','BA-K4':'BA/KBound','BA-K5':'BA/KWard',
 'BA-E1':'BA/EKPins','BA-E2':'BA/EKSum','BA-E3':'BA/EKPrec',
 'BA-G1':'BA/GreenSchur','BA-G2':'BA/GreenLDE','BA-G3':'BA/GbEXPDiag','BA-G4':'BA/GbEXPOff','BA-G5':'BA/GbEXPAvg','BA-G6':'BA/GbEXP',
 'BA-S1':'BA/ConArg','BA-S2':'BA/Step1Boot','BA-S3':'BA/Step1',
 'BA-T1':'BA/Step2Gronwall','BA-T2':'BA/EMn2','BA-T3':'BA/NewKLK','BA-T4':'BA/Step2PathA','BA-T5':'BA/Step2PathB','BA-T6':'BA/Step2Contract','BA-T7':'BA/Step2Events','BA-T8':'BA/Step2',
 'BA-U1':'BA/Step34A','BA-U2':'BA/Step34B','BA-U3':'BA/Step34','BA-U4':'BA/Step5A','BA-U5':'BA/Step5Larget','BA-U6':'BA/Step5',
 'BA-V1':'BA/Step6','BA-V2':'BA/MainInd','BA-V3':'BA/GLoopAtT0',
 'BA-L1':'Graph/BAVocab (T2040)','BA-L2':'Graph/BAExpand (T2040)','BA-L3':'Graph/BALvl1 (T2040)','BA-L4':'Graph/BALWterm (T2040)',
 'BA-M1':'BA/MALocal','BA-M2':'BA/MAQDiff','BA-M3':'BA/MADecolQUE','BA-N1':'BA/UNStep1','BA-N2':'BA/UNBUniv'}
# pins of the probe discharged by the item (the Prop-valued defs of RBM.BA that are owed, see pin_index.py); [] = intermediate item
PROVES = {
 'BA-D1':['(defs, proved base, the pins as Prop defs)'],'BA-D2':['BAmExists','BAmUniqReal'],'BA-D3':['BAWard','BAoffDiag'],'BA-D4':['BAPropM'],'BA-D6':['BAmBoundary'],'BA-D7':['BAImmLower'],
 'BA-P1':['BAProp5s'],'BA-P2':[],'BA-P3':[],'BA-P4':[],'BA-P5':['BAProp5'],'BA-P6':['BAProp6','BAProp7'],'BA-P7':['BAProp8'],'BA-P8':['BAProp5to8'],
 'BA-K1':['BAKsolve'],'BA-K2':[],'BA-K3':[],'BA-K4':['BAKbound'],'BA-K5':[],
 'BA-E1':[],'BA-E2':[],'BA-E3':[],
 'BA-G1':[],'BA-G2':[],'BA-G3':[],'BA-G4':[],'BA-G5':[],'BA-G6':['BAGbEXP'],
 'BA-S1':['BAConArg'],'BA-S2':[],'BA-S3':['BAStep1'],
 'BA-T1':[],'BA-T2':['BAEMn2Exp'],'BA-T3':[],'BA-T4':[],'BA-T5':[],'BA-T6':[],'BA-T7':[],'BA-T8':['BAStep2'],
 'BA-U1':[],'BA-U2':[],'BA-U3':[],'BA-U4':[],'BA-U5':[],'BA-U6':[],
 'BA-V1':[],'BA-V2':['BAMainInd','BAGlueChain'],'BA-V3':[],
 'BA-L1':[],'BA-L2':['BAlanlw','BAlweight','BAGGGamma'],'BA-L3':[],'BA-L4':[],
 'BA-M1':['BAGlueLoc','BAEnd_locSC'],'BA-M2':['BAGlueQDiff','BAEnd_QDiff'],'BA-M3':['BAGlueDecol','BAGlueQUE','BAEnd_decol','BAEnd_QUE'],
 'BA-N1':[],'BA-N2':['BAGlueUniv','BAEnd_BUniv','BAThm27'],
}
groups = collections.OrderedDict([('D','deterministic layer'),('P','propagator (PT-BA)'),('K','K-loops (KL-BA)'),('E','evolution kernels (EK-BA)'),('G','lem_GbEXP_BA chain'),('S','Step 1'),('T','Step 2'),('U','Steps 3-5'),('V','Step 6 and chain'),('L','graph layer (T2040 rows)'),('M','MA-BA'),('N','UN-BA')])
import sys, math
mode = sys.argv[1] if len(sys.argv) > 1 else 'summary'
if mode == 'full':
    print('%-6s %-44s %-12s %-26s %-5s %-6s %-6s  %s' % ('id', 'file (RBM3D/...)', 'role', 'proves (pins)', 'lo', 'central', 'hi', 'depends on'))
    for it in items:
        print('%-6s %-44s %-12s %-26s %-5d %-6d %-6d  %s' % (it[0], FILES[it[0]][:44], it[5], ','.join(PROVES[it[0]])[:26] or '-', it[6][0], it[6][1], it[6][2], it[4]))
    print()
    for it in items:
        print('%s [%s] %s | sources: %s' % (it[0], it[1], it[2], it[3]))
    sys.exit(0)
tot = collections.OrderedDict((g, [0, 0, 0, 0]) for g in groups)
for it in items:
    g = it[1]; lo, c, hi = it[6]
    tot[g][0] += 1; tot[g][1] += lo; tot[g][2] += c; tot[g][3] += hi
print('%-3s %-28s %5s | %-24s' % ('', 'group', 'items', 'lines lo / central / hi'))
T = [0, 0, 0, 0]
for g, n in groups.items():
    a = tot[g]; print('%-3s %-28s %5d | %6d %6d %6d' % (g, n, a[0], a[1], a[2], a[3]))
    for i in range(4): T[i] += a[i]
print('%-3s %-28s %5d | %6d %6d %6d' % ('', 'TOTAL', T[0], T[1], T[2], T[3]))
L = tot['L']
print('lines/1000 (all groups): lo %.1f  central %.1f  hi %.1f ; items %d' % (T[1]/1000, T[2]/1000, T[3]/1000, T[0]))
print('graph layer BA-L1..L4 (T2040 rows, in ROUTES BA 33): items %d, lines %d/%d/%d ; without it: items %d, lines/1000 %.1f / %.1f / %.1f' % (L[0], L[1], L[2], L[3], T[0]-L[0], (T[1]-L[1])/1000, (T[2]-L[2])/1000, (T[3]-L[3])/1000))
big = [(i[0], i[6][1]) for i in items if i[6][1] > 1500]
split2 = sum(math.ceil(i[6][1]/1500) for i in items)
print('items with central > 1500 lines (600-1500 rule):', big, '; tickets if every item is cut at 1500 central lines:', split2)
print('roles:', dict(collections.Counter(i[5] for i in items)))
print('DECISIONS 9 O2 (25/40/50): items %d, lines/1000 central %.1f -> %s' % (T[0], T[2]/1000, 'OVER 50' if T[0] > 50 else ('40-50' if T[0] > 40 else ('25-40' if T[0] > 25 else 'under 25'))))
# coverage: every owed pin of the probe (pin_index.py, registry owed) is discharged by an item
import re, subprocess
pi = subprocess.run(['python3', 'pin_index.py'], capture_output=True, text=True).stdout.split('\n')
owed = [l.split()[0] for l in pi if re.match(r'^\S+\s+\d+\s+(def|structure)\s+owed', l)]
extra = ['BAProp5', 'BAProp5s', 'BAProp6', 'BAProp7', 'BAProp8', 'BAProp5to8', 'BAEnd_decol', 'BAEnd_QUE', 'BAEnd_BUniv', 'BAThm27', 'BAGlueChain', 'BAGlueLoc', 'BAGlueQDiff', 'BAGlueDecol', 'BAGlueQUE', 'BAGlueUniv']
need = sorted(set(owed + extra))
cov = collections.Counter(p for v in PROVES.values() for p in v)
miss = [p for p in need if cov[p] == 0]
dup = [p for p in need if cov[p] > 1]
print('owed pins to discharge: %d; discharged by some item: %d; missing: %s; discharged twice: %s' % (len(need), len(need) - len(miss), miss, dup))
# adaptation-rule cross-check (decl_inv.py, file_gate.py): merged band-hardwired lines of ST-1..ST-4, KL, EK x alpha
gl = {'ST-1':(8989,5682),'ST-2':(10435,5581),'ST-3':(4320,3229),'ST-4':(2431,1964),'KL':(6627,2042),'EK':(498,788)}
base = {g: s + 0.5*b for g, (s, b) in gl.items()}
st = sum(base[g] for g in ('ST-1', 'ST-2', 'ST-3', 'ST-4'))
print('adaptation rule: (sig-hw + 0.5 body-only) lines: ST-1..4 %d, KL %d, EK %d ; x alpha 0.5/0.7/1.0 -> ST-1..4 %.1f/%.1f/%.1f, KL %.1f/%.1f/%.1f, EK %.1f/%.1f/%.1f (lines/1000)' % (
    round(st), round(base['KL']), round(base['EK']), *(a*st/1000 for a in (.5, .7, 1)), *(a*base['KL']/1000 for a in (.5, .7, 1)), *(a*base['EK']/1000 for a in (.5, .7, 1))))
stg = [i for i in items if i[1] in ('S', 'T', 'U', 'V')]
print('items S,T,U,V (Steps 1-6 twins): %d items, lines/1000 %.1f / %.1f / %.1f   (to compare with ST-1..4 above)' % (len(stg), sum(i[6][0] for i in stg)/1000, sum(i[6][1] for i in stg)/1000, sum(i[6][2] for i in stg)/1000))
```
### cites_grouped.py
```python
# External citations of the BA part, grouped to 12 rows: source | cited at | statement | used in | internal route (DECISIONS 5) | items | est. lines.
# est. lines = sum of the central lines of the carrying items of ba_split2.py (distinct items per row; rows share items: not additive).
import sys
src = open('ba_split2.py', encoding='utf-8').read()
ns = {}; exec(src[:src.index('import sys, math')], ns)
items = {it[0]: it for it in ns['items']}
ROWS = [
 ('[Biane]', '1_2:624', 'mu_N=semicircle(x)nu_L, density, m solves (self_m)', '(self_m), rho_N', 'Schwarz-Pick fixed point; RBM2D FreeConv port (719 l.); boundary values', ['BA-D2', 'BA-D6']),
 ('[RBSO1D] L3.3 (zztE_BA)', '7_8:1796', 'sqrt(t0) m(E,g0)=m(z,g), sqrt(t0) M(E,g0)=M(z,g), G =_d sqrt(t0) G_t0', 'flow, all steps', 'algebra, proved in the probe (BAzztE_data/_Mres) + merged Gt_BA', ['BA-D1']),
 ('lem:propM: [RBSO1D L3.9] (commented out), [LSY15 L3.5], [Aizenman Thm 10.5]', '7_8:1844,1846,1908,1911', 'translation inv., Ward, Im m >~ 1, Mbound_AO(2)', 'Theta, Steps 1-6', 'Ward proved (BAward_avg); Taylor; Combes-Thomas (RBM2D CT*, 669 l.); Im m bridge BAImmLower (Holder-1/3 + Poisson)', ['BA-D3', 'BA-D4', 'BA-D7']),
 ('[RBSO1D] L6.1', '7_8:1948', 'lem_GbEXP_BA: GiiGEX, GijGEX, GavLGEX (g <= W^-eps there)', 'Step 1, Step 5(iii)', 'RBSO1D text not in the repo; Schur/LDE rebuild, merged Green/* as the band model', ['BA-G1', 'BA-G2', 'BA-G3', 'BA-G4', 'BA-G5', 'BA-G6']),
 ('[RBSO1D] L7.1, S7.1, S7.3; [YY_25] S5.3', '7_8:1987,1990,2101', 'lem_ConArg_BA; Step 1 (lRB1, Gtmwc); Step 5 large t', 'Steps 1, 5', 'same arguments with (W^d l^d eta)^-1 for W^-d B; merged S1-32.., Step5*', ['BA-S1', 'BA-S2', 'BA-S3', 'BA-U5']),
 ('[RBSO1D] L3.17', '1_2:1046', 'Ward identity for K-loops (lem_WI_K)', 'Steps 2-5, Kbound', 'merged KLWard.lean/KLWardIneq.lean as the model', ['BA-K5']),
 ('[RBSO1D] L4.16, S4, L4.29, Claim 4.30; [YY_25] L3.10', 'A:376,592,734', 'tree representation with M-entries; molecule sum-zero', 'ML:Kbound, Kn2sol', 'ODE d/dt Theta = Theta M Theta; merged KLtreeValW, KLPure', ['BA-K2', 'BA-K3']),
 ('[RBSO1D] L3.10, [yang2024Del] L3.1, (E.19); [DYYY25] L2.14, S8; [Lawler] S2', 'A:50-67', 'Theta(+,-) bounds by summation by parts; Gaussian tail of K^n, local CLT', 'lem_propTH 5-8 for K=|M|^2', 'Fourier symbol of K, Esscher tilt; merged PropUnit/HeatProduct as models', ['BA-P4', 'BA-P5', 'BA-P6']),
 ('[RBSO1D] A.10, (A.112); [DYYY25] S7', '3_5:2213,2248', 'CLT cancellation of the far term ("does not depend on d")', 'Step 5', 'merged Evolution/Clt* (S5-17..24) over the carrier', ['BA-U4']),
 ('[yang2024Del] L B.9-B.11, App. B', 'B:357-407', 'lanlw, lem_lweight, GGGamma; reduction to locally standard graphs', 'LWterm_EXP (Step 6)', 'checked numerically (b.7; delta T2161a); BAlanlw/BAlweight/BAGGGamma; BA-L2, L3', ['BA-L2', 'BA-L3']),
 ('LSY Thm 2.2 (authorized, DECISIONS 5)', '1_2 Thm B_Univ', 'bulk universality of Gaussian-divisible matrices', 'UN', 'external, no proof lines; BA wrappers only', ['BA-N1', 'BA-N2']),
 ('[bourgade2019random] L4.2; [PelSchShaSod]; [LSY15, knowles20]', 'A:25; 1_2:39,634,672', 'band properties of S^(B)(g); localization; background', 'band / remarks', 'not used for BA', []),
]
print('%-2s %-60s | %-26s | %-72s | %-22s | %-118s | %-18s %s' % ('#', 'source', 'cited at', 'statement', 'used in', 'internal route', 'items (BA-)', 'lines c'))
for k, (a, b, c, d, e, its) in enumerate(ROWS, 1):
    cl = sum(items[i][6][1] for i in its)
    its_s = ','.join(i[3:] for i in its) if its else '-'
    print('%-2d %-60s | %-26s | %-72s | %-22s | %-118s | %-18s %s' % (k, a, b, c, d, e, its_s, cl if its else 0))
```
### cites_table.py
```python
# External citations of the BA part (inv_cites.py lists every \cite; this table groups them): statement, where cited, where used,
# internal route (DECISIONS 5: only LSY Thm 2.2 is external), the split items of ba_split2.py that carry it and their central lines.
import re, sys
src = open('ba_split2.py', encoding='utf-8').read()
ns = {}
exec(src[:src.index('import sys, math')], ns)
items = {it[0]: it for it in ns['items']}
ROWS = [
 ('[Biane]', 'mu_N = semicircle (x) nu_L has a continuous density; m solves (self_m), Im m>0', '1_2:624', '(self_m), rho_N, bulk set',
  'Schwarz-Pick/Nevanlinna fixed point of m -> G_nu(E+m); RBM2D FreeConv.lean port (719 lines, 0 d=2 tokens); boundary values', ['BA-D2', 'BA-D6']),
 ('[RBSO1D] L3.3', 'zztE_BA: sqrt(t0) m(E,g0)=m(z,g), z_t0=sqrt(t0) z, sqrt(t0) M=M, G =_d sqrt(t0) G_t0', '7_8:1796', 'flow framework, all steps',
  'algebra; proved here: BAzztE_data, BAzztE_Mres (probe), merged Gt_BA (pointwise)', ['BA-D1']),
 ('[RBSO1D] L3.9', 'lem:propM (1)-(3): translation invariance, Ward, |m|<=1, Mbound_AO(2)', '7_8:1844, 1846 (commented out in the TeX)', 'Theta properties, Steps 1-6',
  'Ward row by row (BAward_avg proved), circulant structure, Combes-Thomas; the printed lemma cites only [LSY15 L3.5] and [Aizenman Thm 10.5] in its proof', ['BA-D3', 'BA-D4']),
 ('[LeeSchSteYau2015] L3.5', 'Im m >~ 1 for |E| <= e - kappa (bulk lower bound)', '7_8:1908', 'lem:propM (2), chain domain',
  'replaced by the bridge pin BAImmLower (rho-bulk => Im m(E+i eta) >= c): uniform Holder-1/3 of rho_N + Poisson smoothing', ['BA-D7']),
 ('[Aizenman_book] Thm 10.5', 'Combes-Thomas estimate (Mbound_AO2)', '7_8:1911', 'lem:propM (3), g >= (2C)^-1',
  'conjugation by e^{t dist}, Neumann series; RBM2D CombesThomas* port (8 files, 669 lines at c9a24cf, 0 d=2 tokens)', ['BA-D4']),
 ('[RBSO1D] L6.1', 'lem_GbEXP_BA: resolvent entry bounds (GiiGEX, GijGEX, GavLGEX), proved there for g <= W^-eps', '7_8:1948', 'Step 1 (lRB1, Gtmwc), Step 5 case (iii)',
  'RBSO1D text is not in the repository; rebuild with Schur complements and large deviations; merged Green/* (24.1k lines) as the band model', ['BA-G1', 'BA-G2', 'BA-G3', 'BA-G4', 'BA-G5', 'BA-G6']),
 ('[RBSO1D] L7.1', 'lem_ConArg_BA: continuity argument for the resolvent bounds', '7_8:1987', 'Step 1', 'same argument with (W^d l^d eta)^-1 for W^-d B; merged S1-32 STConArg', ['BA-S1']),
 ('[RBSO1D] S7.1', 'Step 1 for BA (lRB1) and (Gtmwc): same as the paper cited', '7_8:1990', 'Step 1', 'bootstrap, net lift, forbidden region; merged Step1*/Continuity*', ['BA-S2', 'BA-S3']),
 ('[RBSO1D] S7.3, [YY_25] S5.3', 'sec:Step5_larget: large-t case of Step 5, via lem_GbEXP_BA', '7_8:2101', 'Step 5 case (iii)', 'omitted in the paper; BAGbEXP and merged Step5 twins', ['BA-U5']),
 ('[RBSO1D] L3.17', 'Ward identity for G-loops / K-loops (lem_WI_K)', '1_2:1046', 'K-loop bounds, Steps 2-5', 'merged KLWard.lean/KLWardIneq.lean as the model', ['BA-K5']),
 ('[RBSO1D] L4.16, S4', 'tree representation of K-loops with M-entries (tree-representation_BA)', 'A:592, A:376', 'ML:Kbound, Kn2sol', 'ODE d/dt Theta = Theta M Theta; merged KLtreeValW (KLTree.lean:114)', ['BA-K2']),
 ('[RBSO1D] L4.29, Claim 4.30; [YY_25] L3.10', 'molecule sum-zero (eq:Sigma-empty-sum-zero), pure loops', 'A:734', 'ML:Kbound', 'A:643-734; merged KLPure', ['BA-K3']),
 ('[RBSO1D] L3.10, [yang2024Del] L3.1, (E.19)', 'Theta(+,-) bounds (BD1, BD2, ThfadC0) by summation by parts', 'A:50-55', 'lem_propTH 5-7 for K=|M|^2', 'unit differences of K^n(0,.), Fourier symbol; merged PropUnit.lean as the model', ['BA-P4', 'BA-P6']),
 ('[DYYY25] L2.14, S8; [Lawler_book] S2', 'Gaussian/exponential tail of K^n, local CLT for the walk', 'A:58-67', 'lem_propTH property 5', 'Chernoff/Esscher tilt and on-diagonal bound on Z_L^d; merged HeatProduct.lean (1257 lines) as the model', ['BA-P4', 'BA-P5']),
 ('[RBSO1D] A.10, (A.112); [DYYY25] S7', 'CLT cancellation for the far term; "does not depend on d" (omitted)', '3_5:2213, 2248', 'Step 5 (band and BA)', 'merged Evolution/Clt*.lean (S5-17..24) retargeted at the carrier', ['BA-U4']),
 ('[yang2024Del] L B.9-B.11, App. B', 'lanlw, lem_lweight, GGGamma; reduction to locally standard graphs', 'B:359-407', 'LWterm_EXP (Step 6)', 'checked numerically here (n6_lw*.py; GGGamma coefficient delta T2161a); pins BAlanlw/BAlweight/BAGGGamma; BA-L1..L4 of T2040', ['BA-L2', 'BA-L3']),
 ('[bourgade2019random] L4.2', 'properties of S^(B)(g) (band)', 'A:25', 'band lem_propTH only', 'not used for BA (K = |M|^2 is a different kernel: BA-P2..P4)', []),
 ('LSY Thm 2.2 (authorized, DECISIONS 5)', 'bulk universality of Gaussian-divisible Hermitian matrices (Landon-Sosoe-Yau)', 'DECISIONS 5; 1_2 (Thm B_Univ)', 'bulk universality (UN)', 'the only external input; UN-D1 (T2162) and the BA part BA-N1/N2', ['BA-N1', 'BA-N2']),
 ('[PelSchShaSod], [LeeSchSteYau2015, knowles20]', 'localization for g << W^{-d/2}; random matrix theory background', '1_2:39, 634, 672', 'remarks only', 'not used in any proof', []),
]
print('%-3s %-40s %-22s %-34s %-6s %s' % ('#', 'source', 'cited at', 'used in', 'lines', 'items (central lines lo/c/hi of the carrying items)'))
for k, (name, stmt, at, used, route, its) in enumerate(ROWS, 1):
    lo = sum(items[i][6][0] for i in its); c = sum(items[i][6][1] for i in its); hi = sum(items[i][6][2] for i in its)
    print('%-3d %-40s %-22s %-34s %-6s %s %s' % (k, name[:40], at[:22], used[:34], c if its else 0, ','.join(its) or '-', '(%d/%d/%d)' % (lo, c, hi) if its else ''))
if len(sys.argv) > 1 and sys.argv[1] == 'full':
    for k, (name, stmt, at, used, route, its) in enumerate(ROWS, 1):
        print('%d. %s | statement: %s | cited at %s | used in: %s | route: %s' % (k, name, stmt, at, used, route))
```
### build_report.py
```python
#!/usr/bin/env python3
# Assembles docs/reports/T2161-prove.md (sections (b)-(d) appended to the untouched preflight section (a)) and docs/reports/T2161-portmap.md.
# Every pasted block is the live output of the displayed command (run here with S and W exported); hand-written text is limited to
# the notices, the narrative and the (d) list.  Usage: build_report.py [prove|portmap|both]
import subprocess, os, re, sys, datetime, shutil
S = '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2161'
W = '/Users/junyin/Lean_proof/RBM3D-wt/T2161'
REP = '/Users/junyin/Lean_proof/RBM3D/docs/reports'
env = dict(os.environ, S=S, W=W)
def sh(cmd, cwd=S):
    r = subprocess.run(['/bin/bash', '-c', cmd], cwd=cwd, env=env, capture_output=True, text=True)
    return r.stdout.rstrip('\n')
def blk(cmd, cwd=S, ind='    ', note=None):
    out = sh(cmd, cwd)
    lines = ['%s$ %s%s' % (ind, cmd, ('   # ' + note) if note else '')]
    lines += [ind + l if l else ind for l in out.split('\n')] if out else []
    return '\n'.join(lines)
def now(): return sh('date -u')
head = sh('git log -1 --format=%h', W)
base = sh('git rev-parse --short $(git merge-base HEAD main)', W)

# ---------- numbers pulled from script outputs (no hand-typed figures in the narrative) ----------
def grab(path, pat, grp=1, flags=0):
    t = open(os.path.join(S, path), encoding='utf-8').read()
    m = re.search(pat, t, flags)
    if not m: raise SystemExit('pattern not found in %s: %s' % (path, pat))
    return m.group(grp) if grp else m
split_t = open(os.path.join(S, 'ba_split2.out'), encoding='utf-8').read()
m = re.search(r'lines/1000 \(all groups\): lo ([\d.]+)  central ([\d.]+)  hi ([\d.]+) ; items (\d+)', split_t)
SLO, SCE, SHI, NIT = m.group(1), m.group(2), m.group(3), int(m.group(4))
NGRAPH = int(re.search(r'graph layer BA-L1..L4 .*?items (\d+)', split_t).group(1))
N_DECL = grab('name_clash.out', r'declarations in the probe: (\d+)')
N_AX = len(re.findall(r'depends on axioms', open(os.path.join(S, 'final_lean.out'), encoding='utf-8').read()))
N_PROP = grab('registry.out', r'Prop-valued definitions of the probe: (\d+)')
reg = {k: int(v) for k, v in re.findall(r'^(owed|structural|shape|carrier|borrowed)\s+(\d+):', open(os.path.join(S, 'registry.out'), encoding='utf-8').read(), re.M)}
N_INST = grab('instances_index.out', r'theorems in section 13: (\d+)')
N_BAND = grab('pin_subst2.out', r'^total\s+(\d+)\s+(\d+)', 2, re.M); N_PINS = grab('pin_subst2.out', r'^total\s+(\d+)\s+(\d+)', 1, re.M)
N_SIG = grab('decl_inv.out', r'^TOTAL\s+\d+\s+\d+ \|\s+\d+\s+(\d+)', 1, re.M)
c1_001 = grab('n1_equiv.out', r'L=4 g=0\.01 .*?k=0\.10: ([\d.]+)'); c1_03 = grab('n1_equiv.out', r'L=4 g=0\.3 .*?k=0\.10: ([\d.]+)')
PROBE_LINES = sh('wc -l < $W/RBM3D/Probe/T2161Pins.lean').strip()
n_theorem = sh("grep -c '^theorem' $W/RBM3D/Probe/T2161Pins.lean").strip()

# ====================================== the prove report ======================================
def prove_report():
    t_top = now()
    A = open(os.path.join(S, 'T2161-prove.a.md'), encoding='utf-8').read().rstrip('\n').split('\n')   # untouched section (a), line 1 included
    out = [A[0], '']
    out += [
 '## Top notices (stage 1b, %s; section (a) below is unchanged)' % t_top,
 '1. **Bulk condition (T2001d/l): the decided form changes what Thm 2.7 claims; the dispatcher asks Jun.** Decided: `B_κ = {E : ρ_N(E) ≥ κ}` (`BAbulk`, `ρ_N = π⁻¹ Im m(E+i0, g)`; no `e_λ`, no `supp μ_N`) and the chain domain `Im m(z,g) ≥ κ` with the bridge pin `BAImmLower`. Against the paper\'s `|E| ≤ e_λ − κ` the energy set of Thm 2.7 (i) is defined for odd `L`, (ii) is non-empty at gap couplings, (iii) loses the cusp points `ρ_N = 0` (`L=4`, `g=g_c=0.3542`: `E*=2.508`) where `lem:propM`(2) fails. Evidence: (a), b.3, b.5.',
 '2. **BA count over 50 (DECISIONS §9 O2): the dispatcher asks Jun before any BA proof ticket starts.** b.9: %d tickets (%d new + the %d graph-layer rows BA-L1..L4 of T2040), lines/1000 = %s / %s / %s (lo / central / hi). Not priced: making the merged chain files carrier-generic instead of re-proving the twins (b.8: %s of %s chain pins depend on band objects).' % (NIT, NIT - NGRAPH, NGRAPH, SLO, SCE, SHI, N_BAND, N_PINS),
 '3. Paper findings (d): T2161a `GGGamma` (B:398) is false as printed; T2161b `lem:propM`(2) `Im m ≳ 1` fails at cusps; the TeX cites [RBSO1D] Lemma 3.9 only in comments (7_8:1844, 1846).',
 '']
    out += A[1:]                                   # (a) from its heading to its last line, byte-identical
    t_a = now()
    out += ['',
 '## (a′) Preflight corrections — %s' % t_a,
 'Two phrases of (a) are imprecise; the verdict PASS is unchanged. (1) "strictly extends, never shrinks": the ρ-form removes the cusp points (`ρ_N=0` inside `|E| ≤ e_g−κ`, `L=4`, `g=g_c`), and its constant `κ_ρ(κ)` degrades as `g ↑ g_c(L)` (b.3: `min ρ_N` on `|E| ≤ e−0.1`, `L=4`, is %s at `g=0.01` and %s at `g=0.3`; `ρ_N(E*)=0` at `g_c`). (2) "false at cusp" is the claim `Im m ≳ 1` of `lem:propM`(2), not Thm 2.7. The notices above were inserted below line 1; (a) itself is byte-identical.' % (c1_001, c1_03),
 '',
 '## (b) Script output',
 '`W`=%s (branch `t/T2161`, base %s, HEAD %s, `RBM3D/Probe/T2161Pins.lean`, %s lines); `S`=%s (scripts; `$S/final_run.sh` regenerates every output). Full outputs, tables and scripts: `docs/reports/T2161-portmap.md` (P.1-P.12).' % (W, base, head, PROBE_LINES, S),
 '### b.1 Build, axioms, hygiene',
 blk('git diff --name-only main...t/T2161; lake env lean RBM3D/Probe/T2161Pins.lean > $S/final_lean.out; echo "lean exit=$?"; tail -1 $S/final_lean.out; lake build RBM3D.Probe.T2161Pins > $S/final_build.out 2>&1; tail -2 $S/final_build.out; echo "probe warnings $(grep -c "warning: RBM3D/Probe/T2161Pins" $S/final_build.out)"', cwd=W),
 blk('echo "std-axiom theorems $(grep -c \'depends on axioms: \\[propext, Classical.choice, Quot.sound\\]\' $S/final_lean.out); other axiom lines $(grep \'depends on axioms\' $S/final_lean.out | grep -vc \'\\[propext, Classical.choice, Quot.sound\\]\'); forbidden tokens $(grep -cE \'sorry|admit|native_decide|^axiom\' $W/RBM3D/Probe/T2161Pins.lean)"'),
 blk('python3 $S/name_clash.py | sed -n "1,2p;5p"', note='new public names vs RBM3D and RBM2D@c9a24cf (RBM1D, main: portmap P.10)'),
 '### b.2 Pins (item 2): registry class of every Prop-valued definition (DECISIONS §16, §20); statements of the targets, extracted by script',
 blk('python3 $S/registry.py | sed -n "1,6p" | cut -c1-250'),
 blk('python3 $S/statements.py BAMainInd BAEnd_BUniv BAThm27'),
 '### b.3 Bulk condition (T2001d/l): forms and the bridge `BAImmLower` at the vacuity classes',
 blk('sed -n "442p;448p;451p" $W/RBM3D/Probe/T2161Pins.lean', note='forms 0, 1, 3 (the chain domain `BAdom` and `BAReal` are at :455, :459)'),
 blk('python3 $S/n1_immlower.py', note='min Im m(E+iη) over B_κ (κ=0.05), η∈(0,1], vs πκ'),
 blk('sed -n "1p;2p;4p" $S/n1_equiv.out | cut -c1-175', note='output of `python3 $S/n1_equiv.py`: c1(κ)=min ρ_N on |E| ≤ e−κ, even L, no gaps'),
 '### b.4 Constants where `M ≠ mI` (item 4; DECISIONS §18: constants may depend on Λ = 𝔡⁻¹)',
 blk('python3 $S/n2_table.py | sed -n "2p;3p;5p;7p;22p;23p" | cut -c1-175'),
 '### b.5 Instances (item 7): compiled; the three class sequences of 13.9 and the sequence `sz0`',
 blk('python3 $S/instances_index.py | grep -E "^13\\.(2|5|6|9) "'),
 blk('python3 $S/cls_numerics.py | cut -c1-250', note='class of `g_0` (same formulas as `fp`; `E_*≈0` at even `L`)'),
 '### b.6 Extremes of the PT-BA pins and of `BAKsolve`',
 blk('python3 $S/n3_pt.py | sed -n "1p;2p;3p;33p;38p;40p"'),
 blk('python3 $S/n4_kn2.py | sed -n "1p;3p;5p"'),
 '### b.7 The graph-layer expansions (BA-L2) at an extreme input',
 blk('python3 $S/n6_lw.py | sed -n "2p;4p;6p;8p" | cut -c1-175'),
 blk('python3 $S/n6_lw_mc.py | sed -n "1p;4p"; python3 $S/n6_lw_mc_printed.py | sed -n "2p"', note='W=2, N=6, 4e5 samples'),
 '### b.8 Inventory (item 1): paper statements, merged declarations, RBM2D port candidates (file:line at `c9a24cf`), cost structure',
 blk('python3 $S/inv_paper_summary.py'),
 blk('python3 $S/inv_merged_summary.py | sed -n "1p"; tail -2 $S/inv_merged_ba.out'),
 blk('sed -n "/^group totals/,/^files mentioning/p" $S/inv_rbm2d.out; git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Endpoints.lean', note='port: `BAIsOrthoEigenbasis` = RBM2D/Endpoints.lean:56-59 (c9a24cf); per-file rows: portmap P.1d'),
 blk('sed -n "/^TOTAL/p" $S/decl_inv.out; sed -n "1p;\\$p" $S/pin_subst2.out', note='merged Lean: lines whose signature mentions a band token; chain pins that depend on band objects'),
 '### b.9 External citations (item 3) and the split (item 6): count against DECISIONS §9 O2',
 blk('python3 $S/cites_grouped.py'),
 blk('python3 $S/ba_split2.py | sed -n "1,15p;17p;19p;20p"', note='items = tickets of 600-1500 lines (rows: `$S/ba_split2.py full`, portmap P.9)'),
 '### Reading (narrative)',
 '1. The probe has %s lines, %s declarations, %s theorems with the three standard axioms only; sections: 0-2 resolvent identities and bulk forms, 3 deterministic pins, 4 PT pins, 5-9 chain pins over a flow carrier, 10 graph layer, 11 endpoints, 12-12.1 skeletons with six glue pins, 13 instances (%s theorems).' % (PROBE_LINES, N_DECL, n_theorem, N_INST),
 '2. Proved here, not pinned: subordination (`BASelf_subord`: explicit `(self_m)` data at `z = w − m_w`, `Im w > 1`); `zztE_BA` (clauses 1-3 by `BAzztE_data`, `BAzztE_Mres` for any Hermitian `Ψ`, clause 4 is the merged `Gt_BA`; the hypothesis `|Re z| ≤ 2−κ` of 7_8:1797 is dropped, T2001g); averaged Ward `BAward_avg`; `BAbulk_iff`; `BAdom_real` (chain domain ⇒ real-axis datum `(g_0, E, m_0)`, `g_0 = √t_0 g ≤ g`); `BAlocalEntry_of_flow`; `BAendDom_to_dom`.',
 '3. Steps that reuse the ST pins with `M` for `m`: 3, 4, 5 except `sec:Step5_larget` (`1−t ≥ g²`, case (iii)) and 6 except `lem:LWterm_EXP` "extend verbatim" (7_8:2100-2105), so they get no BA statement. The 16 `ST*g` forms restate the merged band pins over `FlowFM`: at `bandFM` they are the merged pins (`Iff.rfl`), at `baFM` the BA pins. BA statements exist only where the paper changes: Step 1 (`BAGbEXP`, `BAConArg`, `BAStep1`), Step 2 (`BAStep2`, `BAEMn2Exp`: deterministic `𝒥`), 5(iii) (consumes `BAGbEXP`), Step 6 (`BAlanlw`, `BAlweight`, `BAGGGamma`; BA-L1..L4), K-loops (`BAKsolve`, `BAKbound`), PT 5-8 for `K=|M|²` (`BAProp5..8`). Every chain pin quantifies its constants (`κ, ε, 𝔡`, then `c`, `𝔠_d` or `C_d`) before `∀ sz z` (`BAMainInd`, `BAGbEXP`, `BAConArg`, `BAStep1`, `BAStep2`).',
 '4. This does not make the merged proofs generic: %s of %s chain pins depend on band objects and %s signature lines hardwire a band token (b.8): the twins are re-proved (priced in b.9) or the merged files are refactored (not priced).' % (N_BAND, N_PINS, N_SIG),
 '5. Endpoints are in the form of DECISIONS §11 with the ρ-bulk (`BAEnd_*`, `BAThm27`); six glue pins (BA-V2, MA-BA, UN-BA) make `BAThm27_skeleton_chain` a compiled implication graph: the deterministic pins, `BAKsolve`, the Step 1-2 pins, `BAKbound` and the three graph expansions ⇒ `BAThm27`; `inst_cls_Thm27_chain` applies it at the class sequences. Scales as in the ST pins: `≺` is `Prec` at `N` (`W^τ`, `W^{-D}` read as `N^τ`, `N^{-D}`, T2002i; `|x−y|` is `W|[x]−[y]|`, T2001e).',
 '6. Instances (b.5): at `sz0` every chain pin is applied with all deterministic hypotheses discharged (the pin hypothesis is `BAmExists`); at three class sequences (gaps, odd, interval; 13.9) the ρ-bulk contains `E_*` with `ρ_N(E_*) ≥ κ_*` and `𝐃^{BA}` is nonempty for every `n` (compiled); `BAThm27 3` and `BAmUniqReal 3` are the only hypotheses.',
 '7. Not compiled: the ρ-bulk at a prescribed coupling such as `g=10` (needs the spectral form of `(self_m)`, BA-D2); the regime of `g_0` (numerics, b.5); the carrier forms of the Steps 3-6 pins as named pins (BA-U1..V3 name them).',
 '8. Findings: `GGGamma` (B:398) needs `(M⁺S⁺)_{xβ}` in its first two sums (b.7: 1.2e-6 against 1.2e-2 exact; Monte Carlo 6.5e-6 against 1.3e-3); the constants of `BAPropM`, `BAoffDiag`, `BAProp5` depend on `Λ` (b.4, b.6: `r` rises from 0.015 to 0.917 in the rows shown and reaches 0.982 at `L=7, g=3` (P.4); `P5` reaches 98 at `g=10`); RBM2D has no BA chain (0 files mention "anderson", b.8), so only CT, FreeConv and the Main files port; the [RBSO1D] text is not in the repository, so the G group is priced from the band chain (widest spread, b.9).',
 '',
 '## (c) Verified Mathlib names (`#check`, exit 0; absent = `#check_failure` "Unknown constant"; `$S/names_check.lean`)',
 blk('python3 $S/oneline.py $S/names_check.out'),
 '',
 '## (d) Open issues and paper-delta candidates',
 'Paper-delta candidates (the dispatcher numbers them):',
 '- **T2161a** `GGGamma` (B:393-405): in the first two sums the coefficient `S^+_{xβ}` must be `(M^+S^+)_{xβ} = (1+M^+S^+)_{xβ} − δ_{xβ}` (b.7; `BAGGGamma` uses the corrected form; the third sum, `lanlw` and `lem_lweight` hold as printed).',
 '- **T2161b** bulk condition: `|E| ≤ e_λ − κ` (1_2:649, 7_8:1817) and `lem:propM`(2) `Im m ≳ 1` (7_8:1908) are undefined for odd `L`, empty at gaps, and `Im m = 0` at cusps; the probe uses `ρ_N ≥ κ` (top notice 1, b.3). Related: [RBSO1D] L3.9 appears only in comments (7_8:1844, 1846).',
 '- **T2161c** (convention) `B_{t,K}` (1_2:1107-1108) and `ℓ_t` (1_2:1121-1123) carry `ilambda`; in the BA flow the coupling is `g_0 = √t_0 g`; the probe keeps the model `g_n` (merged `Bparam`); the two agree up to the constant `t_0 ≥ κ/(κ+1)` (`Im m ≥ κ`, `Im z ≤ 1`); the paper does not say which.',
 'Open issues for the dispatcher: (1) Jun: the bulk form and the BA count (top notices); the ρ-bulk at a prescribed coupling stays uncompiled until BA-D2. (2) The Steps 3-6 carrier pins are not named here (BA-U1..V3); `BAMainInd` as the end of the chain is BA-V2 (priced, not designed). (3) LSY Thm 2.2 for the BA initial data is UN-D1 (T2162) and BA-N1; the [RBSO1D] text is unavailable, so the G group (%s lines central) has the widest spread. (4) `BAmUniqReal`, `BAmBoundary`, `BAImmLower` are owed pins of BA-D2, D6, D7: the audit should try them at `g → 0` and at a gap coupling (b.3, b.5).' % grab('ba_split2.out', r'^G\s+lem_GbEXP_BA chain\s+\d+ \|\s+\d+\s+(\d+)', 1, re.M),
    ]
    return out

def write_prove():
    out = prove_report()
    text = '\n'.join(out).rstrip('\n') + '\n'
    open(os.path.join(REP, 'T2161-prove.md'), 'w', encoding='utf-8').write(text)
    return text

# ====================================== the portmap ======================================
def cat(name, ind='    '):
    """verbatim content of a cached script output"""
    t = open(os.path.join(S, name), encoding='utf-8').read().rstrip('\n')
    return '\n'.join(ind + l if l else ind for l in t.split('\n'))
def shown(cmd, name, note=None, ind='    '):
    return '%s$ %s%s\n%s' % (ind, cmd, ('   # ' + note) if note else '', cat(name, ind))
RBM2D_FILES = ('RBM2D/Propagator/CombesThomasConjugation.lean RBM2D/Propagator/CombesThomasDistanceWeight.lean RBM2D/Propagator/CombesThomasExponentialWeight.lean '
 'RBM2D/Propagator/CombesThomasPerturbation.lean RBM2D/Propagator/CombesThomasWeightedInverse.lean RBM2D/Propagator/CombesThomasGapParameter.lean '
 'RBM2D/Propagator/CombesThomasKernelDecay.lean RBM2D/Propagator/CombesThomasFixedGap.lean RBM2D/Universality/FreeConv.lean RBM2D/Universality/FreeConvStability.lean '
 'RBM2D/Universality/Step1Band.lean RBM2D/Main/DecolFromLocal.lean RBM2D/Main/QUEFromQDiff.lean RBM2D/Main/RegionUnif.lean RBM2D/Endpoints.lean '
 'RBM2D/Main/Endpoints.lean RBM2D/Main/BUnivHolds.lean')
OWED_NAMES = ('BAmExists BAmUniqReal BAmBoundary BAWard BAPropM BAoffDiag BAImmLower BAProp5 BAProp5s BAProp6 BAProp7 BAProp8 BAProp5to8 BAMainInd BAGbEXP BAConArg BAStep1 '
 'BAStep2 BAEMn2Exp BAKsolve BAKbound BAlanlw BAlweight BAGGGamma BAEnd_locSC BAEnd_QDiff BAEnd_decol BAEnd_QUE BAEnd_BUniv BAThm27 BAGlueChain BAGlueLoc BAGlueQDiff BAGlueDecol BAGlueQUE BAGlueUniv')
BASE_NAMES = 'BASelf BAedgeBulk BAdistBulk BAbulk BAReal BAdom BAFlow BAendDom FlowFM bandFM baFM BAflowT0 BAflowE Thm27At'
STEPS = """    step                    paper                       BA change                                                     pins (this probe)                         tickets
    Step 1                  7_8:1987-1990               lem_GbEXP_BA 7_8:1916, lem_ConArg_BA 7_8:1956                 BAGbEXP, BAConArg, BAStep1               BA-G1..G6, S1..S3
    Step 2                  7_8:1993-2096               (eq:MG_conclusion3_BA) with a deterministic J (7_8:1999)      BAStep2, BAEMn2Exp                       BA-T1..T8
    Steps 3, 4              7_8:2100-2101               none ("extend verbatim")                                      ST pins over baFMz (16 ST*g forms)       BA-U1..U3
    Step 5 except Step5_larget  7_8:2100-2101           none                                                          ST Step 5 pins over baFMz                BA-U4, U6
    Step 5 sec:Step5_larget 7_8:2101 (3_5:2284, 1-t >= g^2)  uses lem_GbEXP_BA ([RBSO1D S7.3] parallel)               BAGbEXP consumed                          BA-U5
    Step 6                  7_8:2100-2101, B:286-525    lem:LWterm_EXP with GGGamma; graph layer (BA-L1..L4 of T2040)   BAlanlw, BAlweight, BAGGGamma           BA-L1..L4, V1
    chain induction in t    7_8:1825-1832               lem:main_ind_BA                                               BAMainInd (carrier pin STMainIndG), BAGlueChain  BA-V2
    from t_0 to Thm 2.7     7_8:1835, 1_2:672           zztE_BA, (eq:BtBt), (Kn2sol), net lemma, corollaries           BAGlue*, BAEnd_*, BAThm27                 BA-M1..M3, N1, N2"""
def write_portmap():
    t = now()
    out = []
    out += ['# T2161 portmap (BA-D1, block Anderson chain design): inventory, pins, bulk decision, constants, instances, routes, citations, split, scripts',
 'Written %s (`date -u`).  Probe `RBM3D/Probe/T2161Pins.lean` on branch `t/T2161`, commit `%s`, base `%s`, %s lines.  Companion of `docs/reports/T2161-prove.md` (section (b) points here as P.1-P.12).  The outputs below are the cached outputs of the displayed commands (`$S/final_run.sh` regenerates them; the scripts are in P.12); RBM2D is read at `c9a24cf` (T2002 O1), kept lines at `0c1330a`.  `S` = %s, `W` = %s.' % (t, head, base, PROBE_LINES, S, W), '',
 '## P.1 Inventory (item 1)',
 '### P.1a the statements of the paper that name the BA model (class: new / shared = BA by substitution / cited = cited-to-be-proved / band; part 3: text that is not a statement environment)',
 shown('python3 $S/inv_paper.py', 'inv_paper.out'),
 '### P.1b every `\\cite` of the BA part, active or commented out in the TeX',
 shown('python3 $S/inv_cites.py', 'inv_cites.out'),
 '### P.1c the merged RBM3D declarations that cover a piece of the BA chain (file:line in the worktree of `t/T2161`)',
 shown('python3 $S/inv_merged_ba.py', 'inv_merged_ba.out'),
 '### P.1d RBM2D files that can be ported (lines at `c9a24cf`, kept lines at `0c1330a`, `d = 2` tokens)',
 shown('python3 $S/inv_rbm2d.py', 'inv_rbm2d.out'),
 blk('git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- %s | tail -20' % RBM2D_FILES, note='the sources of the candidates, c9a24cf -> RBM2D HEAD'),
 '### P.1e cost structure of the merged chain (statements that hardwire the band model)',
 shown('python3 $S/decl_inv.py', 'decl_inv.out'),
 shown('python3 $S/file_gate.py', 'file_gate.out'),
 shown('python3 $S/pin_subst2.py', 'pin_subst2.out'),
 '', '## P.2 The pins (item 2)',
 '### P.2a registry class of every Prop-valued definition (DECISIONS §16, §20) and the index of the probe',
 shown('python3 $S/registry.py', 'registry.out'),
 shown('python3 $S/pin_index.py', 'pin_index.out'),
 '### P.2b pin -> paper map (the first paper line cited is printed to check the reference)',
 blk('python3 $S/pin_map.py'),
 '### P.2c which steps reuse the ST pins with `M` for `m` (paper 7_8:2100-2105) and which BA statements exist',
 STEPS,
 '### P.2d statements of the pins, extracted from the probe by script (`python3 $S/statements.py <names>`; docstrings stripped; they carry the paper cites)',
 blk('python3 $S/statements.py %s' % OWED_NAMES),
 '### P.2e the definitions the pins use (bulk forms, carrier, flow data, `Thm27At`)',
 blk('python3 $S/statements.py %s' % BASE_NAMES),
 '### P.2f the skeleton and the class instance (signatures)',
 blk("python3 $S/statements.py 'BAThm27_skeleton~' 'BAThm27_skeleton_chain~' 'inst_cls_Thm27_chain~' 'inst_cls_Thm27~' 'inst_cls_gaps~' 'inst_cls_odd~' 'inst_cls_interval~' 'inst_BAThm27_skeleton~'"),
 '', '## P.3 The bulk condition (T2001d/l): numerics beyond section (a)',
 'The four forms and the classes are in section (a) (scripts `ba_supp`, `ba_check`, `ba_gcL`, `ba_cusp`, `ba_vac`, `ba_det`, `ba_flow`, `ba_adm`, outputs pasted there; P.12 has their text).',
 shown('python3 $S/n1_immlower.py', 'n1_immlower.out', note='BAImmLower at the vacuity classes and two extremes'),
 shown('python3 $S/n1_equiv.py', 'n1_equiv.out', note='rho-form against the paper form: c1(kappa) = min rho_N on |E| <= e - kappa; c2 = min{e-|E| : rho >= 0.05}'),
 '', '## P.4 Exponent and constant table where `M ≠ mI` (item 4)',
 shown('python3 $S/n2_table.py', 'n2_table.out', note='r = (1-|m|^2)/min_t|1-t m^2|, Dk, lam1, |M_0e|, decay rate ct (j = 1, 2, 3) at bulk points'),
 '', '## P.5 Instances (item 7)',
 shown('python3 $S/instances_index.py', 'instances_index.out'),
 shown('python3 $S/cls_numerics.py', 'cls_numerics.out', note='the classes of 13.9: same formulas as `fp` / `exists_flowPt`'),
 shown('python3 $S/n5_flow_matrix.py', 'n5_flow_matrix.out', note='zztE_BA: the clauses of (eq:zztE_BA) and Ward at (g, z), L = 7'),
 '', '## P.6 Routes: the PT-BA pins and the K-loop equation at extremes',
 shown('python3 $S/n3_pt.py', 'n3_pt.out'),
 shown('python3 $S/n4_kn2.py', 'n4_kn2.out'),
 '', '## P.7 The graph-layer expansions (BA-L2)',
 shown('python3 $S/n6_lw.py', 'n6_lw.out', note='W = 1 (N = 3), exact Gauss-Hermite quadrature'),
 shown('python3 $S/n6_lw_mc.py', 'n6_lw_mc_full.out', note='W = 2, N = 6, 400000 samples'),
 shown('python3 $S/n6_lw_mc_printed.py', 'n6_lw_mc.out', note='GGGamma with the coefficient as printed'),
 '', '## P.8 External citations (item 3)',
 shown('python3 $S/cites_grouped.py', 'cites_grouped.out'),
 shown('python3 $S/cites_table.py full', 'cites_table_full.out'),
 '', '## P.9 The split table (item 6)',
 shown('python3 $S/ba_split2.py', 'ba_split2.out'),
 shown('python3 $S/ba_split2.py full', 'ba_split2_full.out'),
 '', '## P.10 Compiled facts and hygiene',
 shown('python3 $S/name_clash.py', 'name_clash.out'),
 '', '## P.11 Mathlib names (`#check` / `#check_failure` in `$S/names_check.lean`, exit 0)',
 blk('python3 $S/oneline.py $S/names_check.out'),
 shown('python3 $S/names_check.py', 'names_check_grep.out', note='grep of the declarations in Mathlib; #uses = occurrences in the probe'),
 '', '## P.12 Scripts (verbatim)']
    order = ['final_run.sh', 'ba_core.py', 'ba_supp.py', 'ba_det.py', 'ba_check.py', 'ba_gcL.py', 'ba_cusp.py', 'ba_vac.py', 'ba_flow.py', 'ba_adm.py',
             'n1_immlower.py', 'n1_equiv.py', 'n2_table.py', 'n3_pt.py', 'n4_kn2.py', 'n5_flow_matrix.py', 'n6_lw.py', 'n6_lw_mc.py', 'n6_lw_mc_printed.py', 'cls_numerics.py',
             'inv_paper.py', 'inv_paper_summary.py', 'inv_cites.py', 'inv_merged_ba.py', 'inv_merged_summary.py', 'inv_rbm2d.py', 'decl_inv.py', 'file_gate.py', 'pin_subst2.py',
             'pin_index.py', 'registry.py', 'pin_map.py', 'statements.py', 'instances_index.py', 'name_clash.py', 'names_check.py', 'names_check.lean', 'oneline.py',
             'ba_split2.py', 'cites_grouped.py', 'cites_table.py', 'build_report.py']
    for f in order:
        lang = 'bash' if f.endswith('.sh') else ('lean' if f.endswith('.lean') else 'python')
        body = open(os.path.join(S, f), encoding='utf-8').read().rstrip('\n')
        out += ['### %s' % f, '```' + lang, body, '```']
    text = '\n'.join(out) + '\n'
    open(os.path.join(REP, 'T2161-portmap.md'), 'w', encoding='utf-8').write(text)
    return text

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'both'
    if mode in ('prove', 'both'):
        tx = write_prove(); print('prove report lines:', len(tx.split('\n')) - 1)
    if mode in ('portmap', 'both'):
        tx = write_portmap(); print('portmap lines:', len(tx.split('\n')) - 1)
```
