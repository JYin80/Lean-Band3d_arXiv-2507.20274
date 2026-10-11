# T2398-TL-proofs: the twisted loop laws TL1, TL2 for the block Anderson model — statements and proofs

Companion to `T2398-fable.md` (unchanged). Author: Fable. Numbering: Lemmas T.1–T.12 below would sit in [P] §8 after Lemma 8.5 (p.72); they are stated in the setting of Theorem 8.2 (p.71). All page/equation numbers are [P]'s unless marked [68]. Notation of [P]: G_u = G_u(+), G_u(−) = G_u^*, M(+) = M, M(−) = M^*, G̊ = G − M, η_u = (1−u) Im m, B ≡ B_{u,0}, Ψ_u := (W^{-d}B_{u,0})^{1/2}; "≺" as in (1.13) p.8, uniform in all free indices.

## Summary for the supervisor (10 lines)

1. **TL1 (Lemma T.7).** In the setting of Theorem 8.2, for u ∈ [s,t], σ ∈ {±}, all blocks c1, c2: |Tr(G̊_u(σ)P_{c1c2})| ≺ W^{-d}B_{u,0}, and (E|Tr(G̊_u(σ)P_{c1c2})|^{2p})^{1/2p} ≤ C_pW^{ε}W^{-d}B_{u,0} for any fixed ε > 0. (P_{c1c2} = W^{-d}E^{(B)}_{c1c2} ⊗ I; c1 = c2 is (2.87).) Inputs: (2.87), (2.89) for n ≤ 4, Lemma 8.3; proof: one Gaussian integration by parts and a 2p-th moment bootstrap (§C). No [59].
2. **TL2 (Theorem T.12).** Let L̃_{u,σ,(a;c1,c2)} := Tr(G_u(σ1)E_aG_u(σ2)P_{c1c2}) and K̃_{u,σ,(a;c1,c2)} := W^{-d}Σ_{a'}Θ^{(σ1,σ2)}_u(a,a')M^{(B)}(σ1)_{c2a'}M^{(B)}(σ2)_{a'c1}. Fix ε0 > 0. If Theorem 8.2's hypotheses (2.77)–(2.81) hold at s together with (e): max_{σ,a,c1,c2}|L̃_s − K̃_s| ≺ (W^{-d}B_{s,0})^{2−ε0}, then for s < t with (2.82) (c_d possibly smaller) the same bound with the same exponent 2 − ε0 holds uniformly on [s,t] (Theorem T.12); the exponent does not deteriorate along the induction, and at s = 0 one has L̃_0 = K̃_0 exactly, so (TL2) with exponent 2 − ε0 holds at every time of the flow, for every fixed ε0 > 0. Exponent 3/2 is what (B.1) needs; both legs may be G or G̊ (Corollary T.13); c1, c2 are free.
3. **Use.** With TL1 and TL2 (exponent ≥ 3/2) the BA proof of (B.1) (p.87) is the transcription of (B.2)–(B.4) given in `T2398-fable.md` §3.3–§4; nothing else is needed.
4. **[P] results used**: (2.46)–(2.48) (Itô/loop hierarchy, derivation), (2.49)–(2.52), (2.53)–(2.56) (Ward), (2.57), (2.64)–(2.66), (2.70), (2.82), (2.84)–(2.90) (Steps 1–4 outputs on [s,t]), Lemma 3.2 (continuity), Lemma 3.6 (BDG; used with the one-index kernel Ũ and with Q^{(1)}Ũ), (3.11)–(3.14) (Duhamel), Lemma 4.1 (4.1)–(4.5), (4.9), Lemma 4.3 (4.12)–(4.16), Claim 4.5, Definition 4.7 and (4.26)–(4.32), (4.35), Definition 4.12, Lemma 4.13, Lemmas 4.15–4.17 ((4.51)–(4.57)), Lemma 8.3 ((8.4)–(8.6)), Lemma 8.4 (8.9), Lemma 6.1 (6.2) only in the application. Gaussian integration by parts for the matrix Brownian motion (2.35).

---

## A. Setting, objects, standing assumptions

**A.1 (Flow and inputs).** Fix d ≥ 3, κ, ε, 𝔠, 𝔡 as in Theorem 2.7, z ∈ D_{κ,ε} (8.3), the flow of Lemma 8.1 with (E, g0), g := g0 (so W^{-d/2+𝔡} ≤ g ≤ 𝔡^{-1} by (2.10)), H_u = gΨ + V_u with V_u = H_u − H_0 Gaussian, E|(V_u)_{xy}|² = uS_{xy}, S_{xy} = W^{-d}1([x] = [y]) (2.29), (2.35). G_u = (H_u − z_u)^{-1}, z_u = E + (1−u)m, M = (gΨ − E − m)^{-1} = M^{(B)} ⊗ I (2.33). Then
 G_u^{-1} = M^{-1} + V_u + um,  G̊_u = −G_u(V_u + um)M = −M(V_u + um)G_u,  S[M] = mI,                      (A.1)
where S[X]_{xy} = δ_{xy}Σ_wS_{xw}X_{ww} (2.40), so S[G̊] = Σ_c Tr(G̊E_c)1_{[c]}. Standing assumption throughout: the hypotheses (2.77)–(2.81) of Theorem 8.2 at s, and s < u ≤ t with (2.82); hence (Steps 1–4, pp.72–73 for BA): (2.84)–(2.90) hold uniformly in u ∈ [s,t], in particular
 (I1) ‖G_u − M‖_max ≺ Ψ_u, |(G_u−M)_{xy}|² ≺ W^{-d}B_{u,|x−y|/W} (2.86); (I2) max_a|Tr(G̊_uE_a)| ≺ W^{-d}B_{u,0} (2.87); (I3) max_{σ,a}|L^{(n)}_{u,σ,a}| ≺ (W^{-d}B_{u,0})^{n−1} (2.89), each fixed n; (I4) max|(L−K)^{(n)}_u| ≺ (W^{-d}B_{u,0})^n (2.90); (I5) the pointwise 2-loop estimate (2.88) (Step 2; with the factor ((1−s)/(1−u))^{C_d} and the tail e^{-(|a−b|/ℓ_u)^{1/2}}); (I6) the K-loop bounds (2.57), (4.9); (I7) Claim 4.5 (fast decay of L and K loops; for BA its proof uses (8.9) in place of (3.3)).
Deterministic facts: ‖G_u‖ ≤ η_u^{-1}; |m| ≤ 1, Im m ≥ κ' := κ'(κ, d, 𝔡) > 0 (Lemma 8.3(2): "Im m ≳ 1", constants depending on κ of (8.3) and on g ≤ 𝔡^{-1}; numerically κ' ≈ 0.044 at g = 10, which only enters constants); ‖M‖_{op} ≤ (Im m)^{-1} (M = (gΨ − E − m)^{-1}, gΨ − E real symmetric); Σ_b|M^{(B)}_{ab}|² = 1 (8.4); Σ_b|M^{(B)}_{ab}| ≤ C_M and |M^{(B)}_{ab}| ≤ C_Me^{-c_M|a−b|} with c_M, C_M depending on (d, κ, 𝔡) ((8.5)–(8.6); for g < (2C)^{-1} the bound (8.5) is used only as |M_{ab}| ≤ (Cg)^{|a−b|} ≤ 2^{-|a−b|}, never as a series in g); Θ-bounds (2.64)–(2.66).

**A.2 (Twists).** For c1, c2 ∈ Z^d_L let τ_{c1c2} := Σ_o |(c1,o)⟩⟨(c2,o)| (the offset-preserving partial isometry from block c2 onto block c1; τ_{c1c2}^* = τ_{c2c1}, τ_{c1c2}τ_{c2c1} = 1_{[c1]}) and
 P_{c1c2} := W^{-d}τ_{c1c2} = W^{-d}(E^{(B)}_{c1c2} ⊗ I_{W^d}),  so P_{cc} = E_c, P_{c1c2}^* = P_{c2c1}, Tr(XP_{c1c2}) = W^{-d}Σ_o X_{(c2,o),(c1,o)}, M = W^dΣ_{c1,c2}M^{(B)}_{c1c2}P_{c1c2}.
Since M is block-scalar, for any block-diagonal projection: P_{cc'}P_{c1c2} = W^{-d}δ_{c'c1}P_{cc2} and E_cM = Σ_{c'}M^{(B)}_{cc'}P_{cc'}.
**Twisted loops.** For n ≥ 1, σ ∈ {±}^n, a = (a_1,…,a_{n−1}) ∈ (Z^d_L)^{n−1}:
 L̃^{(n)}_{u,σ,a;(c1,c2)} := Tr( G_u(σ_1)E_{a_1}G_u(σ_2)E_{a_2}⋯G_u(σ_{n−1})E_{a_{n−1}}G_u(σ_n)P_{c1c2} ).                                   (A.2)
The twist occupies the n-th vertex. n = 1: L̃^{(1)}_{σ;(c1,c2)} = Tr(G(σ)P_{c1c2}); the *twisted light weight* is T̃_{u,σ;(c1,c2)} := Tr(G̊_u(σ)P_{c1c2}) = L̃^{(1)} − M^{(B)}(σ)_{c2c1}. n = 2: L̃_{u,σ,(a;c1,c2)} := L̃^{(2)}. Charges: for σ = (−,+), L̃ = Tr(G^*E_aGP_{c1c2}) = W^{-2d}Σ_{o}Σ_{x∈[a]}\overline{G_{x,(c2,o)}}G_{x,(c1,o)}. Twisted M-loops: M̃^{(n)}_{σ,a;(c1,c2)} := the same with M(σ_i) in place of G(σ_i); M̃^{(2)}_{σ,(a';c1,c2)} = W^{-d}M^{(B)}(σ1)_{c2a'}M^{(B)}(σ2)_{a'c1}.
**Relation circled/uncircled (used in the application only).** Tr(G(σ1)E_aG̊(σ2)P_{c1c2}) = L̃_{σ,(a;c1,c2)} − W^{-d}M^{(B)}(σ2)_{ac1}·L̃^{(1)}_{σ1;(a,c2)}  (because E_aM(σ2)P_{c1c2} = Σ_{c'}M(σ2)_{ac'}P_{ac'}P_{c1c2} = W^{-d}M(σ2)_{ac1}P_{ac2}), and L̃^{(1)}_{σ1;(a,c2)} = M^{(B)}(σ1)_{c2a} + T̃_{σ1;(a,c2)}.

**A.3 (Twisted K-loops).** K̃^{(n)}_{u,σ,a;(c1,c2)} is the solution of the convolution tree equation (2.49) with the actions (2.50) on the twisted index set, where in every cut (k,l) the left loop (G_L)_{k,l} (which contains the n-th vertex, Definition 2.12(2) p.13) is twisted and the right loop is an ordinary K-loop, with initial condition K̃_0 = M̃ (cf. (2.51)). For n = 2 (one cut (1,2), S^{(B)} = I):
 ∂_uK̃_{u,σ,(a;c1,c2)} = W^dΣ_b K̃_{u,σ,(b;c1,c2)}K^{(2)}_{u,σ,(a,b)},  K̃_0 = M̃^{(2)}.                                                   (A.3)

## B. Deterministic and algebraic lemmas

**Lemma T.1 (Twisted tree for n = 2).** For all u ∈ [0,1), σ, a, c1, c2:
 K̃_{u,σ,(a;c1,c2)} = Σ_{a'}Θ^{(σ1,σ2)}_u(a,a') M̃^{(2)}_{σ,(a';c1,c2)} = W^{-d}Σ_{a'}Θ^{(σ1,σ2)}_u(a,a')M^{(B)}(σ1)_{c2a'}M^{(B)}(σ2)_{a'c1}.           (B.1)
Moreover (i) |K̃_{u,σ,(a;c1,c2)}| ≤ C_dC_M² W^{-d}B_{u,|a−c1|}e^{-c_M|c1−c2|/2}; (ii) Σ_a|K̃_{u,σ,(a;c1,c2)}| ≤ W^{-d}(1−u)^{-1} = (Im m)(W^dη_u)^{-1}; (iii) K̃ satisfies the (u,ε,D)-decay property of Definition 4.4 (p.33) in the pair (a, c1): |K̃| ≤ W^{-D} if |a − c1| ≥ W^εℓ_u, for any ε, D > 0 and W ≥ W_0(ε,D).
*Proof.* With (2.70), K^{(2)}_{u,σ,(a,b)} = W^{-d}(Θ_uM^{(σ1σ2)})_{ab}; Θ_u = (1 − uM^{(σ1σ2)})^{-1} (S^{(B)} = I) and M^{(σ1σ2)} are symmetric and commute, so Θ_uM^{(σ1σ2)} is symmetric and ∂_uΘ_u = Θ_uM^{(σ1σ2)}Θ_u. The right side of (B.1), call it K̂_u, satisfies K̂_0 = M̃ and ∂_uK̂ = Θ_uM^{(σ1σ2)}Θ_uM̃ = Σ_b(Θ_uM^{(σ1σ2)})_{ab}K̂_b = W^dΣ_bK̂_bK^{(2)}_{(a,b)}, i.e. (A.3); by uniqueness (linear ODE) K̃ = K̂. (i): by (2.65), Θ_u(a,a') ≤ C_dB_{u,|a−a'|}e^{-c_d|a−a'|/ℓ_u} and |M_{c2a'}M_{a'c1}| ≤ C_M²e^{-c_M(|a'−c2|+|a'−c1|)}; since B_{u,|a−a'|} ≤ C(1+|a'−c1|)^{d−2}B_{u,|a−c1|} ((2.61)), Σ_{a'}B_{u,|a−a'|}e^{-c_M(|a'−c1|+|a'−c2|)} ≤ CB_{u,|a−c1|}e^{-c_M|c1−c2|/2}. (ii): Σ_a|Θ_u(a,a')| ≤ Σ_aΘ^{(+,−)}_u(a,a') = (1−u)^{-1} ((2.64) and the symmetry Θ(a,a') = Θ(a',a)), then Cauchy–Schwarz and (8.4): Σ_{a'}|M_{c2a'}||M_{a'c1}| ≤ 1. (iii): from (i) and the exponential factors of (2.65) and M (|a − c1| ≥ W^εℓ_u forces |a−a'| ≥ W^εℓ_u/2 or |a'−c1| ≥ W^εℓ_u/2). □
Constants: C_d, c_d of (2.65); C_M, c_M of (8.5)/(8.6); Im m ≥ κ'.

**Lemma T.2 (Folding: twisted loops are bounded by E-loops).** Let X_1, X_2 be N×N matrices and c1, c2 blocks. Then
 |Tr(X_1E_{a}X_2P_{c1c2})| ≤ ( Tr(E_{c2}X_1E_aX_1^*) · Tr(E_aX_2E_{c1}X_2^*) )^{1/2},                                                    (B.2)
 |Tr(X_1P_{c1c2}X_2P_{c1c2}^*)| ≤ ( Tr(E_{c1}X_1E_{c1}X_1^*) · Tr(E_{c2}X_2E_{c2}X_2^*) )^{1/2}.                                                    (B.3)
Consequently, for the twisted loop (A.2) and any 1 ≤ k ≤ n−1, with the folded index lists of (4.3) (p.30) in which a_n is replaced by c2 (resp. c1):
 |L̃^{(n)}_{σ,a;(c1,c2)}| ≤ ( L^{(2k)}_{σ¹,a¹}L^{(2n−2k)}_{σ²,a²} )^{1/2},  a¹ = (a_1,…,a_{k−1},a_k,a_{k−1},…,a_1,c2), σ¹ = (σ_1,…,σ_k,−σ_k,…,−σ_1),  a² = (a_{k+1},…,a_{n−1},c1,a_{n−1},…,a_{k+1},a_k), σ² = (σ_{k+1},…,σ_n,−σ_n,…,−σ_{k+1}).   (B.4)
In particular (F1) |L̃^{(n)}_u| ≺ (W^{-d}B_{u,0})^{n−1} by (I3); for n = 2, |L̃_{u,σ,(a;c1,c2)}| ≤ (L^{(2)}_{u,(σ1,−σ1),(a,c2)}L^{(2)}_{u,(σ2,−σ2),(c1,a)})^{1/2}; and loops with two twists P_{c1c2}, P_{c1c2}^* fold by (B.3) into two E-loops of the same total length, so they are ≺ (W^{-d}B)^{n−1} as well.
*Proof.* Tr(X_1E_aX_2P_{c1c2}) = W^{-2d}Σ_oΣ_{x∈[a]}(X_1)_{(c2,o),x}(X_2)_{x,(c1,o)}; Cauchy–Schwarz over (o,x) and Σ_{o,x}|(X_1)_{(c2,o),x}|² = W^{2d}Tr(E_{c2}X_1E_aX_1^*), Σ_{o,x}|(X_2)_{x,(c1,o)}|² = W^{2d}Tr(E_aX_2E_{c1}X_2^*). (B.3): Tr(X_1P_{c1c2}X_2P_{c2c1}) = W^{-2d}Σ_{o,o'}(X_2)_{(c2,o),(c2,o')}(X_1)_{(c1,o'),(c1,o)}, Cauchy–Schwarz over (o,o'). For (B.4) take X_1 = G(σ_1)E_{a_1}⋯G(σ_k), X_2 = G(σ_{k+1})E_{a_{k+1}}⋯G(σ_n), a = a_k, and read off the two traces as loops; both contain a_k between G(σ_k) and G(σ_k)^* = G(−σ_k). □

**Lemma T.3 (Ward identities at an untwisted vertex).** For n ≥ 2, 1 ≤ k ≤ n−1 and σ_k = −σ_{k+1}: Σ_{a_k}L̃^{(n)}_{u,σ,a;(c1,c2)} = (2iW^dη_u)^{-1}(L̃^{(n−1)}_{u,σ̂^{(+,k)},â^{(k)};(c1,c2)} − L̃^{(n−1)}_{u,σ̂^{(−,k)},â^{(k)};(c1,c2)}), with σ̂^{(±,k)} obtained from σ by deleting σ_{k+1} and replacing σ_k by ±, â^{(k)} by deleting a_k. For n = 2 and σ = (σ1,−σ1): Σ_aL̃_{u,σ,(a;c1,c2)} = (2iW^dη_u)^{-1}(L̃^{(1)}_{+;(c1,c2)} − L̃^{(1)}_{−;(c1,c2)}) = (2iW^dη_u)^{-1}(T̃_{+;(c1,c2)} − T̃_{−;(c1,c2)} + M^{(B)}_{c2c1} − M̄^{(B)}_{c2c1}).
*Proof.* Σ_{a_k}E_{a_k} = W^{-d}I and (2.53): G(σ_k)G(−σ_k) = (2iη_u)^{-1}(G(+) − G(−)) (for σ_k = +; the other sign gives the same expression). The twist is a fixed matrix and plays no role. □

**Lemma T.4 (Loop contraction for twisted loops; twin of Lemma 4.1).** For 1 ≤ k ≤ n−1 and any σ (no charge condition at a_k):
 max_σ Σ_{a_k} |L̃^{(n)}_{u,σ,a;(c1,c2)}| ≤ (W^dη_u)^{-1}( max_{σ',b}|L^{(2k−1)}_{u,σ',b}| · max_{σ',b}|L^{(2n−2k−1)}_{u,σ',b}| )^{1/2},                         (B.5)
and with the extra summation structure of (4.2) (n ≥ 4, k < j < l ≤ n−1, |A(a_n)| ≤ C, p ≥ 1) the same statement as (4.2) holds for twisted loops whenever the twists lie inside the three chains (which is the case for the quadratic-variation loops of T.11(iii), where it is also verified directly). In particular, for the twisted 3-loop: Σ_{a'}|L̃^{(3)}_{u,(σ1,σ2,σ3),(a',a);(c1,c2)}| ≤ (W^dη_u)^{-1}(max L^{(1)} · max L^{(3)})^{1/2} ≺ (W^dη_u)^{-1}(W^{-d}B_{u,0}).
*Proof.* Fold by (B.4) at a_k (the summed vertex) and at the twist; both folded loops are E-loops containing a_k between G(σ_k) and G(−σ_k). Then Cauchy–Schwarz in the sum over a_k and the Ward identity (2.55) at a_k in each folded loop, exactly (4.4)–(4.5): Σ_{a_k}(L^{(2k)}_{σ¹,a¹})^{1/2}(L^{(2n−2k)}_{σ²,a²})^{1/2} ≤ (Σ_{a_k}L^{(2k)})^{1/2}(Σ_{a_k}L^{(2n−2k)})^{1/2}, and Σ_{a_k}L^{(2k)}_{σ¹,a¹} = (2iW^dη)^{-1}(L^{(2k−1)} − L^{(2k−1)}) with the index lists of (4.5) (a_n ↦ c2), so |Σ_{a_k}L^{(2k)}| ≤ (W^dη)^{-1}max|L^{(2k−1)}|; similarly for the other factor (c1 in place of a_n). For (4.2): in its proof (pp.30–31) the loop is split at a_k, a_l, a_n into three chains; put the twist inside a chain (never at a split vertex, which is possible since the split vertices are summation vertices or a_n ≠ twist when we relabel so that the twist is in the chain C^{(l−k)}); the operator norm of the chain's block is bounded by Tr[(AA^*)^p]^{1/2p}, and AA^* for a chain containing P_{c1c2} is a loop containing P_{c1c2} and P_{c1c2}^*, which is ≤ an E-loop of the same length by (B.3). The rest of the proof is unchanged. □

**Lemma T.5 (Fast decay of twisted loops).** Assume (I1), (I5), (I7). For any fixed n, ε, D > 0, with probability 1 − O(W^{-D'}): |L̃^{(n)}_{u,σ,a;(c1,c2)}| ≤ W^{-D} whenever max(|a_i − a_j|, |a_i − c1|, |a_i − c2|, |c1 − c2|) ≥ W^εℓ_u over i,j ≤ n−1, and the same for the twisted loops with two twists appearing in the quadratic variation.
*Proof.* By (B.4) the loop is bounded by the geometric mean of two E-loops whose index lists contain all a_i together with c2, resp. c1; by Claim 4.5 (I7) each is ≤ W^{-D} when two of its indices are W^εℓ_u apart, and |c1 − c2| ≥ W^εℓ_u forces this in one of the two. □

**Lemma T.6 (≺ inside expectations).** Let X, Y be random with |X| ≤ N^{C_0} deterministically, Y ≥ 0 deterministic or random with E Y^2 < ∞, and X ≺ Y' for a deterministic Y' > N^{-C_1}. Then E[|X|Y] ≤ W^εY'E[Y] + N^{-D}(E Y²)^{1/2} for any ε, D > 0 and W ≥ W_0(ε,D). (Proof: split on the event {|X| ≤ W^εY'} of probability ≥ 1 − N^{-2D−2C_0}.) All resolvent quantities below satisfy |X| ≤ N^{C_0} since ‖G_u‖ ≤ η_u^{-1} ≤ N.

## C. TL1: the twisted averaged local law

**Lemma T.7 (TL1).** Under A.1 (inputs (I2), (I3) for n ∈ {2,4}, Lemma 8.3), for every fixed p ∈ N and ε > 0 there is C_p = C_p(d,κ,𝔡) such that, uniformly in u ∈ [s,t], σ ∈ {±} and all c1, c2 ∈ Z^d_L (c1 = c2 allowed),
 ( E|T̃_{u,σ;(c1,c2)}|^{2p} )^{1/2p} ≤ C_pW^ε W^{-d}B_{u,0}   for W ≥ W_0(p,ε),                                                (C.1)
and consequently |T̃_{u,σ;(c1,c2)}| = |Tr(G̊_u(σ)P_{c1c2})| ≺ W^{-d}B_{u,0}, uniformly in u ∈ [s,t], σ, c1, c2.                         (C.2)

*Proof.* By T̃_{−;(c1,c2)} = \overline{T̃_{+;(c2,c1)}} it suffices to take σ = +; write G = G_u, T̃ = T̃_{(c1,c2)}, P = P_{c1c2}, B = B_{u,0}.

*Step 1 (integration by parts).* For every smooth Φ = Φ(G) of polynomial growth,
 E[T̃ Φ] = u E[Tr(G S[G̊] M P) Φ] − u Σ_{x,w} S_{xw} E[(MPG)_{wx} ∂_{h_{wx}}Φ].                                                     (C.3)
Indeed, by (A.1), Tr(G̊P) = −Tr(GV_uMP) − um Tr(GMP) and Tr(GV_uMP) = Σ_{x,w}(V_u)_{xw}(MPG)_{wx}. The Gaussian integration by parts for the entries of V_u (E|(V_u)_{xw}|² = uS_{xw}, (V_u)_{wx} = \overline{(V_u)_{xw}}; for x = w a real Gaussian of variance uS_{xx}) reads E[(V_u)_{xw}F] = uS_{xw}E[∂_{h_{wx}}F], where ∂_{h_{wx}} is the derivative in the (w,x) entry of H, ∂_{h_{wx}}G = −Ge_we_x^TG. With F = (MPG)_{wx}Φ and ∂_{h_{wx}}(MPG)_{wx} = −(MPG)_{ww}G_{xx}: E[Tr(GV_uMP)Φ] = −uΣ_{x,w}S_{xw}E[(MPG)_{ww}G_{xx}Φ] + uΣ_{x,w}S_{xw}E[(MPG)_{wx}∂_{h_{wx}}Φ] = −uE[Tr(GS[G]MP)Φ] + uΣS_{xw}E[(MPG)_{wx}∂_{h_{wx}}Φ], using Σ_xS_{xw}G_{xx} = S[G]_{ww} and Tr(MPG S[G]) = Tr(GS[G]MP). Since S[G] = S[G̊] + m (A.1), the terms um Tr(GMP) cancel and (C.3) follows.

*Step 2 (the non-derivative term).* S[G̊] = W^dΣ_cTr(G̊E_c)E_c and E_cMP_{c1c2} = W^{-d}M^{(B)}_{cc1}P_{cc2} (A.2), hence
 Tr(GS[G̊]MP) = Σ_c Tr(G̊E_c) M^{(B)}_{cc1} L̃^{(1)}_{+;(c,c2)} = Σ_c Tr(G̊E_c) M^{(B)}_{cc1}( M^{(B)}_{c2c} + T̃_{(c,c2)} ).                       (C.4)

*Step 3 (the derivative term for Φ = T̃^{p−1}\bar T̃^p).* ∂_{h_{wx}}T̃ = −(GPG)_{xw}, ∂_{h_{wx}}\bar T̃ = \overline{∂_{h_{xw}}T̃} = −\overline{(GPG)_{wx}}, so
 Σ_{x,w}S_{xw}(MPG)_{wx}∂_{h_{wx}}Φ = −(p−1) 𝒮_1 T̃^{p−2}\bar T̃^p − p 𝒮_2 |T̃|^{2p−2},  𝒮_1 := Σ_{x,w}S_{xw}(MPG)_{wx}(GPG)_{xw},  𝒮_2 := Σ_{x,w}S_{xw}(MPG)_{wx}\overline{(GPG)_{wx}}.  (C.5)

*Step 4 (|𝒮_1| + |𝒮_2| ≺ C_M(W^{-d}B)²).* With w = (c,o'), x ∈ [c]: (MPG)_{wx} = W^{-d}M^{(B)}_{cc1}G_{(c2,o'),x}, (GPG)_{xw} = W^{-d}Σ_oG_{x,(c1,o)}G_{(c2,o),w}, \overline{(GPG)_{wx}} = W^{-d}Σ_o\overline{G_{w,(c1,o)}G_{(c2,o),x}}. Summing x ∈ [c] first (S_{xw} = W^{-d}1(x ∈ [c])):
 𝒮_2 = W^{-2d}Σ_c M^{(B)}_{cc1} Σ_{o',o} (GE_cG^*)_{(c2,o'),(c2,o)} \overline{G_{(c,o'),(c1,o)}},   𝒮_1 = W^{-2d}Σ_c M^{(B)}_{cc1} Σ_{o',o} (GE_cG)_{(c2,o'),(c1,o)} G_{(c2,o),(c,o')}.
Cauchy–Schwarz in (o',o) and Σ_{o',o}|X_{(b,o'),(b',o)}|² = W^{2d}Tr(E_bXE_{b'}X^*) give
 |𝒮_2| ≤ Σ_c|M^{(B)}_{cc1}| ( L^{(4)}_{u,(+,−,+,−),(c,c2,c,c2)} · L^{(2)}_{u,(+,−),(c1,c)} )^{1/2},  |𝒮_1| ≤ Σ_c|M^{(B)}_{cc1}| ( L^{(4)}_{u,(+,+,−,−),(c,c1,c,c2)} · L^{(2)}_{u,(+,−),(c,c2)} )^{1/2},
and (I3) with n = 4, 2 and Σ_c|M^{(B)}_{cc1}| ≤ C_M yield |𝒮_i| ≺ C_M(W^{-d}B)^{3/2+1/2} = C_M(W^{-d}B)², uniformly in c1, c2.

*Step 5 (moment bootstrap).* Let X_{c1c2} := (E|T̃_{(c1,c2)}|^{2p})^{1/2p} and X := max_{c1,c2}X_{c1c2} (a maximum over L^{2d} pairs; X ≤ η_u^{-1} + 1 < N). Apply (C.3) with Φ = T̃_{(c1,c2)}^{p−1}\bar T̃_{(c1,c2)}^p and insert (C.4), (C.5):
 E|T̃_{(c1,c2)}|^{2p} = uΣ_cM^{(B)}_{cc1}E[Tr(G̊E_c)(M^{(B)}_{c2c} + T̃_{(c,c2)})Φ] + u(p−1)E[𝒮_1T̃^{p−2}\bar T̃^p] + upE[𝒮_2|T̃|^{2p−2}].
By Lemma T.6 with (I2) (|Tr(G̊E_c)| ≺ W^{-d}B), |M^{(B)}_{c2c}| ≤ 1, Hölder (E[|T̃_{(c,c2)}||T̃_{(c1,c2)}|^{2p−1}] ≤ X_{cc2}X_{c1c2}^{2p−1}) and Step 4:
 X_{c1c2}^{2p} ≤ C_MW^{ε}(W^{-d}B)( X_{c1c2}^{2p−1} + X X_{c1c2}^{2p−1} ) + 2pC_MW^ε(W^{-d}B)² X_{c1c2}^{2p−2} + N^{-D}.
Take (c1,c2) attaining X. Since W^{-d}B_{u,0} ≤ W^{-d}g^{-2} + (Nη_u)^{-1} ≤ W^{-2𝔡} + N^{-ε}(Im m)^{-1}... ≤ W^{-𝔡} for W ≥ W_0 (by (2.10), (8.3), (2.9)), choose ε < 𝔡/2 so that C_MW^εW^{-d}B ≤ 1/2; then X^{2p} ≤ 2C_MW^ε(W^{-d}B)X^{2p−1} + 4pC_MW^ε(W^{-d}B)²X^{2p−2} + 2N^{-D}, i.e. X² ≤ αX + β with α = 2C_MW^εW^{-d}B, β = 4pC_MW^ε(W^{-d}B)² + 2N^{-D}X^{2−2p}; if X ≤ W^{-d}B we are done, otherwise N^{-D}X^{2−2p} ≤ N^{-D}, and X ≤ α + √β ≤ (2C_M + 2√(pC_M))W^εW^{-d}B + 2N^{-D/2}, which is (C.1).

*Step 6 (high probability).* By Markov, P(|T̃_{(c1,c2)}| > W^{2ε}W^{-d}B) ≤ (C_pW^{-ε})^{2p} ≤ W^{-D} for p ≥ D/ε + 1; a union bound over the L^{2d} ≤ N² pairs, the two signs, and the standard N^{-C}-net in u combined with the continuity estimate of Lemma 3.2 / Lemma 8.5 (as for every estimate of Theorem 8.2, p.18 last paragraph) give (C.2). □

Constants: C_M (row-ℓ¹ of M^{(B)}, (8.5)/(8.6)), the constants of (I2), (I3) for n ≤ 4, Im m ≥ κ', and 𝔡 (smallness of W^{-d}B). No smallness of g; no series in g.

**Remark C.1.** (a) (C.1) also gives E|T̃| ≤ C W^εW^{-d}B, used in D.7 and D.8 for the centred quantity T̃ − E T̃. (b) The proof is the n = 1 case of a general mechanism: one integration by parts turns a twisted loop into "light weight × twisted loop" plus loops that are two orders smaller; only the sharp E-loop bounds (I2)–(I3) enter. (c) The identity (C.3) is the trace form of [68] Lemma B.9 ((B.15), p.89) without the multiplication by M, which is what avoids any new M-tie.

## D. TL2: the twisted 2-loop law

Throughout D, σ = (σ1,σ2) is fixed, G_k := G_u(σ_k), G̊_k := G̊_u(σ_k), P := P_{c1c2}, L̃_u(a) := L̃_{u,σ,(a;c1,c2)}, K̃_u(a) := K̃_{u,σ,(a;c1,c2)}, Z_u(a) := L̃_u(a) − K̃_u(a). Dependence on (c1,c2) is suppressed; all bounds are uniform in (c1,c2).

### D.1 The twisted loop hierarchy (twin of Lemma 2.13 for n = 2)

**Lemma T.8.** Under (2.35), for every a:
 dL̃_u(a) = dẼ^M_u(a) + Ẽ^{G̊}_u(a)du + W^dΣ_b L̃_u(b) L^{(2)}_{u,σ,(a,b)} du,                                                              (D.1)
 dẼ^M_u(a) := Σ_{x,y}∂_{xy}L̃_u(a)·√S_{xy} d(B_u)_{xy},  ∂_{xy}L̃_u(a) = −(G_1E_aG_2PG_1)_{yx} − (G_2PG_1E_aG_2)_{yx},                 (D.2)
 Ẽ^{G̊}_u(a) := W^dΣ_{a'}[ Tr(G̊_1E_{a'}) L̃^{(3)}_{u,(σ1,σ1,σ2),(a',a);(c1,c2)} + Tr(G̊_2E_{a'}) L̃^{(3)}_{u,(σ1,σ2,σ2),(a,a');(c1,c2)} ].     (D.3)
*Proof.* Itô's formula for G_u = (H_u − z_u)^{-1} with dz_u = −m du and d(H_u)_{xy} = √S_{xy}d(B_u)_{xy}: dG = −G dH G + (dz_u)G² + G dH G dH G, and the quadratic variation of the complex matrix Brownian motion gives (G dH G dH G)_{xy} = Σ_{w}S_{xw}G_{xx}... precisely d(H)_{xw}d(H)_{w'y} = S_{xw}δ_{xy}δ_{ww'}du, hence G dH G dH G = G S[G] G du and dG = −G dH G + G S[G̊] G du (since G S[G] G = G S[G̊] G + mG²). The same holds for G^* = G(−) with S[G̊^*]. For the product, d(G_1E_aG_2P) = (dG_1)E_aG_2P + G_1E_a(dG_2)P + (dG_1)E_a(dG_2)P. Taking traces: the first-order parts of the first two terms give dẼ^M (by ∂_{h_{xy}}G = −Ge_xe_y^TG, which yields (D.2)); the S[G̊]-parts give Tr(G_1S[G̊_1]G_1E_aG_2P) + Tr(G_1E_aG_2S[G̊_2]G_2P), which is (D.3) by S[G̊_k] = W^dΣ_{a'}Tr(G̊_kE_{a'})E_{a'}; the cross term (G_1dHG_1)E_a(G_2dHG_2)P contracts to Σ_{x,w}S_{xw}(G_1E_aG_2)_{ww}(G_2PG_1)_{xx}du = W^dΣ_bTr(G_1E_aG_2E_b)Tr(G_2PG_1E_b)du = W^dΣ_bL^{(2)}_{(a,b)}L̃(b)du, which is the last term of (D.1) (it is the term k = 1, l = 2 of (2.46): the left loop (G_L)_{1,2}∘L̃ = L̃(b) carries the twist, the right loop (G_R)_{1,2} = L^{(2)}_{(a,b)} is ordinary, S^{(B)}_{ab} = δ_{ab}). □
(For general n the same computation gives (2.46)–(2.48) with the left loop twisted in every cut; only n = 2 is used.)

### D.2 Linearisation and Duhamel form

**Lemma T.9.** With Θ̃_u∘A := Σ_b(Θ_uM^{(σ1σ2)})_{ab}A(b) = W^dΣ_bK^{(2)}_{u,σ,(a,b)}A(b) (the i = 1 summand of (3.11)),
 dZ_u = (Θ̃_u∘Z_u) du + B̃_1(u)du + B̃_2(u)du + Ẽ^{G̊}_u du + dẼ^M_u,   B̃_1(u)(a) := W^dΣ_bK̃_u(b)(L−K)^{(2)}_{u,σ,(a,b)},  B̃_2(u)(a) := W^dΣ_bZ_u(b)(L−K)^{(2)}_{u,σ,(a,b)}, (D.4)
and for s ≤ u, with the one-index evolution kernel Ũ_{v,u} := (1 − vM^{(σ1σ2)})(1 − uM^{(σ1σ2)})^{-1} = I + (u−v)M^{(σ1σ2)}Θ_u (the i = 1 factor of (3.12), cf. (A.6)):
 Z_u = Ũ_{s,u}∘Z_s + ∫_s^u Ũ_{v,u}∘( B̃_1(v) + B̃_2(v) + Ẽ^{G̊}_v ) dv + ∫_s^u Ũ_{v,u}∘dẼ^M_v.                                        (D.5)
*Proof.* Subtract (A.3) from (D.1) and write L̃L^{(2)} − K̃K^{(2)} = K̃(L−K) + ZK + Z(L−K). Duhamel: ∂_uŨ_{v,u} = Θ_uM^{(σ1σ2)}Ũ_{v,u} = Θ̃_u∘Ũ_{v,u} since ∂_uΘ_u = Θ_uM^{(σ1σ2)}Θ_u; (D.5) is the integrated form of (D.4) as in Lemma 3.4 (p.20). □

### D.3 One-index kernel estimates (twins of Lemmas 4.15–4.17 with one factor)

**Lemma T.10.** Let A : Z^d_L → C, 0 ≤ v ≤ u < 1, Ξ := (u−v)M^{(σ1σ2)}Θ_u, so Ũ_{v,u} = I + Ξ.
 (a) ‖Ũ_{v,u}∘A‖_∞ ≤ ((1−v)/(1−u))‖A‖_∞. [(A.7): Σ_b|Ξ_{ab}| ≤ (u−v)‖M^{(σ1σ2)}‖_{∞→∞}‖Θ_u‖_{∞→∞} ≤ (u−v)(1−u)^{-1}, using Σ_b|M^{(σ1σ2)}_{ab}| = Σ_b|M^{(B)}_{ab}|² = 1 (8.4) and (2.64).]
 (b) (external centre c1, regime u ≤ 1 − g²/L², (1−u)/(1−v) ≥ W^{-1}.) If |A(b)| ≤ W^{-D} for all b with |b − c1| ≥ W^εℓ_v, then
  ‖Ũ_{v,u}∘A‖_∞ ≤ ( 1 + C_1W^{2ε}(g²+1−v)/(g²+1−u) )‖A‖_∞ + W^{-D+1},   C_1 = C_1(d,κ,𝔡).                                                   (D.6)
 (c) If σ1 = σ2: ‖Ũ_{v,u}∘A‖_∞ ≤ C_2‖A‖_∞ with C_2 = 1 + C_κ(1 + 𝔡^{-2}C) from (2.66), for all v ≤ u, no decay needed.
 (d) (zero mode, regime 1 − g²/L² ≤ v ≤ u.) With P^{(1)}A := L^{-d}Σ_bA(b) and Q^{(1)} := I − P^{(1)} (Definition 4.12 with n = 1): Q^{(1)} commutes with Ũ_{v,u} and ‖Q^{(1)}Ũ_{v,u}∘A‖_∞ ≺ ‖A‖_∞ for σ1 ≠ σ2; for σ1 = σ2, (c) applies.
*Proof.* (a) is (A.6)–(A.7) for one factor. (b): Ũ∘A(a) = A(a) + Σ_bΞ_{ab}A(b). Split the sum at |b − c1| < W^εℓ_v. By (A.9) (which for BA uses (2.65) and (8.5)/(8.6)), |Ξ_{ab}| ≤ C(1−v)(g²+1−u)^{-1}(|a−b|+1)^{-(d−2)}e^{-c|a−b|/ℓ_u} (in the regime u ≤ 1 − g²/L² the zero-mode part of B_{u,|a−b|} is dominated by the polynomial part, (4.18)), so Σ_{|b−c1|<W^εℓ_v}|Ξ_{ab}| ≤ C(1−v)(g²+1−u)^{-1}Σ_{|b−c1|<W^εℓ_v}(|a−b|+1)^{-(d−2)} ≤ C(1−v)(g²+1−u)^{-1}(W^εℓ_v)² ≤ CW^{2ε}(g²+1−v)/(g²+1−u), the last step by (A.12) (1−v)ℓ_v² ≍ g²+1−v for v ≤ 1−g²/L². The far part is ≤ W^{-D}Σ_b|Ξ_{ab}| ≤ W^{-D}(1−v)/(1−u) ≤ W^{-D+1}. (c): Σ_b|Ξ_{ab}| ≤ (u−v)Σ_{b}|M^{(+,+)}_{ab'}||Θ^{(+,+)}_u(b',b)| ≤ Σ_{b'}|M_{ab'}|²·C_κ(1 + g²Σ_be^{-c_κ|b'−b|}) ≤ C_2 − 1 by (2.66) and (8.4). (d): Q^{(1)} is the projection Proj_{e⊥} of the proof of Lemma 4.17 (p.78), which commutes with the translation-invariant M^{(σ1σ2)}; for σ1 ≠ σ2, Proj_{e⊥}Ξ = (u−v)M^{(+,−)}Θ̊^{(+,−)}_u and ‖Proj_{e⊥}Ξ‖_{∞→∞} ≺ (1−v)g^{-2}L² ≤ 1 by (2.69) and (8.4) ((A.21)); hence ‖Q^{(1)}Ũ‖_{∞→∞} ≤ ‖Proj_{e⊥}(I + Ξ)‖ ≺ 1. □
Remark: (b) is the one-index case of (A.10)–(A.11) with the decay measured from the fixed centre c1 instead of from the first loop index; this is why no sum-zero mollifier (Definition 4.7) is needed for the twisted 2-loop: the twist supplies an external anchor that the kernel does not move. The tensor-product kernel Ũ_{v,u} ⊗ Ũ_{v,u} on functions of (a,a') (as in (3.18)) satisfies the product of the one-index bounds when the decay holds in each index separately.

### D.4 The sources

**Lemma T.11 (bounds and decay of the sources).** Under A.1 and, for (iv)–(v), the a priori bound ‖Z_v‖_∞ ≤ Ξ̃·(W^{-d}B_{v,0})^{γ_*} on [s,u] for some γ_* ∈ [1,2] and Ξ̃ ≥ 1, the following hold uniformly in v ∈ [s,u], a, c1, c2, w.h.p.:
 (i) |B̃_1(v)(a)| ≺ η_v^{-1}(W^{-d}B_{v,0})²;
 (ii) |Ẽ^{G̊}_v(a)| ≺ η_v^{-1}(W^{-d}B_{v,0})²;
 (iii) (quadratic variation) Q_v(b) := Σ_{x,y}S_{xy}|∂_{xy}L̃_v(b)|² ≺ η_v^{-1}(W^{-d}B_{v,0})^{4−1/(2p)−1/q} for any fixed p, q ∈ N, and (Ẽ⊗Ẽ)_v(b,b') := Σ_{x,y}S_{xy}∂_{xy}L̃_v(b)\overline{∂_{xy}L̃_v(b')} satisfies |(Ẽ⊗Ẽ)_v(b,b')| ≤ (Q_v(b)Q_v(b'))^{1/2};
 (iv) |B̃_2(v)(a)| ≺ Ξ̃·η_v^{-1}(W^{-d}B_{v,0})^{γ_*+1/6};
 (v) each of B̃_1(v), B̃_2(v), Ẽ^{G̊}_v, Z_v, and (Ẽ⊗Ẽ)_v in each of its two indices, satisfies the decay property |·| ≤ W^{-D} when |a − c1| ≥ 3W^εℓ_v, for any ε, D (w.h.p.).
*Proof.* (i) |B̃_1(a)| ≤ W^d max_b|(L−K)^{(2)}_{v,(a,b)}|·Σ_b|K̃_v(b)| ≺ W^d(W^{-d}B)²·(W^dη_v)^{-1} by (I4) and Lemma T.1(ii).
(ii) First term of (D.3): |Tr(G̊_1E_{a'})| ≺ W^{-d}B uniformly (I2), and Σ_{a'}|L̃^{(3)}_{(σ1,σ1,σ2),(a',a);(c1,c2)}| ≤ (W^dη_v)^{-1}(max|L^{(1)}|·max|L^{(3)}|)^{1/2} ≺ (W^dη_v)^{-1}(W^{-d}B) by Lemma T.4 (fold at a' = a_1 and at the twist: folded loops of lengths 2 and 4, Ward at a' in both, (I3) for n = 1, 3). Hence the term is ≺ W^d·W^{-d}B·(W^dη)^{-1}W^{-d}B = η^{-1}(W^{-d}B)². The second term: fold at a' = a_2 and the twist (lengths 4 and 2); same bound.
(iii) Let C_1 := G_1E_bG_2PG_1 and C_2 := G_2PG_1E_bG_2, so Q(b) ≤ 2Σ_{x,y}S_{xy}(|(C_1)_{yx}|² + |(C_2)_{yx}|²) = 2W^dΣ_c[Tr(E_cC_1E_cC_1^*) + Tr(E_cC_2E_cC_2^*)]. We follow the proof of (4.2) (pp.30–31). *C_1:* Tr(E_cC_1E_cC_1^*) = W^{-3d}Σ_{x_1∈[c],x_2∈[b],x_6∈[b]}(G_1)_{x_1x_2}𝒜_{x_2x_6}(G_1^*)_{x_6x_1} with 𝒜 := G_2PG_1E_cG_1^*P^*G_2^* (the factors W^{-d} of P, E_c, P^* are inside 𝒜). Cauchy–Schwarz in (x_2,x_6) with the operator norm of the [b]×[b] block 𝒜_{bb}, then Cauchy–Schwarz in x_1 and the sum over c (Ward (2.54) at x_2):
 W^dΣ_cTr(E_cC_1E_cC_1^*) ≤ W^{-2d}·max_c‖𝒜_{bb}‖_{op}·Σ_{x_1}(Σ_{x_2∈[b]}|(G_1)_{x_1x_2}|²)^{1/2}(Σ_{x_6∈[b]}|(G_1)_{x_1x_6}|²)^{1/2} ≤ W^{-2d}max_c‖𝒜_{bb}‖_{op}·Σ_{x_2∈[b]}Im(G_1)_{x_2x_2}/η_v ≤ C W^{-d}η_v^{-1}max_c‖𝒜_{bb}‖_{op}.
Now 𝒜 = YY^* with Y := G_2PG_1E_c^{1/2}, so 𝒜_{bb} = (1_{[b]}Y)(1_{[b]}Y)^* and ‖𝒜_{bb}‖_{op} = ‖Y^*1_{[b]}Y‖_{op} = W^d‖E_c^{1/2}G_1^*(P^*𝒲P)G_1E_c^{1/2}‖_{op} with 𝒲 := G_2^*E_bG_2 ≥ 0 and P^*𝒲P = W^{-2d}τ_{c2c1}𝒲τ_{c1c2} ≤ W^{-2d}‖𝒲_{c1c1}‖_{op}1_{[c2]} = W^{-d}‖𝒲_{c1c1}‖_{op}E_{c2} (𝒲_{c1c1} = the [c1]×[c1] block of 𝒲). By monotonicity of R ↦ R^*ZR and of the operator norm on positive matrices,
 ‖𝒜_{bb}‖_{op} ≤ ‖𝒲_{c1c1}‖_{op}·‖E_c^{1/2}G_1^*E_{c2}G_1E_c^{1/2}‖_{op} ≤ Tr[(𝒲_{c1c1})^q]^{1/q}·Tr[(E_cG_1^*E_{c2}G_1)^p]^{1/p} = (W^{qd}L^{(2q)}_{v,(−σ2,σ2,…),(b,c1,…,b,c1)})^{1/q}·(L^{(2p)}_{v,(−σ1,σ1,…),(c2,c,…,c2,c)})^{1/p},
both loops being alternating (hence ≥ 0). With (I3): ‖𝒜_{bb}‖_{op} ≺ W^d(W^{-d}B)^{(2q−1)/q}(W^{-d}B)^{(2p−1)/p} = W^d(W^{-d}B)^{4−1/p−1/q}. Therefore W^dΣ_cTr(E_cC_1E_cC_1^*) ≺ η_v^{-1}(W^{-d}B)^{4−1/p−1/q}, and relabelling p ↦ 2p gives the claim. *C_2:* split at x_1 ∈ [c] (summed), x_2, x_6 ∈ [b]: the outer chains are G_2PG_1 and G_1^*P^*G_2^* (twist inside), the middle chain is G_2E_cG_2^*. Cauchy–Schwarz in x_1 and Σ_c gives Σ_{x_1}(Σ_{x_2}|(G_2PG_1)_{x_1x_2}|²)^{1/2}(…)^{1/2} ≤ W^d Tr(G_2PG_1E_bG_1^*P^*G_2^*)·… = W^d(2η_v)^{-1}|Tr((G_2 − G_2^*)P[G_1E_bG_1^*]P^*)| ≤ W^dη_v^{-1}max_±(L^{(2)}_{(c1,c1)}L^{(4)}_{(b,c2,b,c2)})^{1/2} ≺ W^dη_v^{-1}(W^{-d}B)² by (2.53) and (B.3); the middle block satisfies W^{-d}‖(G_2E_cG_2^*)_{bb}‖_{op} ≤ (max L^{(4p)})^{1/2p} ≺ (W^{-d}B)^{2−1/(2p)} as in (4.8). Hence W^dΣ_cTr(E_cC_2E_cC_2^*) ≺ W^d·W^{-3d}·W^dη^{-1}(W^{-d}B)²·W^d(W^{-d}B)^{2−1/2p} = η_v^{-1}(W^{-d}B)^{4−1/2p}. The bound on (Ẽ⊗Ẽ) is Cauchy–Schwarz in (x,y) for the inner product Σ_{x,y}S_{xy}(·)(·̄).
(iv) |B̃_2(a)| ≤ ‖Z_v‖_∞·W^dΣ_b|(L−K)^{(2)}_{v,(a,b)}| ≺ Ξ̃(W^{-d}B)^{γ_*}·η_v^{-1}(W^{-d}B)^{1/6} by (4.16) (p.33; it holds for all v ∈ [s,t] under (2.82) once c_d ≤ c_d(C_d) is small).
(v) K̃: Lemma T.1(iii). L̃ (hence Z): Lemma T.5. B̃_1(a): for |a − c1| ≥ 3W^εℓ each summand has |b − c1| ≥ W^εℓ (then |K̃(b)| ≤ W^{-D}) or |a − b| ≥ W^εℓ (then |(L−K)_{(a,b)}| ≤ W^{-D} by (I7)); same for B̃_2 and, by Lemma T.5 applied to the 3-loops (indices a', a, c1, c2) and to the 6-loops of (iii), for Ẽ^{G̊} and (Ẽ⊗Ẽ). □
Constants: (I2)–(I4), (I7), (4.16) (needs (2.82) with c_d small), Im m ≥ κ', C_M. Lemma T.11(iii) is the only place where the Schatten trick of (4.8) is used; its loss (W^{-d}B)^{-1/q} is arbitrary.

### D.5 The Grönwall-free closing estimate

**Proposition T.12' (one induction step).** Under A.1, fix p, q ∈ N, ε > 0 and γ ∈ [1, 2], and suppose
 (e_s)  max_{σ,a,c1,c2}|Z_s(a)| = max|L̃_s − K̃_s| ≺ (W^{-d}B_{s,0})^{γ}.
Then, with γ_* := min{γ, 2 − 1/(4p) − 1/(2q)}, uniformly in u ∈ [s,t], σ, a, c1, c2:
 |Z_u(a)| ≺ (W^{-d}B_{u,0})^{γ_*}.                                                                                                     (D.7)
*Proof.* Write Ξ̃_u := sup_{v∈[s,u]}max_{σ,a,c1,c2}|Z_v(a)|(W^{-d}B_{v,0})^{−γ_*}; by (F1) and T.1(i), Ξ̃ ≤ N^C a priori. Fix u ∈ [s,t] and (a,c1,c2). We bound the four terms of (D.5), in each of the two regimes of Section 4.1–4.2 (p.33, 38; footnote 6: if 1−t < g²/L² < 1−s insert the time 1 − g²/L² and treat the two pieces in turn, the output (D.7) of the first piece being the input (e) of the second).

*Case σ1 = σ2 (any regime).* By T.10(c), ‖Ũ_{v,u}‖_{∞→∞} ≤ C_2. Hence |Ũ_{s,u}∘Z_s| ≤ C_2‖Z_s‖ ≺ (W^{-d}B_{s,0})^γ ≤ (W^{-d}B_{u,0})^γ (B_{·,0} is increasing); ∫_s^u‖Ũ∘(B̃_1 + Ẽ^{G̊})‖dv ≺ C_2∫_s^uη_v^{-1}(W^{-d}B_{v,0})²dv ≤ C_2(Im m)^{-1}W^{-2d}B_{u,0}²·log((1−s)/(1−u)) ≺ (W^{-d}B_{u,0})² by T.11(i)–(ii) (B_{v,0} ≤ B_{u,0}, log((1−s)/(1−u)) ≤ c_d log(W^{-d}B_{t,0})^{-1} ≤ C log W by (2.82)); ∫_s^u‖Ũ∘B̃_2‖dv ≺ Ξ̃_u(W^{-d}B_{u,0})^{γ_*+1/6}log W by T.11(iv). Martingale: by Lemma 3.6 (3.18) (valid for any deterministic kernel; the proof is the BDG inequality), for p' ∈ N,
 E|∫_s^uŨ_{v,u}∘dẼ^M_v(a)|^{2p'} ≤ C_{p'}E[∫_s^u((Ũ_{v,u}⊗Ũ_{v,u})∘(Ẽ⊗Ẽ)_v)(a,a)dv]^{p'} ≤ C_{p'}C_2^{2p'}E[∫_s^u max_{b,b'}|(Ẽ⊗Ẽ)_v(b,b')|dv]^{p'} ≤ C'(W^ε(W^{-d}B_{u,0})^{4−1/(2p)−1/q}log W)^{p'} + N^{-D}
by T.11(iii) and Lemma T.6 (the deterministic bound |(Ẽ⊗Ẽ)| ≤ N^C on the bad event), whence by Markov |∫Ũ∘dẼ^M(a)| ≺ (W^{-d}B_{u,0})^{2−1/(4p)−1/(2q)} for the fixed (u,a,c1,c2). Collecting, |Z_u(a)| ≺ (W^{-d}B_{u,0})^γ + (W^{-d}B_{u,0})² + (W^{-d}B_{u,0})^{2−1/(4p)−1/(2q)} + Ξ̃_u(W^{-d}B_{u,0})^{γ_*+1/6}.

*Case σ1 ≠ σ2, regime (i): 1−t ≥ g²/L².* All sources and Z_s have the decay property of T.11(v) centred at c1 at scale W^εℓ_v (for Z_s: T.5 and T.1(iii)), so T.10(b) applies with κ_{v,u} := 1 + C_1W^{2ε}(g²+1−v)/(g²+1−u) ≤ 2C_1W^{2ε}(g²+1−v)/(g²+1−u). In this regime B_{v,0} ≍ (g²+1−v)^{-1} (4.18), so for γ ≥ 1:
 |Ũ_{s,u}∘Z_s| ≤ κ_{s,u}‖Z_s‖ + W^{-D+1} ≺ W^{2ε}(g²+1−s)/(g²+1−u)·(W^{-d}B_{s,0})^γ ≲ W^{2ε}(W^{-d}B_{u,0})^γ((g²+1−u)/(g²+1−s))^{γ−1} ≤ W^{2ε}(W^{-d}B_{u,0})^γ;
 ∫_s^uκ_{v,u}‖B̃_1(v) + Ẽ^{G̊}_v‖dv ≺ W^{2ε}W^{-2d}(g²+1−u)^{-1}∫_s^u(g²+1−v)·η_v^{-1}(g²+1−v)^{-2}dv ≤ W^{2ε}(Im m)^{-1}W^{-2d}(g²+1−u)^{-2}log((1−s)/(1−u)) ≺ (W^{-d}B_{u,0})²;
 ∫_s^uκ_{v,u}‖B̃_2(v)‖dv ≺ Ξ̃_uW^{2ε}W^{-d(γ_*+1/6)}(g²+1−u)^{-1}∫_s^u(1−v)^{-1}(g²+1−v)^{−γ_*−1/6+1}dv ≺ Ξ̃_u(W^{-d}B_{u,0})^{γ_*+1/6} (γ_* + 1/6 ≥ 1);
 martingale: ((Ũ⊗Ũ)∘(Ẽ⊗Ẽ)_v)(a,a) ≤ κ_{v,u}²max|(Ẽ⊗Ẽ)_v| + W^{-D+2} (T.10(b) in each index, decay in each index by T.11(v)), and ∫_s^uκ_{v,u}²η_v^{-1}(W^{-d}B_{v,0})^{4−1/(2p)−1/q}dv ≺ (W^{-d}B_{u,0})^{4−1/(2p)−1/q} (same computation, exponent 4 − 1/(2p) − 1/q − 2 ≥ 1 in (g²+1−v)); then (3.18) and Markov as above.

*Case σ1 ≠ σ2, regime (ii): 1−s ≤ g²/L².* Decompose Z_u = P^{(1)}Z_u + Q^{(1)}Z_u (Definition 4.12, n = 1). Zero mode: by Lemma T.12'' below, |P^{(1)}Z_u| = |L^{-d}Σ_aZ_u(a)| ≺ (W^{-d}B_{u,0})^{γ_*}; this is where TL1 enters (through the Ward identity of Lemma T.3 at the untwisted vertex, the twisted 1-loops T̃_{u,±} appear, and the deterministic parts cancel exactly by the twisted K-loop Ward identity). Zero-mode-free part: Q^{(1)} commutes with Ũ_{v,u} (T.10(d)), so applying Q^{(1)} to (D.5),
 Q^{(1)}Z_u = Q^{(1)}Ũ_{s,u}∘Z_s + ∫_s^uQ^{(1)}Ũ_{v,u}∘(B̃_1 + B̃_2 + Ẽ^{G̊})dv + ∫_s^uQ^{(1)}Ũ_{v,u}∘dẼ^M_v,
with ‖Q^{(1)}Ũ_{v,u}‖_{∞→∞} ≺ 1 (T.10(d)); the four terms are bounded exactly as in the case σ1 = σ2 (O(1) kernel), with ∫_s^uη_v^{-1}(W^{-d}B_{v,0})²dv ≤ C log W·(W^{-d}B_{u,0})² also in this regime (for 1−v ≤ g²/L²: B_{v,0} ≤ 2g^{-2} + (L^d(1−v))^{-1}, and ∫_s^u(1−v)^{-1}[g^{-4} + (L^d(1−v))^{-2}]dv ≤ g^{-4}log((1−s)/(1−u)) + (L^d(1−u))^{-2} ≤ C log W·B_{u,0}²). Hence |Q^{(1)}Z_u(a)| ≺ (W^{-d}B_{u,0})^γ + (W^{-d}B_{u,0})^{2−1/(4p)−1/(2q)} + Ξ̃_u(W^{-d}B_{u,0})^{γ_*+1/6}.

*Conclusion.* In every case, for each fixed (u,a,c1,c2,σ): |Z_u(a)| ≺ (W^{-d}B_{u,0})^{γ_*} (1 + (W^{-d}B_{u,0})^{1/6}Ξ̃_u) (in regime (ii) after adding the zero-mode bound of T.12''). The N^{-C}-net in u with the continuity estimate (Lemma 3.2 / Lemma 8.5(1) applied to the folded loops of (B.4), which control the increments of L̃ between nearby times, and the Lipschitz continuity of K̃ in u from (B.1)) makes this uniform in u ∈ [s,t] and in the O(N^C) other indices, so Ξ̃_t ≺ 1 + (W^{-d}B_{t,0})^{1/6}Ξ̃_t and therefore Ξ̃_t ≺ 1, which is (D.7). □

**Lemma T.12'' (the zero mode in regime (ii)).** Under A.1, (e_s) and 1 − s ≤ g²/L², for σ1 ≠ σ2 and u ∈ [s,t]:
 |L^{-d}Σ_a Z_u(a)| ≺ (W^{-d}B_{u,0})^{γ_*}.                                                                                               (D.8)
*Proof.* By Lemma T.3, L^{-d}Σ_aZ_u(a) = (2iNη_u)^{-1}(L̃^{(1)}_{u,+} − L̃^{(1)}_{u,−}) − L^{-d}Σ_aK̃_u(a), where L̃^{(1)}_{u,±} = M^{(B)}(±)_{c2c1} + T̃_{u,±}. Define the deterministic function D_u := (2iNη_u)^{-1}(M^{(B)}_{c2c1} − M̄^{(B)}_{c2c1}) − L^{-d}Σ_aK̃_u(a). We claim D_u = 0 for σ = (−,+) (and (+,−)). Indeed, Σ_aK̃_u(a) = Σ_aΣ_{a'}Θ^{(−,+)}_u(a,a')M̃(a') = (1−u)^{-1}Σ_{a'}M̃(a') (row sums of Θ^{(−,+)}_u are (1−u)^{-1}, (2.64) with (8.4)), and Σ_{a'}M̃^{(2)}_{(−,+),(a';c1,c2)} = W^{-d}Σ_{a'}M̄^{(B)}_{c2a'}M^{(B)}_{a'c1} = W^{-d}(M̄^{(B)}M^{(B)})_{c2c1} = W^{-d}((M^{(B)})^*M^{(B)})_{c2c1}. The Ward identity for M^{(B)} (the matrix identity behind (8.4)): (M^{(B)})^* − M^{(B)} = (M^{(B)})^*[(M^{(B)})^{-1} − ((M^{(B)})^*)^{-1}]M^{(B)} = (M^{(B)})^*[(gΨ^{(B)} − E − m) − (gΨ^{(B)} − E − m̄)]M^{(B)} = −2i(Im m)(M^{(B)})^*M^{(B)}, hence W^{-d}((M^{(B)})^*M^{(B)})_{c2c1} = (2iW^d Im m)^{-1}(M^{(B)} − M̄^{(B)})_{c2c1} (M symmetric so (M^*)_{c2c1} = M̄_{c2c1}). Therefore L^{-d}Σ_aK̃_u(a) = (1−u)^{-1}L^{-d}(2iW^dIm m)^{-1}(M − M̄)_{c2c1} = (2iNη_u)^{-1}(M − M̄)_{c2c1}, i.e. D_u = 0 (this is the K-loop Ward identity (2.56) for the twisted tree). Consequently L^{-d}Σ_aZ_u(a) = (2iNη_u)^{-1}(T̃_{u,+} − T̃_{u,−}), and by (C.2) |·| ≺ (Nη_u)^{-1}W^{-d}B_{u,0} ≤ (Im m)^{-1}(W^{-d}B_{u,0})² ≤ (Im m)^{-1}(W^{-d}B_{u,0})^{γ_*}, using (Nη_u)^{-1} = (Im m)^{-1}(N(1−u))^{-1} ≤ (Im m)^{-1}W^{-d}B_{u,0} from (2.61). □
(The exact cancellation D_u = 0 is the twisted analogue of the K-loop Ward identity (2.56); without it the zero mode would be bounded only through the lossy kernel norm (1−s)/(1−u) of T.10(a).)

### D.6 The theorem, the induction along the flow, and the forms used in (B.1)

**Theorem T.12 (TL2).** Fix δ ∈ (0, 1/2]. In the setting of Theorem 8.2 (p.71), suppose that at s ∈ [0,t_0] the hypotheses (2.77)–(2.81) hold together with
 (e)  max_{σ∈{±}²} max_{a,c1,c2} |L̃_{s,σ,(a;c1,c2)} − K̃_{s,σ,(a;c1,c2)}| ≺ (W^{-d}B_{s,0})^{2−δ}.
Then there is c_d' = c_d'(d,κ,ε,𝔡,δ) ∈ (0, c_d] such that for all s < t < 1 with (W^{-d}B_{t,0})^{c_d'} ≤ (1−t)/(1−s) < 1 (i.e. (2.82) with c_d'), uniformly in u ∈ [s,t]:
 max_{σ,a,c1,c2} |L̃_{u,σ,(a;c1,c2)} − K̃_{u,σ,(a;c1,c2)}| ≺ (W^{-d}B_{u,0})^{2−δ},                                                      (TL2)
and (C.2) holds. Consequently, by the induction of the proof of Theorem 2.7 (p.71) started at s = 0 where L̃_0 = K̃_0 = M̃ exactly (G_0 = M), (TL2) holds at every u ∈ [0,t_0] with the same δ; in particular at the end time t_0 of Lemma 8.1.
*Proof.* Steps 1–4 of Theorem 8.2 give (I1)–(I7) on [s,t] (they do not use (e)). Apply Proposition T.12' with γ = 2 − δ and p, q so large that 1/(4p) + 1/(2q) ≤ δ: then γ_* = 2 − δ and (D.7) is (TL2). Lemma T.7 gives (C.2). For the induction: the output exponent is min{γ, 2 − 1/(2p) − 1/q} and p, q may be chosen afresh in each step, so the exponent 2 − δ is reproduced at every step (no accumulation); the number of steps is O(1) anyway (each step shrinks 1−t by a factor ≥ (W^{-d}B)^{c_d'} ≤ W^{-2𝔡c_d'}, and 1 − t_0 ≥ η ≥ N^{-1+ε} with W ≥ N^𝔠, so at most (1−ε)/(2𝔡𝔠c_d') steps). The constant c_d' is c_d of Theorem 8.2 reduced so that (4.16) holds with the exponent 1/6 (proof of Lemma 4.3, p.33) — no new smallness requirement arises from T.11–T.12'. □

**Corollary T.13 (forms used in the application).** Under the hypotheses of Theorem T.12, uniformly in u ∈ [s,t], σ, a, c1, c2:
 (i) (circled leg) |Tr(G_u(σ1)E_aG̊_u(σ2)P_{c1c2}) − K̃_{u,σ,(a;c1,c2)} + W^{-d}M^{(B)}(σ2)_{ac1}M^{(B)}(σ1)_{c2a}| ≺ (W^{-d}B_{u,0})^{2−δ} + W^{-d}|M^{(B)}(σ2)_{ac1}|·W^{-d}B_{u,0};
 (ii) the deterministic part of (i), K̃^∘_{u,σ,(a;c1,c2)} := K̃_{u,σ,(a;c1,c2)} − W^{-d}M^{(B)}(σ2)_{ac1}M^{(B)}(σ1)_{c2a}, satisfies |K̃^∘| ≤ C W^{-d}B_{u,|a−c1|} and Σ_a|K̃^∘| ≤ C(W^dη_u)^{-1};
 (iii) the exponent needed in `T2398-fable.md` §3.3 (ii) is 3/2 ≤ 2 − δ, and the term (iv) there uses (C.2).
*Proof.* (i) is A.2 (relation circled/uncircled) with (TL2) and (C.2); (ii) from Lemma T.1 and W^{-d}|M_{ac1}M_{c2a}| ≤ C_M²W^{-d}e^{-c_M|a−c1|} ≤ C_M²C W^{-d}(|a−c1|+1)^{-(d−2)} ≤ C(g²+1)W^{-d}B_{u,|a−c1|}, using W^{-d} ≤ (g²+1)W^{-d}(g²+1−u)^{-1} and (2.61); the sum over a of the exponentially decaying term is ≤ C W^{-d} ≤ C(g²+1)(W^dη_u)^{-1}·η_u(g²+1−u)^{-1} ≤ C'(W^dη_u)^{-1}. □

**Where TL2 sits in the induction.** (e) is a fifth hypothesis of Theorem 8.2 at s (true at s = 0) and (TL2) a fifth conclusion on [s,t]; its proof uses the outputs of Steps 1–4 and nothing of Steps 5–6, and Lemma 6.2 (Step 6) uses it. TL1 is a consequence of Steps 2–3 alone (no hypothesis (e)).

## E. Items of `T2398-fable.md` §7, closed or flagged

1. (TL2 proof) Closed: D.1–D.6. The alternating case needs no sum-zero mollifier (T.10(b), external anchor) and in regime (ii) only the one-index zero-mode projection (T.10(d)) plus the exact cancellation of T.12''. The iteration over n and the Ξ-bootstrap of Lemma 4.10/4.11 are not needed: the only self-referential source is B̃_2 with the factor (W^{-d}B)^{1/6} from (4.16). Constants: C_1, C_2 of T.10, C_M, Im m ≥ κ', and the constants of (2.57), (2.64)–(2.66), (2.86)–(2.91), (4.16); the exponent loss 1/(4p) + 1/(2q) is arbitrary and does not accumulate.
2. (TL1 without [59]) Closed: Lemma T.7, by integration by parts and a 2p-th moment bound; inputs (2.87), (2.89) with n ≤ 4.
3. (|c1 − c2|) Closed: all statements hold for all c1, c2; for |c1 − c2| ≥ C log W both L̃ and K̃ are ≤ W^{-D} (Lemma T.5 and T.1(i)), so nothing is lost by stating them for all pairs.
4. (powers of W^d in 𝒰) Unchanged: the derivation in `T2398-fable.md` §3.1; the forms used here are the loop-level objects of A.2, so Lean re-derives 𝒰 from `twTie_ba` once and feeds Corollary T.13.
5. (derivative convention) Closed and now also checked numerically (Appendix F: the identity (C.3) with Φ = 1 and Φ = T̃).
6. (T3C-tr, lever C; T3B alternative) Unchanged; T3B now uses (C.2) directly.
7. ([68]'s (2.10)) Irrelevant to the proofs here: nothing from [68] is used except the integration-by-parts identity (B.2)/(B.15) in its trace form, which is re-derived in Step 1 of T.7.
8. (numerics) Appendix F adds the check of (C.3).
Flagged (not fully written): (α) In T.11(iii) for C_2 and in Lemma T.4's extension of (4.2), the choice of split vertices with a twist inside a chain is justified by (B.3)/monotonicity as written for n = 2; the general-n version of Lemma T.4 (not needed here) would need the same case analysis for each chain. (β) The N^{-C}-net/continuity step for L̃ uses Lemma 3.2 / Lemma 8.5(1) through the folded loops (B.4); I have not written the continuity estimate for the twisted loop itself, but |L̃_u − L̃_{u'}| ≤ |L̃_u| + |L̃_{u'}| with (B.4) and the band argument of [P] p.18 (which is what [P] invokes for every estimate) suffices since the net is of size N^C and the bounds are ≺-bounds. (γ) Lemma T.6 is applied inside E[(∫…)^{p'}] in D.5; the deterministic bound |(Ẽ⊗Ẽ)| ≤ N^C (from ‖G‖ ≤ η^{-1} ≤ N) makes the bad-event contribution ≤ N^{-D}, as in the proof of Lemma 4.6 (p.34).

## F. Numerics appendix (only what is new)

`num/ibp2.py` (d = 1, L = 4 blocks, W = 3, g = 0.8, z = 0.1 + 0.5i, static model u = 1, 4·10⁶ samples; `num/ktilde.py` as in `T2398-fable.md` §3.5) checks the integration-by-parts identity (C.3):
 Φ = 1: E T̃ = 0.00066 − 0.00005i vs E Tr(G S[G̊] M P) = 0.00065 + 0.00003i (MC error ≈ 5·10⁻⁵);
 Φ = T̃: E T̃² = −0.00075 + 0.00000i vs E[Tr(GS[G̊]MP)T̃] + E 𝒮_1 = −0.00075 + 0.00001i (with E[X T̃] = 0.00049 + 0.00010i, E 𝒮_1 = −0.00124 − 0.00009i).
So the signs of (C.3) and (C.5) (in particular the sign and index order of 𝒮_1, the (w,x) ↔ (x,w) placement, and the absence of a stray m-term) are as stated. The earlier check (`ktilde.py`) that E L̃ = K̃ with K̃ of (B.1) to Monte-Carlo accuracy confirms Lemma T.1 and the vanishing of D_u in T.12'' (the zero-mode identity is a consequence of the same algebra).
