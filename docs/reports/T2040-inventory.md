# T2040 inventory and scripts (optional report file of ticket T2040; every block below is verbatim script output)

Generated Sat Oct  3 10:08:37 UTC 2026 by `t2040_mkinv.py` (scratch scripts are reproduced at the end).  Paper files: `7_8` = `7_8_light_weight.tex`, `B` = `B_graphical_lemmas.tex`, `A` = `A_deterministic_estimates.tex`, `3_5`, `6`, `1_2` as in `paper/README.md`.

## 1. Statements (definitions, lemmas, claims, examples, strategy, remarks) of 7_8:1-1791 and B:1-525, with the three consumers
Columns: statement cites = labels cited in the statement text; proof cites = labels cited in the RBM proof text (BA-variant proofs in the next column); `class` = proved:<file> / cited:<source> / def / deferred.  Unlabeled statements carry the alias printed by the script.

```
$ python3 t2040_inv.py stmts
## stmts
| # | label | kind | span | stmt cites | proof cites | proof (RBM) | proof (BA variant) | class |
|---|---|---|---|---|---|---|---|---|
| 1 | `lem:LWterm_EXP` | lemma | 6:83-88 | lem:main_ind Gt_bound_flow Eq:Gdecay_flow | eq:EGC Oe2x eq:ELW_term eq:def-Spm prop:ThfadC_short eq:bcal_k res_ELK_n=1 Gt_avgbound_flow Eq:L-KGt-flow (+14) | proof-section B:7-121 | - | proved:B |
| 2 | `lem:LWterm` | lemma | 3_5:385-404 | lem:main_ind initialGT2 | lem: EWGn2_N eq:LW_moment eq:Psi eq:directG1 eq:recoltermwt eq:LW_conclusion eq:LW_moment_exp eq:directG2 eq:recoltermwt2 (+1) | proof-env 7_8:84-91 [joint proof with lem: EWGn2_N: 7_8:84-91 (reduction to lem:LW_moment, lem:LW_moment_exp)] | proof-section B:286-526 | proved:7_8 |
| 3 | `lem: EWGn2_N` | lemma | 3_5:406-415 | initialGT2 | lem:LWterm eq:LW_moment eq:Psi eq:directG1 eq:recoltermwt eq:LW_conclusion eq:LW_moment_exp eq:directG2 eq:recoltermwt2 (+1) | proof-env 7_8:84-91 [joint proof with lem:LWterm: 7_8:84-91] | proof-section B:286-526 | proved:7_8 |
| 4 | `lem:LW_moment` | lemma | 7_8:72-77 | lem:LWterm | lem:Anp GtoAG eq:local_Gs eq:sizeGammamu fxyG_sum eq:LW_moment lvl1 lemma eq:far_ab scalemole (+18) | proof-env 7_8:943-950; proof-section 7_8:716-952 | proof-env B:415-523 | proved:7_8 |
| 5 | `lem:LW_moment_exp` | lemma | 7_8:78-83 | lem: EWGn2_N | lem:LW_moment eq:LW_moment_exp lem:LW_moment_exp_far lem:localregular def_auxgraph lem:Anp_key lem:Anp_key_gh lem:LW_moment_exp_near adsuu_exp (+9) | proof-section 7_8:1600-1791 | proof-env B:415-523 | proved:7_8 |
| 6 | `def_graph1` | definition | 7_8:116-147 | - | - | - | - | def |
| 7 | `ValG` | definition | 7_8:159-164 | - | - | - | - | def |
| 8 | `def_poly` | definition | 7_8:171-188 | - | - | - | - | def |
| 9 | `defnlvl0` | definition | 7_8:196-210 | - | - | - | - | def |
| 10 | `dot-def` | definition | 7_8:214-225 | - | - | - | - | def |
| 11 | `def scaling` | definition | 7_8:232-255 | eq_defsizemax | - | - | - | def |
| 12 | `claim:size (Gamma << size(Gamma), 7_8:264)` | claim | 7_8:264-266 | lem:LWterm lem: EWGn2_N | - | - | - | no-proof |
| 13 | `def scaling order` | definition | 7_8:270-284 | eq_defsize eq:ordG | - | - | - | def |
| 14 | `ssl` | lemma | 7_8:294-306 | - | - | - | - | cited:yang2021delocalization |
| 15 | `Oe14` | lemma | 7_8:309-330 | multi setting Oe1x | - | - | - | cited:yang2021delocalization |
| 16 | `T eq0` | lemma | 7_8:334-349 | - | - | - | - | cited:yang2021delocalization |
| 17 | `deflvl1` | definition | 7_8:367-386 | - | - | - | - | def |
| 18 | `lvl1 lemma` | lemma | 7_8:392-399 | - | - | - | - | cited:yang2021delocalization |
| 19 | `example:p=2 (sec:graphs_ideas, 7_8:505)` | example | 7_8:505-679 | eq:p=2graph sec:graphs lvl1 lemma fig:p=2expansion ssl eq:LW_moment | - | - | - | example |
| 20 | `lem:localregular` | lemma | 7_8:786-821 | eq:far_ab scalemole | lvl1 lemma eq:local_Gs eq:MolVW ssl Oe14 T eq0 eq:originGamma Oe2x Owx (+13) | proof-env B:172-278; proof-section B:122-285 | - | proved:B |
| 21 | `def: BM2` | definition | 7_8:863-869 | eq:blockIa | - | - | - | def |
| 22 | `claim:xi (eq:Gbyxi2 bounds of xi, 7_8:884)` | claim | 7_8:884-890 | lem:LWterm | - | - | - | no-proof |
| 23 | `def_auxgraph` | definition | 7_8:894-903 | ValG eq:ordG | - | - | - | def |
| 24 | `GtoAG` | lemma | 7_8:907-912 | lem:localregular eq:local_Gs def_auxgraph | eq:estSpm-W yixi lem_GbEXP def scaling eq:MolVW eq:ordG eq:ordGaux G_by_auxG | proof-env 7_8:914-928 | - | proved:7_8 |
| 25 | `lem:Anp` | lemma | 7_8:933-939 | GtoAG | def_auxgraph eq:Gbyxi2 lem:localregular lem:Anp_key eq:bddGamma_aux adsuu_orig eq:xia1a2 eq:ordGaux lem:Anp_key_gh (+17) | proof-env 7_8:987-989; proof-section 7_8:953-1599 | - | proved:7_8 |
| 26 | `lem:Anp_key` | lemma | 7_8:960-985 | eq:xia1a2 eq:ordGaux | - | proved by lem:Anp_key_gh ("easy corollary", 7_8:1025) | - | no-proof |
| 27 | `lem:Anp_key_gh` | lemma | 7_8:1041-1077 | lem:Anp_key | adsuu22 eq:Gbyxi3 kwuyayw eq:noA2 eq:induc_Ggraph eq:jthpath eq:change_of_order eq:change_of_order2 eq:bound_new_graph (+8) | proof-env 7_8:1110-1534 | - | proved:7_8 |
| 28 | `lem:LW_moment_exp_far` | lemma | 7_8:1615-1620 | lem:LW_moment_exp | lem:localregular def_auxgraph lem:Anp_key lem:Anp_key_gh | proof-env 7_8:1631-1643 | - | proved:7_8 |
| 29 | `lem:LW_moment_exp_near` | lemma | 7_8:1621-1626 | lem:LW_moment_exp | lem:localregular def_auxgraph lem:Anp_key adsuu_exp eq:ordGaux adsuu_exp2 lem:propT TTT2 claim:TTk (+4) | proof-env 7_8:1646-1788 | - | proved:7_8 |
| 30 | `claim:TTk` | claim | 7_8:1661-1666 | lem:propT TTT2 | eq:key_T_reudce eq:KtKt eq:key_T_reudce_pf eq:TtTt | proof-section A:265-314 [proof deferred to A.4 (pf:claim_TTk, A:265-314) = merged EKTTk / ekTTk_holds] | - | proved:A |
| 31 | `strat_local` | strategy | B:135-157 | Owx dot-def eq:neutralcharge Oe2x Oe1x eq:smallsize | - | - | - | strategy |
| 32 | `remark:3p (stronger ord bound, B:280)` | remark | B:280-282 | eq:LW_moment lem: EMn2_N rmk_bottleneck | - | - | - | remark |
| 33 | `def_atom` | definition | B:302-314 | - | - | - | - | def |
| 34 | `defn_normalBA` | definition | B:329-339 | - | - | - | - | def |
| 35 | `def scalingBA` | definition | B:345-356 | eq_defsizemax | - | - | - | def |
| 36 | `lanlw` | lemma | B:359-372 | - | - | - | - | cited:yang2024Del |
| 37 | `lem_lweight` | lemma | B:376-387 | - | - | - | - | cited:yang2024Del |
| 38 | `GGGamma (BA GG expansion, B:393)` | lemma | B:393-405 | - | - | - | - | cited:yang2024Del |
```

## 2. Labeled displayed equations in scope (86), their home and where they are cited

```
$ python3 t2040_inv.py eqs
## eqs
| label | line | home | cited at (first 5, outside its own line) |
|---|---|---|---|
| `eq:EGC` | 7_8:10 | sect Sec:graph 7_8:1-1791 | B:10 B:15 |
| `eq:directG1` | 7_8:17 | sect Sec:graph 7_8:1-1791 | 7_8:30 7_8:40 7_8:50 7_8:87 7_8:88 |
| `eq:directG2` | 7_8:25 | sect Sec:graph 7_8:1-1791 | 7_8:30 7_8:40 7_8:54 7_8:90 |
| `fxyG_sum` | 7_8:31 | sect Sec:graph 7_8:1-1791 | 7_8:68 7_8:949 |
| `eq:recolterm` | 7_8:41 | sect Sec:graph 7_8:1-1791 | 7_8:50 |
| `eq:recolterm2` | 7_8:45 | sect Sec:graph 7_8:1-1791 | 7_8:54 |
| `eq:recoltermwt` | 7_8:51 | sect Sec:graph 7_8:1-1791 | 7_8:87 |
| `eq:recoltermwt2` | 7_8:55 | sect Sec:graph 7_8:1-1791 | 7_8:90 |
| `eq:boundfxyGinf` | 7_8:62 | sect Sec:graph 7_8:1-1791 | 7_8:67 7_8:95 |
| `eq:LW_moment` | 7_8:74 | lem:LW_moment 7_8:72-77 | 7_8:85 7_8:95 7_8:551 7_8:698 7_8:949 (+1) |
| `eq:LW_moment_exp` | 7_8:80 | lem:LW_moment_exp 7_8:78-83 | 7_8:88 7_8:95 7_8:1602 |
| `eq:far_ab` | 7_8:96 | sect Sec:graph 7_8:1-1791 | 7_8:792 |
| `eq:def-Spm` | 7_8:110 | sect sec:graphs 7_8:105-401 | B:34 B:289 |
| `scalemole` | 7_8:191 | sect sec:graphs 7_8:105-401 | 7_8:258 7_8:792 |
| `odot` | 7_8:220 | dot-def 7_8:214-225 | - |
| `eq_defsize` | 7_8:240 | def scaling 7_8:232-255 | 7_8:257 7_8:274 |
| `eq_defsizemax` | 7_8:249 | def scaling 7_8:232-255 | 7_8:250 B:354 |
| `eq:estSpm-W` | 7_8:260 | sect sec:graphs 7_8:105-401 | 7_8:916 |
| `eq:ordG` | 7_8:272 | def scaling order 7_8:270-284 | 7_8:274 7_8:900 7_8:926 B:222 B:235 (+3) |
| `Owx` | 7_8:298 | ssl 7_8:294-306 | B:124 B:138 B:138 B:209 B:209 (+2) |
| `multi setting` | 7_8:311 | Oe14 7_8:309-330 | 7_8:328 |
| `Oe1x` | 7_8:316 | Oe14 7_8:309-330 | 7_8:329 B:125 B:146 B:146 B:275 |
| `Oe2x` | 7_8:339 | T eq0 7_8:334-349 | B:16 B:98 B:100 B:104 B:107 (+6) |
| `eq:neutralcharge` | 7_8:382 | deflvl1 7_8:367-386 | B:146 |
| `expand lvl1` | 7_8:394 | lvl1 lemma 7_8:392-399 | - |
| `eq:p=2graph` | 7_8:507 | example:p=2 7_8:505-679 | 7_8:547 7_8:554 7_8:674 |
| `eq:local_Gs` | 7_8:788 | lem:localregular 7_8:786-821 | 7_8:849 7_8:908 7_8:944 B:173 |
| `eq:MolVW` | 7_8:797 | lem:localregular 7_8:786-821 | 7_8:926 B:176 |
| `eq:deg_mole` | 7_8:806 | lem:localregular 7_8:786-821 | - |
| `eq:sizeGammamu` | 7_8:816 | lem:localregular 7_8:786-821 | 7_8:948 B:277 |
| `yixi` | 7_8:876 | sect Proof of Lemma \ref{lem: 7_8:716-952 | 7_8:879 7_8:916 7_8:920 B:316 |
| `eq:Gbyxi` | 7_8:880 | sect Proof of Lemma \ref{lem: 7_8:716-952 | - |
| `eq:xia1a2` | 7_8:882 | sect Proof of Lemma \ref{lem: 7_8:716-952 | 7_8:962 B:85 |
| `eq:Gbyxi2` | 7_8:887 | claim 7_8:884-890 | 7_8:957 7_8:988 B:85 B:427 |
| `eq:ordGaux` | 7_8:902 | def_auxgraph 7_8:894-903 | 7_8:926 7_8:984 7_8:1658 |
| `G_by_auxG` | 7_8:909 | GtoAG 7_8:907-912 | 7_8:926 7_8:1786 B:84 B:87 |
| `eq:bddGamma_aux` | 7_8:935 | lem:Anp 7_8:933-939 | 7_8:988 |
| `eq:Gbyxi3` | 7_8:963 | lem:Anp_key 7_8:960-985 | 7_8:1117 7_8:1142 7_8:1178 7_8:1348 7_8:1421 (+3) |
| `eq:deg_mole_aux` | 7_8:973 | lem:Anp_key 7_8:960-985 | 7_8:1403 |
| `adsuu_orig` | 7_8:981 | lem:Anp_key 7_8:960-985 | 7_8:988 |
| `adsuu22` | 7_8:1043 | lem:Anp_key_gh 7_8:1041-1077 | 7_8:1112 7_8:1112 7_8:1112 7_8:1117 7_8:1117 |
| `kwuyayw` | 7_8:1121 | proof 7_8:1110-1534 | 7_8:1127 7_8:1142 7_8:1144 7_8:1149 7_8:1173 (+5) |
| `eq:noA2` | 7_8:1146 | proof 7_8:1110-1534 | 7_8:1149 |
| `eq:induc_Ggraph` | 7_8:1166 | proof 7_8:1110-1534 | 7_8:1173 7_8:1232 |
| `eq:change_of_order` | 7_8:1169 | proof 7_8:1110-1534 | 7_8:1236 |
| `eq:change_of_order2` | 7_8:1172 | proof 7_8:1110-1534 | 7_8:1236 |
| `kwuyayw_case1` | 7_8:1174 | proof 7_8:1110-1534 | 7_8:1240 |
| `eq:jthpath` | 7_8:1211 | proof 7_8:1110-1534 | 7_8:1221 |
| `eq:bound_new_graph` | 7_8:1233 | proof 7_8:1110-1534 | 7_8:1240 |
| `kwuyayw_case3` | 7_8:1344 | proof 7_8:1110-1534 | - |
| `kwuyayw_ng` | 7_8:1397 | proof 7_8:1110-1534 | 7_8:1400 7_8:1417 |
| `eq:degali` | 7_8:1404 | proof 7_8:1110-1534 | 7_8:1428 7_8:1447 |
| `kwuyayw_ng_tree` | 7_8:1414 | proof 7_8:1110-1534 | 7_8:1419 7_8:1423 7_8:1428 7_8:1533 |
| `eq:far_ab_K` | 7_8:1603 | sect subsec_pf_LW_moment_exp 7_8:1600-1791 | - |
| `eq:LW_moment_exp_far` | 7_8:1617 | lem:LW_moment_exp_far 7_8:1615-1620 | - |
| `eq:LW_moment_exp_near` | 7_8:1623 | lem:LW_moment_exp_near 7_8:1621-1626 | - |
| `adsuu33` | 7_8:1634 | proof 7_8:1631-1643 | - |
| `adsuu44` | 7_8:1639 | proof 7_8:1631-1643 | - |
| `adsuu_exp` | 7_8:1649 | proof 7_8:1646-1788 | 7_8:1654 |
| `adsuu_exp2` | 7_8:1655 | proof 7_8:1646-1788 | 7_8:1660 7_8:1782 7_8:1786 |
| `eq:key_T_reudce` | 7_8:1663 | claim:TTk 7_8:1661-1666 | 7_8:1671 7_8:1671 7_8:1765 7_8:1773 A:266 (+1) |
| `eq:ELW_term` | B:13 | sect subsec:pf-LWterm_EXP B:7-121 | B:16 B:77 |
| `eq:termI1` | B:40 | sect subsec:pf-LWterm_EXP B:7-121 | B:77 |
| `eq:termI2` | B:47 | sect subsec:pf-LWterm_EXP B:7-121 | - |
| `eq:termI41` | B:64 | sect subsec:pf-LWterm_EXP B:7-121 | B:77 |
| `eq;I42inG` | B:68 | sect subsec:pf-LWterm_EXP B:7-121 | B:75 |
| `eq;EGxy:x=y` | B:72 | sect subsec:pf-LWterm_EXP B:7-121 | B:80 B:91 B:108 |
| `Gammamuxy` | B:88 | sect subsec:pf-LWterm_EXP B:7-121 | - |
| `eq:sizeGammamu_E` | B:92 | sect subsec:pf-LWterm_EXP B:7-121 | B:102 B:102 B:104 B:104 B:107 (+1) |
| `eq:GGraisesord` | B:99 | sect subsec:pf-LWterm_EXP B:7-121 | B:104 B:107 |
| `eq:smallsize` | B:140 | strat_local B:135-157 | B:147 B:152 |
| `eq:originGamma` | B:174 | proof B:172-278 | B:204 B:204 B:206 |
| `eq:initial_scaling` | B:201 | proof B:172-278 | B:271 |
| `eq:relateG1G0` | B:215 | proof B:172-278 | B:222 B:235 B:246 B:247 B:253 (+2) |
| `eq:ordGinter` | B:272 | proof B:172-278 | B:277 |
| `scaleatom` | B:317 | sect subsec:LWchange-to-BA B:286-526 | B:423 B:431 |
| `eq_defsize_BA` | B:350 | def scalingBA B:345-356 | - |
| `eq:ordG_BA` | B:353 | def scalingBA B:345-356 | - |
| `eq:BE` | B:361 | lanlw B:359-372 | - |
| `eq:LW` | B:378 | lem_lweight B:376-387 | - |
| `GGGamma` | B:398 | lemma B:393-405 | B:118 |
| `Gyiyjatom` | B:424 | proof B:415-523 | - |
| `eq:Gbyxi2_BA` | B:428 | proof B:415-523 | B:488 B:492 B:496 B:522 |
| `Gyiyjatom2` | B:432 | proof B:415-523 | - |
| `eq:ordGaux_BAM` | B:486 | proof B:415-523 | - |
| `G_by_auxG_BA` | B:489 | proof B:415-523 | - |

labeled displayed equations in scope: 86
```

## 3. Dependency tree from lem:LWterm, lem: EWGn2_N, lem:LWterm_EXP (statement and proof cross-references; BA-variant proofs excluded)

```
$ python3 t2040_inv.py deps
## deps
lem:LWterm [lemma 3_5:385]  uses outside LW layer: lem:main_ind(1_2:1256) initialGT2(3_5:28) eq:Psi(3_5:391) eq:directG1(7_8:17) eq:recoltermwt(7_8:51) eq:LW_conclusion(3_5:396) eq:directG2(7_8:25) eq:recoltermwt2(7_8:55)
  lem: EWGn2_N [lemma 3_5:406]  uses outside LW layer: initialGT2(3_5:28) eq:directG1(7_8:17) eq:recoltermwt(7_8:51) eq:directG2(7_8:25) eq:recoltermwt2(7_8:55) eq:LW_conclusion_exp(3_5:411)
    lem:LW_moment [lemma 7_8:72]
      lem:Anp [lemma 7_8:933]
        GtoAG [lemma 7_8:907]
          lem:localregular [lemma 7_8:786]
            lvl1 lemma [lemma 7_8:392]
            ssl [lemma 7_8:294]
            Oe14 [lemma 7_8:309]
            T eq0 [lemma 7_8:334]
            def scaling order [definition 7_8:270]
              def scaling [definition 7_8:232]
            dot-def [definition 7_8:214]
            deflvl1 [definition 7_8:367]
            strat_local [strategy B:135]
              ssl [lemma 7_8:294] (expanded above)
              dot-def [definition 7_8:214] (expanded above)
              deflvl1 [definition 7_8:367] (expanded above)
              T eq0 [lemma 7_8:334] (expanded above)
              Oe14 [lemma 7_8:309] (expanded above)
          def_auxgraph [definition 7_8:894]
            ValG [definition 7_8:159]
            def scaling order [definition 7_8:270] (expanded above)
          def scaling [definition 7_8:232] (expanded above)
          def scaling order [definition 7_8:270] (expanded above)
        def_auxgraph [definition 7_8:894] (expanded above)
        claim@7_8:884 [claim 7_8:884]
        lem:localregular [lemma 7_8:786] (expanded above)
        lem:Anp_key [lemma 7_8:960]
          def_auxgraph [definition 7_8:894] (expanded above)
        lem:Anp_key_gh [lemma 7_8:1041]
          lem:Anp_key [lemma 7_8:960] (expanded above)
          def_graph1 [definition 7_8:116]
        def_graph1 [definition 7_8:116] (expanded above)
      GtoAG [lemma 7_8:907] (expanded above)
      lem:localregular [lemma 7_8:786] (expanded above)
      lvl1 lemma [lemma 7_8:392] (expanded above)
      ssl [lemma 7_8:294] (expanded above)
      Oe14 [lemma 7_8:309] (expanded above)
      T eq0 [lemma 7_8:334] (expanded above)
      def_graph1 [definition 7_8:116] (expanded above)
      ValG [definition 7_8:159] (expanded above)
      def scaling order [definition 7_8:270] (expanded above)
      def_auxgraph [definition 7_8:894] (expanded above)
      def scaling [definition 7_8:232] (expanded above)
    lem:LW_moment_exp [lemma 7_8:78]
      lem:LW_moment [lemma 7_8:72] (expanded above)
      lem:LW_moment_exp_far [lemma 7_8:1615]
        lem:localregular [lemma 7_8:786] (expanded above)
        def_auxgraph [definition 7_8:894] (expanded above)
        lem:Anp_key [lemma 7_8:960] (expanded above)
        lem:Anp_key_gh [lemma 7_8:1041] (expanded above)
      lem:localregular [lemma 7_8:786] (expanded above)
      def_auxgraph [definition 7_8:894] (expanded above)
      lem:Anp_key [lemma 7_8:960] (expanded above)
      lem:Anp_key_gh [lemma 7_8:1041] (expanded above)
      lem:LW_moment_exp_near [lemma 7_8:1621]
        lem:localregular [lemma 7_8:786] (expanded above)
        def_auxgraph [definition 7_8:894] (expanded above)
        lem:Anp_key [lemma 7_8:960] (expanded above)
        claim:TTk [claim 7_8:1661]
        GtoAG [lemma 7_8:907] (expanded above)
      claim:TTk [claim 7_8:1661] (expanded above)
      GtoAG [lemma 7_8:907] (expanded above)
  lem:LW_moment [lemma 7_8:72] (expanded above)
  lem:LW_moment_exp [lemma 7_8:78] (expanded above)

lem: EWGn2_N [lemma 3_5:406] (expanded above)

lem:LWterm_EXP [lemma 6:83]  uses outside LW layer: lem:main_ind(1_2:1256) Gt_bound_flow(1_2:1342) Eq:Gdecay_flow(1_2:1380) eq:EGC(7_8:10) eq:ELW_term(B:13) eq:def-Spm(7_8:110) prop:ThfadC_short(1_2:1148) eq:bcal_k(1_2:1056) res_ELK_n=1(6:14) Gt_avgbound_flow(1_2:1344) Eq:L-KGt-flow(1_2:1371) WI_calL(1_2:1036) WI_calK(1_2:1039) eq;I42inG(B:68) eq:termI1(B:40) eq:termI41(B:64) eq;EGxy:x=y(B:72) eq:sizeGammamu_E(B:92) eq:GGraisesord(B:99)
  T eq0 [lemma 7_8:334] (expanded above)
  GtoAG [lemma 7_8:907] (expanded above)
  lem:LW_moment [lemma 7_8:72] (expanded above)
  claim@7_8:884 [claim 7_8:884] (expanded above)
  lemma@B:393 [lemma B:393]

statements of the inventory not reachable from the three consumers by explicit cross-references: 11
def_poly defnlvl0 claim@7_8:264 example:p=2 def: BM2 remark@B:280 def_atom defn_normalBA def scalingBA lanlw lem_lweight

reverse view: statements that cite no other statement of the layer (leaves):
def_graph1 ValG def_poly defnlvl0 dot-def def scaling ssl Oe14 T eq0 deflvl1 lvl1 lemma def: BM2 claim:TTk def_atom defn_normalBA lanlw lem_lweight lemma@B:393
```

## 4. Layers of the dependency graph (longest path from the consumers)
Uses outside the layer (`initialGT2`, `eq:Psi`, `lem_GbEXP_BA`, `prop:ThfadC_short`, ...) are listed by `deps` per consumer.  Implicit uses without `\Cref` (manual): `defnlvl0` (normal graphs) by `strat_local`, `lem:localregular`; `def_poly` (molecules) by `lem:localregular` (2)-(5); `claim:size` (7_8:264) by `lvl1 lemma` (the size of Err); `def: BM2` by `def_auxgraph`.

```
$ python3 t2040_inv.py layers
## layers
L0: lem:LWterm_EXP; lem:LWterm
L1: GGGamma (BA GG expansion, B:393); lem:LW_moment_exp
L2: lem:LW_moment_exp_near; lem:LW_moment_exp_far; lem: EWGn2_N
L3: claim:TTk; lem:LW_moment
L4: lem:Anp
L5: lem:Anp_key_gh; claim:xi (eq:Gbyxi2 bounds of xi, 7_8:884); GtoAG
L6: def_graph1; lem:Anp_key; lem:localregular
L7: def_auxgraph; strat_local; lvl1 lemma
L8: ValG; deflvl1; dot-def; def scaling order; T eq0; Oe14; ssl
L9: def scaling
statements outside the layering (no explicit \Cref path from the consumers): def_poly defnlvl0 claim:size (Gamma << size(Gamma), 7_8:264) example:p=2 (sec:graphs_ideas, 7_8:505) def: BM2 remark:3p (stronger ord bound, B:280) def_atom defn_normalBA def scalingBA lanlw lem_lweight
```

## 5. Sketch markers per proof span (words that signal a missing detail or a reuse)

```
$ python3 t2040_inv.py sketch
## sketch
| statement | proof span (RBM) | non-blank TeX lines | sketch markers (word: line numbers) |
|---|---|---|---|
| `lem:LWterm_EXP` | B:7-121 | 94 | analogous: 15,118; exactly the same: 34,49,105; standard: 80,100; as in: 84; easy to see: 102; it is easy: 102; omit: 118 |
| `lem:LWterm` | 7_8:84-91 | 8 | - |
| `lem: EWGn2_N` | 7_8:84-91 | 8 | - |
| `lem:LW_moment` | 7_8:943-950 | 8 | standard: 944 |
| `lem:LW_moment_exp` | 7_8:1600-1791 | 150 | similar: 1630,1632,1647; standard: 1632,1647,1648; as in: 1632,1642,1648; analogous: 1633; roughly speaking: 1637; omit: 1642,1773; same: 1642; exactly the same: 1642; easy to see: 1781; it is easy: 1781 |
| `lem:localregular` | B:172-278 | 62 | as in: 173; similar: 179,197; without loss of generality: 194,210; standard: 196,205,275; analogous: 210; same: 263; not hard to see: 263; omit: 275; straightforward: 275; direct check: 275 |
| `GtoAG` | 7_8:914-928 | 13 | as in: 915 |
| `lem:Anp` | 7_8:987-989 | 3 | - |
| `lem:Anp_key_gh` | 7_8:1110-1534 | 281 | easy to see: 1142,1231; it is easy: 1142,1231; without loss of generality: 1154,1157,1207,1246,1407,1413..; similar: 1232,1240,1254; as in: 1400,1529 |
| `lem:LW_moment_exp_far` | 7_8:1631-1643 | 13 | similar: 1632; standard: 1632; as in: 1632,1642; analogous: 1633; roughly speaking: 1637; omit: 1642; same: 1642; exactly the same: 1642 |
| `lem:LW_moment_exp_near` | 7_8:1646-1788 | 110 | similar: 1647; standard: 1647,1648; as in: 1648; omit: 1773; easy to see: 1781; it is easy: 1781 |
| `claim:TTk` | A:265-314 | 40 | without loss of generality: 277,297,305 |
```

## 6. Counts by class

```
$ python3 t2040_inv.py sizes
## sizes
| class | statements | non-blank TeX lines of statements | non-blank TeX lines of proofs (RBM) |
|---|---|---|---|
| cited | 7 | 74 | 0 |
| def | 13 | 131 | 0 |
| example | 1 | 128 | 0 |
| no-proof | 3 | 32 | 0 |
| proved | 12 | 114 | 790 |
| remark | 1 | 3 | 0 |
| strategy | 1 | 18 | 0 |

file 7_8 lines 1-1791: 973 non-blank non-comment TeX lines

file B lines 1-525: 335 non-blank non-comment TeX lines
```

## 7. Block Anderson section 7_8:1792-2108 (outside the LW scope; item 6)

```
$ python3 t2040_inv.py ba
## ba
| label | kind | span | note |
|---|---|---|---|
| `zztE_BA` | lemma | 7_8:1796-1808 | Lemma 3.3 of \cite{RBSO1D} |
| `lem:main_ind_BA` | theorem | 7_8:1825-1828 |  |
| `lem:propM` | lemma | 7_8:1846-1906 |  |
| `lem_GbEXP_BA` | lemma | 7_8:1916-1946 |  |
| `lem_ConArg_BA` | lemma | 7_8:1956-1985 |  |
| (proof) | proof | 7_8:1834-1836 | \bf Proof of \Cref{MR:decol_BA} |
| (proof) | proof | 7_8:1907-1912 |  |
| (proof) | proof | 7_8:1947-1949 |  |
| (proof) | proof | 7_8:1986-1988 |  |
| (proof) | proof | 7_8:2036-2096 | \bf Proof of \Cref{lem: EMn2_N} for the block Anderson model |
```

## 8. Size of gate LW computed from the inventory (item 7)
TeX kchar = characters of the span without comments, figures and tikz code; "omitted-step lines" = lines of the span containing omit / straightforward / direct check / not hard to see / easy to see / it is easy / we do not pursue / roughly speaking; m = 1, 1.5, 2 for 0, 1-3, >=4 such lines; lo: m = 1; central: m; hi: m + 1.  Fixed items have no proof text in the paper (cited or infrastructure): their lines are judgments, stated in the item title.

```
$ python3 t2040_size.py
## calibration: merged d>=3 formalizations of paper proofs (lines of the merged Lean files / TeX kchars of the paper span)
| lem:propT + claim:TTk (A:230-314)                    | Kernel/PropT.lean                                |  1080 lines |   6.92 kchar |  156.1 lines/kchar |
| evolution kernel estimates (A:84-229), merged part   | Kernel/{Evolution,SumDecay}, Evolution/SumDecay  |  2024 lines |  13.70 kchar |  147.7 lines/kchar |
R = total merged lines / total kchar = 151 lines per TeX kchar

## random band matrix layer (gate LW)
| id | work item | TeX kchar | omitted-step lines | m | lines lo | lines central | lines hi |
|---|---|---|---|---|---|---|---|
| LW-01 | reduction of lem:LWterm, lem: EWGn2_N to the moments (eq:directG, recolterm, M | 8.5 | - | 1 | 1278 | 1278 | 2557 |
| LW-02 | moment => LW_moment, LW_moment_exp assembly; far/near split | 3.1 | - | 1 | 461 | 461 | 922 |
| LW-03 | graph record, values, counters, molecules, normal graphs, dotted-edge partitio | 11.9 | - | - | 1400 | 1400 | 1400 |
| LW-04 | Gaussian bridge: E Z_w = 0 for resolvent polynomials (GaussIBP, Tame) and the  | 0.0 | - | - | 1200 | 1200 | 1200 |
| LW-05 | weight expansion (Owx) on graphs (cited: yang2021, Lemma 3.5) | 0.6 | - | - | 800 | 800 | 800 |
| LW-06 | edge expansion (Oe1x) on graphs (cited: Lemma 3.10) | 2.0 | - | - | 1100 | 1100 | 1100 |
| LW-07 | GG expansion (Oe2x) on graphs (cited: Lemma 3.14) | 1.0 | - | - | 1000 | 1000 | 1000 |
| LW-08 | lvl1 lemma: expansion strategy to locally standard graphs, termination, Err of | 8.1 | - | - | 1500 | 1500 | 1500 |
| LW-09 | claim: Gamma << size(Gamma) (molecules, free vertex, scalemole, S^pm decay) | 1.2 | - | - | 1300 | 1300 | 1300 |
| LW-10 | lem:localregular (1)-(6): paths, molecules, scaling order through every expans | 12.9 | B:263,B:275 | 1.5 | 1945 | 2918 | 4863 |
| LW-11 | auxiliary graph, GtoAG | 6.6 | - | 1 | 989 | 989 | 1979 |
| LW-12 | nested graphs: lem:Anp_key, lem:Anp_key_gh, lem:Anp (cases I-IV, induction, sp | 32.3 | 7_8:1142,7_8:1231 | 1.5 | 4875 | 7312 | 12187 |
| LW-13 | lem:LW_moment_exp_far, _near (claim:TTk merged as EKTTk) | 8.3 | 7_8:1637,7_8:1642,7_8:1773,7_8:1781 | 2 | 1255 | 2511 | 3766 |
| LW-14 | lem:LWterm_EXP (I1..I4, J-terms, case (1)-(4) of ord) | 11.1 | B:102,B:118 | 1.5 | 1683 | 2524 | 4207 |
| LW-15 | deterministic sublemmas: (eq:Psi) for the B-class, W^-d T~ ~ sT^2, Psi_t windo | 0.0 | - | - | 600 | 600 | 600 |
| LW-16 | regime split of lem: EWGn2_N along sub-sequences (7_8:20 "immediate consequenc | 0.0 | - | - | 500 | 500 | 500 |
| total | | | | | 21888 | 27395 | 39883 |
tickets at 1000 lines: lo 22, central 27, hi 40   (design band 600-1500 lines: central 18..46)

## block Anderson additions (gate BA, item 6)
| id | work item | TeX kchar | omitted-step lines | m | lines lo | lines central | lines hi |
|---|---|---|---|---|---|---|---|
| BA-L1 | BA graph vocabulary: Psi- and M-dotted edges, atoms, def scalingBA | 5.8 | - | 1 | 873 | 873 | 1746 |
| BA-L2 | BA expansions lanlw, lem_lweight, GGGamma (cited: yang2024Del B.9-B.11) | 1.9 | - | - | 2400 | 2400 | 2400 |
| BA-L3 | BA lvl1, atomic reduction and auxiliary graph, Anp for atoms (B:415-523) | 7.0 | B:409 | 1.5 | 1060 | 1590 | 2650 |
| BA-L4 | BA LWterm_EXP (B:118: analogous with GGGamma) | 0.0 | - | - | 1500 | 1500 | 1500 |
| total | | | | | 5833 | 6363 | 8296 |
tickets at 1000 lines: lo 6, central 6, hi 8   (design band 600-1500 lines: central 4..11)

LW + BA tickets at 1000 lines: lo 28, central 34, hi 48

## reduced routes (items kept; tickets at 1000 lines: lo / central / hi)
| full random band layer                                       | LW-01 LW-02 LW-03 LW-04 LW-05 LW-06 LW-07 LW-08 LW-09 LW-10 LW-11 LW-12 LW-13 LW-14 LW-15 LW-16 | 22 / 27 / 40 |
| R1: expansions + lvl1 lemma as authorized external inputs (DECISIONS 5) | LW-01 LW-02 LW-03 LW-09 LW-10 LW-11 LW-12 LW-13 LW-14 LW-15 LW-16 | 16 / 22 / 34 |
| R2: Step 6 only (lem:LWterm_EXP; no lem:LWterm, lem: EWGn2_N) | LW-03 LW-04 LW-07 LW-09 LW-11 LW-14 LW-15 | 8 / 9 / 12 |
| R1 and R2 intersect: Step 6 only, expansions external        | LW-03 LW-09 LW-11 LW-14 LW-15 | 6 / 7 / 9 |
```

## 9. Probe statistics: code lines of the two candidate representations and of the other parts

```
$ python3 t2040_stats.py /Users/junyin/Lean_proof/RBM3D-wt/T2040/RBM3D/Probe/T2040Graphs.lean
candidate A (record LGraph: LData, edges, LGraph, term/val, counters/molecules): lines 62-173, code lines 65
candidate B (syntax with binders: GTerm, eval, one graph + its value theorem):    lines 297-329, code lines 26
  A: two example graphs (p2Graph, figGraph) with value and counters:               lines 180-281, code lines 76
nested graphs (NGraph, predicates, value, figAux and its checks):                  lines 339-430, code lines 48
weight expansion on the vocabulary (defect identity, 2 graphs, expectation):       lines 440-730, code lines 224
   of which owx_defect_identity (generic f, df; one proof):                       code lines 86
(Owx) for the smallest graph, candidate A: three records + counters + value theorem: lines 554-598, code lines 30
(Owx) for the smallest graph, candidate B: three binder terms + value theorem:       lines 705-730, code lines 19
three expansion pins (+ flow data definitions):                                    lines 732-868, code lines 89
sequence-level pins and their definitions (section 6):                             lines 870-1157, code lines 189
skeleton (section 7: Markov step, (eq:Psi) shift, regimes):                        lines 1157-1566, code lines 340
instances (section 8):                                                             lines 1566-2142, code lines 411
whole probe: 2142 lines, 1485 code lines
```

## 10. Numeric check of the three expansion pins (pathwise identity with the Stein defect, generic f)

```
$ ./t2040_expansions_all.sh
pathwise check (n=5, E=0.70, t=0.55, |m|=1.000000; central difference h=1e-05):
identity       |LHS-RHS|      |LHS-RHS-(-m*defect)|    |LHS|
Owx            7.335e-02      2.278e-13                8.196e-02
Oe2x           9.542e-03      7.779e-14                1.015e-02
Oe1x k=(1,0,0,0) 1.125e-01      2.444e-13                5.958e-02
Oe1x k=(2,2,1,1) 9.478e-04      4.347e-14                8.921e-04
Oe1x k=(3,1,2,2) 4.436e-05      4.076e-15                6.188e-05
max residual of the defect identity: 2.44e-13
== seed E t h = 13 0.0 0.001 1e-5
max residual of the defect identity: 1.18e-16
== seed E t h = 17 -1.2 0.9 1e-5
max residual of the defect identity: 6.21e-14
== seed E t h = 11 1.9 0.999 1e-7 (t -> 1: |LHS| up to 1e10; relative residual |LHS-RHS-(-m*defect)|/|LHS| per identity)
Owx 1.097e+05      rel=7.39e-09
Oe2x 4.085e+05     rel=1.61e-08
Oe1x k=(1,0,0,0)   rel=7.07e-09
Oe1x k=(2,2,1,1)   rel=4.89e-09
Oe1x k=(3,1,2,2)   rel=2.09e-08
```

## 11. End of the flow at the preflight data

```
$ python3 t2040_endflow.py
  n           N        1-t0     lam^2/L^2     lam^2/L^3 | strict regime 1-t0 > lam^2/L^2     1-t0 >= lam^2/L^3 (LWterm_EXP index set)
  0   2.097e+06  9.0512e-06    1.5259e-05    3.8147e-06 | False                              True
  1   5.498e+11  4.1868e-10    9.3132e-10    1.1642e-10 | False                              True
  2   8.125e+14  1.2195e-12    3.1902e-12    2.6585e-13 | False                              True
  5   2.130e+20  5.6407e-17    1.9472e-16    8.1132e-18 | False                              True
 10   1.166e+25  9.1339e-21    4.0181e-20    9.1321e-22 | False                              True
 50   1.143e+37  2.3318e-30    1.8947e-29    9.2877e-32 | False                              True
500   8.293e+54  1.1996e-44    2.4310e-43    1.2131e-46 | False                              True
t = 1/16 (tInst): the strict regime lam^2/L^2 < 15/16 holds for every n (lam <= 1/64; Lean: strict_all).
```

## 12. Target statements extracted from the probe: the pins

```
$ python3 t2040_extract.py /Users/junyin/Lean_proof/RBM3D-wt/T2040/RBM3D/Probe/T2040Graphs.lean LWterm LWtermB LWtermExp LWtermExpS LWtermExpN LWtermEXP LWMoment LWMomentExp LWAnpKey LWAnpKeyGh LWAnp LWReduceB LWReduceT LWweightExp LWedgeExp LWggExp
-- probe lines 949-958
def LWterm (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ),
          LWAssm sz (STflowE z) t ε₀ Ψ Φ C₁ C₂ C₃ Cc →
          Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
            (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1 p.2 ω‖)
            (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * Φ n 0 *
              Φ n ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2)

-- probe lines 964-979
def LWtermB (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ (ε₀ c₀ C₃ : ℝ) (K : ℕ → ℕ) (Ψ : ℕ → ℝ), 0 < c₀ → (∀ n, K n ≤ sz.L n) →
          0 < ε₀ → LWWindow sz ε₀ Ψ → LWInit sz (STflowE z) t ε₀ Ψ →
          LWClass sz ε₀ C₃ (fun n r => (((sz.W n : ℕ) : ℝ) ^ (-c₀) *
            Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊r⌋₊ (K n))) ^ (1 / 2 : ℝ)) →
          LWLoop2 sz (STflowE z) t (fun n r => (((sz.W n : ℕ) : ℝ) ^ (-c₀) *
            Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊r⌋₊ (K n))) ^ (1 / 2 : ℝ)) →
          Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
            (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1 p.2 ω‖)
            (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ *
              (((sz.W n : ℕ) : ℝ) ^ (-c₀) * Bparam d (sz.L n) (sz.lam n) (t n) 0) ^ (1 / 2 : ℝ) *
              (((sz.W n : ℕ) : ℝ) ^ (-c₀) *
                Bparam d (sz.L n) (sz.lam n) (t n) (min (zdistInf d (sz.L n) (p.2 0 - p.2 1)) (K n))))

-- probe lines 999-1009
def LWtermExp (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ →
          ∀ D : ℝ, 0 < D →
            Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
              (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1 p.2 ω‖)
              (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
                  ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ)))

-- probe lines 1406-1417
def LWtermExpS (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ →
          ∀ D : ℝ, 0 < D →
            Prec sz (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
                sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
              (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1.1 p.1.2 ω‖)
              (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
                  ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ)))

-- probe lines 1421-1432
def LWtermExpN (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ →
          ∀ D : ℝ, 0 < D →
            Prec sz (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
                1 - t n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2})
              (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1.1 p.1.2 ω‖)
              (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
                  ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ)))

-- probe lines 1020-1029
def LWtermEXP (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLocalEntry sz (STflowE z) t → LWAvgLaw sz (STflowE z) t → STLmax sz (STflowE z) t →
        STLK sz (STflowE z) t → STDecay sz (STflowE z) t →
        Prec sz (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
            sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
          (fun n p _ => ‖∫ ω, LWE sz n (STflowE z n) (t n) p.1.1 p.1.2 ω ∂(sz.seqP)‖)
          (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

-- probe lines 1034-1045
def LWMoment (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p : ℕ), 2 ∣ p → ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ),
      ∃ c : ℝ, 0 < c ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
            ∀ (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ),
              LWAssm sz (STflowE z) t ε₀ Ψ Φ C₁ C₂ C₃ Cc →
              Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
                (fun n q _ => ∫ ω, ‖LWf sz n (STflowE z n) (t n) ω q.1 q.2‖ ^ p ∂(sz.seqP))
                (fun n q _ => ((etaT (STflowE z n) (t n))⁻¹ * Φ n 0 *
                  Φ n (c * ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ))) ^ p)

-- probe lines 1050-1063
def LWMomentExp (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p : ℕ), 2 ∣ p →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
          ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ →
            ∀ D : ℝ, 0 < D →
              Prec sz (U := fun n => {_q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
                  sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
                (fun n q _ => ∫ ω, ‖LWf sz n (STflowE z n) (t n) ω q.1.1 q.1.2‖ ^ p ∂(sz.seqP))
                (fun n q _ => ((etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                  sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
                    (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))) ^ p +
                  ((sz.W n : ℕ) : ℝ) ^ (-D))

-- probe lines 1084-1097
def LWAnpKey (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p q : ℕ), q ≤ p → ∀ Γ : RBM.Graph.NGraph p q, Γ.NoGhost → Γ.IsNested →
      ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
            ∀ Φ : ℕ → ℝ → ℝ, LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
              ∀ ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ,
                LWXi sz (STflowE z) t Φ ξ →
                Prec sz (U := fun n => (Fin p → Zd d (sz.L n)) × (Fin p → Zd d (sz.L n)))
                  (fun n ab ω => Γ.val (fun α β => ξ n α β ω) ab.1 ab.2)
                  (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (STflowE z n) (t n))⁻¹ ^ q *
                    Φ n 0 ^ (Γ.ordN - p) *
                    ∏ i, Φ n (c * ((zdistInf d (sz.L n) (ab.1 i - ab.2 i) : ℕ) : ℝ)))

-- probe lines 1101-1115
def LWAnpKeyGh (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p q : ℕ), q ≤ p → ∀ Γ : RBM.Graph.NGraph p q, Γ.GhostOK → Γ.IsNested →
      ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
            ∀ Φ : ℕ → ℝ → ℝ, LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
              ∀ ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ,
                LWXi sz (STflowE z) t Φ ξ →
                Prec sz (U := fun n => (Fin p → Zd d (sz.L n)) × (Fin p → Zd d (sz.L n)))
                  (fun n ab ω => Γ.val (fun α β => ξ n α β ω) ab.1 ab.2)
                  (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (STflowE z n) (t n))⁻¹ ^ q *
                    Φ n 0 ^ (Γ.ordN - Γ.nngh) *
                    ∏ i, (if Γ.noGhostPath i = true then
                      Φ n (c * ((zdistInf d (sz.L n) (ab.1 i - ab.2 i) : ℕ) : ℝ)) else 1))

-- probe lines 1121-1134
def LWAnp (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p q : ℕ), q ≤ p → ∀ Γ : RBM.Graph.NGraph p q, Γ.NoGhost → Γ.IsNested →
      ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
            ∀ Φ : ℕ → ℝ → ℝ, LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ →
              ∀ ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ,
                LWXi sz (STflowE z) t Φ ξ →
                Prec sz (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
                  (fun n ab ω => Γ.val (fun α β => ξ n α β ω) (fun _ => ab.1) (fun _ => ab.2))
                  (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (STflowE z n) (t n))⁻¹ ^ q *
                    Φ n (c * ((zdistInf d (sz.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ p *
                    Φ n 0 ^ (Γ.ordN - p))

-- probe lines 1140-1153
def LWReduceB (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ),
          LWAssm sz (STflowE z) t ε₀ Ψ Φ C₁ C₂ C₃ Cc →
          Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n q ω => ‖LWf sz n (STflowE z n) (t n) ω q.1 q.2‖)
            (fun n q _ => (etaT (STflowE z n) (t n))⁻¹ * Φ n 0 *
              Φ n ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ)) →
          Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
            (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1 p.2 ω‖)
            (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * Φ n 0 *
              Φ n ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2)

-- probe lines 1437-1455
def LWReduceT (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ →
          ∀ D : ℝ, 0 < D →
            Prec sz (U := fun n => {_q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
                sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
              (fun n q ω => ‖LWf sz n (STflowE z n) (t n) ω q.1.1 q.1.2‖)
              (fun n q _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
                  (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n)) +
                ((sz.W n : ℕ) : ℝ) ^ (-D)) →
            Prec sz (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
                sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
              (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1.1 p.1.2 ω‖)
              (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
                  ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ)))

-- probe lines 789-799
def LWweightExp (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ g E t : ℝ, |E| < 2 → 0 ≤ t → t < 1 →
    ∀ (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (x : Idx d L W),
      ∫ ω, lwGc d L W E t ω x x * lwf d L W E t P ω ∂(PF d L W g) =
        ∫ ω, (mE E * ∑ α, lwS d L W g t x α * lwGc d L W E t ω x x * lwGc d L W E t ω α α *
                lwf d L W E t P ω +
            mE E ^ 3 * ∑ α, ∑ β, lwSp d L W E g t x α * lwS d L W g t α β *
                lwGc d L W E t ω α α * lwGc d L W E t ω β β * lwf d L W E t P ω -
            mE E * ∑ α, lwS d L W g t x α * lwG d L W E t ω α x * lwdf d L W E t P ω α x -
            mE E ^ 3 * ∑ α, ∑ β, lwSp d L W E g t x α * lwS d L W g t α β *
                lwG d L W E t ω β α * lwdf d L W E t P ω β α) ∂(PF d L W g)

-- probe lines 814-843
def LWedgeExp (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ g E t : ℝ, |E| < 2 → 0 ≤ t → t < 1 →
    ∀ (k₁ k₂ k₃ k₄ : ℕ) (x : Idx d L W) (y : Fin (k₁ + 1) → Idx d L W) (y' : Fin k₂ → Idx d L W)
      (w : Fin k₃ → Idx d L W) (w' : Fin k₄ → Idx d L W)
      (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ),
      ∫ ω, lwG d L W E t ω x (y 0) * (oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ *
          lwf d L W E t P ω) ∂(PF d L W g) =
        ∫ ω, (mE E * (if x = y 0 then 1 else 0) *
            (oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ * lwf d L W E t P ω) +
          mE E * (∑ α, lwS d L W g t x α * lwGc d L W E t ω α α) *
            (lwG d L W E t ω x (y 0) * (oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ *
              lwf d L W E t P ω)) +
          ∑ i : Fin k₂, (mE E * star (mE E)) *
            (∑ α, lwS d L W g t x α * lwG d L W E t ω α (y 0) * lwGb d L W E t ω α (y' i)) *
            (oe1xRest d L W E t ω x y y' w w' (Finset.univ.erase i) Finset.univ * lwf d L W E t P ω) +
          ∑ i : Fin k₃, mE E ^ 2 *
            (∑ α, lwS d L W g t x α * lwG d L W E t ω α (y 0) * lwG d L W E t ω (w i) α) *
            (oe1xRest d L W E t ω x y y' w w' Finset.univ (Finset.univ.erase i) * lwf d L W E t P ω) +
          ∑ i : Fin k₂, mE E * lwGcb d L W E t ω x x *
            (∑ α, lwS d L W g t x α * lwG d L W E t ω α (y 0) * lwGb d L W E t ω α (y' i)) *
            (oe1xRest d L W E t ω x y y' w w' (Finset.univ.erase i) Finset.univ * lwf d L W E t P ω) +
          ∑ i : Fin k₃, mE E * lwGc d L W E t ω x x *
            (∑ α, lwS d L W g t x α * lwG d L W E t ω α (y 0) * lwG d L W E t ω (w i) α) *
            (oe1xRest d L W E t ω x y y' w w' Finset.univ (Finset.univ.erase i) * lwf d L W E t P ω) +
          (k₁ : ℂ) * mE E * (∑ α, lwS d L W g t x α * lwG d L W E t ω x α * lwG d L W E t ω α (y 0)) *
            (oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ * lwf d L W E t P ω) +
          (k₄ : ℂ) * mE E * (∑ α, lwS d L W g t x α * lwGb d L W E t ω α x * lwG d L W E t ω α (y 0)) *
            (oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ * lwf d L W E t P ω) -
          mE E * ∑ α, lwS d L W g t x α * oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ *
            lwG d L W E t ω α (y 0) * lwdf d L W E t P ω α x) ∂(PF d L W g)

-- probe lines 847-864
def LWggExp (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ g E t : ℝ, |E| < 2 → 0 ≤ t → t < 1 →
    ∀ (x y y' : Idx d L W) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ),
      ∫ ω, lwG d L W E t ω x y * lwG d L W E t ω y' x * lwf d L W E t P ω ∂(PF d L W g) =
        ∫ ω, (mE E * (if x = y then 1 else 0) * lwG d L W E t ω y' x * lwf d L W E t P ω +
          mE E ^ 3 * lwSp d L W E g t x y * lwG d L W E t ω y' y * lwf d L W E t P ω +
          mE E * (∑ α, lwS d L W g t x α * lwGc d L W E t ω α α) *
            (lwG d L W E t ω x y * lwG d L W E t ω y' x * lwf d L W E t P ω) +
          mE E ^ 3 * ∑ α, ∑ β, lwSp d L W E g t x α * lwS d L W g t α β * lwGc d L W E t ω β β *
            lwG d L W E t ω α y * lwG d L W E t ω y' α * lwf d L W E t P ω +
          mE E * lwGc d L W E t ω x x * ∑ α, lwS d L W g t x α * lwG d L W E t ω α y *
            lwG d L W E t ω y' α * lwf d L W E t P ω +
          mE E ^ 3 * ∑ α, ∑ β, lwSp d L W E g t x α * lwS d L W g t α β * lwGc d L W E t ω α α *
            lwG d L W E t ω β y * lwG d L W E t ω y' β * lwf d L W E t P ω -
          mE E * ∑ α, lwS d L W g t x α * lwG d L W E t ω α y * lwG d L W E t ω y' x *
            lwdf d L W E t P ω α x -
          mE E ^ 3 * ∑ α, ∑ β, lwSp d L W E g t x α * lwS d L W g t α β * lwG d L W E t ω β y *
            lwG d L W E t ω y' α * lwdf d L W E t P ω β α) ∂(PF d L W g)
```

## 13. Definitions the pins use

```
$ python3 t2040_extract.py /Users/junyin/Lean_proof/RBM3D-wt/T2040/RBM3D/Probe/T2040Graphs.lean LWAssm LWAssmExp LWInteg LWInit LWWindow LWLoop2 LWLoopExp LWClass LWPsiRel LWPsiAll LWXi LWAvgLaw LWf LWE LWcut LWS resPoly dH lwG lwGc lwS lwSp lwf lwdf oe1xRest
-- probe lines 943-945
def LWAssm (E t : ℕ → ℝ) (ε₀ : ℝ) (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ) (C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) : Prop :=
  0 < ε₀ ∧ LWWindow sz ε₀ Ψ ∧ LWInit sz E t ε₀ Ψ ∧ LWClass sz ε₀ C₃ Φ ∧ LWPsiRel C₁ C₂ Cc Φ ∧
    LWLoop2 sz E t Φ

-- probe lines 992-995
def LWAssmExp (E t : ℕ → ℝ) (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ) : Prop :=
  0 < ε₀ ∧ LWWindow sz ε₀ Ψ ∧ LWInit sz E t ε₀ Ψ ∧ (∀ n, 0 ≤ ℓ n) ∧
    (∀ n, ℓ n ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) (t n)) ∧
    LWLoopExp sz E t ℓ

-- probe lines 896-898
def LWInteg (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E t : ℝ), |E| < 2 → 0 ≤ t → t < 1 → ∀ (p : ℕ)
    (x y : Idx d (sz.L n) (sz.W n)), Integrable (fun ω => ‖LWf sz n E t ω x y‖ ^ p) sz.seqP

-- probe lines 913-916
def LWInit (E t : ℕ → ℝ) (ε₀ : ℝ) (Ψ : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖STGM sz n (E n) (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ∧
    Prec sz (U := fun _ => Unit) (fun n _ ω => STmaxLoop2 sz n (E n) (t n) ω) (fun n _ _ => Ψ n ^ 2)

-- probe lines 919-920
def LWWindow (ε₀ : ℝ) (Ψ : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧ Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)

-- probe lines 923-926
def LWLoop2 (E t : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ) : Prop :=
  Prec sz (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
    (fun n p ω => ‖Lloop sz n (E n) (t n) ![p.1, !p.1] ![p.2.1, p.2.2] ω‖)
    (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.2.1 - p.2.2) : ℕ) : ℝ) ^ 2)

-- probe lines 983-988
def LWLoopExp (E t : ℕ → ℝ) (ℓ : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz (U := fun n => Bool × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖Lloop sz n (E n) (t n) ![p.1, !p.1] ![p.2.1, p.2.2] ω‖)
      (fun n p _ => (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
        ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.2.1 - p.2.2) : ℕ) : ℝ))

-- probe lines 930-932
def LWClass (ε₀ C₃ : ℝ) (Φ : ℕ → ℝ → ℝ) : Prop :=
  (∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r → 0 < Φ n r ∧ Φ n r ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ∧
    0 < C₃ ∧ ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ C₃ * Φ n 0

-- probe lines 937-940
def LWPsiRel (C₁ C₂ : ℝ) (Cc : ℝ → ℝ) (Φ : ℕ → ℝ → ℝ) : Prop :=
  (∀ n, AntitoneOn (Φ n) (Set.Ici 0)) ∧ 1 < C₁ ∧ 1 < C₂ ∧
    (∀ C : ℝ, 1 < C → ∀ᶠ n in atTop, ∀ ℓ : ℝ, 0 ≤ ℓ → ℓ ≤ C → Φ n 0 ≤ Cc C * Φ n ℓ) ∧
    ∀ᶠ n in atTop, ∀ ℓ₁ ℓ₂ : ℝ, 1 ≤ ℓ₁ → ℓ₁ ≤ ℓ₂ → Φ n ℓ₁ ≤ C₁ * (ℓ₂ / ℓ₁) ^ C₂ * Φ n ℓ₂

-- probe lines 1077-1078
def LWPsiAll (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Φ : ℕ → ℝ → ℝ) : Prop :=
  0 < ε₀ ∧ LWClass sz ε₀ C₃ Φ ∧ LWPsiRel C₁ C₂ Cc Φ

-- probe lines 1069-1074
def LWXi (E t : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ) (ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) : Prop :=
  (∀ n α β ω, 0 ≤ ξ n α β ω ∧ ξ n α β ω = ξ n β α ω) ∧
    Prec sz (U := fun n => Zd d (sz.L n) × Zd d (sz.L n)) (fun n p ω => ξ n p.1 p.2 ω)
      (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.1 - p.2) : ℕ) : ℝ)) ∧
    Prec sz (U := fun n => Zd d (sz.L n)) (fun n α ω => ∑ β, ξ n α β ω ^ 2)
      (fun n _ _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (E n) (t n))⁻¹)

-- probe lines 1012-1015
def LWAvgLaw (E t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Zd d (sz.L n))
    (fun n a ω => ‖Lloop sz n (E n) (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - mE (E n)‖)
    (fun n _ _ => sz.Bctl n (t n))

-- probe lines 890-892
def LWf (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  ∑ α, if α = x ∨ α = y then 0 else
    ∑ β, (LWS sz n α β : ℂ) * STGM sz n E t ω β β * Gt sz n E t true ω x α * Gt sz n E t true ω α y

-- probe lines 909-910
def LWE (n : ℕ) (E t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  LWcut sz n E t (σ 1) (σ 0) (a 1) (a 0) ω + LWcut sz n E t (σ 0) (σ 1) (a 0) (a 1) ω

-- probe lines 902-904
def LWcut (n : ℕ) (E t : ℝ) (σc σo : Bool) (ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, SB d (sz.L n) (sz.lam n) a₁ a₂ *
    (Lloop sz n E t ![σc] ![a₁] ω - mSigma E σc) * Lloop sz n E t ![σc, σc, σo] ![a₂, ac, ao] ω

-- probe lines 885-886
def LWS (n : ℕ) (α β : Idx d (sz.L n) (sz.W n)) : ℝ :=
  svarF d (sz.L n) (sz.W n) (sz.lam n) α β

-- probe lines 756-758
def resPoly (z : ℂ) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) :
    Matrix (Idx d L W) (Idx d L W) ℂ → ℂ :=
  fun H => MvPolynomial.eval (fun v => Gres H z v.1 v.2.1 v.2.2) P

-- probe lines 745-746
def dH {ι : Type*} [DecidableEq ι] (F : Matrix ι ι ℂ → ℂ) (H : Matrix ι ι ℂ) (α w : ι) : ℂ :=
  deriv (fun s : ℂ => F (H + s • Matrix.single α w 1)) 0

-- probe lines 762-762
def lwG (ω : Ω d L W) (x y : Idx d L W) : ℂ := Gres (Hflow d L W t ω) (zt E t) true x y

-- probe lines 764-764
def lwGc (ω : Ω d L W) (x y : Idx d L W) : ℂ := lwG d L W E t ω x y - if x = y then mE E else 0

-- probe lines 766-766
def lwS (x y : Idx d L W) : ℂ := (t : ℂ) * svarF d L W g x y

-- probe lines 767-768
def lwSp : Matrix (Idx d L W) (Idx d L W) ℂ :=
  Matrix.of (lwS d L W g t) * Ring.inverse (1 - (mE E) ^ 2 • Matrix.of (lwS d L W g t))

-- probe lines 777-778
def lwf (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (ω : Ω d L W) : ℂ :=
  resPoly d L W (zt E t) P (Hflow d L W t ω)

-- probe lines 781-782
def lwdf (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (ω : Ω d L W) (α w : Idx d L W) : ℂ :=
  dH (resPoly d L W (zt E t) P) (Hflow d L W t ω) α w

-- probe lines 804-808
def oe1xRest {k₁ k₂ k₃ k₄ : ℕ} (ω : Ω d L W) (x : Idx d L W) (y : Fin (k₁ + 1) → Idx d L W)
    (y' : Fin k₂ → Idx d L W) (w : Fin k₃ → Idx d L W) (w' : Fin k₄ → Idx d L W)
    (s₂ : Finset (Fin k₂)) (s₃ : Finset (Fin k₃)) : ℂ :=
  (∏ i : Fin k₁, lwG d L W E t ω x (y i.succ)) * (∏ i ∈ s₂, lwGb d L W E t ω x (y' i)) *
    (∏ i ∈ s₃, lwG d L W E t ω (w i) x) * (∏ i : Fin k₄, lwGb d L W E t ω (w' i) x)
```

## 14. Vocabulary: structures, value, counters, nested graphs

```
$ python3 t2040_extract.py /Users/junyin/Lean_proof/RBM3D-wt/T2040/RBM3D/Probe/T2040Graphs.lean LData SEdge WEdge DEdge LGraph GTerm GTerm.eval SEdge.val WEdge.val DEdge.val LGraph.term LGraph.val LGraph.counters NGraph NEdge IsNested GhostOK ordN val
-- probe lines 62-66
structure LData (ι : Type*) where
  G : Matrix ι ι ℂ
  M : Matrix ι ι ℂ
  S : Matrix ι ι ℂ
  Sp : Matrix ι ι ℂ

-- probe lines 71-75
structure SEdge (V : Type*) where
  σ : Bool
  circ : Bool
  src : V
  dst : V

-- probe lines 78-82
structure WEdge (V : Type*) where
  col : Bool
  σ : Bool
  x : V
  y : V

-- probe lines 85-88
structure DEdge (V : Type*) where
  eq : Bool
  x : V
  y : V

-- probe lines 93-97
structure LGraph (E I : Type*) where
  solid : List (SEdge (E ⊕ I))
  waved : List (WEdge (E ⊕ I))
  dotted : List (DEdge (E ⊕ I))
  coeff : ℂ

-- probe lines 297-303
inductive GTerm : Type → Type 1
  | one {V : Type} : GTerm V
  | solid {V : Type} (e : SEdge V) : GTerm V
  | waved {V : Type} (e : WEdge V) : GTerm V
  | const {V : Type} (c : ℂ) : GTerm V
  | mul {V : Type} (a b : GTerm V) : GTerm V
  | sum {V : Type} (a : GTerm (Option V)) : GTerm V

-- probe lines 306-312
def GTerm.eval (D : LData ι) : {V : Type} → GTerm V → (V → ι) → ℂ
  | _, .one, _ => 1
  | _, .const c, _ => c
  | _, .solid e, ℓ => e.val D ℓ
  | _, .waved e, ℓ => e.val D ℓ
  | _, .mul a b, ℓ => a.eval D ℓ * b.eval D ℓ
  | _, .sum a, ℓ => ∑ u : ι, a.eval D (fun v => v.elim u ℓ)

-- probe lines 104-106
def SEdge.val (D : LData ι) (ℓ : V → ι) (e : SEdge V) : ℂ :=
  let g : ℂ := D.G (ℓ e.src) (ℓ e.dst) - if e.circ then D.M (ℓ e.src) (ℓ e.dst) else 0
  if e.σ then g else star g

-- probe lines 109-111
def WEdge.val (D : LData ι) (ℓ : V → ι) (e : WEdge V) : ℂ :=
  if e.col then (if e.σ then D.Sp (ℓ e.x) (ℓ e.y) else star (D.Sp (ℓ e.y) (ℓ e.x)))
  else D.S (ℓ e.x) (ℓ e.y)

-- probe lines 114-115
def DEdge.val (ℓ : V → ι) (e : DEdge V) : ℂ :=
  if (ℓ e.x = ℓ e.y) ↔ (e.eq = true) then 1 else 0

-- probe lines 118-120
def LGraph.term (Γ : LGraph E I) (D : LData ι) (ℓ : E ⊕ I → ι) : ℂ :=
  Γ.coeff * (Γ.solid.map (SEdge.val D ℓ)).prod * (Γ.waved.map (WEdge.val D ℓ)).prod *
    (Γ.dotted.map (DEdge.val ℓ)).prod

-- probe lines 124-127
def LGraph.val (Γ : LGraph E I) (D : LData ι) (ℓe : E → ι) : ℂ :=
  ∑ ℓi : I → ι, Γ.term D (Sum.elim ℓe ℓi)

omit [DecidableEq ι] in

-- probe lines 171-171
def LGraph.counters (Γ : LGraph E I) : Counters := ⟨Γ.nS, Γ.nW, Γ.nV, Γ.nM, 0, 0⟩

-- probe lines 348-350
structure NGraph (p q : ℕ) where
  es : List (NEdge p q)
  path : Fin p → List (Fin es.length × NV p q)

-- probe lines 342-345
structure NEdge (p q : ℕ) where
  ghost : Bool
  u : NV p q
  v : NV p q

-- probe lines 374-380
def IsNested : Prop :=
  (∀ e ∈ Γ.es, e.u ≠ e.v) ∧
  (∀ i, Γ.WalkOK i) ∧
  (∀ i, ((Γ.path i).map Prod.fst).Nodup) ∧
  (∀ i j, i ≠ j → ∀ st ∈ Γ.path i, ∀ st' ∈ Γ.path j, st.1 ≠ st'.1) ∧
  (∀ α : Fin q, ∃ i j, i ≠ j ∧ Γ.Visits i (Sum.inr α) ∧ Γ.Visits j (Sum.inr α)) ∧
  (∀ A : Finset (Fin q), A.card ≤ (Finset.univ.filter fun j : Fin p => ∃ α ∈ A, Γ.Visits j (Sum.inr α)).card)

-- probe lines 387-389
def GhostOK : Prop :=
  ∀ i, (((Γ.path i).filter fun st => (Γ.es.get st.1).ghost).length ≤ 1) ∧
    ∀ st ∈ Γ.path i, (Γ.es.get st.1).ghost = true → (Γ.path i).head? = some st ∨ (Γ.path i).getLast? = some st

-- probe lines 402-402
def ordN : ℤ := ord ⟨Γ.nSolid, 0, q, 0, 0, 0⟩

-- probe lines 104-106
def SEdge.val (D : LData ι) (ℓ : V → ι) (e : SEdge V) : ℂ :=
  let g : ℂ := D.G (ℓ e.src) (ℓ e.dst) - if e.circ then D.M (ℓ e.src) (ℓ e.dst) else 0
  if e.σ then g else star g

-- probe lines 109-111
def WEdge.val (D : LData ι) (ℓ : V → ι) (e : WEdge V) : ℂ :=
  if e.col then (if e.σ then D.Sp (ℓ e.x) (ℓ e.y) else star (D.Sp (ℓ e.y) (ℓ e.x)))
  else D.S (ℓ e.x) (ℓ e.y)

-- probe lines 114-115
def DEdge.val (ℓ : V → ι) (e : DEdge V) : ℂ :=
  if (ℓ e.x = ℓ e.y) ↔ (e.eq = true) then 1 else 0

-- probe lines 124-127
def LGraph.val (Γ : LGraph E I) (D : LData ι) (ℓe : E → ι) : ℂ :=
  ∑ ℓi : I → ι, Γ.term D (Sum.elim ℓe ℓi)

omit [DecidableEq ι] in

-- probe lines 406-408
def val {ι : Type*} [Fintype ι] (ξ : ι → ι → ℝ) (a b : Fin p → ι) : ℝ :=
  ∑ ℓ : Fin q → ι, (Γ.es.map fun e =>
    if e.ghost then (1 : ℝ) else ξ (Sum.elim (Sum.elim a b) ℓ e.u) (Sum.elim (Sum.elim a b) ℓ e.v)).prod
```

## 15. Skeleton and proved lemmas: statements

```
$ python3 t2040_extract.py /Users/junyin/Lean_proof/RBM3D-wt/T2040/RBM3D/Probe/T2040Graphs.lean lwterm_of_moment lwtermexpS_of_momentexp lwtermexp_of_regimes stochDomAt_det stochDomAt_of_split stochDomAt_congr_right shift lwanp_of_key owx_defect_identity owx_smallest owx_second owx_smallest_E owxT_smallest p2Graph_val p2Graph_val_eq p2Graph_counters figGraph_counters figGraph_val figAux_nested figAux_ord
-- probe lines 1268-1269
theorem lwterm_of_moment (hMom : LWMoment d) (hRed : LWReduceB d) (hint : LWInteg d) :
    LWterm d := ...

-- probe lines 1459-1460
theorem lwtermexpS_of_momentexp (hMom : LWMomentExp d) (hRed : LWReduceT d) (hint : LWInteg d) :
    LWtermExpS d := ...

-- probe lines 1537-1537
theorem lwtermexp_of_regimes (hS : LWtermExpS d) (hN : LWtermExpN d) : LWtermExp d := ...

-- probe lines 1168-1171
theorem stochDomAt_det {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {U : ℕ → Type*} {size : ℕ → ℕ} {a ζ : ∀ l, U l → ℝ} (hsize : Tendsto size atTop atTop)
    (h : StochDomAt P size (fun l u _ => a l u) (fun l u _ => ζ l u)) :
    ∀ τ > (0 : ℝ), ∀ᶠ l in atTop, ∀ u, a l u ≤ (size l : ℝ) ^ τ * ζ l u := ...

-- probe lines 1358-1365
theorem stochDomAt_of_split {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}
    {size : ℕ → ℕ} (hsize : Tendsto size atTop atTop) (p : ∀ l, U l → Prop)
    {ξ ζ : ∀ l, U l → Ω → ℝ}
    (h1 : StochDomAt P size (U := fun l => {u : U l // p l u}) (fun l u ω => ξ l u.1 ω)
      (fun l u ω => ζ l u.1 ω))
    (h2 : StochDomAt P size (U := fun l => {u : U l // ¬ p l u}) (fun l u ω => ξ l u.1 ω)
      (fun l u ω => ζ l u.1 ω)) :
    StochDomAt P size ξ ζ := ...

-- probe lines 1245-1247
theorem stochDomAt_congr_right {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}
    {size : ℕ → ℕ} {ξ ζ ζ' : ∀ l, U l → Ω → ℝ} (h : StochDomAt P size ξ ζ')
    (heq : ∀ᶠ l in atTop, ∀ u ω, ζ' l u ω = ζ l u ω) : StochDomAt P size ξ ζ := ...

-- probe lines 1200-1202
theorem LWPsiAll.shift {ε₀ C₁ C₂ C₃ : ℝ} {Cc : ℝ → ℝ} {Φ : ℕ → ℝ → ℝ}
    (h : LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ) {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r → Φ n (c * r) ≤ K * Φ n r := ...

-- probe lines 1551-1551
theorem lwanp_of_key (h : LWAnpKey d) : LWAnp d := ...

-- probe lines 456-464
theorem owx_defect_identity (z m s : ℂ) (hm0 : m ≠ 0) (hzm : z + s * m = -m⁻¹)
    (G S Sp : Matrix ι ι ℂ) (hS : ∀ i, ∑ j, S i j = s)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * S w j = S i j) (f : ℂ) (df : ι → ι → ℂ) (x : ι) :
    (G x x - m) * f -
      (m * ∑ α, S x α * (G x x - m) * (G α α - m) * f +
        m ^ 3 * ∑ α, ∑ β, Sp x α * S α β * (G α α - m) * (G β β - m) * f -
        m * ∑ α, S x α * G α x * df α x -
        m ^ 3 * ∑ α, ∑ β, Sp x α * S α β * G β α * df β α) =
      -m * ∑ w, ((if x = w then 1 else 0) + m ^ 2 * Sp x w) * owxDefect z G S f df w := ...

-- probe lines 585-590
theorem owx_smallest (D : LData ι) (m z s : ℂ) (hm0 : m ≠ 0) (hzm : z + s * m = -m⁻¹)
    (hM : ∀ i j, D.M i j = if i = j then m else 0) (hS : ∀ i, ∑ j, D.S i j = s)
    (hSp : ∀ i j, D.Sp i j - m ^ 2 * ∑ w, D.Sp i w * D.S w j = D.S i j) (x : ι) :
    owxG0.val D (fun _ => x) - ((owxG1 m).val D (fun _ => x) + (owxG2 m).val D (fun _ => x)) =
      -m * ∑ w, ((if x = w then 1 else 0) + m ^ 2 * D.Sp x w) *
        owxDefect z D.G D.S 1 (fun _ _ => 0) w := ...

-- probe lines 640-646
theorem owx_second (D : LData ι) (m z s : ℂ) (hm0 : m ≠ 0) (hzm : z + s * m = -m⁻¹)
    (hM : ∀ i j, D.M i j = if i = j then m else 0) (hS : ∀ i, ∑ j, D.S i j = s)
    (hSp : ∀ i j, D.Sp i j - m ^ 2 * ∑ w, D.Sp i w * D.S w j = D.S i j) (x y : ι) :
    owxH0.val D ![x, y] - ((owxH1 m).val D ![x, y] + (owxH2 m).val D ![x, y] +
        (owxH3 m).val D ![x, y] + (owxH4 m).val D ![x, y]) =
      -m * ∑ w, ((if x = w then 1 else 0) + m ^ 2 * D.Sp x w) *
        owxDefect z D.G D.S (D.G x y) (fun α w => -(D.G x α * D.G w y)) w := ...

-- probe lines 676-687
theorem owx_smallest_E {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Dω : Ω → LData ι) (m z s : ℂ)
    (Sp₀ : Matrix ι ι ℂ) (hm0 : m ≠ 0) (hzm : z + s * m = -m⁻¹)
    (hM : ∀ ω i j, (Dω ω).M i j = if i = j then m else 0) (hS : ∀ ω i, ∑ j, (Dω ω).S i j = s)
    (hSp : ∀ ω i j, (Dω ω).Sp i j - m ^ 2 * ∑ w, (Dω ω).Sp i w * (Dω ω).S w j = (Dω ω).S i j)
    (hSp0 : ∀ ω, (Dω ω).Sp = Sp₀) (x : ι)
    (hZint : ∀ w, Integrable (fun ω => owxDefect z (Dω ω).G (Dω ω).S 1 (fun _ _ => 0) w) P)
    (hZ : ∀ w, ∫ ω, owxDefect z (Dω ω).G (Dω ω).S 1 (fun _ _ => 0) w ∂P = 0)
    (h0 : Integrable (fun ω => owxG0.val (Dω ω) (fun _ => x)) P)
    (h1 : Integrable (fun ω => (owxG1 m).val (Dω ω) (fun _ => x)) P)
    (h2 : Integrable (fun ω => (owxG2 m).val (Dω ω) (fun _ => x)) P) :
    ∫ ω, owxG0.val (Dω ω) (fun _ => x) ∂P =
      ∫ ω, (owxG1 m).val (Dω ω) (fun _ => x) ∂P + ∫ ω, (owxG2 m).val (Dω ω) (fun _ => x) ∂P := ...

-- probe lines 719-724
theorem owxT_smallest (D : LData ι) (m z s : ℂ) (hm0 : m ≠ 0) (hzm : z + s * m = -m⁻¹)
    (hM : ∀ i j, D.M i j = if i = j then m else 0) (hS : ∀ i, ∑ j, D.S i j = s)
    (hSp : ∀ i j, D.Sp i j - m ^ 2 * ∑ w, D.Sp i w * D.S w j = D.S i j) (x : ι) :
    owxT0.eval D (fun _ => x) - ((owxT1 m).eval D (fun _ => x) + (owxT2 m).eval D (fun _ => x)) =
      -m * ∑ w, ((if x = w then 1 else 0) + m ^ 2 * D.Sp x w) *
        owxDefect z D.G D.S 1 (fun _ _ => 0) w := ...

-- probe lines 191-197
theorem p2Graph_val (D : LData ι) (x y : ι) :
    p2Graph.val D ![x, y] =
      ∑ a₁, ∑ b₁, ∑ a₂, ∑ b₂,
        (if a₁ ≠ x ∧ a₁ ≠ y ∧ a₂ ≠ x ∧ a₂ ≠ y then 1 else 0) *
        (D.S a₁ b₁ * D.S a₂ b₂ *
         ((D.G b₁ b₁ - D.M b₁ b₁) * D.G x a₁ * D.G a₁ y) *
         star ((D.G b₂ b₂ - D.M b₂ b₂) * D.G x a₂ * D.G a₂ y)) := ...

-- probe lines 210-211
theorem p2Graph_val_eq (D : LData ι) (hS : ∀ i j, star (D.S i j) = D.S i j) (x y : ι) :
    p2Graph.val D ![x, y] = fxyVal D x y * star (fxyVal D x y) := ...

-- probe lines 229-230
theorem p2Graph_counters :
    p2Graph.nS = 6 ∧ p2Graph.nW = 2 ∧ p2Graph.nV = 4 ∧ p2Graph.nM = 2 := ...

-- probe lines 255-256
theorem figGraph_counters :
    figGraph.nS = 8 ∧ figGraph.nW = 4 ∧ figGraph.nV = 6 ∧ figGraph.nM = 2 := ...

-- probe lines 266-273
theorem figGraph_val (D : LData ι) (x y : ι) :
    figGraph.val D ![x, y] =
      ∑ a₁, ∑ b₁, ∑ c₁, ∑ a₂, ∑ b₂, ∑ c₂,
        (if x = a₁ then 0 else 1) * (if a₁ = b₂ then 0 else 1) * (if c₂ = y then 0 else 1) *
        (if b₁ = c₁ then 0 else 1) * (if x = c₁ then 0 else 1) * (if b₁ = a₂ then 0 else 1) *
        (if a₂ = y then 0 else 1) * (if c₂ = b₂ then 0 else 1) *
        (D.G x a₁ * D.G a₁ b₂ * D.G c₂ y * D.G b₁ c₁ * star (D.G x c₁) * star (D.G b₁ a₂) *
          star (D.G a₂ y) * star (D.G c₂ b₂) * (D.S a₁ b₁ * D.S b₁ c₁ * D.S a₂ b₂ * D.S b₂ c₂)) := ...

-- probe lines 425-425
theorem figAux_nested : figAux.IsNested ∧ figAux.NoGhost := ...

-- probe lines 430-430
theorem figAux_ord : figAux.ordN = 2 := ...
```

## 16. Compiled nonempty instances: statements

```
$ python3 t2040_extract.py /Users/junyin/Lean_proof/RBM3D-wt/T2040/RBM3D/Probe/T2040Graphs.lean inst_LWterm inst_LWtermB inst_LWtermExp inst_LWtermExpS inst_LWMoment inst_LWMomentExp inst_LWtermEXP inst_AnpKey inst_AnpKeyGh inst_Anp inst_ssl inst_edge inst_gg inst_LWterm_endT inst_LWtermExp_endT inst_LWMoment_endT inst_AnpKey_endT inst_LWtermEXP_endT inst_chain_LWterm inst_chain_LWtermExp inst_chain_Anp inst_shift inst_owx_smallest inst_owx_second inst_owx_smallest_E inst_owx_smallest_E_unit inst_figGraph_val inst_p2Graph_val_eq
-- probe lines 1628-1633
theorem inst_LWterm (h : LWterm 3) (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0)
    (hL : LWLoop2 sz0 (STflowE z0) tInst Φ0) :
    Prec sz0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖LWE sz0 n (STflowE z0 n) (tInst n) p.1 p.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * Φ0 n 0 *
        Φ0 n ((zdistInf 3 (sz0.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2) := ...

-- probe lines 1952-1959
theorem inst_LWtermB (h : LWtermB 3) (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0)
    (hL : LWLoop2 sz0 (STflowE z0) tInst ΦB) :
    Prec sz0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖LWE sz0 n (STflowE z0 n) (tInst n) p.1 p.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ *
        (((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) * Bparam 3 (sz0.L n) (sz0.lam n) (tInst n) 0) ^ (1 / 2 : ℝ) *
        (((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) *
          Bparam 3 (sz0.L n) (sz0.lam n) (tInst n) (min (zdistInf 3 (sz0.L n) (p.2 0 - p.2 1)) 1))) := ...

-- probe lines 1670-1676
theorem inst_LWtermExp (h : LWtermExp 3) (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0)
    (hL : LWLoopExp sz0 (STflowE z0) tInst ℓ0) (D : ℝ) (hD : 0 < D) :
    Prec sz0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖LWE sz0 n (STflowE z0 n) (tInst n) p.1 p.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ (1 / 2 : ℝ) *
        ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailW 3 (sz0.L n) (sz0.lam n) (tInst n) (ℓ0 n)
          ((sz0.W n : ℕ) : ℝ) D ((zdistInf 3 (sz0.L n) (p.2 0 - p.2 1) : ℕ) : ℝ))) := ...

-- probe lines 2104-2111
theorem inst_LWtermExpS (h : LWtermExpS 3) (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0)
    (hL : LWLoopExp sz0 (STflowE z0) tInst ℓ0) (D : ℝ) (hD : 0 < D) :
    Prec sz0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 < 1 - tInst n})
      (fun n p ω => ‖LWE sz0 n (STflowE z0 n) (tInst n) p.1.1 p.1.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ (1 / 2 : ℝ) *
        ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailW 3 (sz0.L n) (sz0.lam n) (tInst n) (ℓ0 n)
          ((sz0.W n : ℕ) : ℝ) D ((zdistInf 3 (sz0.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ))) := ...

-- probe lines 1682-1688
theorem inst_LWMoment (h : LWMoment 3) (p : ℕ) (hp : 2 ∣ p)
    (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoop2 sz0 (STflowE z0) tInst Φ0) :
    ∃ c : ℝ, 0 < c ∧
      Prec sz0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
        (fun n q _ => ∫ ω, ‖LWf sz0 n (STflowE z0 n) (tInst n) ω q.1 q.2‖ ^ p ∂(sz0.seqP))
        (fun n q _ => ((etaT (STflowE z0 n) (tInst n))⁻¹ * Φ0 n 0 *
          Φ0 n (c * ((zdistInf 3 (sz0.L n) (STblk sz0 n q.1 - STblk sz0 n q.2) : ℕ) : ℝ))) ^ p) := ...

-- probe lines 1695-1704
theorem inst_LWMomentExp (h : LWMomentExp 3) (p : ℕ) (hp : 2 ∣ p)
    (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst ℓ0)
    (D : ℝ) (hD : 0 < D) :
    Prec sz0 (U := fun n => {_q : Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 < 1 - tInst n})
      (fun n q _ => ∫ ω, ‖LWf sz0 n (STflowE z0 n) (tInst n) ω q.1.1 q.1.2‖ ^ p ∂(sz0.seqP))
      (fun n q _ => ((etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ (1 / 2 : ℝ) *
        sfT 3 (sz0.L n) ((sz0.W n : ℕ) : ℝ) (sz0.lam n) (tInst n)
          (min ((zdistInf 3 (sz0.L n) (STblk sz0 n q.1.1 - STblk sz0 n q.1.2) : ℕ) : ℝ) (ℓ0 n))) ^ p +
        ((sz0.W n : ℕ) : ℝ) ^ (-D)) := ...

-- probe lines 1710-1716
theorem inst_LWtermEXP (h : LWtermEXP 3) (h1 : STLocalEntry sz0 (STflowE z0) tInst)
    (h2 : LWAvgLaw sz0 (STflowE z0) tInst) (h3 : STLmax sz0 (STflowE z0) tInst)
    (h4 : STLK sz0 (STflowE z0) tInst) (h5 : STDecay sz0 (STflowE z0) tInst) :
    Prec sz0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - tInst n})
      (fun n p _ => ‖∫ ω, LWE sz0 n (STflowE z0 n) (tInst n) p.1.1 p.1.2 ω ∂(sz0.seqP)‖)
      (fun n _ _ => (1 - tInst n)⁻¹ * (sz0.Bctl n (tInst n)) ^ (5 / 2 : ℝ)) := ...

-- probe lines 1730-1737
theorem inst_AnpKey (h : LWAnpKey 3)
    (ξ : ∀ n, Zd 3 (sz0.L n) → Zd 3 (sz0.L n) → sz0.SeqΩ → ℝ) (hξ : LWXi sz0 (STflowE z0) tInst Φ0 ξ) :
    ∃ c : ℝ, 0 < c ∧
      Prec sz0 (U := fun n => (Fin 2 → Zd 3 (sz0.L n)) × (Fin 2 → Zd 3 (sz0.L n)))
        (fun n ab ω => RBM.Graph.figAux.val (fun α β => ξ n α β ω) ab.1 ab.2)
        (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * etaT (STflowE z0 n) (tInst n))⁻¹ ^ 2 *
          Φ0 n 0 ^ (RBM.Graph.figAux.ordN - (2 : ℕ)) *
          ∏ i, Φ0 n (c * ((zdistInf 3 (sz0.L n) (ab.1 i - ab.2 i) : ℕ) : ℝ))) := ...

-- probe lines 2117-2125
theorem inst_AnpKeyGh (h : LWAnpKeyGh 3)
    (ξ : ∀ n, Zd 3 (sz0.L n) → Zd 3 (sz0.L n) → sz0.SeqΩ → ℝ) (hξ : LWXi sz0 (STflowE z0) tInst Φ0 ξ) :
    ∃ c : ℝ, 0 < c ∧
      Prec sz0 (U := fun n => (Fin 2 → Zd 3 (sz0.L n)) × (Fin 2 → Zd 3 (sz0.L n)))
        (fun n ab ω => RBM.Graph.figAux.val (fun α β => ξ n α β ω) ab.1 ab.2)
        (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * etaT (STflowE z0 n) (tInst n))⁻¹ ^ 2 *
          Φ0 n 0 ^ (RBM.Graph.figAux.ordN - RBM.Graph.figAux.nngh) *
          ∏ i, (if RBM.Graph.figAux.noGhostPath i = true then
            Φ0 n (c * ((zdistInf 3 (sz0.L n) (ab.1 i - ab.2 i) : ℕ) : ℝ)) else 1)) := ...

-- probe lines 1743-1750
theorem inst_Anp (h : LWAnp 3)
    (ξ : ∀ n, Zd 3 (sz0.L n) → Zd 3 (sz0.L n) → sz0.SeqΩ → ℝ) (hξ : LWXi sz0 (STflowE z0) tInst Φ0 ξ) :
    ∃ c : ℝ, 0 < c ∧
      Prec sz0 (U := fun n => Zd 3 (sz0.L n) × Zd 3 (sz0.L n))
        (fun n ab ω => RBM.Graph.figAux.val (fun α β => ξ n α β ω) (fun _ => ab.1) (fun _ => ab.2))
        (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * etaT (STflowE z0 n) (tInst n))⁻¹ ^ 2 *
          Φ0 n (c * ((zdistInf 3 (sz0.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ 2 *
          Φ0 n 0 ^ (RBM.Graph.figAux.ordN - (2 : ℕ))) := ...

-- probe lines 1776-1777
def inst_ssl (h : LWweightExp 3) (x : Idx 3 3 2) :=
  h 3 2 (by norm_num) 1 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) P01 x

-- probe lines 1780-1782
def inst_edge (h : LWedgeExp 3) (x : Idx 3 3 2) (y : Fin 2 → Idx 3 3 2) (y' : Fin 1 → Idx 3 3 2)
    (w : Fin 1 → Idx 3 3 2) (w' : Fin 1 → Idx 3 3 2) :=
  h 3 2 (by norm_num) 1 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) 1 1 1 1 x y y' w w' P01

-- probe lines 1785-1786
def inst_gg (h : LWggExp 3) (x y y' : Idx 3 3 2) :=
  h 3 2 (by norm_num) 1 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) x y y' P01

-- probe lines 1805-1810
theorem inst_LWterm_endT (h : LWterm 3) (hI : LWInit sz0 (STflowE z0) tEnd (1 / 20) Ψ0)
    (hL : LWLoop2 sz0 (STflowE z0) tEnd Φ0) :
    Prec sz0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖LWE sz0 n (STflowE z0 n) (tEnd n) p.1 p.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tEnd n))⁻¹ * Φ0 n 0 *
        Φ0 n ((zdistInf 3 (sz0.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2) := ...

-- probe lines 1815-1821
theorem inst_LWtermExp_endT (h : LWtermExp 3) (hI : LWInit sz0 (STflowE z0) tEnd (1 / 20) Ψ0)
    (hL : LWLoopExp sz0 (STflowE z0) tEnd ℓ0) (D : ℝ) (hD : 0 < D) :
    Prec sz0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖LWE sz0 n (STflowE z0 n) (tEnd n) p.1 p.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tEnd n))⁻¹ * (sz0.Bctl n (tEnd n)) ^ (1 / 2 : ℝ) *
        ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailW 3 (sz0.L n) (sz0.lam n) (tEnd n) (ℓ0 n)
          ((sz0.W n : ℕ) : ℝ) D ((zdistInf 3 (sz0.L n) (p.2 0 - p.2 1) : ℕ) : ℝ))) := ...

-- probe lines 1828-1834
theorem inst_LWMoment_endT (h : LWMoment 3) (p : ℕ) (hp : 2 ∣ p)
    (hI : LWInit sz0 (STflowE z0) tEnd (1 / 20) Ψ0) (hL : LWLoop2 sz0 (STflowE z0) tEnd Φ0) :
    ∃ c : ℝ, 0 < c ∧
      Prec sz0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
        (fun n q _ => ∫ ω, ‖LWf sz0 n (STflowE z0 n) (tEnd n) ω q.1 q.2‖ ^ p ∂(sz0.seqP))
        (fun n q _ => ((etaT (STflowE z0 n) (tEnd n))⁻¹ * Φ0 n 0 *
          Φ0 n (c * ((zdistInf 3 (sz0.L n) (STblk sz0 n q.1 - STblk sz0 n q.2) : ℕ) : ℝ))) ^ p) := ...

-- probe lines 1840-1847
theorem inst_AnpKey_endT (h : LWAnpKey 3)
    (ξ : ∀ n, Zd 3 (sz0.L n) → Zd 3 (sz0.L n) → sz0.SeqΩ → ℝ) (hξ : LWXi sz0 (STflowE z0) tEnd Φ0 ξ) :
    ∃ c : ℝ, 0 < c ∧
      Prec sz0 (U := fun n => (Fin 2 → Zd 3 (sz0.L n)) × (Fin 2 → Zd 3 (sz0.L n)))
        (fun n ab ω => RBM.Graph.figAux.val (fun α β => ξ n α β ω) ab.1 ab.2)
        (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * etaT (STflowE z0 n) (tEnd n))⁻¹ ^ 2 *
          Φ0 n 0 ^ (RBM.Graph.figAux.ordN - (2 : ℕ)) *
          ∏ i, Φ0 n (c * ((zdistInf 3 (sz0.L n) (ab.1 i - ab.2 i) : ℕ) : ℝ))) := ...

-- probe lines 1852-1858
theorem inst_LWtermEXP_endT (h : LWtermEXP 3) (h1 : STLocalEntry sz0 (STflowE z0) tEnd)
    (h2 : LWAvgLaw sz0 (STflowE z0) tEnd) (h3 : STLmax sz0 (STflowE z0) tEnd)
    (h4 : STLK sz0 (STflowE z0) tEnd) (h5 : STDecay sz0 (STflowE z0) tEnd) :
    Prec sz0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - tEnd n})
      (fun n p _ => ‖∫ ω, LWE sz0 n (STflowE z0 n) (tEnd n) p.1.1 p.1.2 ω ∂(sz0.seqP)‖)
      (fun n _ _ => (1 - tEnd n)⁻¹ * (sz0.Bctl n (tEnd n)) ^ (5 / 2 : ℝ)) := ...

-- probe lines 1980-1985
theorem inst_chain_LWterm (hMom : LWMoment 3) (hRed : LWReduceB 3) (hint : LWInteg 3)
    (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoop2 sz0 (STflowE z0) tInst Φ0) :
    Prec sz0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖LWE sz0 n (STflowE z0 n) (tInst n) p.1 p.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * Φ0 n 0 *
        Φ0 n ((zdistInf 3 (sz0.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2) := ...

-- probe lines 1989-1996
theorem inst_chain_LWtermExp (hMom : LWMomentExp 3) (hRed : LWReduceT 3) (hint : LWInteg 3)
    (hN : LWtermExpN 3) (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0)
    (hL : LWLoopExp sz0 (STflowE z0) tInst ℓ0) (D : ℝ) (hD : 0 < D) :
    Prec sz0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖LWE sz0 n (STflowE z0 n) (tInst n) p.1 p.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ (1 / 2 : ℝ) *
        ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailW 3 (sz0.L n) (sz0.lam n) (tInst n) (ℓ0 n)
          ((sz0.W n : ℕ) : ℝ) D ((zdistInf 3 (sz0.L n) (p.2 0 - p.2 1) : ℕ) : ℝ))) := ...

-- probe lines 2131-2138
theorem inst_chain_Anp (h : LWAnpKey 3)
    (ξ : ∀ n, Zd 3 (sz0.L n) → Zd 3 (sz0.L n) → sz0.SeqΩ → ℝ) (hξ : LWXi sz0 (STflowE z0) tInst Φ0 ξ) :
    ∃ c : ℝ, 0 < c ∧
      Prec sz0 (U := fun n => Zd 3 (sz0.L n) × Zd 3 (sz0.L n))
        (fun n ab ω => RBM.Graph.figAux.val (fun α β => ξ n α β ω) (fun _ => ab.1) (fun _ => ab.2))
        (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * etaT (STflowE z0 n) (tInst n))⁻¹ ^ 2 *
          Φ0 n (c * ((zdistInf 3 (sz0.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ 2 *
          Φ0 n 0 ^ (RBM.Graph.figAux.ordN - (2 : ℕ))) := ...

-- probe lines 2000-2001
theorem inst_shift :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r → Φ0 n (1 / 3 * r) ≤ K * Φ0 n r := ...

-- probe lines 2037-2040
theorem inst_owx_smallest (x : Fin 2) :
    owxG0.val D0 (fun _ => x) - ((owxG1 I).val D0 (fun _ => x) + (owxG2 I).val D0 (fun _ => x)) =
      -I * ∑ w, ((if x = w then 1 else 0) + I ^ 2 * D0.Sp x w) *
        owxDefect 0 D0.G D0.S 1 (fun _ _ => 0) w := ...

-- probe lines 2044-2048
theorem inst_owx_second :
    owxH0.val D0 ![0, 1] - ((owxH1 I).val D0 ![0, 1] + (owxH2 I).val D0 ![0, 1] +
        (owxH3 I).val D0 ![0, 1] + (owxH4 I).val D0 ![0, 1]) =
      -I * ∑ w, ((if (0 : Fin 2) = w then 1 else 0) + I ^ 2 * D0.Sp 0 w) *
        owxDefect 0 D0.G D0.S (D0.G 0 1) (fun α w => -(D0.G 0 α * D0.G w 1)) w := ...

-- probe lines 2054-2064
theorem inst_owx_smallest_E {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (Gω : Ω → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2)
    (hZint : ∀ w, MeasureTheory.Integrable
      (fun ω => owxDefect 0 (Gω ω) S0 1 (fun _ _ => 0) w) P)
    (hZ : ∀ w, ∫ ω, owxDefect 0 (Gω ω) S0 1 (fun _ _ => 0) w ∂P = 0)
    (h0 : MeasureTheory.Integrable (fun ω => owxG0.val ⟨Gω ω, D0.M, S0, Sp0⟩ (fun _ => x)) P)
    (h1 : MeasureTheory.Integrable (fun ω => (owxG1 I).val ⟨Gω ω, D0.M, S0, Sp0⟩ (fun _ => x)) P)
    (h2 : MeasureTheory.Integrable (fun ω => (owxG2 I).val ⟨Gω ω, D0.M, S0, Sp0⟩ (fun _ => x)) P) :
    ∫ ω, owxG0.val ⟨Gω ω, D0.M, S0, Sp0⟩ (fun _ => x) ∂P =
      ∫ ω, (owxG1 I).val ⟨Gω ω, D0.M, S0, Sp0⟩ (fun _ => x) ∂P +
        ∫ ω, (owxG2 I).val ⟨Gω ω, D0.M, S0, Sp0⟩ (fun _ => x) ∂P := ...

-- probe lines 2075-2081
theorem inst_owx_smallest_E_unit (x : Fin 2) :
    ∫ _ : Unit, owxG0.val ⟨Matrix.diagonal fun _ => I, D0.M, S0, Sp0⟩ (fun _ => x)
        ∂(MeasureTheory.Measure.dirac ()) =
      ∫ _ : Unit, (owxG1 I).val ⟨Matrix.diagonal fun _ => I, D0.M, S0, Sp0⟩ (fun _ => x)
          ∂(MeasureTheory.Measure.dirac ()) +
        ∫ _ : Unit, (owxG2 I).val ⟨Matrix.diagonal fun _ => I, D0.M, S0, Sp0⟩ (fun _ => x)
          ∂(MeasureTheory.Measure.dirac ()) := ...

-- probe lines 2089-2089
def inst_figGraph_val := figGraph_val D0 0 1

-- probe lines 2092-2093
theorem inst_p2Graph_val_eq :
    p2Graph.val D0 ![0, 1] = fxyVal D0 0 1 * star (fxyVal D0 0 1) := ...
```

## 17. Prop-valued definitions of the probe (candidates for the registry, DECISIONS 16, 20)

```
$ python3 t2040_props.py /Users/junyin/Lean_proof/RBM3D-wt/T2040/RBM3D/Probe/T2040Graphs.lean
357 RBM.Graph.NGraph.WalkOK
364 RBM.Graph.NGraph.Visits
374 RBM.Graph.NGraph.IsNested
383 RBM.Graph.NGraph.NoGhost
387 RBM.Graph.NGraph.GhostOK
789 RBM.Graph.LWweightExp
814 RBM.Graph.LWedgeExp
847 RBM.Graph.LWggExp
896 RBM.Gauss.Sizes.LWInteg
913 RBM.Gauss.Sizes.LWInit
919 RBM.Gauss.Sizes.LWWindow
923 RBM.Gauss.Sizes.LWLoop2
930 RBM.Gauss.Sizes.LWClass
937 RBM.Gauss.Sizes.LWPsiRel
943 RBM.Gauss.Sizes.LWAssm
949 RBM.Gauss.Sizes.LWterm
964 RBM.Gauss.Sizes.LWtermB
983 RBM.Gauss.Sizes.LWLoopExp
992 RBM.Gauss.Sizes.LWAssmExp
999 RBM.Gauss.Sizes.LWtermExp
1012 RBM.Gauss.Sizes.LWAvgLaw
1020 RBM.Gauss.Sizes.LWtermEXP
1034 RBM.Gauss.Sizes.LWMoment
1050 RBM.Gauss.Sizes.LWMomentExp
1069 RBM.Gauss.Sizes.LWXi
1077 RBM.Gauss.Sizes.LWPsiAll
1084 RBM.Gauss.Sizes.LWAnpKey
1101 RBM.Gauss.Sizes.LWAnpKeyGh
1121 RBM.Gauss.Sizes.LWAnp
1140 RBM.Gauss.Sizes.LWReduceB
1406 RBM.Gauss.Sizes.LWtermExpS
1421 RBM.Gauss.Sizes.LWtermExpN
1437 RBM.Gauss.Sizes.LWReduceT
```

## 18. Mathlib names used (one line each)

```
$ python3 t2040_names.py --lines
names listed 63, of which occurring in the probe text 62
one line per name (`#check @name`, type cut at 130 characters): 64 lines
@Fin.consEquiv : {n : ℕ} → (α : Fin (n + 1) → Type u_1) → α 0 × ((i : Fin n) → α i.succ) ≃ ((i : Fin (n + 1)) → α i)
@Fintype.sum_prod_type : ∀ {γ : Type u_1} {α₁ : Type u_2} {α₂ : Type u_3} [inst : Fintype α₁] [inst_1 : Fintype α₂] [inst_2 : AddC ...
@Fintype.sum_unique : ∀ {M : Type u_1} {ι : Type u_2} [inst : Fintype ι] [inst_1 : AddCommMonoid M] [inst_2 : Unique ι] (f : ι → M ...
@Finset.sum_comm : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ →  ...
@Finset.sum_mul_sum : ∀ {ι : Type u_1} {κ : Type u_2} {R : Type u_3} [inst : NonUnitalNonAssocSemiring R] (s : Finset ι) (t : Fins ...
@Finset.mul_sum : ∀ {ι : Type u_1} {R : Type u_2} [inst : NonUnitalNonAssocSemiring R] (s : Finset ι) (f : ι → R) (a : R), a * ∑ i ...
@Finset.sum_mul : ∀ {ι : Type u_1} {R : Type u_2} [inst : NonUnitalNonAssocSemiring R] (s : Finset ι) (f : ι → R) (a : R), (∑ i ∈  ...
@Finset.sum_congr : ∀ {ι : Type u_1} {M : Type u_2} {s₁ s₂ : Finset ι} [inst : AddCommMonoid M] {f g : ι → M}, s₁ = s₂ → (∀ x ∈ s₂ ...
@Finset.sum_add_distrib : ∀ {ι : Type u_1} {M : Type u_2} {s : Finset ι} [inst : AddCommMonoid M] {f g : ι → M}, ∑ x ∈ s, (f x + g ...
@Finset.sum_sub_distrib : ∀ {ι : Type u_1} {G : Type u_2} {s : Finset ι} [inst : SubtractionCommMonoid G] (f g : ι → G), ∑ x ∈ s,  ...
@Finset.sum_neg_distrib : ∀ {ι : Type u_1} {G : Type u_2} {s : Finset ι} [inst : SubtractionCommMonoid G] (f : ι → G), ∑ x ∈ s, -f ...
@star_sum : ∀ {R : Type u_1} [inst : AddCommMonoid R] [inst_1 : StarAddMonoid R] {α : Type u_2} (s : Finset α) (f : α → R), star ( ...
@star_mul' : ∀ {R : Type u_1} [inst : CommMagma R] [inst_1 : StarMul R] (x y : R), star (x * y) = star x * star y
@MeasureTheory.integral_sub : ∀ {α : Type u_1} {G : Type u_2} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : Measur ...
@MeasureTheory.integral_add : ∀ {α : Type u_1} {G : Type u_2} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : Measur ...
@MeasureTheory.integral_const_mul : ∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {L : Type u_2} [inst :  ...
@MeasureTheory.integral_finsetSum : ∀ {α : Type u_1} {G : Type u_2} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m :  ...
@MeasureTheory.Integrable.add : ∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ε' : Type u_2} [inst : Top ...
@MeasureTheory.Integrable.const_mul : ∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_2} [inst  ...
@pow_add_pow_le : ∀ {R : Type u_1} [inst : Semiring R] [inst_1 : PartialOrder R] [IsOrderedRing R] {x y : R} {n : ℕ}, 0 ≤ x → 0 ≤  ...
@pow_le_pow_left₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀] ...
@Real.rpow_mul : ∀ {x : ℝ}, 0 ≤ x → ∀ (y z : ℝ), x ^ (y * z) = (x ^ y) ^ z
@Real.rpow_add : ∀ {x : ℝ}, 0 < x → ∀ (y z : ℝ), x ^ (y + z) = x ^ y * x ^ z
@Real.rpow_le_rpow : ∀ {x y z : ℝ}, 0 ≤ x → x ≤ y → 0 ≤ z → x ^ z ≤ y ^ z
@Real.rpow_le_rpow_of_exponent_le : ∀ {x y z : ℝ}, 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
@Real.one_le_rpow : ∀ {x z : ℝ}, 1 ≤ x → 0 ≤ z → 1 ≤ x ^ z
@Real.le_sqrt_of_sq_le : ∀ {x y : ℝ}, x ^ 2 ≤ y → x ≤ √y
@one_le_div : ∀ {α : Type u_1} [inst : Semifield α] [inst_1 : PartialOrder α] [PosMulReflectLT α] {a b : α}, 0 < b → (1 ≤ a / b ↔  ...
@inv_le_comm₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] [MulPosReflectLT G₀] { ...
@le_inv_comm₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] [MulPosReflectLT G₀] { ...
@inv_anti₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b ...
@inv_le_one_of_one_le₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀} [Zer ...
@inv_lt_one_of_one_lt₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀} [Zer ...
@div_le_one : ∀ {α : Type u_1} [inst : Semifield α] [inst_1 : PartialOrder α] [PosMulReflectLT α] {a b : α}, 0 < b → (a / b ≤ 1 ↔  ...
@div_le_self : ∀ {α : Type u_1} [inst : Semifield α] [inst_1 : PartialOrder α] [PosMulReflectLT α] {a b : α} [IsStrictOrderedRing  ...
@ite_eq_left : ∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u_1} {t e : α}, (if c then t else e) = t
@ite_eq_right : ∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u_1} {t e : α}, (if c then t else e) = e
@ENNReal.one_le_ofReal : ∀ {p : ℝ}, 1 ≤ ENNReal.ofReal p ↔ 1 ≤ p
@ENNReal.ofReal_le_ofReal : ∀ {p q : ℝ}, p ≤ q → ENNReal.ofReal p ≤ ENNReal.ofReal q
@ENNReal.ofReal_add : ∀ {p q : ℝ}, 0 ≤ p → 0 ≤ q → ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q
@MeasureTheory.measure_union_le : ∀ {α : Type u_1} {F : Type u_2} [inst : FunLike F (Set α) ENNReal] [MeasureTheory.OuterMeasureCl ...
@MeasureTheory.measure_mono : ∀ {α : Type u_1} {F : Type u_2} [inst : FunLike F (Set α) ENNReal] [MeasureTheory.OuterMeasureClass  ...
@MeasureTheory.measure_univ : ∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProb ...
@Fintype.card_subtype_le : ∀ {α : Type u_1} [inst : Fintype α] (p : α → Prop) [inst_1 : Fintype { a // p a }], Fintype.card { x // ...
@abs_norm : ∀ {E : Type u_1} [inst : SeminormedAddGroup E] (z : E), |‖z‖| = ‖z‖
@MvPolynomial.eval : {R : Type u_1} → {σ : Type u_2} → [inst : CommSemiring R] → (σ → R) → MvPolynomial σ R →+* R
@MvPolynomial.X : {R : Type u_1} → {σ : Type u_2} → [inst : CommSemiring R] → σ → MvPolynomial σ R
@Matrix.single : {m : Type u_1} → {n : Type u_2} → {α : Type u_3} → [DecidableEq m] → [DecidableEq n] → [Zero α] → m → n → α → Mat ...
@deriv : {𝕜 : Type u_1} → [inst : NontriviallyNormedField 𝕜] → {F : Type u_2} → [inst_1 : AddCommGroup F] → [Module 𝕜 F] → [Topolo ...
@Nat.floor_zero : ∀ {R : Type u_1} [inst : Semiring R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] [IsStrictOrderedRing R] ...
@Even.pow_nonneg : ∀ {R : Type u_1} [inst : Semiring R] [inst_1 : LinearOrder R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ}, Even ...
@not_lt : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ a
@add_pos_of_nonneg_of_pos : ∀ {α : Type u_1} {a b c : α} [inst : AddZeroClass α] [inst_1 : Preorder α] [AddLeftStrictMono α], b ≤  ...
@Finset.sum_ite_eq : ∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoid M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ...
@lt_of_lt_of_le : ∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b ≤ c → a < c
@mul_lt_mul_of_pos_left : ∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : Preorder α] {a b c : α} [PosMulStrictMono α] ...
@Equiv.sum_comp : ∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M ...
@if_pos : ∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u_1} {t e : α}, (if c then t else e) = t
@if_neg : ∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u_1} {t e : α}, (if c then t else e) = e
@if_true : ∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then t else e) = t
@if_false : ∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False then t else e) = e
@Set.mem_setOf_eq : ∀ {α : Type u_1} {x : α} {p : α → Prop}, (x ∈ {y | p y}) = p x
@MeasureTheory.integral_finset_sum : ∀ {α : Type u_1} {G : Type u_2} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : ...
@ite_cond_eq_true : ∀ {α : Sort u_1} {c : Prop} {x : Decidable c} (a b : α), c = True → (if c then a else b) = a
#check elaborates, not deprecated: 62 of 62 names requested:
  Fin.consEquiv Fintype.sum_prod_type Fintype.sum_unique Finset.sum_comm Finset.sum_mul_sum Finset.mul_sum
  Finset.sum_mul Finset.sum_congr Finset.sum_add_distrib Finset.sum_sub_distrib Finset.sum_neg_distrib
  star_sum star_mul' MeasureTheory.integral_sub MeasureTheory.integral_add MeasureTheory.integral_const_mul
  MeasureTheory.integral_finsetSum MeasureTheory.Integrable.add MeasureTheory.Integrable.const_mul
  pow_add_pow_le pow_le_pow_left₀ Real.rpow_natCast Real.rpow_mul Real.rpow_add Real.rpow_neg_one
  Real.rpow_two Real.rpow_le_rpow Real.rpow_le_rpow_of_exponent_le Real.one_le_rpow Real.sqrt_eq_rpow
  Real.le_sqrt_of_sq_le one_le_div inv_le_comm₀ le_inv_comm₀ inv_anti₀ inv_le_one_of_one_le₀
  inv_lt_one_of_one_lt₀ div_le_one div_le_self ite_eq_left ite_eq_right ENNReal.one_le_ofReal
  ENNReal.ofReal_le_ofReal ENNReal.ofReal_add MeasureTheory.measure_union_le MeasureTheory.measure_mono
  MeasureTheory.measure_univ Fintype.card_subtype_le Fintype.card_prod abs_norm MvPolynomial.eval
  MvPolynomial.X Matrix.single deriv Nat.floor_zero Even.pow_nonneg not_lt add_pos_of_nonneg_of_pos
  Finset.sum_ite_eq lt_of_lt_of_le mul_lt_mul_of_pos_left Equiv.sum_comp
requested names that are deprecated: none
deprecated names checked and avoided (replacement used): if_pos -> ite_eq_left, if_neg -> ite_eq_right, if_true -> ite_true, if_false -> ite_false, Set.mem_setOf_eq -> Set.mem_ofPred_eq, MeasureTheory.integral_finset_sum -> MeasureTheory.integral_finsetSum, ite_cond_eq_true -> ite_eq_left_of_eq_true
error lines: 1 (the tactic `push_neg`, which is not a term; replaced by `push Not`)
```

## 19. `#print axioms` of every theorem and instance named in the report, and of the whole module

```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2040 && lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2040/ax_report.lean && lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2040/axioms.lean
'RBM.Gauss.LWInst.classB' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.figAux_ghostOK' depends on axioms: [propext]
'RBM.Gauss.LWInst.inst_Anp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.inst_AnpKey' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.inst_AnpKeyGh' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.inst_AnpKey_endT' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.inst_LWMoment' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.inst_LWMomentExp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.inst_LWMoment_endT' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.inst_LWterm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.inst_LWtermB' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.inst_LWtermEXP' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.inst_LWtermEXP_endT' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.inst_LWtermExp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.inst_LWtermExpS' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.inst_LWtermExp_endT' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.inst_LWterm_endT' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.inst_chain_Anp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.inst_chain_LWterm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.inst_chain_LWtermExp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.inst_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LWPsiAll.shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwanp_of_key' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwterm_of_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwtermexpS_of_momentexp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwtermexp_of_regimes' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWInstFixed.inst_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWInstFixed.inst_gg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWInstFixed.inst_ssl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWInstOwx.inst_figGraph_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWInstOwx.inst_owx_second' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWInstOwx.inst_owx_smallest' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWInstOwx.inst_owx_smallest_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWInstOwx.inst_owx_smallest_E_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWInstOwx.inst_p2Graph_val_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.figAux_nested' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.figAux_ord' depends on axioms: [propext]
'RBM.Graph.figGraph_counters' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.figGraph_ord' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.figGraph_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.fxyTerm_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.owxT_smallest' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.owx_defect_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.owx_ord' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.owx_ord_H' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.owx_second' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.owx_smallest' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.owx_smallest_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.p2Graph_counters' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.p2Graph_ord' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.p2Graph_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.p2Graph_val_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.stochDomAt_congr_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.stochDomAt_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.stochDomAt_of_split' depends on axioms: [propext, Classical.choice, Quot.sound]
declarations of the probe module (not internal): 335; theorems: 116; only the three standard axioms: 335; others: 0
```

## 20. Registry pre-check (DECISIONS 20): the library plus the probe, `#assert_rbm_axioms`; the premises it finds unregistered

```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2040 && lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2040/precheck.lean 2>&1 | cut -c1-300
/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2040/precheck.lean:3:0: error: axiom audit: 16 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`:
  [RBM.Gauss.Sizes.LWAvgLaw,
 RBM.Gauss.Sizes.STLocalEntry,
 RBM.Gauss.Sizes.LWtermEXP,
 RBM.Gauss.Sizes.LWInteg,
 RBM.Gauss.Sizes.LWReduceT,
 RBM.Gauss.Sizes.LWMomentExp,
 RBM.Gauss.Sizes.LWLoopExp,
 RBM.Gauss.Sizes.LWInit,
 RBM.Gauss.Sizes.LWLoop2,
 RBM.Gauss.Sizes.LWReduceB,
 RBM.Gauss.Sizes.LWMoment,
 RBM.Gauss.Sizes.LWXi,
 RBM.Gauss.Sizes.LWAnpKeyGh,
 RBM.Gauss.Sizes.LWAnpKey,
 RBM.Gauss.Sizes.LWtermB,
 RBM.Gauss.Sizes.LWtermExpN]
Classify each of them: borrowed from the literature, owed by this formalization, or a predicate that defines the objects under study.
```

## 21. Name clashes: (a) every probe declaration against the environment of `import RBM3D` (compiled), (b) last components against the sources of main

```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2040 && lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2040/clash_final.lean 2>&1 | cut -c1-300; cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad && python3 t2040_clash.py
probe declarations checked against `import RBM3D` (the library without the probe): 335; already declared there: 0 []
probe declarations: 335, distinct last components: 222; main worktree HEAD 1c1f5e4, tracked non-probe .lean files scanned: 80
last components that are also declared (any namespace) in main: 3
  const -> RBM3D/Green/LDEQuad.lean:177 const
  mul -> RBM3D/Defs/Domination.lean:128 mul; RBM3D/Defs/Domination.lean:188 mul; RBM3D/Defs/StochDom.lean:178 mul
  sum -> RBM3D/Green/LDEQuad.lean:271 sum
```

## 22. Pins, one line per pin (full width; the report shows the same lines cut at 430 characters)

```
$ python3 t2040_pins.py /Users/junyin/Lean_proof/RBM3D-wt/T2040/RBM3D/Probe/T2040Graphs.lean 3000
| pin | probe lines | paper | binders and hypotheses (<FLOW> = 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →) | conclusion (the scale of every `Prec` is N = sz.size n) |
| `LWterm` | 949-958 | 3_5:385-404 (eq:LW_conclusion) | <FLOW> ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ), LWAssm sz (STflowE z) t ε₀ Ψ Φ C₁ C₂ C₃ Cc → | Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1 p.2 ω‖) (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * Φ n ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2) |
| `LWtermB` | 964-979 | 3_5:393-397 (eq:LW_conclusion2) | <FLOW> ∀ (ε₀ c₀ C₃ : ℝ) (K : ℕ → ℕ) (Ψ : ℕ → ℝ), 0 < c₀ → (∀ n, K n ≤ sz.L n) → 0 < ε₀ → LWWindow sz ε₀ Ψ → LWInit sz (STflowE z) t ε₀ Ψ → LWClass sz ε₀ C₃ (fun n r => (((sz.W n : ℕ) : ℝ) ^ (-c₀) * Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊r⌋₊ (K n))) ^ (1 / 2 : ℝ)) → LWLoop2 sz (STflowE z) t (fun n  ... | Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1 p.2 ω‖) (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (((sz.W n : ℕ) : ℝ) ^ (-c₀) * Bparam d (sz.L n) (sz.lam n) (t n) 0) ^ (1 / 2 : ℝ) * (((sz.W n : ℕ) : ℝ) ^ (-c₀) * Bparam d (sz.L n) (sz.lam n) (t n) (min (zdistInf d (sz.L n) (p.2 0 - p.2 1)) (K n)))) |
| `LWtermExp` | 999-1009 | 3_5:406-415 (eq:LW_conclusion_exp) | <FLOW> ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ → ∀ D : ℝ, 0 < D → | Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1 p.2 ω‖) (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ))) |
| `LWtermExpS` | 1406-1417 | regime 1-t > g^2/L^2 of 3_5:406 | <FLOW> ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ → ∀ D : ℝ, 0 < D → | Prec sz (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n}) (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1.1 p.1.2 ω‖) (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ))) |
| `LWtermExpN` | 1421-1432 | regime 1-t <= g^2/L^2 of 3_5:406 (7_8:20) | <FLOW> ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ → ∀ D : ℝ, 0 < D → | Prec sz (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // 1 - t n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2}) (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1.1 p.1.2 ω‖) (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ))) |
| `LWtermEXP` | 1020-1029 | 6:83-88 (eq:ExpLWn=2) | <FLOW> STLocalEntry sz (STflowE z) t → LWAvgLaw sz (STflowE z) t → STLmax sz (STflowE z) t → STLK sz (STflowE z) t → STDecay sz (STflowE z) t → | Prec sz (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n}) (fun n p _ => ‖∫ ω, LWE sz n (STflowE z n) (t n) p.1.1 p.1.2 ω ∂(sz.seqP)‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) |
| `LWMoment` | 1034-1045 | 7_8:72-77 (eq:LW_moment) | 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (p : ℕ), 2 ∣ p → ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) → ∀ (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ), LWAssm sz (STflowE z) t ε₀ Ψ Φ C₁ C₂ C ... | Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (fun n q _ => ∫ ω, ‖LWf sz n (STflowE z n) (t n) ω q.1 q.2‖ ^ p ∂(sz.seqP)) (fun n q _ => ((etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * Φ n (c * ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ))) ^ p) |
| `LWMomentExp` | 1050-1063 | 7_8:78-83 (eq:LW_moment_exp) | 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (p : ℕ), 2 ∣ p → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) → ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ → ∀ D : ℝ, 0 < D → | Prec sz (U := fun n => {_q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n}) (fun n q _ => ∫ ω, ‖LWf sz n (STflowE z n) (t n) ω q.1.1 q.1.2‖ ^ p ∂(sz.seqP)) (fun n q _ => ((etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n) (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))) ^ p + ((sz.W n : ℕ) : ℝ) ^ (-D)) |
| `LWAnpKey` | 1084-1097 | 7_8:960-985 (adsuu_orig) | 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (p q : ℕ), q ≤ p → ∀ Γ : RBM.Graph.NGraph p q, Γ.NoGhost → Γ.IsNested → ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) → ∀ Φ : ℕ → ℝ →  ... | Prec sz (U := fun n => (Fin p → Zd d (sz.L n)) × (Fin p → Zd d (sz.L n))) (fun n ab ω => Γ.val (fun α β => ξ n α β ω) ab.1 ab.2) (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (STflowE z n) (t n))⁻¹ ^ q * Φ n 0 ^ (Γ.ordN - p) * ∏ i, Φ n (c * ((zdistInf d (sz.L n) (ab.1 i - ab.2 i) : ℕ) : ℝ))) |
| `LWAnpKeyGh` | 1101-1115 | 7_8:1041-1077 (adsuu22) | 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (p q : ℕ), q ≤ p → ∀ Γ : RBM.Graph.NGraph p q, Γ.GhostOK → Γ.IsNested → ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) → ∀ Φ : ℕ → ℝ →  ... | Prec sz (U := fun n => (Fin p → Zd d (sz.L n)) × (Fin p → Zd d (sz.L n))) (fun n ab ω => Γ.val (fun α β => ξ n α β ω) ab.1 ab.2) (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (STflowE z n) (t n))⁻¹ ^ q * Φ n 0 ^ (Γ.ordN - Γ.nngh) * ∏ i, (if Γ.noGhostPath i = true then Φ n (c * ((zdistInf d (sz.L n) (ab.1 i - ab.2 i) : ℕ) : ℝ)) else 1)) |
| `LWAnp` | 1121-1134 | 7_8:933-939 (eq:bddGamma_aux) | 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (p q : ℕ), q ≤ p → ∀ Γ : RBM.Graph.NGraph p q, Γ.NoGhost → Γ.IsNested → ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) → ∀ Φ : ℕ → ℝ →  ... | Prec sz (U := fun n => Zd d (sz.L n) × Zd d (sz.L n)) (fun n ab ω => Γ.val (fun α β => ξ n α β ω) (fun _ => ab.1) (fun _ => ab.2)) (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (STflowE z n) (t n))⁻¹ ^ q * Φ n (c * ((zdistInf d (sz.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ p * Φ n 0 ^ (Γ.ordN - p)) |
| `LWReduceB` | 1140-1153 | 7_8:20-91 reduction (eq:directG1..recoltermwt) | <FLOW> ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ), LWAssm sz (STflowE z) t ε₀ Ψ Φ C₁ C₂ C₃ Cc → Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (fun n q ω => ‖LWf sz n (STflowE z n) (t n) ω q.1 q.2‖) (fun n q _ => (etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * Φ n ... | Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1 p.2 ω‖) (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * Φ n ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2) |
| `LWReduceT` | 1437-1455 | 7_8:20-58 reduction (eq:directG2..recoltermwt2) | <FLOW> ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ → ∀ D : ℝ, 0 < D → Prec sz (U := fun n => {_q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n}) (fun n q ω => ‖LWf sz n (STflowE z n) (t n) ω q.1.1 q.1.2‖) (fun n q _ => (etaT (S ... | Prec sz (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n}) (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1.1 p.1.2 ω‖) (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ))) |
| `LWweightExp` | 789-799 | 7_8:294-306 (Owx) | ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ g E t : ℝ, |E| < 2 → 0 ≤ t → t < 1 → ∀ (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (x : Idx d L W), | ∫ ω, lwGc d L W E t ω x x * lwf d L W E t P ω ∂(PF d L W g) = ∫ ω, (mE E * ∑ α, lwS d L W g t x α * lwGc d L W E t ω x x * lwGc d L W E t ω α α * lwf d L W E t P ω + mE E ^ 3 * ∑ α, ∑ β, lwSp d L W E g t x α * lwS d L W g t α β * lwGc d L W E t ω α α * lwGc d L W E t ω β β * lwf d L W E t P ω - mE E * ∑ α, lwS d L W g t x α * lwG d L W E t ω α x * lwdf d L W E t P ω α x - mE E ^ 3 * ∑ α, ∑ β, lwSp d L W E g t x α * lwS d L W g t α β * lwG d L W E t ω β α * lwdf d L W E t P ω β α) ∂(PF d L W g) |
| `LWedgeExp` | 814-843 | 7_8:309-330 (Oe1x) | ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ g E t : ℝ, |E| < 2 → 0 ≤ t → t < 1 → ∀ (k₁ k₂ k₃ k₄ : ℕ) (x : Idx d L W) (y : Fin (k₁ + 1) → Idx d L W) (y' : Fin k₂ → Idx d L W) (w : Fin k₃ → Idx d L W) (w' : Fin k₄ → Idx d L W) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ), | ∫ ω, lwG d L W E t ω x (y 0) * (oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ * lwf d L W E t P ω) ∂(PF d L W g) = ∫ ω, (mE E * (if x = y 0 then 1 else 0) * (oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ * lwf d L W E t P ω) + mE E * (∑ α, lwS d L W g t x α * lwGc d L W E t ω α α) * (lwG d L W E t ω x (y 0) * (oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ * lwf d L W E t P ω)) + ∑ i : Fin k₂, (mE E * star (mE E)) * (∑ α, lwS d L W g t x α * lwG d L W E t ω α (y 0) * lwGb d L W E t ω α (y' i)) * (oe1xRest d L W E t ω x y y' w w' (Finset.univ.erase i) Finset.univ * lwf d L W E t P ω) + ∑ i : Fin k₃, mE E ^ 2 * (∑ α, lwS d L W g t x α * lwG d L W E t ω α (y 0) * lwG d L W E t ω (w i) α) * (oe1xRest d L W E t ω x y y' w w' Finset.univ (Finset.univ.erase i) * lwf d L W E t P ω) + ∑ i : Fin k₂, mE E * lwGcb d L W E t ω x x * (∑ α, lwS d L W g t x α * lwG d L W E t ω α (y 0) * lwGb d L W E t ω α (y' i)) * (oe1xRest d L W E t ω x y y' w w' (Finset.univ.erase i) Finset.univ * lwf d L W E t P ω) + ∑ i : Fin k₃, mE E * lwGc d L W E t ω x x * (∑ α, lwS d L W g t x α * lwG d L W E t ω α (y 0) * lwG d L W E t ω (w i) α) * (oe1xRest d L W E t ω x y y' w w' Finset.univ (Finset.univ.erase i) * lwf d L W E t P ω) + (k₁ : ℂ) * mE E * (∑ α, lwS d L W g t x α * lwG d L W E t ω x α * lwG d L W E t ω α (y 0)) * (oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ * lwf d L W E t P ω) + (k₄ : ℂ) * mE E * (∑ α, lwS d L W g t x α * lwGb d L W E t ω α x * lwG d L W E t ω α (y 0)) * (oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ * lwf d L W E t P ω) - mE E * ∑ α, lwS d L W g t x α * oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ * lwG d L W E t ω α (y 0) * lwdf d L W E t P ω α x) ∂(PF d L W g) |
| `LWggExp` | 847-864 | 7_8:334-349 (Oe2x) | ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ g E t : ℝ, |E| < 2 → 0 ≤ t → t < 1 → ∀ (x y y' : Idx d L W) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ), | ∫ ω, lwG d L W E t ω x y * lwG d L W E t ω y' x * lwf d L W E t P ω ∂(PF d L W g) = ∫ ω, (mE E * (if x = y then 1 else 0) * lwG d L W E t ω y' x * lwf d L W E t P ω + mE E ^ 3 * lwSp d L W E g t x y * lwG d L W E t ω y' y * lwf d L W E t P ω + mE E * (∑ α, lwS d L W g t x α * lwGc d L W E t ω α α) * (lwG d L W E t ω x y * lwG d L W E t ω y' x * lwf d L W E t P ω) + mE E ^ 3 * ∑ α, ∑ β, lwSp d L W E g t x α * lwS d L W g t α β * lwGc d L W E t ω β β * lwG d L W E t ω α y * lwG d L W E t ω y' α * lwf d L W E t P ω + mE E * lwGc d L W E t ω x x * ∑ α, lwS d L W g t x α * lwG d L W E t ω α y * lwG d L W E t ω y' α * lwf d L W E t P ω + mE E ^ 3 * ∑ α, ∑ β, lwSp d L W E g t x α * lwS d L W g t α β * lwGc d L W E t ω α α * lwG d L W E t ω β y * lwG d L W E t ω y' β * lwf d L W E t P ω - mE E * ∑ α, lwS d L W g t x α * lwG d L W E t ω α y * lwG d L W E t ω y' x * lwdf d L W E t P ω α x - mE E ^ 3 * ∑ α, ∑ β, lwSp d L W E g t x α * lwS d L W g t α β * lwG d L W E t ω β y * lwG d L W E t ω y' α * lwdf d L W E t P ω β α) ∂(PF d L W g) |
```

## 23. Route and risk (item 4)

```
$ python3 t2040_route.py
| item (paper) | route | routine / graph-combinatorial | est. lines central (size model) | risk | only sketched in the paper |
|---|---|---|---|---|---|
| lem:LWterm, lem: EWGn2_N (3_5:385-415; 7_8:1-104) | Markov on LW_moment(_exp) [compiled: lwterm_of_moment, lwtermexpS_of_momentexp]; reduction by (eq:directG1/2), (eq:recolterm*), (eq:recoltermwt*) from merged lem_GbEXP pins and (LW_assm); regimes | all routine (union bound, Markov, (eq:Psi) shift compiled); deterministic T~ vs [sT]^2 comparison | LW-01 1278+LW-15 600+LW-16 500 | low-medium | 7_8:20 "an immediate consequence" (regime 1-t <= g^2/L^2: sub-sequence transfer, T2040k) |
| lem:LW_moment, lem:LW_moment_exp, assembly (7_8:716-720, 943-950, 1600-1630) | dist(a,b) <= (log W)^{3/2} (_exp: <= (log W)^{3/2} l_t, from LW_moment) by the max-bound (eq:boundfxyGinf) [Ward + Cauchy-Schwarz]; else expand E‖f‖^p to graphs, lvl1, GtoAG, lem:Anp; _exp: cut f = f^{>l} + f^{<=l}; expectation upgrade ‖f‖ <~ N eta^-3 | routine: far/near, upgrade, Markov | LW-02 461 | medium | 7_8:944 "standard" |
| ssl, Oe14, T eq0: (Owx),(Oe1x),(Oe2x) (7_8:294-349; cited yang2021 Lemmas 3.5, 3.10, 3.14: no proof in the paper) | row Stein identity + resummation S+ = S(1-m^2 S)^-1 [(Owx) proved pathwise: owx_defect_identity; (Oe1x),(Oe2x) checked numerically b.7]; E Z_w = 0 (merged GaussIBP, owed S1-19); derivative of resolvent polynomials (merged hasDerivAt_inverse_apply); each term a graph with counter changes ((a)(i)) | routine algebra; size of the statements (nine and eight terms, k1..k4 generic) | LW-04 1200+LW-05 800+LW-06 1100+LW-07 1000 | medium | whole proofs cited |
| lvl1 lemma, strat_local, deflvl1 (7_8:367-399; B:135-157) | iterate (Owx), (Oe1x), (Oe2x) with the dot-def normal form until locally standard; discard graphs of size <= W^-D (claim:size) | graph-combinatorial: termination (ord, size), normal-graph normal form | LW-08 1500+LW-03 1400+LW-09 1300 | high | strategy only (B:135-157); claim:size 7_8:264 has no proof; lvl1 cited (Lemma 3.22) |
| lem:localregular (7_8:786-821; proof B:172-278) | (1) trivial, (2) the number of internal molecules never increases (B:173-177); (3)-(5): paths persist through every expansion (B:178-199, three alternatives); (6) ord >= 3p - n_dv: weight cases (i)-(vi) B:209-263 [arithmetic merged: Graph/ScalingOrder, Graph/Model], edge and GG expansions B:275 | merged: the arithmetic of (i)-(vi); to do: Case.Rel on records, edge/GG case analysis | LW-10 2918 (-393 merged) | high | B:263 "not hard to see"; B:275 "straightforward", "direct check", "omit the details" |
| GtoAG, def_auxgraph, def: BM2 (7_8:863-932) | block-level auxiliary graph of a locally standard graph; ord(G) - ord(G_aux) >= 0 via (eq:MolVW) (nV(M_i) <= nW(M_i)+1) | graph-combinatorial (molecules, paths) | LW-11 989 | medium | 7_8:915 "as in"; claim:xi 7_8:884 has no proof |
| lem:Anp_key_gh, lem:Anp_key, lem:Anp (7_8:933-1599) | Anp from Anp_key [compiled: lwanp_of_key]; Anp_key = gh version (7_8:1025 "easy corollary"); gh by induction on internal vertices, ending-edge types A1/A2/B1/B2, cases (I)-(IV), Cauchy-Schwarz with (eq:Gbyxi3), change of summation order | Cauchy-Schwarz sums, order bookkeeping; graph-combinatorial: nested graphs, spanning paths | LW-12 7312 | high (largest item) | 7_8:1142, 1231 "easy to see"; 1154-1413 "without loss of generality"; 1232-1254 "similar"; 1400, 1529 "as in" |
| lem:LW_moment_exp_far, _near (7_8:1615-1791) | far (f^{>l}, internal vertices in D_{>l}): every path has an ending edge longer than l, T(l) as an A2/ghost edge, rest "exactly the same argument" as Anp_key_gh; near (f^{<=l}): edges bounded by T_t(.^l), internal sums in a fixed order with the key estimate from claim:TTk (merged EKTTk), lem:propT | graph-combinatorial (reuse of LW-12); sums with the exponential tail | LW-13 2511 | high-medium | 7_8:1632, 1647 "similar", "standard"; 1642, 1773 "omit"; 1781 "easy to see" |
| lem:LWterm_EXP (B:7-121; 6:83-88) | GG expansion at G_xa G_ay: I1..I4 (J1..J4 "exactly the same" with prop:ThfadC_short); I42 = 5-loop -> graphs G_xy, GtoAG, ord >= 4.1_{x=y}+5.1_{x!=y} from (eq:GGraisesord), cases (1)-(4) | Ward, averaged local law, K-loop bounds (merged); ord of every term of (Oe2x) | LW-14 2524 | medium-high | B:34, 49, 105 "exactly the same"; B:102 "easy to see"; B:118 "omit" (BA part) |
| remark:3p (B:280) | refinement ord >= 3p (not needed): not planned | - | 0 | none | remark only |
| block Anderson graph layer (B:286-523) | Psi-dotted and M-dotted edges, atoms, scalingBA; lanlw, lem_lweight, GGGamma (cited yang2024Del B.9-B.11); BA lvl1; atomic reduction + auxiliary graph; LWterm_EXP with GGGamma | graph-combinatorial; same shape as LW-03..LW-14 | BA-L1 873+BA-L2 2400+BA-L3 1590+BA-L4 1500 | high | B:409 sketch; B:118 "omit"; "carries over verbatim" |
```

## 24. Split table and size (item 7)

```
$ python3 t2040_split.py
credit: merged Graph/ScalingOrder.lean + Graph/Model.lean = 393 lines (arithmetic and exhaustiveness of the cases (i)-(vi), B:209-263) subtracted from LW-10
| id | file RBM3D/Graph/... | statements | needs | role | lines lo/central/hi | tickets (central) |
| LW-03 | Vocab | def_graph1 ValG def_poly defnlvl0 dot-def (def scaling, order); records, value, counters, molecules | MD-1..3, merged Counters/ord | prover-hard | 1400/1400/1400 | 1.4 |
| LW-04 | SteinBridge | E Z_w = 0 for resolvent polynomials; derivative calculus; graph derivative | S1-19 GaussIBP (T2031) | prover-hard | 1200/1200/1200 | 1.2 |
| LW-05 | ExpOwx | ssl (Owx) as a graph operation, counters per term | LW-03, 04 | prover | 800/800/800 | 0.8 |
| LW-06 | ExpOe1x | Oe14 (Oe1x), nine terms, k1..k4 generic | LW-03, 04 | prover-hard | 1100/1100/1100 | 1.1 |
| LW-07 | ExpOe2x | T eq0 (Oe2x), eight terms | LW-03, 04 | prover | 1000/1000/1000 | 1.0 |
| LW-09 | SizeClaim | claim:size (Gamma << size), S^pm decay (estSpm-W), scalemole | LW-03 | prover-hard | 1300/1300/1300 | 1.3 |
| LW-08 | Lvl1 | deflvl1, strat_local, lvl1 lemma (termination, Err <= W^-D) | LW-03, 05-07, 09 | prover-max | 1500/1500/1500 | 1.5 |
| LW-10 | LocalRegular | lem:localregular (1)-(6): paths, molecules, ord through (Owx),(Oe1x),(Oe2x) | LW-03, 05-08 | prover-max | 1552/2525/4470 | 2.5 |
| LW-11 | AuxGraph | def: BM2, def_auxgraph, GtoAG | LW-10 | prover-hard | 989/989/1979 | 1.0 |
| LW-12 | Nested, AnpKeyGh, Anp | lem:Anp_key_gh (cases I-IV), lem:Anp_key, lem:Anp (NGraph) | LW-11 | prover-max | 4875/7312/12187 | 7.3 |
| LW-13 | MomentExp | lem:LW_moment_exp_far, _near (uses merged EKTTk) | LW-12 | prover-max | 1255/2511/3766 | 2.5 |
| LW-14 | LWtermEXP | lem:LWterm_EXP (B:7-121): I1..I4, J-terms, (eq:GGraisesord), cases (1)-(4) | LW-03, 07, 09, 11 | prover-max | 1683/2524/4207 | 2.5 |
| LW-15 | LWDet | (eq:Psi) for the B class, W^-d T~ ~ [sT]^2, Psi_t window (T2040a) | merged Defs/Tail | prover | 600/600/600 | 0.6 |
| LW-02 | LWMoment | lem:LW_moment, lem:LW_moment_exp (far/near split, expectation upgrade) | LW-08, 10-13 | prover-hard | 461/461/922 | 0.5 |
| LW-16 | LWRegime | regime transfer of lem: EWGn2_N (T2040k) | LW-01 | prover-hard | 500/500/500 | 0.5 |
| LW-01 | LWterm | lem:LWterm, lem: EWGn2_N from the moments (reduction (eq:directG), recolterm) | LW-02, 15, 16, ST-D2 | prover-hard | 1278/1278/2557 | 1.3 |
| total | | | | | 21495/27002/39490 | 27.0 |
tickets of ~1000 lines: lo 21, central 27, hi 39; band 600-1500 lines per ticket: central 18..45
block Anderson additions (BA-L1..L4: Psi- and M-dotted edges, atoms, scalingBA; lanlw, lem_lweight, GGGamma; BA lvl1/Anp; BA LWterm_EXP): 6.4 tickets (lo 5.8, hi 8.3)
LW + BA: central 33 tickets (lo 27, hi 48); DECISIONS 9 O2 thresholds 25/40/50: exceeds 50: no (neither central, lo nor hi)
reduced route R1 (expansions ssl, Oe14, T eq0 and lvl1 lemma = Lemmas 3.5, 3.10, 3.14, 3.22 of yang2021 as external inputs; needs a change of DECISIONS 5): 21 tickets (lo 16, hi 34); gives up LW-04..08
reduced route R2 (Step 6 only: LW-03,04,07,09,11,14,15): 9 tickets (lo 8, hi 12); gives up lem:LWterm and lem: EWGn2_N (Step 2), which the main theorems need: not a route by itself
```

## 25. Comparison of the two representations (item 2)

```
$ python3 t2040_compare.py /Users/junyin/Lean_proof/RBM3D-wt/T2040/RBM3D/Probe/T2040Graphs.lean
| criterion | A: record `LGraph E I` (probe §1, §3, §4) | B: binder terms `GTerm V` (§2, §4.3) |
| core vocabulary, code lines | 65 (LData, edges, value, counters, molecules) | 26 (terms, eval; no counters, no molecules) |
| (Owx) on `Ǧ_xx`: three terms + value theorem, code lines | 30 (incl. the `ord` theorem; unfolds `Fin n → ι` sums) | 19 (structural `eval`; same `owx_defect_identity`) |
| counters, molecules, ord; expansion at x | from the record by `decide`: p2Graph (6,2,4,2), ord 2; figGraph (8,4,6,2), ord 4; filter `solid` by endpoint | not visible: a flattening to a record is needed; the factors at x sit in a product tree under `Option` shifts |
| lem:Anp nested bound | `NGraph p q` (edges, p paths), `IsNested` decided on `figAux`; pin `LWAnpKey` | paths are no property of the term: the record is needed again |
```

## 26. Expansion check, one line per setting (item 8 extreme inputs)

```
$ python3 t2040_expansions_summary.py
setting (seed E t h)               | |LHS| range              | |LHS-RHS| range          | max resid. | max relative resid.
7 0.7 0.55 1e-5                    | 6.2e-05 .. 8.2e-02        | 4.4e-05 .. 1.1e-01        | 2.4e-13    | 6.6e-11
13 0.0 0.001 1e-5                  | 3.1e-07 .. 5.5e-02        | 3.1e-07 .. 5.5e-02        | 1.2e-16    | 4.8e-14
17 -1.2 0.9 1e-5                   | 2.8e-07 .. 3.3e-02        | 2.7e-07 .. 2.6e-02        | 6.2e-14    | 4.3e-11
11 1.9 0.999 1e-7                  | 1.6e+03 .. 1.3e+10        | 5.4e+04 .. 1.1e+12        | 2.6e+02    | 2.1e-08
```

## 27. Scripts (verbatim)

### t2040_inv.py

```python
#!/usr/bin/env python3
"""T2040 item 1: inventory of the light-weight layer from the TeX (labels, spans, cites, proof location,
displayed estimates, sketch markers, dependency graph).  Usage: python3 inv.py <mode>
modes: stmts | eqs | deps | sketch | sizes | all"""
import re, sys, collections
TEX = '/Users/junyin/Lean_proof/RBM3D/paper/tex/'
FILES = ['1_2_Intro_model_result.tex', '3_5_Loop_Hierarchy.tex', '6_Step6_two_loop.tex',
         '7_8_light_weight.tex', 'A_deterministic_estimates.tex', 'B_graphical_lemmas.tex']
SHORT = {'1_2_Intro_model_result.tex': '1_2', '3_5_Loop_Hierarchy.tex': '3_5', '6_Step6_two_loop.tex': '6',
         '7_8_light_weight.tex': '7_8', 'A_deterministic_estimates.tex': 'A', 'B_graphical_lemmas.tex': 'B'}
# the paper targets of T2040: 7_8 lines 1-1791, B in full; consumers at the lines named in the ticket
SCOPE = {'7_8_light_weight.tex': (1, 1791), 'B_graphical_lemmas.tex': (1, 525)}
CONSUMERS = [('lem:LWterm', '3_5_Loop_Hierarchy.tex'), ('lem: EWGn2_N', '3_5_Loop_Hierarchy.tex'),
             ('lem:LWterm_EXP', '6_Step6_two_loop.tex')]
STMT_KINDS = ('lemma', 'definition', 'claim', 'example', 'remark', 'strategy', 'theorem')
# manual overrides (printed with the tables): unlabeled statements get a name; special proof locations
ALIAS = {'claim@7_8:264': 'claim:size (Gamma << size(Gamma), 7_8:264)',
         'claim@7_8:884': 'claim:xi (eq:Gbyxi2 bounds of xi, 7_8:884)',
         'lemma@B:393': 'GGGamma (BA GG expansion, B:393)',
         'remark@B:280': 'remark:3p (stronger ord bound, B:280)',
         'example:p=2': 'example:p=2 (sec:graphs_ideas, 7_8:505)'}
PROOF_NOTE = {'lem:Anp_key': 'proved by lem:Anp_key_gh (\"easy corollary\", 7_8:1025)',
              'claim:TTk': 'proof deferred to A.4 (pf:claim_TTk, A:265-314) = merged EKTTk / ekTTk_holds',
              'lem:LWterm': 'joint proof with lem: EWGn2_N: 7_8:84-91 (reduction to lem:LW_moment, lem:LW_moment_exp)',
              'lem: EWGn2_N': 'joint proof with lem:LWterm: 7_8:84-91'}
EQ_ENVS = ('equation', 'align', 'align*', 'split', 'gather', 'multline')


def strip_comment(l):
    out, i = [], 0
    while i < len(l):
        if l[i] == '%' and (i == 0 or l[i - 1] != '\\'):
            break
        out.append(l[i]); i += 1
    return ''.join(out)


class Tex:
    def __init__(self, fn):
        self.fn = fn
        self.raw = open(TEX + fn, encoding='utf-8').read().split('\n')
        self.cl = [strip_comment(l).replace('\\be ', '\\begin{equation} ').replace('\\be\n', '\\begin{equation}\n')
                   for l in self.raw]
        # \be / \ee shorthands at the end of line or alone
        self.cl = [re.sub(r'\\be(?![a-zA-Z])', r'\\begin{equation}', l) for l in self.cl]
        self.cl = [re.sub(r'\\ee(?![a-zA-Z])', r'\\end{equation}', l) for l in self.cl]
        self.envs, self.eqs, self.secs, self.figs = [], [], [], []
        self._parse()

    def _parse(self):
        stack = []
        tok = re.compile(r'\\begin\{([a-z*]+)\}|\\end\{([a-z*]+)\}|\\label\{([^}]*)\}|\\(sub)*section\*?\{|\\paragraph\{')
        for i, l in enumerate(self.cl, 1):
            for m in tok.finditer(l):
                if m.group(1):
                    nm = m.group(1)
                    e = dict(name=nm, start=i, end=None, label=None, arg='', id=len(self.envs))
                    rest = l[m.end():]
                    ma = re.match(r'\s*\[(.*?)\]', rest)
                    if ma and nm in STMT_KINDS + ('proof',):
                        e['arg'] = ma.group(1)
                    stack.append(e); self.envs.append(e)
                elif m.group(2):
                    nm = m.group(2)
                    for k in range(len(stack) - 1, -1, -1):
                        if stack[k]['name'] == nm:
                            stack[k]['end'] = i
                            del stack[k:]
                            break
                elif m.group(3) is not None:
                    lab = m.group(3).strip()
                    inner = [e for e in stack if e['name'] in EQ_ENVS]
                    if inner:
                        self.eqs.append(dict(label=lab, line=i, stack=[e['id'] for e in stack]))
                    elif any(e['name'] == 'figure' for e in stack):
                        self.figs.append(dict(label=lab, line=i))
                    else:
                        tgt = None
                        for e in reversed(stack):
                            if e['name'] in STMT_KINDS:
                                tgt = e; break
                            if e['name'] == 'proof':
                                break
                        if tgt is not None:
                            if tgt['label'] is None:
                                tgt['label'] = lab
                        elif not any(e['name'] == 'proof' for e in stack) and self.secs and self.secs[-1]['label'] is None and self.secs[-1]['line'] >= i - 2:
                            self.secs[-1]['label'] = lab
                else:
                    txt = m.group(0)
                    if txt.startswith('\\paragraph'):
                        lvl = 4
                    else:
                        lvl = 1 + txt.count('sub')
                    self.secs.append(dict(line=i, level=lvl, title=l[m.end():].strip(), label=None))
        for e in self.envs:
            if e['end'] is None:
                e['end'] = e['start']
        for q in self.eqs:
            ee = next(e for e in self.envs if e['id'] == q['stack'][-1]) if q['stack'] else None
            q['env'] = (ee['start'], ee['end']) if ee else (q['line'], q['line'])
        for k, s in enumerate(self.secs):
            end = len(self.cl)
            for s2 in self.secs[k + 1:]:
                if s2['level'] <= s['level']:
                    end = s2['line'] - 1
                    break
            s['end'] = end

    def text(self, a, b):
        return '\n'.join(self.cl[a - 1:b])


def stack_has_stmt(stack):
    return any(e['name'] in STMT_KINDS + ('proof',) + EQ_ENVS for e in stack)


def cites(text):
    out = []
    for m in re.finditer(r'\\(?:Cref|cref|eqref|ref|autoref)\{([^}]*)\}', text):
        for x in m.group(1).split(','):
            x = x.strip()
            if x:
                out.append(x)
    return out


def ext_cites(text):
    out = []
    for m in re.finditer(r'\\cite[a-z]*(?:\[[^\]]*\])?\{([^}]*)\}', text):
        for x in m.group(1).split(','):
            out.append(x.strip())
    return out


T = {fn: Tex(fn) for fn in FILES}
# global label map: label -> (file, line, kind)
LAB = {}
for fn, t in T.items():
    for e in t.envs:
        if e['label']:
            LAB[e['label']] = (fn, e['start'], e['name'])
    for q in t.eqs:
        LAB.setdefault(q['label'], (fn, q['line'], 'eq'))
    for s in t.secs:
        if s['label']:
            LAB[s['label']] = (fn, s['line'], 'sec')
    for i, l in enumerate(t.cl, 1):
        for m in re.finditer(r'\\label\{([^}]*)\}', l):
            LAB.setdefault(m.group(1).strip(), (fn, i, 'other'))


def in_scope(fn, line):
    if fn not in SCOPE:
        return False
    a, b = SCOPE[fn]
    return a <= line <= b


def nonblank_lines(t, a, b):
    return sum(1 for l in t.cl[a - 1:b] if l.strip())


def home_of(fn, line):
    """innermost statement env / proof env containing the line (for equations), else enclosing section"""
    t = T[fn]
    best = None
    for e in t.envs:
        if e['name'] in STMT_KINDS + ('proof',) and e['start'] <= line <= e['end']:
            if best is None or e['start'] >= best['start']:
                best = e
    if best:
        return best
    return None


def sec_of(fn, line):
    t = T[fn]
    best = None
    for s in t.secs:
        if s['line'] <= line <= s['end'] and s['level'] <= 3:
            if best is None or s['line'] >= best['line']:
                best = s
    return best


# statements ------------------------------------------------------------------------------------------------------
def statements():
    rows = []
    for fn in SCOPE:
        t = T[fn]
        for e in t.envs:
            if e['name'] in STMT_KINDS and in_scope(fn, e['start']):
                lab = e['label'] or '%s@%s:%d' % (e['name'], SHORT[fn], e['start'])
                rows.append(dict(fn=fn, env=e, label=lab, kind=e['name'], a=e['start'], b=e['end']))
    # consumers (statements in other files)
    for lab, fn in CONSUMERS:
        fn0, line, kind = LAB[lab]
        for e in T[fn0].envs:
            if e['label'] == lab:
                rows.append(dict(fn=fn0, env=e, label=lab, kind=e['name'], a=e['start'], b=e['end'], consumer=True))
    rows.sort(key=lambda r: (FILES.index(r['fn']) if not r.get('consumer') else -1, r['a']))
    return rows


def proof_info(row):
    """where is the proof: list of (kind, file, a, b, note)"""
    fn, lab = row['fn'], row['label']
    t = T[fn]
    out = []
    # 1. proof environments whose optional argument cites the label
    for fn2 in FILES:
        for e in T[fn2].envs:
            if e['name'] == 'proof' and (fn2 == fn or True):
                if lab in cites(e['arg']):
                    out.append(('proof-env', fn2, e['start'], e['end']))
    # 2. subsections 'Proof of ... \Cref{lab}'
    for fn2 in FILES:
        for s in T[fn2].secs:
            if s['level'] <= 3 and re.match(r'(Proof|Proofs) of', s['title']) and lab in cites(s['title']):
                out.append(('proof-section', fn2, s['line'], s['end']))
    # 3. the proof env immediately after the statement (no optional argument naming another label)
    if not out:
        nxt = [e for e in t.envs if e['name'] == 'proof' and e['start'] >= row['b'] and e['start'] - row['b'] <= 3]
        for e in nxt:
            if not cites(e['arg']):
                out.append(('proof-env', fn, e['start'], e['end']))
                break
    # 4. 'defer/postpone ... \Cref{target}' in the next 15 lines
    if not out:
        seg = t.text(row['b'], min(len(t.cl), row['b'] + 15))
        for m in re.finditer(r'(defer|postpone)[^.]*', seg):
            for c in cites(m.group(0)):
                if c != lab and c in LAB:
                    fn2, ln2, k2 = LAB[c]
                    if k2 == 'sec':
                        s = next(s for s in T[fn2].secs if s['label'] == c)
                        out.append(('deferred-to', fn2, s['line'], s['end']))
    return out


def classify(row, pinfo):
    fn = row['fn']; a, b = row['a'], row['b']
    arg = row['env']['arg']
    ext = ext_cites(arg)
    kind = row['kind']
    if kind in ('definition', 'example', 'strategy', 'remark'):
        return 'def' if kind == 'definition' else kind
    rbm_p = split_proofs(pinfo)[0] if pinfo else []
    if rbm_p or pinfo:
        k = (rbm_p or pinfo)[0]
        where = SHORT[k[1]]
        return 'proved:%s' % where if k[0] != 'deferred-to' else 'deferred:%s' % where
    if ext:
        return 'cited:' + ','.join(ext)
    return 'no-proof'


def sketch_hits(text_lines, a):
    pats = ['omit', 'similar', 'analogous', 'straightforward', 'standard', 'as in', 'same (argument|reasoning)',
            'easy to see', 'not hard to see', 'verbatim', 'exactly the same', 'one can (check|verify)', 'direct check',
            'we do not pursue', 'without loss of generality', 'heuristic', 'roughly speaking', 'it is easy']
    hits = collections.OrderedDict()
    for k, l in enumerate(text_lines):
        for p in pats:
            if re.search(p, l, re.I):
                hits.setdefault(p.split('(')[0].strip(), []).append(a + k)
    return hits


def chars_excl(fkey, a, b):
    """TeX characters of lines a..b of file `fkey` (a key of SHORT values or file name), comments and
    figure/tikz environments removed (figure code is drawing, not mathematics)"""
    fn = next((f for f, sh in SHORT.items() if sh == fkey or f == fkey), None)
    t = T[fn]
    skip = set()
    for e in t.envs:
        if e['name'] in ('figure', 'tikzpicture'):
            skip.update(range(e['start'], e['end'] + 1))
    n = 0
    for i in range(a, min(b, len(t.cl)) + 1):
        if i in skip:
            continue
        n += len(t.cl[i - 1].strip())
    return n


def is_ba(fn, a):
    return fn == 'B' or (fn == '7_8_light_weight.tex' and a >= 1792)


def split_proofs(pi):
    rbm = [x for x in pi if not (x[1] == 'B_graphical_lemmas.tex' and x[2] >= 286)]
    ba = [x for x in pi if (x[1] == 'B_graphical_lemmas.tex' and x[2] >= 286)]
    return rbm, ba


def name_of(r):
    return ALIAS.get(r['label'], r['label'])


def mode_stmts():
    rows = statements()
    print('| # | label | kind | span | stmt cites | proof cites | proof (RBM) | proof (BA variant) | class |')
    print('|---|---|---|---|---|---|---|---|---|')
    for k, r in enumerate(rows, 1):
        t = T[r['fn']]
        pi = proof_info(r)
        rbm, ba = split_proofs(pi)
        stext = t.text(r['a'], r['b'])
        sc = [c for c in dict.fromkeys(cites(stext)) if c != r['label']]
        pc = []
        for (kind, fn2, a, b) in rbm:
            pc += cites(T[fn2].text(a, b))
        pc = [c for c in dict.fromkeys(pc) if c != r['label'] and c not in sc]
        loc = '; '.join('%s %s:%d-%d' % (kind, SHORT[fn2], a, b) for (kind, fn2, a, b) in rbm) or PROOF_NOTE.get(r['label'], '-')
        if r['label'] in PROOF_NOTE and rbm:
            loc += ' [' + PROOF_NOTE[r['label']] + ']'
        locb = '; '.join('%s %s:%d-%d' % (kind, SHORT[fn2], a, b) for (kind, fn2, a, b) in ba) or '-'
        cls = classify(r, pi)

        def fmt(lst, n=9):
            return ' '.join(lst[:n]) + (' (+%d)' % (len(lst) - n) if len(lst) > n else '')
        print('| %d | `%s` | %s | %s:%d-%d | %s | %s | %s | %s | %s |' % (
            k, name_of(r), r['kind'], SHORT[r['fn']], r['a'], r['b'], fmt(sc) or '-', fmt(pc) or '-', loc, locb, cls))


def mode_ba():
    """statements of the block Anderson section 7_8:1792-2108 (outside the LW scope; item 6)"""
    t = T['7_8_light_weight.tex']
    print('| label | kind | span | note |')
    print('|---|---|---|---|')
    for e in t.envs:
        if e['name'] in STMT_KINDS and e['start'] >= 1792:
            lab = e['label'] or '%s@7_8:%d' % (e['name'], e['start'])
            arg = e['arg'][:60]
            print('| `%s` | %s | 7_8:%d-%d | %s |' % (lab, e['name'], e['start'], e['end'], arg))
    for e in t.envs:
        if e['name'] == 'proof' and e['start'] >= 1792:
            print('| (proof) | proof | 7_8:%d-%d | %s |' % (e['start'], e['end'], e['arg'][:70]))


def rev_cites():
    """label -> list of 'file:line' where it is cited (inside scope files and the consumer files)"""
    out = collections.defaultdict(list)
    for fn in FILES:
        t = T[fn]
        for i, l in enumerate(t.cl, 1):
            for c in cites(l):
                out[c].append('%s:%d' % (SHORT[fn], i))
    return out


def mode_eqs():
    rc = rev_cites()
    print('| label | line | home | cited at (first 5, outside its own line) |')
    print('|---|---|---|---|')
    n = 0
    for fn in SCOPE:
        t = T[fn]
        for q in t.eqs:
            if not in_scope(fn, q['line']):
                continue
            h = home_of(fn, q['line'])
            if h and h['name'] != 'proof':
                hs = '%s %s:%d-%d' % (h['label'] or h['name'], SHORT[fn], h['start'], h['end'])
            elif h:
                hs = 'proof %s:%d-%d' % (SHORT[fn], h['start'], h['end'])
            else:
                s = sec_of(fn, q['line'])
                hs = ('sect %s %s:%d-%d' % (s['label'] or s['title'][:24], SHORT[fn], s['line'], s['end'])) if s else '-'
            cs = [c for c in rc.get(q['label'], []) if c != '%s:%d' % (SHORT[fn], q['line'])]
            print('| `%s` | %s:%d | %s | %s%s |' % (q['label'], SHORT[fn], q['line'], hs, ' '.join(cs[:5]) or '-', ' (+%d)' % (len(cs) - 5) if len(cs) > 5 else ''))
            n += 1
    print('\nlabeled displayed equations in scope: %d' % n)


def graph():
    """node -> children (cited labels resolved to statement nodes); equation labels are mapped to their home statement"""
    rows = statements()
    node = {r['label']: r for r in rows}
    # map every in-scope equation label to its home statement label (or proof-home)
    def resolve(c, here):
        if c in node:
            return c
        if c in LAB:
            fn, ln, k = LAB[c]
            h = home_of(fn, ln)
            if h is not None:
                # a proof env belongs to the statement it proves
                if h['name'] == 'proof':
                    for r in rows:
                        for (kind, fn2, a, b) in proof_info(r):
                            if fn2 == fn and a <= ln <= b:
                                return r['label']
                    return None
                lab = h['label'] or '%s@%s:%d' % (h['name'], SHORT[fn], h['start'])
                if lab in node:
                    return lab
            # inside a proof section: home = the statement proved by the section
            for r in rows:
                for (kind, fn2, a, b) in proof_info(r):
                    if fn2 == fn and a <= ln <= b:
                        return r['label']
        return None
    edges = collections.OrderedDict()
    ext = collections.OrderedDict()
    for r in rows:
        t = T[r['fn']]
        txt = t.text(r['a'], r['b'])
        for (kind, fn2, a, b) in split_proofs(proof_info(r))[0]:
            txt += '\n' + T[fn2].text(a, b)
        ch, ex = [], []
        for c in dict.fromkeys(cites(txt)):
            if c == r['label']:
                continue
            res = resolve(c, r)
            if res and res != r['label']:
                if res not in ch:
                    ch.append(res)
            else:
                if c in LAB:
                    fn, ln, k = LAB[c]
                    ex.append('%s(%s:%d)' % (c, SHORT[fn], ln))
                else:
                    ex.append('%s(?)' % c)
        edges[r['label']] = ch
        ext[r['label']] = ex
    return rows, node, edges, ext


def mode_deps():
    rows, node, edges, ext = graph()
    seen = set()
    order = {r['label']: i for i, r in enumerate(rows)}

    def show(lab, depth, path):
        r = node[lab]
        tag = '%s:%d' % (SHORT[r['fn']], r['a'])
        if lab in seen:
            print('%s%s [%s %s] (expanded above)' % ('  ' * depth, lab, r['kind'], tag))
            return
        seen.add(lab)
        e = ext[lab]
        print('%s%s [%s %s]%s' % ('  ' * depth, lab, r['kind'], tag, ('  uses outside LW layer: ' + ' '.join(e)) if e and depth <= 1 else ''))
        for c in edges[lab]:
            if c in path:
                continue
            show(c, depth + 1, path | {lab})
    for lab, fn in CONSUMERS:
        show(lab, 0, frozenset())
        print()
    # nodes never reached from the three consumers
    reach = set(seen)
    unreached = [r['label'] for r in rows if r['label'] not in reach]
    print('statements of the inventory not reachable from the three consumers by explicit cross-references: %d' % len(unreached))
    print(' '.join(unreached))
    print('\nreverse view: statements that cite no other statement of the layer (leaves):')
    print(' '.join(l for l in node if not edges[l]))


def mode_layers():
    rows, node, edges, ext = graph()
    cons = [c for c, _ in CONSUMERS]
    dist = {c: 0 for c in cons}
    # longest path layering over the DAG obtained by dropping edges between the consumers and back edges (DFS order)
    order = []
    state = {}

    def dfs(u):
        state[u] = 1
        for v in edges[u]:
            if v in cons and u in cons:
                continue
            if state.get(v) == 1:
                continue
            if v not in state:
                dfs(v)
        state[u] = 2
        order.append(u)
    for c in cons:
        if c not in state:
            dfs(c)
    topo = list(reversed(order))
    dist = {u: 0 for u in topo}
    for u in topo:
        for v in edges[u]:
            if v in dist and not (v in cons and u in cons) and state.get(v) == 2 and topo.index(v) > topo.index(u):
                dist[v] = max(dist[v], dist[u] + 1)
    layers = collections.defaultdict(list)
    for u in topo:
        layers[dist[u]].append(name_of(node[u]))
    for L in sorted(layers):
        print('L%d: %s' % (L, '; '.join(layers[L])))
    print('statements outside the layering (no explicit \\Cref path from the consumers): ' + ' '.join(name_of(r) for r in rows if r['label'] not in dist))


def mode_sketch():
    rows = statements()
    print('| statement | proof span (RBM) | non-blank TeX lines | sketch markers (word: line numbers) |')
    print('|---|---|---|---|')
    for r in rows:
        pi = split_proofs(proof_info(r))[0]
        for (kind, fn2, a, b) in pi[:1]:
            tt = T[fn2]
            hits = sketch_hits(tt.cl[a - 1:b], a)
            hs = '; '.join('%s: %s' % (k, ','.join(map(str, v[:6])) + ('..' if len(v) > 6 else '')) for k, v in hits.items())
            print('| `%s` | %s:%d-%d | %d | %s |' % (name_of(r), SHORT[fn2], a, b, nonblank_lines(tt, a, b), hs or '-'))


def mode_sizes():
    rows = statements()
    print('| class | statements | non-blank TeX lines of statements | non-blank TeX lines of proofs (RBM) |')
    print('|---|---|---|---|')
    agg = collections.defaultdict(lambda: [0, 0, 0])
    for r in rows:
        pi = split_proofs(proof_info(r))[0]
        cls = classify(r, proof_info(r)).split(':')[0]
        t = T[r['fn']]
        agg[cls][0] += 1
        agg[cls][1] += nonblank_lines(t, r['a'], r['b'])
        for (kind, fn2, a, b) in pi[:1]:
            agg[cls][2] += nonblank_lines(T[fn2], a, b)
    for k, v in sorted(agg.items()):
        print('| %s | %d | %d | %d |' % (k, v[0], v[1], v[2]))
    for fn, (a, b) in SCOPE.items():
        print('\nfile %s lines %d-%d: %d non-blank non-comment TeX lines' % (SHORT[fn], a, b, nonblank_lines(T[fn], a, b)))


def mode_classes():
    """statements grouped by class (where the proof is): label (file:span)"""
    rows = statements()
    agg = collections.OrderedDict()
    for r in rows:
        agg.setdefault(classify(r, proof_info(r)), []).append('%s (%s:%d-%d)' % (name_of(r), SHORT[r['fn']], r['a'], r['b']))
    for k, v in agg.items():
        print('%s [%d]: %s' % (k, len(v), '; '.join(v)))


if __name__ == '__main__':
    m = sys.argv[1] if len(sys.argv) > 1 else 'all'
    for name, f in (('stmts', mode_stmts), ('eqs', mode_eqs), ('deps', mode_deps), ('layers', mode_layers), ('sketch', mode_sketch), ('sizes', mode_sizes), ('ba', mode_ba), ('classes', mode_classes)):
        if m in (name, 'all'):
            print('## ' + name)
            f()
            print()
```

### t2040_size.py

```python
#!/usr/bin/env python3
"""T2040 item 7: size of gate LW computed from the item-1 inventory (spans, TeX characters, sketch markers).
Model: lines(item) = chars(item)/1000 * R * m(item)            for items with a proof in the paper
       lines(item) = fixed(item)                                 for items the paper only cites or that are infrastructure
R  = measured lines per TeX kchar of merged d>=3 proofs (calibration section below, from the merged files);
m  = 1,2,3 by the density of 'sketch markers' (omit/similar/standard/as in/...) in the proof text (thresholds below);
lo: m=1 for every item; central: m by density; hi: m+1 (at most 4).  Tickets = lines / 1000 (the design band is 600-1500)."""
import sys, subprocess, re
sys.path.insert(0, '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad')
import t2040_inv as I

WT = '/Users/junyin/Lean_proof/RBM3D-wt/T2040/'


def nlines(f):
    return len(open(WT + f, encoding='utf-8').read().split('\n')) - 1


print('## calibration: merged d>=3 formalizations of paper proofs (lines of the merged Lean files / TeX kchars of the paper span)')
cal = []
c1 = nlines('RBM3D/Kernel/PropT.lean'); k1 = (I.chars_excl('A', 230, 264) + I.chars_excl('A', 265, 314)) / 1000
cal.append(('lem:propT + claim:TTk (A:230-314)', 'Kernel/PropT.lean', c1, k1))
c2 = sum(nlines(f) for f in ('RBM3D/Kernel/Evolution.lean', 'RBM3D/Kernel/SumDecay.lean', 'RBM3D/Evolution/SumDecay.lean'))
k2 = I.chars_excl('A', 84, 229) / 1000
cal.append(('evolution kernel estimates (A:84-229), merged part', 'Kernel/{Evolution,SumDecay}, Evolution/SumDecay', c2, k2))
for name, files, c, k in cal:
    print('| %-52s | %-48s | %5d lines | %6.2f kchar | %6.1f lines/kchar |' % (name, files, c, k, c / k))
R = round(sum(c for _, _, c, _ in cal) / sum(k for _, _, _, k in cal))
print('R = total merged lines / total kchar = %d lines per TeX kchar' % R)
print()

# thresholds for the multiplier m by sketch-marker density (markers per TeX kchar of the proof text)
GAP = ['omit', 'straightforward', 'direct check', 'not hard to see', 'easy to see', 'it is easy', 'we do not pursue', 'roughly speaking']


def gap_lines(fn, a, b):
    """lines of the proof text that say a step is omitted / easy / straightforward (the details are missing)"""
    t = I.T[fn]
    out = []
    for k, l in enumerate(t.cl[a - 1:b]):
        if any(re.search(g, l, re.I) for g in GAP):
            out.append(a + k)
    return out


def m_of(ngap):
    """multiplier on the measured rate: 1 (no omitted step), 1.5 (one to three), 2 (four or more)"""
    return 1 if ngap == 0 else (1.5 if ngap < 4 else 2)


# work items of the random band matrix layer: (id, title, [(file, a, b)] proof/statement spans counted, kind, fixed lines, note)
ITEMS = [
    ('LW-01', 'reduction of lem:LWterm, lem: EWGn2_N to the moments (eq:directG, recolterm, Markov, expectation upgrade)', [('7_8', 1, 104)], 'proof', 0),
    ('LW-02', 'moment => LW_moment, LW_moment_exp assembly; far/near split', [('7_8', 716, 720), ('7_8', 943, 950), ('7_8', 1600, 1630)], 'proof', 0),
    ('LW-03', 'graph record, values, counters, molecules, normal graphs, dotted-edge partition (def_graph1 ... def scaling order)', [('7_8', 105, 285)], 'fixed', 1400),
    ('LW-04', 'Gaussian bridge: E Z_w = 0 for resolvent polynomials (GaussIBP, Tame) and the formal graph derivative', [], 'fixed', 1200),
    ('LW-05', 'weight expansion (Owx) on graphs (cited: yang2021, Lemma 3.5)', [('7_8', 294, 306)], 'fixed', 800),
    ('LW-06', 'edge expansion (Oe1x) on graphs (cited: Lemma 3.10)', [('7_8', 309, 330)], 'fixed', 1100),
    ('LW-07', 'GG expansion (Oe2x) on graphs (cited: Lemma 3.14)', [('7_8', 334, 349)], 'fixed', 1000),
    ('LW-08', 'lvl1 lemma: expansion strategy to locally standard graphs, termination, Err of size W^-D (cited: Lemma 3.22)', [('7_8', 351, 399), ('B', 122, 157)], 'fixed', 1500),
    ('LW-09', 'claim: Gamma << size(Gamma) (molecules, free vertex, scalemole, S^pm decay)', [('7_8', 257, 266)], 'fixed', 1300),
    ('LW-10', 'lem:localregular (1)-(6): paths, molecules, scaling order through every expansion term', [('B', 158, 278)], 'proof', 0),
    ('LW-11', 'auxiliary graph, GtoAG', [('7_8', 863, 932)], 'proof', 0),
    ('LW-12', 'nested graphs: lem:Anp_key, lem:Anp_key_gh, lem:Anp (cases I-IV, induction, spanning trees)', [('7_8', 933, 1599)], 'proof', 0),
    ('LW-13', 'lem:LW_moment_exp_far, _near (claim:TTk merged as EKTTk)', [('7_8', 1631, 1791)], 'proof', 0),
    ('LW-14', 'lem:LWterm_EXP (I1..I4, J-terms, case (1)-(4) of ord)', [('B', 7, 121)], 'proof', 0),
    ('LW-15', 'deterministic sublemmas: (eq:Psi) for the B-class, W^-d T~ ~ sT^2, Psi_t window (paper-delta T2040a)', [], 'fixed', 600),
    ('LW-16', 'regime split of lem: EWGn2_N along sub-sequences (7_8:20 "immediate consequence"; finding T2040k)', [], 'fixed', 500),
]
# block Anderson additions (item 6)
BA = [
    ('BA-L1', 'BA graph vocabulary: Psi- and M-dotted edges, atoms, def scalingBA', [('B', 286, 356)], 'proof', 0),
    ('BA-L2', 'BA expansions lanlw, lem_lweight, GGGamma (cited: yang2024Del B.9-B.11)', [('B', 359, 405)], 'fixed', 2400),
    ('BA-L3', 'BA lvl1, atomic reduction and auxiliary graph, Anp for atoms (B:415-523)', [('B', 407, 523)], 'proof', 0),
    ('BA-L4', 'BA LWterm_EXP (B:118: analogous with GGGamma)', [], 'fixed', 1500),
]


def eval_items(items, label):
    print('## %s' % label)
    print('| id | work item | TeX kchar | omitted-step lines | m | lines lo | lines central | lines hi |')
    print('|---|---|---|---|---|---|---|---|')
    tot = [0, 0, 0]
    rows = []
    for (iid, title, spans, kind, fixed) in items:
        ch = sum(I.chars_excl(f, a, b) for f, a, b in spans)
        gl = []
        for (f, a, b) in spans:
            fn = next(x for x, sh in I.SHORT.items() if sh == f)
            gl += ['%s:%d' % (f, x) for x in gap_lines(fn, a, b)]
        if kind == 'proof':
            m = m_of(len(gl))
            lo = ch / 1000 * R
            ce = ch / 1000 * R * m
            hi = ch / 1000 * R * (m + 1)
        else:
            m = '-'
            lo = ce = hi = fixed
        tot[0] += lo; tot[1] += ce; tot[2] += hi
        print('| %s | %s | %.1f | %s | %s | %d | %d | %d |' % (iid, title[:78], ch / 1000, (','.join(gl) or '-')[:60], m, lo, ce, hi))
        rows.append((iid, lo, ce, hi))
    print('| total | | | | | %d | %d | %d |' % tuple(tot))
    print('tickets at 1000 lines: lo %.0f, central %.0f, hi %.0f   (design band 600-1500 lines: central %.0f..%.0f)' % (
        tot[0] / 1000, tot[1] / 1000, tot[2] / 1000, tot[1] / 1500, tot[1] / 600))
    return tot, rows


a, arows = eval_items(ITEMS, 'random band matrix layer (gate LW)')
print()
b, brows = eval_items(BA, 'block Anderson additions (gate BA, item 6)')
print()
print('LW + BA tickets at 1000 lines: lo %.0f, central %.0f, hi %.0f' % ((a[0] + b[0]) / 1000, (a[1] + b[1]) / 1000, (a[2] + b[2]) / 1000))
print()
print('## reduced routes (items kept; tickets at 1000 lines: lo / central / hi)')
def route(name, keep):
    t = [sum(r[i] for r in arows if r[0] in keep) for i in (1, 2, 3)]
    print('| %-60s | %s | %.0f / %.0f / %.0f |' % (name, ' '.join(sorted(keep)), t[0] / 1000, t[1] / 1000, t[2] / 1000))
allids = {r[0] for r in arows}
route('full random band layer', allids)

route('R1: expansions + lvl1 lemma as authorized external inputs (DECISIONS 5)', allids - {'LW-04', 'LW-05', 'LW-06', 'LW-07', 'LW-08'})
route('R2: Step 6 only (lem:LWterm_EXP; no lem:LWterm, lem: EWGn2_N)', {'LW-03', 'LW-04', 'LW-07', 'LW-09', 'LW-11', 'LW-14', 'LW-15'})
route('R1 and R2 intersect: Step 6 only, expansions external', {'LW-03', 'LW-09', 'LW-11', 'LW-14', 'LW-15'})
```

### t2040_extract.py

```python
#!/usr/bin/env python3
"""T2040: extract declarations of the probe by name (docstrings omitted); theorems are cut at `:=`.
usage: t2040_extract.py FILE name [name ...]      (name = last component, e.g. LWterm)
       t2040_extract.py FILE --list KIND           (KIND = def|theorem: names with line numbers)"""
import re, sys

fn = sys.argv[1]
L = open(fn, encoding='utf-8').read().split('\n')
START = re.compile(r'^(?:private )?(?:noncomputable )?(theorem|def|abbrev|structure|inductive|instance|lemma)\s+([^\s({\[:]+)')
BOUND = re.compile(r'^(/--|/-!|theorem |def |abbrev |structure |inductive |instance |lemma |end |namespace |section|open |variable|set_option|noncomputable)')


def decl(name):
    out = []
    for i, l in enumerate(L):
        m = START.match(l)
        if m and (m.group(2) == name or m.group(2).split('.')[-1] == name):
            j = i + 1
            while j < len(L) and not (BOUND.match(L[j]) and L[j].strip()):
                j += 1
            body = L[i:j]
            while body and not body[-1].strip():
                body.pop()
            kind = m.group(1)
            if kind in ('theorem', 'lemma'):
                text = '\n'.join(body)
                depth = 0
                cut = None
                for pos, ch in enumerate(text):
                    if ch in '([{⟨':
                        depth += 1
                    elif ch in ')]}⟩':
                        depth -= 1
                    elif ch == ':' and text[pos:pos + 2] == ':=' and depth == 0:
                        cut = pos
                        break
                if cut is not None:
                    body = (text[:cut].rstrip() + ' := ...').split('\n')
            out.append((i + 1, i + len(body), body))
    return out


if sys.argv[2] == '--list':
    kind = sys.argv[3]
    for i, l in enumerate(L):
        m = START.match(l)
        if m and m.group(1) == kind:
            print('%d %s' % (i + 1, m.group(2)))
else:
    for nm in sys.argv[2:]:
        r = decl(nm)
        if not r:
            print('-- %s: NOT FOUND' % nm)
        for (a, b, body) in r:
            print('-- probe lines %d-%d' % (a, b))
            print('\n'.join(body))
            print()
```

### t2040_stats.py

```python
#!/usr/bin/env python3
"""T2040: code-line counts of the two candidate representations and of the pins in the probe (docstrings, comments, blank lines excluded)."""
import re, sys
fn = sys.argv[1]
L = open(fn, encoding='utf-8').read().split('\n')


def code_lines(a, b):
    n = 0
    indoc = False
    for i in range(a - 1, b):
        l = L[i]
        s = l.strip()
        if indoc:
            if '-/' in s:
                indoc = False
            continue
        if s.startswith('/--') or s.startswith('/-!') or s.startswith('/-'):
            if '-/' not in s[2:]:
                indoc = True
            continue
        if not s or s.startswith('--'):
            continue
        n += 1
    return n


def find(pat, start=1):
    for i in range(start - 1, len(L)):
        if re.match(pat, L[i]):
            return i + 1
    raise SystemExit('not found ' + pat)


A0 = find(r'^structure LData'); A1 = find(r'^end Counters')
B0 = find(r'^inductive GTerm'); B1 = find(r'^end Syntax')
ex0 = find(r'^def p2Graph'); ex1 = find(r'^end Examples')
print('candidate A (record LGraph: LData, edges, LGraph, term/val, counters/molecules): lines %d-%d, code lines %d' % (A0, A1, code_lines(A0, A1)))
print('candidate B (syntax with binders: GTerm, eval, one graph + its value theorem):    lines %d-%d, code lines %d' % (B0, B1, code_lines(B0, B1)))
print('  A: two example graphs (p2Graph, figGraph) with value and counters:               lines %d-%d, code lines %d' % (ex0, ex1, code_lines(ex0, ex1)))
N0 = find(r'^abbrev NV'); N1 = find(r'^theorem figAux_ord')
print('nested graphs (NGraph, predicates, value, figAux and its checks):                  lines %d-%d, code lines %d' % (N0, N1, code_lines(N0, N1)))
O0 = find(r'^section OwxAlg'); O1 = find(r'^end OwxSmallest')
print('weight expansion on the vocabulary (defect identity, 2 graphs, expectation):       lines %d-%d, code lines %d' % (O0, O1, code_lines(O0, O1)))
print('   of which owx_defect_identity (generic f, df; one proof):                       code lines %d' % code_lines(find(r'^theorem owx_defect_identity'), find(r'^end OwxAlg')))
a0 = find(r'^def owxG0'); a1 = find(r'^def owxH0') - 1
b0 = find(r'^def owxT0'); b1 = find(r'^end OwxSmallest')
print('(Owx) for the smallest graph, candidate A: three records + counters + value theorem: lines %d-%d, code lines %d' % (a0, a1, code_lines(a0, a1)))
print('(Owx) for the smallest graph, candidate B: three binder terms + value theorem:       lines %d-%d, code lines %d' % (b0, b1, code_lines(b0, b1)))
P0 = find(r'^/-! ## 5\. The three expansions'); P1 = find(r'^end RBM.Graph', P0)
print('three expansion pins (+ flow data definitions):                                    lines %d-%d, code lines %d' % (P0, P1, code_lines(P0, P1)))
Q0 = find(r'^/-! ## 6\. The pins at sequence level'); Q1 = find(r'^/-! ## 7\.')
print('sequence-level pins and their definitions (section 6):                             lines %d-%d, code lines %d' % (Q0, Q1, code_lines(Q0, Q1)))
S0 = find(r'^/-! ## 7\.'); S1 = find(r'^/-! ## 8\.')
print('skeleton (section 7: Markov step, (eq:Psi) shift, regimes):                        lines %d-%d, code lines %d' % (S0, S1, code_lines(S0, S1)))
I0 = find(r'^/-! ## 8\.')
print('instances (section 8):                                                             lines %d-%d, code lines %d' % (I0, len(L), code_lines(I0, len(L))))
print('whole probe: %d lines, %d code lines' % (len(L), code_lines(1, len(L))))
```

### t2040_expansions.py

```python
#!/usr/bin/env python3
"""T2040: pathwise check of the three expansion pins (Owx), (Oe1x), (Oe2x) as stated in the probe (generic f).
For a Hermitian H (any), z = E+(1-t)m, S = t*S0 (row sums t), Sp = S(1-m^2 S)^{-1}:
   LHS - RHS = -m * sum_w (delta_xw + m^2 Sp_xw) Z_w   (Owx, Oe2x)       and       LHS - RHS = -m Z_x   (Oe1x)
with the Stein defect Z_w = sum_a H_wa F_a - sum_a S_wa d_{h_aw} F_a  (F_a the function the IBP is applied to).
d_{h_aw} is the complex derivative along E_{aw} of H -> F(R+(H), R-(H)), R+ = (H-z)^-1, R- = (H-zbar)^-1,
red entry  Gb_xy = conj G_xy = R-[y,x] for Hermitian H.   d via central difference (holomorphic in the entries)."""
import numpy as np, sys
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
n = 5
E = float(sys.argv[2]) if len(sys.argv) > 2 else 0.7
t = float(sys.argv[3]) if len(sys.argv) > 3 else 0.55
m = (-E + 1j * np.sqrt(4 - E ** 2)) / 2           # m^2 + E m + 1 = 0, Im m > 0
z = E + (1 - t) * m
A = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n)); H = (A + A.conj().T) / 2
S0 = np.abs(rng.normal(size=(n, n))); S0 = (S0 + S0.T) / 2; S0 = S0 / S0.sum(1, keepdims=True)   # rows sum to 1 (symmetrised row sums only approx)
S0 = S0 / S0.sum(1, keepdims=True)
S = t * S0
Sp = S @ np.linalg.inv(np.eye(n) - m ** 2 * S)
I = np.eye(n)
Rp = lambda Hm: np.linalg.inv(Hm - z * I)
Rm = lambda Hm: np.linalg.inv(Hm - np.conj(z) * I)
G = lambda Hm, i, j: Rp(Hm)[i, j]
Gb = lambda Hm, i, j: Rm(Hm)[j, i]          # conj(G_ij) for Hermitian
Gc = lambda Hm, i, j: Rp(Hm)[i, j] - (m if i == j else 0)
Gcb = lambda Hm, i, j: Rm(Hm)[j, i] - (np.conj(m) if i == j else 0)   # conj(G-M)_ij
h = float(sys.argv[4]) if len(sys.argv) > 4 else 1e-5


def dH(F, Hm, a, w):
    Ea = np.zeros((n, n), complex); Ea[a, w] = 1
    return (F(Hm + h * Ea) - F(Hm - h * Ea)) / (2 * h)


def stein_defect(Fa, Hm, w):
    """Z_w = sum_a H_wa F_a(H) - sum_a S_wa d_{h_aw} F_a ;  Fa(a, H) -> complex"""
    return sum(Hm[w, a] * Fa(a, Hm) for a in range(n)) - sum(S[w, a] * dH(lambda X, a=a: Fa(a, X), Hm, a, w) for a in range(n))


# a generic polynomial f of the resolvent entries (G and Gb), independent of x
u, v, p, q = 1, 3, 2, 0
f = lambda Hm: Gb(Hm, u, v) * G(Hm, p, q) * G(Hm, v, u) + 0.3 * G(Hm, q, q)
fH = f(H)
x = 2
res = {}
# ---------------- (Owx) ----------------
lhs = Gc(H, x, x) * fH
rhs = (m * sum(S[x, a] * Gc(H, x, x) * Gc(H, a, a) * fH for a in range(n))
       + m ** 3 * sum(Sp[x, a] * S[a, b] * Gc(H, a, a) * Gc(H, b, b) * fH for a in range(n) for b in range(n))
       - m * sum(S[x, a] * G(H, a, x) * dH(f, H, a, x) for a in range(n))
       - m ** 3 * sum(Sp[x, a] * S[a, b] * G(H, b, a) * dH(f, H, b, a) for a in range(n) for b in range(n)))
Z = [stein_defect(lambda a, Hm, w=w: G(Hm, a, w) * f(Hm), H, w) for w in range(n)]
pred = -m * sum(((1 if x == w else 0) + m ** 2 * Sp[x, w]) * Z[w] for w in range(n))
res['Owx'] = (abs(lhs - rhs), abs(lhs - rhs - pred), abs(lhs))
# ---------------- (Oe2x)  G_xy G_y'x f ----------------
y, yp = 3, 4
lhs = G(H, x, y) * G(H, yp, x) * fH
rhs = (m * (1 if x == y else 0) * G(H, yp, x) * fH + m ** 3 * Sp[x, y] * G(H, yp, y) * fH
       + m * sum(S[x, a] * Gc(H, a, a) for a in range(n)) * lhs
       + m ** 3 * sum(Sp[x, a] * S[a, b] * Gc(H, b, b) * G(H, a, y) * G(H, yp, a) * fH for a in range(n) for b in range(n))
       + m * Gc(H, x, x) * sum(S[x, a] * G(H, a, y) * G(H, yp, a) * fH for a in range(n))
       + m ** 3 * sum(Sp[x, a] * S[a, b] * Gc(H, a, a) * G(H, b, y) * G(H, yp, b) * fH for a in range(n) for b in range(n))
       - m * sum(S[x, a] * G(H, a, y) * G(H, yp, x) * dH(f, H, a, x) for a in range(n))
       - m ** 3 * sum(Sp[x, a] * S[a, b] * G(H, b, y) * G(H, yp, a) * dH(f, H, b, a) for a in range(n) for b in range(n)))
Z = [stein_defect(lambda a, Hm, w=w: G(Hm, a, y) * G(Hm, yp, w) * f(Hm), H, w) for w in range(n)]
pred = -m * sum(((1 if x == w else 0) + m ** 2 * Sp[x, w]) * Z[w] for w in range(n))
res['Oe2x'] = (abs(lhs - rhs), abs(lhs - rhs - pred), abs(lhs))
# ---------------- (Oe1x) k1+1 blue out-edges, k2 red out-edges, k3 blue in-edges, k4 red in-edges ----------------
for (k1, k2, k3, k4, tag) in [(0, 0, 0, 0, 'k=(1,0,0,0)'), (1, 2, 1, 1, 'k=(2,2,1,1)'), (2, 1, 2, 2, 'k=(3,1,2,2)')]:
    ys = [rng.integers(0, n) for _ in range(k1 + 1)]
    ysp = [rng.integers(0, n) for _ in range(k2)]
    ws = [rng.integers(0, n) for _ in range(k3)]
    wsp = [rng.integers(0, n) for _ in range(k4)]

    def rest(Hm, skip=None):
        """G' = G/G_{x y_1}  (with optionally one factor removed: ('yp',i) or ('w',i))"""
        val = 1.0
        for i in range(1, k1 + 1): val *= G(Hm, x, ys[i])
        for i in range(k2):
            if skip != ('yp', i): val *= Gb(Hm, x, ysp[i])
        for i in range(k3):
            if skip != ('w', i): val *= G(Hm, ws[i], x)
        for i in range(k4): val *= Gb(Hm, wsp[i], x)
        return val * f(Hm)
    calG = lambda Hm: G(Hm, x, ys[0]) * rest(Hm)
    lhs = calG(H)
    rhs = m * (1 if x == ys[0] else 0) * rest(H)
    rhs += m * sum(S[x, a] * Gc(H, a, a) for a in range(n)) * calG(H)
    for i in range(k2):
        sm = sum(S[x, a] * G(H, a, ys[0]) * Gb(H, a, ysp[i]) for a in range(n))
        rhs += (m * np.conj(m)) * sm * rest(H, ('yp', i)) + m * Gcb(H, x, x) * sm * rest(H, ('yp', i))
    for i in range(k3):
        sm = sum(S[x, a] * G(H, a, ys[0]) * G(H, ws[i], a) for a in range(n))
        rhs += m ** 2 * sm * rest(H, ('w', i)) + m * Gc(H, x, x) * sm * rest(H, ('w', i))
    rhs += k1 * m * sum(S[x, a] * G(H, x, a) * G(H, a, ys[0]) for a in range(n)) * rest(H)
    rhs += k4 * m * sum(S[x, a] * Gb(H, a, x) * G(H, a, ys[0]) for a in range(n)) * rest(H)
    # derivative of f only: rest = (explicit) * f  -> (explicit) * d f
    expl = lambda Hm: rest(Hm) / f(Hm)
    rhs -= m * sum(S[x, a] * G(H, a, ys[0]) * expl(H) * dH(f, H, a, x) for a in range(n))
    Zx = stein_defect(lambda a, Hm: G(Hm, a, ys[0]) * rest(Hm), H, x)
    pred = -m * Zx
    res['Oe1x ' + tag] = (abs(lhs - rhs), abs(lhs - rhs - pred), abs(lhs))
print("pathwise check (n=%d, E=%.2f, t=%.2f, |m|=%.6f; central difference h=%.0e):" % (n, E, t, abs(m), h))
print("%-14s %-14s %-24s %s" % ("identity", "|LHS-RHS|", "|LHS-RHS-(-m*defect)|", "|LHS|"))
for k, (a, b, c) in res.items():
    print("%-14s %-14.3e %-24.3e %.3e" % (k, a, b, c))
print("max residual of the defect identity: %.2e" % max(b for (a, b, c) in res.values()))
```

### t2040_expansions_all.sh

```python
#!/bin/zsh
# T2040: the pathwise check of the three expansion pins at four settings (seed E t h); last line of each run and the table of the first
cd "$(dirname "$0")"
python3 t2040_expansions.py 7 0.7 0.55 1e-5
for a in "13 0.0 0.001 1e-5" "17 -1.2 0.9 1e-5"; do echo "== seed E t h = $a"; python3 t2040_expansions.py ${=a} | tail -1; done
echo "== seed E t h = 11 1.9 0.999 1e-7 (t -> 1: |LHS| up to 1e10; relative residual |LHS-RHS-(-m*defect)|/|LHS| per identity)"
python3 t2040_expansions.py 11 1.9 0.999 1e-7 | awk 'NR>=3 && NF>=4 {printf "%-18s rel=%.2e\n",$1" "$2, $(NF-1)/$NF}' | head -5
```

### t2040_endflow.py

```python
#!/usr/bin/env python3
"""T2040: the end of the flow at the preflight data (merged sz0, z_n = 1/2 + i N^{-4/5}): 1 - t0 against lam^2/L^2 and lam^2/L^d.
t0 = |msc z|^2, E = -2 Re msc z/|msc z|, and (merged zt_im_lemma28) (1-t0) Im mE(E) = sqrt(t0) Im z, Im mE(E) = sqrt(4-E^2)/2."""
import cmath, math
def msc(z):
    r = (-z + cmath.sqrt(z * z - 4)) / 2
    return r if r.imag > 0 else (-z - cmath.sqrt(z * z - 4)) / 2
print("%3s %11s %11s %13s %13s | %-34s %s" % ("n", "N", "1-t0", "lam^2/L^2", "lam^2/L^3", "strict regime 1-t0 > lam^2/L^2", "1-t0 >= lam^2/L^3 (LWterm_EXP index set)"))
for n in (0, 1, 2, 5, 10, 50, 500):
    L = 4 * (n + 1); W = (2 * (n + 1)) ** 5; lam = 1.0 / (2 * (n + 1)) ** 6
    N = float(W * L) ** 3
    z = complex(0.5, N ** (-0.8))
    m = msc(z); t0 = abs(m) ** 2
    E = -2 * m.real / abs(m)
    om = math.sqrt(t0) * z.imag / (math.sqrt(4 - E * E) / 2)
    print("%3d %11.3e %11.4e %13.4e %13.4e | %-34s %s" % (n, N, om, lam ** 2 / L ** 2, lam ** 2 / L ** 3, om > lam ** 2 / L ** 2, om >= lam ** 2 / L ** 3))
print("t = 1/16 (tInst): the strict regime lam^2/L^2 < 15/16 holds for every n (lam <= 1/64; Lean: strict_all).")
```

### t2040_names.py

```python
#!/usr/bin/env python3
"""T2040: `#check` every Mathlib/Lean name the probe uses (one line each, type cut at 90 characters); deprecated names reported."""
import subprocess, re, sys
WT = '/Users/junyin/Lean_proof/RBM3D-wt/T2040'
names = """Fin.consEquiv Fintype.sum_prod_type Fintype.sum_unique Finset.sum_comm Finset.sum_mul_sum Finset.mul_sum Finset.sum_mul
Finset.sum_congr Finset.sum_add_distrib Finset.sum_sub_distrib Finset.sum_neg_distrib star_sum star_mul' MeasureTheory.integral_sub
MeasureTheory.integral_add MeasureTheory.integral_const_mul MeasureTheory.integral_finsetSum MeasureTheory.Integrable.add
MeasureTheory.Integrable.const_mul pow_add_pow_le pow_le_pow_left₀ Real.rpow_natCast Real.rpow_mul Real.rpow_add Real.rpow_neg_one
Real.rpow_two Real.rpow_le_rpow Real.rpow_le_rpow_of_exponent_le Real.one_le_rpow Real.sqrt_eq_rpow Real.le_sqrt_of_sq_le one_le_div
inv_le_comm₀ le_inv_comm₀ inv_anti₀ inv_le_one_of_one_le₀ inv_lt_one_of_one_lt₀ div_le_one div_le_self ite_eq_left ite_eq_right
ENNReal.one_le_ofReal ENNReal.ofReal_le_ofReal ENNReal.ofReal_add MeasureTheory.measure_union_le MeasureTheory.measure_mono
MeasureTheory.measure_univ Fintype.card_subtype_le Fintype.card_prod abs_norm MvPolynomial.eval MvPolynomial.X Matrix.single deriv
Nat.floor_zero Even.pow_nonneg not_lt add_pos_of_nonneg_of_pos Finset.sum_ite_eq lt_of_lt_of_le mul_lt_mul_of_pos_left
Finset.card_filter_le Equiv.sum_comp""".split()
src = open('/Users/junyin/Lean_proof/RBM3D-wt/T2040/RBM3D/Probe/T2040Graphs.lean', encoding='utf-8').read()
names_all = names
names = [n for n in names_all if n.split('.')[-1] in src]
print('names listed %d, of which occurring in the probe text %d' % (len(names_all), len(names)))
deprec = "if_pos if_neg if_true if_false Set.mem_setOf_eq MeasureTheory.integral_finset_sum ite_cond_eq_true push_neg".split()
lines = ['import RBM3D.Probe.T2040Graphs', 'set_option linter.deprecated true']
for n in names + deprec:
    lines.append('#check @%s' % n)
open('/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2040/names.lean', 'w').write('\n'.join(lines) + '\n')
r = subprocess.run(['lake', 'env', 'lean', '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2040/names.lean'], cwd=WT, capture_output=True, text=True)
out = (r.stdout + r.stderr)
dep = {}
for m in re.finditer(r"warning: [^\n]*?`([^`]+)` has been deprecated: Use `([^`]+)` instead", out):
    dep[m.group(1)] = m.group(2)
errs = [l for l in out.split('\n') if 'error' in l]
okn = [n for n in names if n not in dep and n.split('.')[-1] not in dep]
if '--lines' in sys.argv:
    ents = []
    for l in out.split('\n'):
        if l.startswith('@'):
            ents.append(l)
        elif l.startswith('  ') and ents:
            ents[-1] += ' ' + l.strip()
    print('one line per name (`#check @name`, type cut at 130 characters): %d lines' % len(ents))
    for e in ents:
        print(e[:130] + (' ...' if len(e) > 130 else ''))
print('#check elaborates, not deprecated: %d of %d names requested:' % (len(okn), len(names)))
import textwrap
print(textwrap.fill(' '.join(okn), 110, initial_indent='  ', subsequent_indent='  '))
print('requested names that are deprecated: %s' % (', '.join('%s -> %s' % (k, v) for k, v in dep.items() if k in names) or 'none'))
print('deprecated names checked and avoided (replacement used): ' + ', '.join('%s -> %s' % (k, v) for k, v in dep.items() if k in deprec))
print('error lines: %d (the tactic `push_neg`, which is not a term; replaced by `push Not`)' % len(errs))
```

### t2040_props.py

```python
#!/usr/bin/env python3
"""T2040: Prop-valued definitions of the probe, with namespace (line, qualified name)."""
import re, sys
L = open(sys.argv[1], encoding='utf-8').read().split('\n')
ns = []
for i, l in enumerate(L, 1):
    m = re.match(r'^namespace\s+(\S+)', l)
    if m:
        ns.append(m.group(1)); continue
    m = re.match(r'^end\s+(\S+)', l)
    if m and ns and ns[-1] == m.group(1):
        ns.pop(); continue
    m = re.match(r'^(?:private )?def\s+(\S+)', l)
    if m:
        head = '\n'.join(L[i - 1:i + 12]).split(':=')[0]
        if re.search(r':\s*Prop\s*$', head.strip()) or re.search(r'\)\s*:\s*Prop\b', head):
            print('%d %s' % (i, '.'.join(ns + [m.group(1)])))
```

### t2040_clash.py

```python
#!/usr/bin/env python3
"""T2040: name-clash grep.  For every declaration of the probe (list produced by a Lean metaprogram, t2040/probe_names.txt) look for a
declaration with the same last component in the sources of the main worktree (RBM3D/**/*.lean, read only); report the full-name matches."""
import re, subprocess, sys, os
S = '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2040/'
MAIN = '/Users/junyin/Lean_proof/RBM3D'
names = [l.strip() for l in open(S + 'probe_names.txt') if l.strip()]
lasts = sorted({n.split('.')[-1] for n in names})
files = subprocess.run(['git', '-C', MAIN, '--no-optional-locks', 'ls-files', 'RBM3D'], capture_output=True, text=True).stdout.split()
files = [f for f in files if f.endswith('.lean') and not f.startswith('RBM3D/Probe/')]
head = subprocess.run(['git', '-C', MAIN, '--no-optional-locks', 'log', '-1', '--format=%h'], capture_output=True, text=True).stdout.strip()
decl = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom)\s+(\S+)')
hits = {}
nfiles = 0
for f in files:
    try:
        txt = open(os.path.join(MAIN, f), encoding='utf-8').read().split('\n')
    except Exception:
        continue
    nfiles += 1
    for i, l in enumerate(txt, 1):
        m = decl.match(l)
        if m:
            last = m.group(1).split('.')[-1]
            if last in lasts:
                hits.setdefault(last, []).append('%s:%d %s' % (f, i, m.group(1)))
print('probe declarations: %d, distinct last components: %d; main worktree HEAD %s, tracked non-probe .lean files scanned: %d' % (len(names), len(lasts), head, nfiles))
print('last components that are also declared (any namespace) in main: %d' % len(hits))
for k in sorted(hits):
    print('  %s -> %s' % (k, '; '.join(hits[k][:3])))
```

### t2040_pins.py

```python
#!/usr/bin/env python3
"""T2040 item 3: one line per pin, extracted from the probe by script: name, probe lines, paper statement, and the statement text with the
common flow prefix replaced by <FLOW> (whitespace collapsed; the order of the binders is kept).
usage: t2040_pins.py PROBE [width]"""
import re, sys
fn = sys.argv[1]
W = int(sys.argv[2]) if len(sys.argv) > 2 else 600
L = open(fn, encoding='utf-8').read().split('\n')
START = re.compile(r'^(?:private )?(?:noncomputable )?(theorem|def|abbrev|structure|inductive|instance|lemma)\s+([^\s({\[:]+)')
BOUND = re.compile(r'^(/--|/-!|theorem |def |abbrev |structure |inductive |instance |lemma |end |namespace |section|open |variable|set_option|noncomputable)')


def decl(name):
    for i, l in enumerate(L):
        m = START.match(l)
        if m and m.group(2).split('.')[-1] == name:
            j = i + 1
            while j < len(L) and not (BOUND.match(L[j]) and L[j].strip()):
                j += 1
            body = [x for x in L[i:j]]
            while body and not body[-1].strip():
                body.pop()
            return i + 1, i + len(body), ' '.join(x.strip() for x in body)
    return None


FLOW = ('3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → '
        '∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →')
PINS = [('LWterm', '3_5:385-404 (eq:LW_conclusion)'), ('LWtermB', '3_5:393-397 (eq:LW_conclusion2)'), ('LWtermExp', '3_5:406-415 (eq:LW_conclusion_exp)'),
        ('LWtermExpS', 'regime 1-t > g^2/L^2 of 3_5:406'), ('LWtermExpN', 'regime 1-t <= g^2/L^2 of 3_5:406 (7_8:20)'),
        ('LWtermEXP', '6:83-88 (eq:ExpLWn=2)'), ('LWMoment', '7_8:72-77 (eq:LW_moment)'), ('LWMomentExp', '7_8:78-83 (eq:LW_moment_exp)'),
        ('LWAnpKey', '7_8:960-985 (adsuu_orig)'), ('LWAnpKeyGh', '7_8:1041-1077 (adsuu22)'), ('LWAnp', '7_8:933-939 (eq:bddGamma_aux)'),
        ('LWReduceB', '7_8:20-91 reduction (eq:directG1..recoltermwt)'), ('LWReduceT', '7_8:20-58 reduction (eq:directG2..recoltermwt2)'),
        ('LWweightExp', '7_8:294-306 (Owx)'), ('LWedgeExp', '7_8:309-330 (Oe1x)'), ('LWggExp', '7_8:334-349 (Oe2x)')]
print('| pin | probe lines | paper | binders and hypotheses (<FLOW> = %s) | conclusion (the scale of every `Prec` is N = sz.size n) |' % FLOW)
for nm, paper in PINS:
    r = decl(nm)
    if r is None:
        print('| %s | NOT FOUND |' % nm); continue
    a, b, txt = r
    k = txt.find(':= ')
    stm = txt[k + 3:] if k >= 0 else txt
    stm = re.sub(r'\s+', ' ', stm).replace(FLOW, '<FLOW>')
    cut = stm.rfind(' Prec sz')
    if cut < 0:
        cut = stm.find(' ∫ ω,')
    head, concl = (stm[:cut], stm[cut + 1:]) if cut >= 0 else (stm, '')
    wh, wc = (W, W) if W < 400 else (W, W)
    if len(head) > 300:
        head = head[:300] + ' ...'
    if len(concl) > W:
        concl = concl[:W] + ' ...'
    print('| `%s` | %d-%d | %s | %s | %s |' % (nm, a, b, paper, head, concl))
```

### t2040_route.py

```python
#!/usr/bin/env python3
"""T2040 item 4: route and risk per pin and per Appendix B lemma.  The line counts are the items of t2040_size.py (inventory spans x measured
rate x omitted-step multiplier); `sketched` = the sketch markers of the inventory (t2040_inv.py sketch), with TeX line numbers."""
import io, contextlib, sys
sys.path.insert(0, '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad')
buf = io.StringIO()
with contextlib.redirect_stdout(buf):
    import t2040_size as Z
R = {r[0]: r[2] for r in Z.arows}
RB = {r[0]: r[2] for r in Z.brows}
L = lambda *ids: '+'.join('%s %d' % (i, R.get(i, RB.get(i))) for i in ids)
rows = [
    ('lem:LWterm, lem: EWGn2_N (3_5:385-415; 7_8:1-104)',
     'Markov on LW_moment(_exp) [compiled: lwterm_of_moment, lwtermexpS_of_momentexp]; reduction by (eq:directG1/2), (eq:recolterm*), (eq:recoltermwt*) from merged lem_GbEXP pins and (LW_assm); regimes',
     'all routine (union bound, Markov, (eq:Psi) shift compiled); deterministic T~ vs [sT]^2 comparison',
     L('LW-01', 'LW-15', 'LW-16'), 'low-medium', '7_8:20 "an immediate consequence" (regime 1-t <= g^2/L^2: sub-sequence transfer, T2040k)'),
    ('lem:LW_moment, lem:LW_moment_exp, assembly (7_8:716-720, 943-950, 1600-1630)',
     'dist(a,b) <= (log W)^{3/2} (_exp: <= (log W)^{3/2} l_t, from LW_moment) by the max-bound (eq:boundfxyGinf) [Ward + Cauchy-Schwarz]; else expand E‖f‖^p to graphs, lvl1, GtoAG, lem:Anp; _exp: cut f = f^{>l} + f^{<=l}; expectation upgrade ‖f‖ <~ N eta^-3',
     'routine: far/near, upgrade, Markov', L('LW-02'), 'medium', '7_8:944 "standard"'),
    ('ssl, Oe14, T eq0: (Owx),(Oe1x),(Oe2x) (7_8:294-349; cited yang2021 Lemmas 3.5, 3.10, 3.14: no proof in the paper)',
     'row Stein identity + resummation S+ = S(1-m^2 S)^-1 [(Owx) proved pathwise: owx_defect_identity; (Oe1x),(Oe2x) checked numerically b.7]; E Z_w = 0 (merged GaussIBP, owed S1-19); derivative of resolvent polynomials (merged hasDerivAt_inverse_apply); each term a graph with counter changes ((a)(i))',
     'routine algebra; size of the statements (nine and eight terms, k1..k4 generic)', L('LW-04', 'LW-05', 'LW-06', 'LW-07'), 'medium', 'whole proofs cited'),
    ('lvl1 lemma, strat_local, deflvl1 (7_8:367-399; B:135-157)',
     'iterate (Owx), (Oe1x), (Oe2x) with the dot-def normal form until locally standard; discard graphs of size <= W^-D (claim:size)',
     'graph-combinatorial: termination (ord, size), normal-graph normal form', L('LW-08', 'LW-03', 'LW-09'), 'high', 'strategy only (B:135-157); claim:size 7_8:264 has no proof; lvl1 cited (Lemma 3.22)'),
    ('lem:localregular (7_8:786-821; proof B:172-278)',
     '(1) trivial, (2) the number of internal molecules never increases (B:173-177); (3)-(5): paths persist through every expansion (B:178-199, three alternatives); (6) ord >= 3p - n_dv: weight cases (i)-(vi) B:209-263 [arithmetic merged: Graph/ScalingOrder, Graph/Model], edge and GG expansions B:275',
     'merged: the arithmetic of (i)-(vi); to do: Case.Rel on records, edge/GG case analysis', L('LW-10') + ' (-393 merged)', 'high', 'B:263 "not hard to see"; B:275 "straightforward", "direct check", "omit the details"'),
    ('GtoAG, def_auxgraph, def: BM2 (7_8:863-932)',
     'block-level auxiliary graph of a locally standard graph; ord(G) - ord(G_aux) >= 0 via (eq:MolVW) (nV(M_i) <= nW(M_i)+1)',
     'graph-combinatorial (molecules, paths)', L('LW-11'), 'medium', '7_8:915 "as in"; claim:xi 7_8:884 has no proof'),
    ('lem:Anp_key_gh, lem:Anp_key, lem:Anp (7_8:933-1599)',
     'Anp from Anp_key [compiled: lwanp_of_key]; Anp_key = gh version (7_8:1025 "easy corollary"); gh by induction on internal vertices, ending-edge types A1/A2/B1/B2, cases (I)-(IV), Cauchy-Schwarz with (eq:Gbyxi3), change of summation order',
     'Cauchy-Schwarz sums, order bookkeeping; graph-combinatorial: nested graphs, spanning paths', L('LW-12'), 'high (largest item)', '7_8:1142, 1231 "easy to see"; 1154-1413 "without loss of generality"; 1232-1254 "similar"; 1400, 1529 "as in"'),
    ('lem:LW_moment_exp_far, _near (7_8:1615-1791)',
     'far (f^{>l}, internal vertices in D_{>l}): every path has an ending edge longer than l, T(l) as an A2/ghost edge, rest "exactly the same argument" as Anp_key_gh; near (f^{<=l}): edges bounded by T_t(.^l), internal sums in a fixed order with the key estimate from claim:TTk (merged EKTTk), lem:propT', 'graph-combinatorial (reuse of LW-12); sums with the exponential tail', L('LW-13'), 'high-medium',
     '7_8:1632, 1647 "similar", "standard"; 1642, 1773 "omit"; 1781 "easy to see"'),
    ('lem:LWterm_EXP (B:7-121; 6:83-88)',
     'GG expansion at G_xa G_ay: I1..I4 (J1..J4 "exactly the same" with prop:ThfadC_short); I42 = 5-loop -> graphs G_xy, GtoAG, ord >= 4.1_{x=y}+5.1_{x!=y} from (eq:GGraisesord), cases (1)-(4)',
     'Ward, averaged local law, K-loop bounds (merged); ord of every term of (Oe2x)', L('LW-14'), 'medium-high', 'B:34, 49, 105 "exactly the same"; B:102 "easy to see"; B:118 "omit" (BA part)'),
    ('remark:3p (B:280)', 'refinement ord >= 3p (not needed): not planned', '-', '0', 'none', 'remark only'),
    ('block Anderson graph layer (B:286-523)',
     'Psi-dotted and M-dotted edges, atoms, scalingBA; lanlw, lem_lweight, GGGamma (cited yang2024Del B.9-B.11); BA lvl1; atomic reduction + auxiliary graph; LWterm_EXP with GGGamma',
     'graph-combinatorial; same shape as LW-03..LW-14', L('BA-L1', 'BA-L2', 'BA-L3', 'BA-L4'), 'high', 'B:409 sketch; B:118 "omit"; "carries over verbatim"'),
]
print('| item (paper) | route | routine / graph-combinatorial | est. lines central (size model) | risk | only sketched in the paper |')
print('|---|---|---|---|---|---|')
for r in rows:
    print('| ' + ' | '.join(r) + ' |')
```

### t2040_split.py

```python
#!/usr/bin/env python3
"""T2040 item 7: split of gate LW into tickets (new files under RBM3D/Graph), computed from the size model of t2040_size.py
(item lines from the item-1 inventory), with the credit for the merged arithmetic of lem_scalingorder (Graph/ScalingOrder.lean, Graph/Model.lean)."""
import io, contextlib, sys
sys.path.insert(0, '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad')
buf = io.StringIO()
with contextlib.redirect_stdout(buf):
    import t2040_size as Z
R = {r[0]: r[1:] for r in Z.arows}
RB = {r[0]: r[1:] for r in Z.brows}
credit = Z.nlines('RBM3D/Graph/ScalingOrder.lean') + Z.nlines('RBM3D/Graph/Model.lean')
# id: (new file under RBM3D/Graph, statements, needs, role)   -- order = dependency order
META = [
    ('LW-03', 'Vocab', 'def_graph1 ValG def_poly defnlvl0 dot-def (def scaling, order); records, value, counters, molecules', 'MD-1..3, merged Counters/ord', 'prover-hard'),
    ('LW-04', 'SteinBridge', 'E Z_w = 0 for resolvent polynomials; derivative calculus; graph derivative', 'S1-19 GaussIBP (T2031)', 'prover-hard'),
    ('LW-05', 'ExpOwx', 'ssl (Owx) as a graph operation, counters per term', 'LW-03, 04', 'prover'),
    ('LW-06', 'ExpOe1x', 'Oe14 (Oe1x), nine terms, k1..k4 generic', 'LW-03, 04', 'prover-hard'),
    ('LW-07', 'ExpOe2x', 'T eq0 (Oe2x), eight terms', 'LW-03, 04', 'prover'),
    ('LW-09', 'SizeClaim', 'claim:size (Gamma << size), S^pm decay (estSpm-W), scalemole', 'LW-03', 'prover-hard'),
    ('LW-08', 'Lvl1', 'deflvl1, strat_local, lvl1 lemma (termination, Err <= W^-D)', 'LW-03, 05-07, 09', 'prover-max'),
    ('LW-10', 'LocalRegular', 'lem:localregular (1)-(6): paths, molecules, ord through (Owx),(Oe1x),(Oe2x)', 'LW-03, 05-08', 'prover-max'),
    ('LW-11', 'AuxGraph', 'def: BM2, def_auxgraph, GtoAG', 'LW-10', 'prover-hard'),
    ('LW-12', 'Nested, AnpKeyGh, Anp', 'lem:Anp_key_gh (cases I-IV), lem:Anp_key, lem:Anp (NGraph)', 'LW-11', 'prover-max'),
    ('LW-13', 'MomentExp', 'lem:LW_moment_exp_far, _near (uses merged EKTTk)', 'LW-12', 'prover-max'),
    ('LW-14', 'LWtermEXP', 'lem:LWterm_EXP (B:7-121): I1..I4, J-terms, (eq:GGraisesord), cases (1)-(4)', 'LW-03, 07, 09, 11', 'prover-max'),
    ('LW-15', 'LWDet', '(eq:Psi) for the B class, W^-d T~ ~ [sT]^2, Psi_t window (T2040a)', 'merged Defs/Tail', 'prover'),
    ('LW-02', 'LWMoment', 'lem:LW_moment, lem:LW_moment_exp (far/near split, expectation upgrade)', 'LW-08, 10-13', 'prover-hard'),
    ('LW-16', 'LWRegime', 'regime transfer of lem: EWGn2_N (T2040k)', 'LW-01', 'prover-hard'),
    ('LW-01', 'LWterm', 'lem:LWterm, lem: EWGn2_N from the moments (reduction (eq:directG), recolterm)', 'LW-02, 15, 16, ST-D2', 'prover-hard'),
]
print('credit: merged Graph/ScalingOrder.lean + Graph/Model.lean = %d lines (arithmetic and exhaustiveness of the cases (i)-(vi), B:209-263) subtracted from LW-10' % credit)
print('| id | file RBM3D/Graph/... | statements | needs | role | lines lo/central/hi | tickets (central) |')
tot = [0, 0, 0]
for (iid, f, st, needs, role) in META:
    lo, ce, hi = R[iid]
    if iid == 'LW-10':
        lo, ce, hi = max(lo - credit, 0), max(ce - credit, 0), max(hi - credit, 0)
    tot[0] += lo; tot[1] += ce; tot[2] += hi
    print('| %s | %s | %s | %s | %s | %d/%d/%d | %.1f |' % (iid, f, st, needs, role, lo, ce, hi, ce / 1000))
print('| total | | | | | %d/%d/%d | %.1f |' % (tot[0], tot[1], tot[2], tot[1] / 1000))
print('tickets of ~1000 lines: lo %.0f, central %.0f, hi %.0f; band 600-1500 lines per ticket: central %.0f..%.0f' % (tot[0] / 1000, tot[1] / 1000, tot[2] / 1000, tot[1] / 1500, tot[1] / 600))
b = [sum(RB[k][i] for k in RB) for i in range(3)]
print('block Anderson additions (BA-L1..L4: Psi- and M-dotted edges, atoms, scalingBA; lanlw, lem_lweight, GGGamma; BA lvl1/Anp; BA LWterm_EXP): %.1f tickets (lo %.1f, hi %.1f)' % (b[1] / 1000, b[0] / 1000, b[2] / 1000))
print('LW + BA: central %.0f tickets (lo %.0f, hi %.0f); DECISIONS 9 O2 thresholds 25/40/50: exceeds 50: %s' % ((tot[1] + b[1]) / 1000, (tot[0] + b[0]) / 1000, (tot[2] + b[2]) / 1000, 'yes' if (tot[2] + b[2]) / 1000 > 50 else 'no (neither central, lo nor hi)'))
keep = lambda ids: [sum(R[i][j] for i in ids) for j in range(3)]
r1 = keep([i for i in R if i not in ('LW-04', 'LW-05', 'LW-06', 'LW-07', 'LW-08')]); r1[1] -= credit; r1[0] -= credit; r1[2] -= credit
r2 = keep(['LW-03', 'LW-04', 'LW-07', 'LW-09', 'LW-11', 'LW-14', 'LW-15'])
print('reduced route R1 (expansions ssl, Oe14, T eq0 and lvl1 lemma = Lemmas 3.5, 3.10, 3.14, 3.22 of yang2021 as external inputs; needs a change of DECISIONS 5): %.0f tickets (lo %.0f, hi %.0f); gives up LW-04..08' % (r1[1] / 1000, r1[0] / 1000, r1[2] / 1000))
print('reduced route R2 (Step 6 only: LW-03,04,07,09,11,14,15): %.0f tickets (lo %.0f, hi %.0f); gives up lem:LWterm and lem: EWGn2_N (Step 2), which the main theorems need: not a route by itself' % (r2[1] / 1000, r2[0] / 1000, r2[2] / 1000))
```

### t2040_compare.py

```python
#!/usr/bin/env python3
"""T2040 item 2: the comparison of the two candidate representations; the code-line counts are read from t2040_stats.py (docstrings, comments, blank lines excluded)."""
import re, subprocess, sys
S = '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad'
out = subprocess.run('python3 t2040_stats.py %s' % sys.argv[1], shell=True, cwd=S, capture_output=True, text=True).stdout
num = lambda pat: int(re.search(pat + r'.*code lines (\d+)', out).group(1))
oA = num(r'\(Owx\) for the smallest graph, candidate A'); oB = num(r'\(Owx\) for the smallest graph, candidate B')
vA = num(r'candidate A \(record'); vB = num(r'candidate B \(syntax')
print('| criterion | A: record `LGraph E I` (probe §1, §3, §4) | B: binder terms `GTerm V` (§2, §4.3) |')
print('| core vocabulary, code lines | %d (LData, edges, value, counters, molecules) | %d (terms, eval; no counters, no molecules) |' % (vA, vB))
print('| (Owx) on `Ǧ_xx`: three terms + value theorem, code lines | %d (incl. the `ord` theorem; unfolds `Fin n → ι` sums) | %d (structural `eval`; same `owx_defect_identity`) |' % (oA, oB))
print('| counters, molecules, ord; expansion at x | from the record by `decide`: p2Graph (6,2,4,2), ord 2; figGraph (8,4,6,2), ord 4; filter `solid` by endpoint | not visible: a flattening to a record is needed; the factors at x sit in a product tree under `Option` shifts |')
print('| lem:Anp nested bound | `NGraph p q` (edges, p paths), `IsNested` decided on `figAux`; pin `LWAnpKey` | paths are no property of the term: the record is needed again |')
```

### t2040_expansions_summary.py

```python
#!/usr/bin/env python3
"""T2040: one line per setting for the pathwise check of the three expansion pins (t2040_expansions.py: five identities per setting: (Owx), (Oe2x),
(Oe1x) with k=(1,0,0,0), (2,2,1,1), (3,1,2,2)); LHS-RHS is the difference of the two sides, the residual is LHS-RHS-(-m*defect) with the Stein
defect of the row identity; relative = residual/|LHS|."""
import subprocess, re, sys
S = '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad'
row = re.compile(r'^(Owx|Oe2x|Oe1x k=\(\d,\d,\d,\d\))\s+(\S+)\s+(\S+)\s+(\S+)\s*$')
print('%-34s | %-24s | %-24s | %-10s | %s' % ('setting (seed E t h)', '|LHS| range', '|LHS-RHS| range', 'max resid.', 'max relative resid.'))
for args in ('7 0.7 0.55 1e-5', '13 0.0 0.001 1e-5', '17 -1.2 0.9 1e-5', '11 1.9 0.999 1e-7'):
    out = subprocess.run('python3 t2040_expansions.py ' + args, shell=True, cwd=S, capture_output=True, text=True, executable='/bin/zsh').stdout
    rs = [row.match(l) for l in out.split('\n')]
    rs = [(float(m.group(2)), float(m.group(3)), float(m.group(4))) for m in rs if m]
    assert len(rs) == 5, (args, out)
    lhs = [r[2] for r in rs]; diff = [r[0] for r in rs]; res = [r[1] for r in rs]
    print('%-34s | %.1e .. %.1e        | %.1e .. %.1e        | %.1e    | %.1e' % (args, min(lhs), max(lhs), min(diff), max(diff), max(res), max(r[1] / r[2] for r in rs)))
```

### t2040_endflow_short.sh

```python
#!/bin/zsh
# T2040: the end-of-flow table, header and the rows n = 0, 5, 500, and the last line
cd "$(dirname "$0")"
python3 t2040_endflow.py | awk 'NR==1 || $1=="0" || $1=="5" || $1=="500" || /^t = 1\/16/'
```

### t2040_prep.py

```python
#!/usr/bin/env python3
"""T2040: generate the helper Lean files that depend on the list of declarations of the probe module
(t2040/probe_names.txt, written by names_list.lean): ax_report.lean (#print axioms of the named theorems and instances),
clash_final.lean (every probe declaration against the environment of `import RBM3D`)."""
S = '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2040/'
names = [l.strip() for l in open(S + 'probe_names.txt') if l.strip()]
named = set('''owx_defect_identity owx_smallest owx_second owx_smallest_E owxT_smallest p2Graph_val p2Graph_val_eq p2Graph_counters p2Graph_ord
figGraph_counters figGraph_ord figGraph_val figAux_nested figAux_ord figAux_ghostOK lwterm_of_moment lwtermexpS_of_momentexp
lwtermexp_of_regimes lwanp_of_key stochDomAt_det stochDomAt_of_split stochDomAt_congr_right shift fxyTerm_eval owx_ord owx_ord_H classB'''.split())
sel = [n for n in names if n.split('.')[-1].startswith('inst_') or n.split('.')[-1] in named]


def q(n):
    return '.'.join(n.split('.'))


open(S + 'ax_report.lean', 'w').write('import RBM3D.Probe.T2040Graphs\n' + '\n'.join('#print axioms %s' % q(n) for n in sel) + '\n')


def qn(n):
    return '`' + '.'.join('«%s»' % p if not p.replace('_', '').replace("'", '').isalnum() else p for p in n.split('.'))


lines = ['import RBM3D', 'import Lean', 'open Lean Elab Command', 'run_cmd do', '  let env ← getEnv',
         '  let names : List Name := [' + ', '.join(qn(n) for n in names) + ']', '  let mut clash : Array Name := #[]',
         '  for n in names do', '    if env.contains n then clash := clash.push n',
         '  logInfo m!"probe declarations checked against `import RBM3D` (the library without the probe): {names.length}; already declared there: {clash.size} {clash}"']
open(S + 'clash_final.lean', 'w').write('\n'.join(lines) + '\n')
print('names %d, axiom lines %d' % (len(names), len(sel)))
```

### t2040_report.py

```python
#!/usr/bin/env python3
"""T2040: assemble docs/reports/T2040-prove.md = section (a) of the preflight (lines 1-83 of the file as it stood, copied unchanged) + (a'), (b), (c), (d).
Every script block is run here and pasted verbatim (indented, optionally cut to a width or joined in pairs by `paste`); the narrative strings below are
wrapped at 190 characters and counted."""
import subprocess, sys, re, textwrap
S = '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad'
WT = '/Users/junyin/Lean_proof/RBM3D-wt/T2040'
MAIN = '/Users/junyin/Lean_proof/RBM3D'
REP = MAIN + '/docs/reports/T2040-prove.md'
PROBE = WT + '/RBM3D/Probe/T2040Graphs.lean'
orig = open(S + '/t2040/orig_prove.md', encoding='utf-8').read().split('\n')
assert orig[0].startswith('Prover model:')
A = orig[:83]
assert A[-1].startswith('- Instance uses L=3')


def sh(cmd, cwd=S):
    r = subprocess.run(cmd, shell=True, cwd=cwd, capture_output=True, text=True, executable='/bin/zsh')
    return (r.stdout + r.stderr).rstrip('\n')


out, narr = [], []


def N(*paras, width=190):
    for p in paras:
        for l in textwrap.wrap(p, width=width, break_long_words=False, break_on_hyphens=False):
            out.append(l)
            narr.append(l)


def H(l):
    out.append(l)


def C(shown, cmd, cwd=S, filt=None, cut=None):
    """script block: the displayed command, then the verbatim output (optionally filtered by line / cut to a width)"""
    out.append('    $ ' + shown)
    txt = sh(cmd, cwd)
    ls = txt.split('\n') if txt else []
    if filt:
        ls = [l for l in ls if filt(l)]
    for l in ls:
        out.append('    ' + (l[:cut] + ' ...' if cut and len(l) > cut else l))


HEAD = sh('git log -1 --format=%h', WT)

# ----------------------------------------------------------------------------------------------------------------------- (a')
H('## (a′) Preflight corrections — %s' % sh('date -u'))
N('No correction changes a verdict; (a) is untouched. (1) T2040b ((Oe1x) unchecked in (a)) is closed by b.7. (2) (eq:Psi) in (a)(i) has C1=1, C2=1/2; the paper needs C1, C2>1 (3_5:390): larger pairs hold, '
  'the probe uses (2,2). (3) (a)(ii) tests G(z) (row sums 1); the pins are the flow versions (S_t=tS, z_t=E+(1-t)m): `owx_defect_identity` holds for row sum s, b.7 checks all three.')

# ----------------------------------------------------------------------------------------------------------------------- (b)
H('## (b) Script output and design — probe `RBM3D/Probe/T2040Graphs.lean` on branch `t/T2040` (commit %s); inventory, scripts: `docs/reports/T2040-inventory.md`' % HEAD)
N('**Size headline (item 7, b.9): gate LW = 27 tickets of ~1000 lines (21-39); with the block Anderson additions 33 (27-48). No estimate exceeds 50 (DECISIONS §9 O2): no first-line flag; both central '
  'values lie in 25-40.**')
H('### b.1 Build and hygiene')
C('date -u; cd $WT && git log -1 --format="%h %an <%ae>"; git diff --name-only $(git merge-base HEAD main) HEAD', 'date -u; git log -1 --format="%h %an <%ae>" ; git diff --name-only $(git merge-base HEAD main) HEAD', WT)
C('lake build RBM3D.Probe.T2040Graphs 2>&1 | tail -1; time lake env lean RBM3D/Probe/T2040Graphs.lean; echo exit=$?', '(lake build RBM3D.Probe.T2040Graphs 2>&1 | tail -1; time lake env lean RBM3D/Probe/T2040Graphs.lean; echo exit=$?) 2>&1 | grep -v "^$" | grep -v "^user\\|^sys"', WT)
C('lake build RBM3D 2>&1 | tail -1   # the library at the branch base (the probe is not imported); module axioms; forbidden tokens', 'lake build RBM3D 2>&1 | tail -1; lake env lean %s/t2040/axioms.lean; echo "forbidden tokens: $(grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Probe/T2040Graphs.lean); lines: $(wc -l < RBM3D/Probe/T2040Graphs.lean)"' % S, WT)
C('lake env lean $S/t2040/ax_main.lean   # four targets; all 55 theorems and instances: inventory block 19', 'lake env lean %s/t2040/ax_main.lean 2>&1 | sed "s/depends on axioms:/:/"' % S, WT, filt=lambda l: 'lwterm_of_moment' in l or 'owx_defect' in l)

H('### b.2 Inventory of 7_8:1-1791 and B:1-525 (item 1; all 38 statements with spans, citations and proof location, 86 equations, dependency tree, sketch markers: inventory blocks 1-7)')
C('cd $S && python3 t2040_inv.py classes | cut -c1-400   # statements by class (where the proof is), label (file:span)', 'python3 t2040_inv.py classes | tail -n +2 | cut -c1-400', S)
C('python3 t2040_inv.py layers | paste -d"|" - - | cut -c1-330   # dependency graph from lem:LWterm, lem: EWGn2_N, lem:LWterm_EXP (longest path), two layers per line', 'python3 t2040_inv.py layers | tail -n +2 | grep -v "^statements outside" | grep -v "^$" | paste -d"|" - - | cut -c1-330', S)

H('### b.3 Vocabulary (item 2)')
C('python3 t2040_compare.py $PROBE   # code lines from t2040_stats.py: docstrings, comments, blank lines excluded', 'python3 t2040_compare.py %s' % PROBE, S)
N('Reused (compiled): `Counters`, `ord`. Named, not applied: `hasDerivAt_inverse_apply` (the law `dH` implements), `Case`/`classify` (arithmetic and exhaustiveness of cases (i)-(vi); their counter relations on a '
  'record: LW-10). Choice: A. B has the shorter value proofs, but the statements of §7 and App. B (molecules, ord, paths, nested bound) are about the edge multiset, which only A exposes; B can be a printing '
  'syntax over A. Both graphs: values unfolded by `simp` (`p2Graph_val`, `p2Graph_val_eq`: = |f_xy|², `figGraph_val`).')

H('### b.4 Pins (item 3): one line per pin, extracted from the probe by script')
C('python3 t2040_pins.py $PROBE 430', 'python3 t2040_pins.py %s 430' % PROBE, S)
N('Conventions: constants (κ ε 𝔡, p, ε₀ C₁ C₂ C₃ Cc, the graph) precede the sequence, `∃ c` follows them and precedes (𝔠, sz, z, t); every `≺` is `Prec` at N=`sz.size n`; |a-b| is `zdistInf`; regime index '
  'sets are subtypes; the expansions are identities of expectations over `PF` at fixed (L,W) with S=tS, S⁺=S(1-m²S)⁻¹, z_t.')

H('### b.5 Skeleton and the proved expansion (item 5)')
C('python3 t2040_extract.py $PROBE lwterm_of_moment lwtermexpS_of_momentexp lwtermexp_of_regimes lwanp_of_key owx_smallest | grep -v "^-- probe" | cut -c1-190', 'python3 t2040_extract.py %s lwterm_of_moment lwtermexpS_of_momentexp lwtermexp_of_regimes lwanp_of_key owx_smallest | grep -v "^-- probe" | grep -v "^$" | cut -c1-190' % PROBE, S)
N('Proved: LWterm from LW_moment + `LWReduceB` (merged Markov bridge; `stochDomAt_det`, `LWPsiAll.shift` new); EWGn2_N from the strict regime + `LWtermExpN` (`stochDomAt_of_split`); Anp from Anp_key; '
  '(Owx) with the Stein defect: Ǧ_xx (`owx_smallest`), Ǧ_xx G_xy (`owx_second`), in expectation. Left: `LWMoment(Exp)`, `LWReduceB/T`, `LWtermExpN`, `LWInteg`, E Z_w=0.')

H('### b.6 Route and risk (item 4): `t2040_route.py` (lines = size model, b.9; markers = inventory block 5)')
C('python3 t2040_route.py', 'python3 t2040_route.py | tail -n +3 | grep -v "remark:3p"', S)

H('### b.7 Extreme inputs (t → 1, L large; each pin tried at one)')
C('python3 t2040_expansions_summary.py   # (Owx),(Oe1x),(Oe2x), pathwise identity with the Stein defect, generic f; full output: inventory block 10', 'python3 t2040_expansions_summary.py', S)
C('./t2040_endflow_short.sh   # t = t0 = lemT z_n, n = 0, 5, 500 (L_n = 4, 24, 2004)', './t2040_endflow_short.sh', S)
N('t → 1: at t=0.999 the identities hold to 2.1e-8 relative (h=1e-7). At t=t₀ the deterministic hypotheses of LWterm, LWtermExp, LWMoment, LWAnpKey, LWtermEXP are discharged by the same data (`inst_*_endT`); '
  'the strict regime of LW_moment_exp is empty at the listed n (its instance sits at t=1/16, `strict_all`), so EWGn2_N at t₀ rests on the other regime `LWtermExpN` (T2040k). L large: L_500=2004; the (a) '
  'ratio W^-d T/(sT)² falls from 2.4815 (L=3) to 2.0010 (L=1000).')

H('### b.8 Block Anderson reuse (item 6)')
N('lem:LWterm, lem: EWGn2_N stay valid for BA (7_8:1994). Outside LW, gate BA changes the model (H=V+λΨ, M not scalar: `zztE_BA`, `lem:propM`, `lem_GbEXP_BA`), Step 2 (`eq:MG_conclusion3_BA`) and the Step 5/6 '
  'inputs. In the graph layer (B:286-523) it adds Ψ- and M-dotted edges, atoms with `ord=nS+2(nW-nA)` (the merged `ord` serves both), the expansions `lanlw`, `lem_lweight`, `GGGamma` (cited, yang2024Del '
  'B.9-B.11: proved internally, DECISIONS §5), BA lvl1, the atomic reduction with ζ (`eq:Gbyxi2_BA`), `lem:LWterm_EXP` with GGGamma (B:118, omitted). Reused: `LData` (M is already a general matrix), Anp* '
  '(B:497 "carries over verbatim"), (eq:Psi) lemmas, the regime lemma, the skeleton. Cost: 6.4 tickets (b.9).')

H('### b.9 Split table and size (item 7): `t2040_split.py`; size model `t2040_size.py` = inventory span chars × 151 lines/kchar (measured on merged proofs) × omitted-step multiplier (inventory block 8)')
C('python3 t2040_split.py', 'python3 t2040_split.py', S, filt=lambda l: not l.startswith('| id |'))
N('No reduced route within DECISIONS §5 was found: Steps 2 and 6 consume lem:LWterm, lem: EWGn2_N, lem:LWterm_EXP with sharp exponents (the figure graph has ord = 2p exactly), so R2 is not a route; R1 needs '
  'Jun to authorize Lemmas 3.5, 3.10, 3.14, 3.22 of yang2021.')

H('### b.10 Compiled nonempty instances at d = 3 (item 8)')
C('grep -ho "^\\(theorem\\|def\\) inst_[A-Za-z_0-9]*" $PROBE | sed "s/^[a-z]* //" | sort | tr "\\n" " "', 'grep -ho "^\\(theorem\\|def\\) inst_[A-Za-z_0-9]*" %s | sed "s/^[a-z]* //" | sort | tr "\\n" " "; echo' % PROBE, S)
C('python3 t2040_extract.py $PROBE inst_LWterm inst_owx_smallest | grep -v "^-- probe" | cut -c1-170', 'python3 t2040_extract.py %s inst_LWterm inst_owx_smallest | grep -v "^-- probe" | grep -v "^$" | cut -c1-170' % PROBE, S)
N('Data: merged `sz0, z0, flow_z0` (d=3, L_n=4(n+1), W_n=(2(n+1))^5, λ_n=(2(n+1))^-6, κ=ε=𝔡=1/10, 𝔠=1/6), t=1/16 and t=t₀, `Ψ≡W^-1` or the B-class (c₀=1, K≡1, `classB`); graph pins on `figAux`; '
  'expansions at (d,L,W,g,E,t)=(3,3,2,1,0,1/2); `owx_*` at m=i, z=0, s=1, S=J/2, S⁺=J/4. Every deterministic hypothesis is discharged; left: the stochastic premises (`LWInit`, `LWLoop2`, `LWLoopExp`, '
  '`LWXi`, local laws), E Z_w=0, and pins used as hypotheses. Limit check of (LW_assm) at these data: 𝓛^{(2)} ≈ W^-d Θ_ab ≤ W^-d/(1-t) < W^-2 = Ψ² (Θ=(1-tS^B)⁻¹ with row sums 1/(1-t), (a) Part B).')

H('### b.11 Registry (DECISIONS §16, §20): the pre-check `import RBM3D` + probe + `#assert_rbm_axioms` (inventory block 20); name clashes; ports')
C('lake env lean $S/t2040/precheck.lean 2>&1 | grep "RBM\\." | sed "s/RBM.Gauss.Sizes.//; s/[],]//g" | tr "\\n" " "   # premises it finds unregistered', 'lake env lean %s/t2040/precheck.lean 2>&1 | grep "RBM\\." | sed "s/RBM.Gauss.Sizes.//; s/[],]//g" | tr "\\n" " "; echo' % S, WT)
N('Proposed — owed: `LWMoment`, `LWMomentExp`, `LWReduceB/T`, `LWtermExpN`, `LWtermB`, `LWtermEXP`, `LWAnpKey(Gh)`, `LWInteg`, the three expansion Props (not borrowed: DECISIONS §5), `STLocalEntry`, `LWAvgLaw`; '
  'structural: `LWInit`, `LWLoop2`, `LWLoopExp`, `LWXi` (lemma assumptions, proved by the consumer T2039), `LWWindow`, `LWClass`, `LWPsiRel`, `LWPsiAll`, `LWAssm(Exp)`, `NGraph.{IsNested,NoGhost,GhostOK}`. '
  'None borrowed.')
C('lake env lean $S/t2040/clash_final.lean; cd $S && python3 t2040_clash.py | head -2; grep -c "RBM1D\\|RBM2D" $PROBE', 'lake env lean %s/t2040/clash_final.lean 2>&1 | cut -c1-200; cd %s && python3 t2040_clash.py | head -2; grep -c "RBM1D\\|RBM2D" %s' % (S, S, PROBE), WT)
N('No port: nothing copied from RBM1D/RBM2D (grep count 0; no sister project has this layer): no diff-stat. `const`, `mul`, `sum` are `GTerm` constructors.')

# ----------------------------------------------------------------------------------------------------------------------- (c)
H('## (c) Verified Mathlib names (62 `#check`ed, none deprecated; one line each with its type: inventory block 18)')
C('python3 t2040_names.py | tail -n +2 | (join the indented name lines) | fold -s -w 190', "python3 t2040_names.py | tail -n +2 | awk 'BEGIN{n=\"\"} /^  /{n=n\" \"$0; next} {if(n!=\"\"){print n; n=\"\"} print} END{if(n!=\"\")print n}' | fold -s -w 190", S)

# ----------------------------------------------------------------------------------------------------------------------- (d)
H('## (d) Open issues and paper-delta candidates')
N('T2040a (a): 7_8:65 takes Ψ_t=(W^-d B_{t,0})^{1/2}, violating W^-d/2 ≤ Ψ_t when B_{t,0}<1 (t=1/2, ĝ=1, L=3: 0.7407): pinned with a window hypothesis and a constant C₃. T2040c (a): L=3 odd, the paper defines Z_L^d for even L (1_2:269); the pins take 3 ≤ L. T2040d: f is a resolvent polynomial (`MvPolynomial` in the entries of G, G*), the paper: "differentiable function of G" (7_8:295, 310, 335); T2040i: ∂_{h_{αx}} = complex derivative along E_{αx}, undefined in §7; T2040e: the expansions for G_t (7_8:291) are pinned with S_t=tS, S⁺_t=S_t(1-m²S_t)⁻¹, z_t=E+(1-t)m. T2040f: lem: EWGn2_N says "any t∈[0,1)" (3_5:407), pinned for 0 ≤ t ≤ `lemT z`; T2040g: lem:Anp_key\'s Ψ_t is Ψ_t(0) (7_8:949); T2040h: "w.l.o.g. Ψ_t decreasing" (3_5:389) is a hypothesis (the sup-envelope keeps (eq:Psi); not proved). T2040j: `∃ c` precedes the sequence (c depends on p or the graph and the constants only); the Markov step needs `LWInteg` (true: bounded, measurable). T2040k: lem: EWGn2_N for 1-t ≤ ĝ²/L² is "an immediate consequence" (7_8:20): needs a class from (LW_assm_exp), W^-d T~ ≍ B for r ≤ L and a sub-sequence transfer; pinned as `LWtermExpN`. T2040l: lem:Anp (7_8:933) is about Γ^aux of a locally standard graph; `LWAnp` is the nested form (`lwanp_of_key`), def_auxgraph and GtoAG are LW-11; T2040m: Anp_key is "an easy corollary" of the ghost version (7_8:1025); claim:size (7_8:264), claim:xi (7_8:884) have no proof in the paper (LW-09, LW-11). T2040n: the range "(Gt_bound_flow)-(Eq:Gdecay_flow)" of lem:LWterm_EXP (6:83) is read as `STLocalEntry`, `LWAvgLaw`, `STLmax`, `STLK`, `STDecay` at time t ((Eq:Gdecay_w) is implied by (Eq:Gdecay_flow)). T2040o: the reductions 7_8:20-91 (`LWReduceB/T`) and the regime split (`LWtermExpS/N`) are not numbered statements in the paper; `LWedgeExp` writes k₁+1 for the paper\'s k₁ ≥ 1. Open: (Oe1x), (Oe2x) checked numerically, not proved; `LWMomentExp` has no instance at t=t₀; the size model uses one rate (151 lines/kchar, two merged proof sets, 20.6 kchar) and fixed judgments for 9 items (9.4k of 27.0k lines).')

body = A + out
open(REP, 'w', encoding='utf-8').write('\n'.join(body) + '\n')
print('lines total: %d (a: %d, rest: %d), narrative lines: %d' % (len(body), len(A), len(out), len(narr)))
```

