/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWExpCert

/-!
# LW-14e-1: the kernel certificate for `LWG5Graph false false` (chunks)

Root terms `0..8` of `(k, s) = (false, false)` in one kernel run each; root terms `9`, `10`: one theorem per depth-1 node
(`ch_FF_i_j_l`), assembled by `goodB_succ_of`.  Namespace `RBM.Graph.LWCert`.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option maxRecDepth 1000000

noncomputable section

namespace RBM.Graph.LWCert

/-! ### `s = false` -/

theorem root_FF_0 : goodB 3 (rootAt false false 0) = true := by
  have h : (cands (rootAt false false 0).g).length = 2 ∧ ∀ j < 2, kidsOk (rootAt false false 0) j = true ∧ (kids (rootAt false false 0) j).length = 0 := by decide +kernel
  apply goodB_succ_of 2 _ 2 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have := (h.2 j hj).2
  omega
theorem root_FF_1 : goodB 3 (rootAt false false 1) = true := by
  have h : (cands (rootAt false false 1).g).length = 2 ∧ ∀ j < 2, kidsOk (rootAt false false 1) j = true ∧ (kids (rootAt false false 1) j).length = 0 := by decide +kernel
  apply goodB_succ_of 2 _ 2 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have := (h.2 j hj).2
  omega
theorem root_FF_2 : goodB 3 (rootAt false false 2) = true := by
  have h : (cands (rootAt false false 2).g).length = 2 ∧ ∀ j < 2, kidsOk (rootAt false false 2) j = true ∧ (kids (rootAt false false 2) j).length = 0 := by decide +kernel
  apply goodB_succ_of 2 _ 2 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have := (h.2 j hj).2
  omega
theorem root_FF_3 : goodB 3 (rootAt false false 3) = true := by
  have h : (cands (rootAt false false 3).g).length = 2 ∧ ∀ j < 2, kidsOk (rootAt false false 3) j = true ∧ (kids (rootAt false false 3) j).length = 0 := by decide +kernel
  apply goodB_succ_of 2 _ 2 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have := (h.2 j hj).2
  omega
theorem root_FF_4 : goodB 3 (rootAt false false 4) = true := by
  have h : (cands (rootAt false false 4).g).length = 2 ∧ ∀ j < 2, kidsOk (rootAt false false 4) j = true ∧ (kids (rootAt false false 4) j).length = 0 := by decide +kernel
  apply goodB_succ_of 2 _ 2 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have := (h.2 j hj).2
  omega
theorem root_FF_5 : goodB 3 (rootAt false false 5) = true := by
  have h : (cands (rootAt false false 5).g).length = 2 ∧ ∀ j < 2, kidsOk (rootAt false false 5) j = true ∧ (kids (rootAt false false 5) j).length = 0 := by decide +kernel
  apply goodB_succ_of 2 _ 2 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have := (h.2 j hj).2
  omega
theorem root_FF_6 : goodB 3 (rootAt false false 6) = true := by
  have h : (cands (rootAt false false 6).g).length = 2 ∧ ∀ j < 2, kidsOk (rootAt false false 6) j = true ∧ (kids (rootAt false false 6) j).length = 0 := by decide +kernel
  apply goodB_succ_of 2 _ 2 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have := (h.2 j hj).2
  omega
theorem root_FF_7 : goodB 3 (rootAt false false 7) = true := by
  have h : (cands (rootAt false false 7).g).length = 2 ∧ ∀ j < 2, kidsOk (rootAt false false 7) j = true ∧ (kids (rootAt false false 7) j).length = 0 := by decide +kernel
  apply goodB_succ_of 2 _ 2 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have := (h.2 j hj).2
  omega
theorem root_FF_8 : goodB 3 (rootAt false false 8) = true := by
  have h : (cands (rootAt false false 8).g).length = 3 ∧ ∀ j < 3, kidsOk (rootAt false false 8) j = true ∧ (kids (rootAt false false 8) j).length = 0 := by decide +kernel
  apply goodB_succ_of 2 _ 3 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have := (h.2 j hj).2
  omega
theorem ch_FF_9_0_0 : goodB 2 (kid (rootAt false false 9) 0 0) = true := by decide +kernel
theorem ch_FF_9_0_1 : goodB 2 (kid (rootAt false false 9) 0 1) = true := by decide +kernel
theorem ch_FF_9_0_2 : goodB 2 (kid (rootAt false false 9) 0 2) = true := by decide +kernel
theorem ch_FF_9_0_3 : goodB 2 (kid (rootAt false false 9) 0 3) = true := by decide +kernel
theorem ch_FF_9_0_4 : goodB 2 (kid (rootAt false false 9) 0 4) = true := by decide +kernel
theorem ch_FF_9_0_5 : goodB 2 (kid (rootAt false false 9) 0 5) = true := by decide +kernel
theorem ch_FF_9_0_6 : goodB 2 (kid (rootAt false false 9) 0 6) = true := by decide +kernel
theorem ch_FF_9_0_7 : goodB 2 (kid (rootAt false false 9) 0 7) = true := by decide +kernel
theorem ch_FF_9_0_8 : goodB 2 (kid (rootAt false false 9) 0 8) = true := by decide +kernel
theorem ch_FF_9_0_9 : goodB 2 (kid (rootAt false false 9) 0 9) = true := by decide +kernel
theorem ch_FF_9_0_10 : goodB 2 (kid (rootAt false false 9) 0 10) = true := by decide +kernel
theorem ch_FF_9_0_11 : goodB 2 (kid (rootAt false false 9) 0 11) = true := by decide +kernel
theorem chs_FF_9_0 (l : ℕ) (hl : l < 12) : goodB 2 (kid (rootAt false false 9) 0 l) = true := by
  match l, hl with
  | 0, _ => exact ch_FF_9_0_0
  | 1, _ => exact ch_FF_9_0_1
  | 2, _ => exact ch_FF_9_0_2
  | 3, _ => exact ch_FF_9_0_3
  | 4, _ => exact ch_FF_9_0_4
  | 5, _ => exact ch_FF_9_0_5
  | 6, _ => exact ch_FF_9_0_6
  | 7, _ => exact ch_FF_9_0_7
  | 8, _ => exact ch_FF_9_0_8
  | 9, _ => exact ch_FF_9_0_9
  | 10, _ => exact ch_FF_9_0_10
  | 11, _ => exact ch_FF_9_0_11
  | n + 12, h => omega
theorem ch_FF_9_1_0 : goodB 2 (kid (rootAt false false 9) 1 0) = true := by decide +kernel
theorem ch_FF_9_1_1 : goodB 2 (kid (rootAt false false 9) 1 1) = true := by decide +kernel
theorem ch_FF_9_1_2 : goodB 2 (kid (rootAt false false 9) 1 2) = true := by decide +kernel
theorem ch_FF_9_1_3 : goodB 2 (kid (rootAt false false 9) 1 3) = true := by decide +kernel
theorem ch_FF_9_1_4 : goodB 2 (kid (rootAt false false 9) 1 4) = true := by decide +kernel
theorem ch_FF_9_1_5 : goodB 2 (kid (rootAt false false 9) 1 5) = true := by decide +kernel
theorem ch_FF_9_1_6 : goodB 2 (kid (rootAt false false 9) 1 6) = true := by decide +kernel
theorem ch_FF_9_1_7 : goodB 2 (kid (rootAt false false 9) 1 7) = true := by decide +kernel
theorem ch_FF_9_1_8 : goodB 2 (kid (rootAt false false 9) 1 8) = true := by decide +kernel
theorem ch_FF_9_1_9 : goodB 2 (kid (rootAt false false 9) 1 9) = true := by decide +kernel
theorem ch_FF_9_1_10 : goodB 2 (kid (rootAt false false 9) 1 10) = true := by decide +kernel
theorem ch_FF_9_1_11 : goodB 2 (kid (rootAt false false 9) 1 11) = true := by decide +kernel
theorem chs_FF_9_1 (l : ℕ) (hl : l < 12) : goodB 2 (kid (rootAt false false 9) 1 l) = true := by
  match l, hl with
  | 0, _ => exact ch_FF_9_1_0
  | 1, _ => exact ch_FF_9_1_1
  | 2, _ => exact ch_FF_9_1_2
  | 3, _ => exact ch_FF_9_1_3
  | 4, _ => exact ch_FF_9_1_4
  | 5, _ => exact ch_FF_9_1_5
  | 6, _ => exact ch_FF_9_1_6
  | 7, _ => exact ch_FF_9_1_7
  | 8, _ => exact ch_FF_9_1_8
  | 9, _ => exact ch_FF_9_1_9
  | 10, _ => exact ch_FF_9_1_10
  | 11, _ => exact ch_FF_9_1_11
  | n + 12, h => omega
theorem ch_FF_9_2_0 : goodB 2 (kid (rootAt false false 9) 2 0) = true := by decide +kernel
theorem ch_FF_9_2_1 : goodB 2 (kid (rootAt false false 9) 2 1) = true := by decide +kernel
theorem ch_FF_9_2_2 : goodB 2 (kid (rootAt false false 9) 2 2) = true := by decide +kernel
theorem ch_FF_9_2_3 : goodB 2 (kid (rootAt false false 9) 2 3) = true := by decide +kernel
theorem ch_FF_9_2_4 : goodB 2 (kid (rootAt false false 9) 2 4) = true := by decide +kernel
theorem ch_FF_9_2_5 : goodB 2 (kid (rootAt false false 9) 2 5) = true := by decide +kernel
theorem ch_FF_9_2_6 : goodB 2 (kid (rootAt false false 9) 2 6) = true := by decide +kernel
theorem ch_FF_9_2_7 : goodB 2 (kid (rootAt false false 9) 2 7) = true := by decide +kernel
theorem ch_FF_9_2_8 : goodB 2 (kid (rootAt false false 9) 2 8) = true := by decide +kernel
theorem ch_FF_9_2_9 : goodB 2 (kid (rootAt false false 9) 2 9) = true := by decide +kernel
theorem ch_FF_9_2_10 : goodB 2 (kid (rootAt false false 9) 2 10) = true := by decide +kernel
theorem ch_FF_9_2_11 : goodB 2 (kid (rootAt false false 9) 2 11) = true := by decide +kernel
theorem chs_FF_9_2 (l : ℕ) (hl : l < 12) : goodB 2 (kid (rootAt false false 9) 2 l) = true := by
  match l, hl with
  | 0, _ => exact ch_FF_9_2_0
  | 1, _ => exact ch_FF_9_2_1
  | 2, _ => exact ch_FF_9_2_2
  | 3, _ => exact ch_FF_9_2_3
  | 4, _ => exact ch_FF_9_2_4
  | 5, _ => exact ch_FF_9_2_5
  | 6, _ => exact ch_FF_9_2_6
  | 7, _ => exact ch_FF_9_2_7
  | 8, _ => exact ch_FF_9_2_8
  | 9, _ => exact ch_FF_9_2_9
  | 10, _ => exact ch_FF_9_2_10
  | 11, _ => exact ch_FF_9_2_11
  | n + 12, h => omega
theorem root_FF_9 : goodB 3 (rootAt false false 9) = true := by
  have h : (cands (rootAt false false 9).g).length = 3 ∧ ∀ j < 3, kidsOk (rootAt false false 9) j = true ∧ (kids (rootAt false false 9) j).length = 12 := by decide +kernel
  apply goodB_succ_of 2 _ 3 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have hl' : l < 12 := (h.2 j hj).2 ▸ hl
  match j, hj with
  | 0, _ => exact chs_FF_9_0 l hl'
  | 1, _ => exact chs_FF_9_1 l hl'
  | 2, _ => exact chs_FF_9_2 l hl'
  | n + 3, h => omega
theorem ch_FF_10_0_0 : goodB 2 (kid (rootAt false false 10) 0 0) = true := by decide +kernel
theorem ch_FF_10_0_1 : goodB 2 (kid (rootAt false false 10) 0 1) = true := by decide +kernel
theorem ch_FF_10_0_2 : goodB 2 (kid (rootAt false false 10) 0 2) = true := by decide +kernel
theorem ch_FF_10_0_3 : goodB 2 (kid (rootAt false false 10) 0 3) = true := by decide +kernel
theorem ch_FF_10_0_4 : goodB 2 (kid (rootAt false false 10) 0 4) = true := by decide +kernel
theorem ch_FF_10_0_5 : goodB 2 (kid (rootAt false false 10) 0 5) = true := by decide +kernel
theorem ch_FF_10_0_6 : goodB 2 (kid (rootAt false false 10) 0 6) = true := by decide +kernel
theorem ch_FF_10_0_7 : goodB 2 (kid (rootAt false false 10) 0 7) = true := by decide +kernel
theorem ch_FF_10_0_8 : goodB 2 (kid (rootAt false false 10) 0 8) = true := by decide +kernel
theorem ch_FF_10_0_9 : goodB 2 (kid (rootAt false false 10) 0 9) = true := by decide +kernel
theorem ch_FF_10_0_10 : goodB 2 (kid (rootAt false false 10) 0 10) = true := by decide +kernel
theorem ch_FF_10_0_11 : goodB 2 (kid (rootAt false false 10) 0 11) = true := by decide +kernel
theorem ch_FF_10_0_12 : goodB 2 (kid (rootAt false false 10) 0 12) = true := by decide +kernel
theorem ch_FF_10_0_13 : goodB 2 (kid (rootAt false false 10) 0 13) = true := by decide +kernel
theorem chs_FF_10_0 (l : ℕ) (hl : l < 14) : goodB 2 (kid (rootAt false false 10) 0 l) = true := by
  match l, hl with
  | 0, _ => exact ch_FF_10_0_0
  | 1, _ => exact ch_FF_10_0_1
  | 2, _ => exact ch_FF_10_0_2
  | 3, _ => exact ch_FF_10_0_3
  | 4, _ => exact ch_FF_10_0_4
  | 5, _ => exact ch_FF_10_0_5
  | 6, _ => exact ch_FF_10_0_6
  | 7, _ => exact ch_FF_10_0_7
  | 8, _ => exact ch_FF_10_0_8
  | 9, _ => exact ch_FF_10_0_9
  | 10, _ => exact ch_FF_10_0_10
  | 11, _ => exact ch_FF_10_0_11
  | 12, _ => exact ch_FF_10_0_12
  | 13, _ => exact ch_FF_10_0_13
  | n + 14, h => omega
theorem ch_FF_10_1_0 : goodB 2 (kid (rootAt false false 10) 1 0) = true := by decide +kernel
theorem ch_FF_10_1_1 : goodB 2 (kid (rootAt false false 10) 1 1) = true := by decide +kernel
theorem ch_FF_10_1_2 : goodB 2 (kid (rootAt false false 10) 1 2) = true := by decide +kernel
theorem ch_FF_10_1_3 : goodB 2 (kid (rootAt false false 10) 1 3) = true := by decide +kernel
theorem ch_FF_10_1_4 : goodB 2 (kid (rootAt false false 10) 1 4) = true := by decide +kernel
theorem ch_FF_10_1_5 : goodB 2 (kid (rootAt false false 10) 1 5) = true := by decide +kernel
theorem ch_FF_10_1_6 : goodB 2 (kid (rootAt false false 10) 1 6) = true := by decide +kernel
theorem ch_FF_10_1_7 : goodB 2 (kid (rootAt false false 10) 1 7) = true := by decide +kernel
theorem ch_FF_10_1_8 : goodB 2 (kid (rootAt false false 10) 1 8) = true := by decide +kernel
theorem ch_FF_10_1_9 : goodB 2 (kid (rootAt false false 10) 1 9) = true := by decide +kernel
theorem ch_FF_10_1_10 : goodB 2 (kid (rootAt false false 10) 1 10) = true := by decide +kernel
theorem ch_FF_10_1_11 : goodB 2 (kid (rootAt false false 10) 1 11) = true := by decide +kernel
theorem ch_FF_10_1_12 : goodB 2 (kid (rootAt false false 10) 1 12) = true := by decide +kernel
theorem ch_FF_10_1_13 : goodB 2 (kid (rootAt false false 10) 1 13) = true := by decide +kernel
theorem chs_FF_10_1 (l : ℕ) (hl : l < 14) : goodB 2 (kid (rootAt false false 10) 1 l) = true := by
  match l, hl with
  | 0, _ => exact ch_FF_10_1_0
  | 1, _ => exact ch_FF_10_1_1
  | 2, _ => exact ch_FF_10_1_2
  | 3, _ => exact ch_FF_10_1_3
  | 4, _ => exact ch_FF_10_1_4
  | 5, _ => exact ch_FF_10_1_5
  | 6, _ => exact ch_FF_10_1_6
  | 7, _ => exact ch_FF_10_1_7
  | 8, _ => exact ch_FF_10_1_8
  | 9, _ => exact ch_FF_10_1_9
  | 10, _ => exact ch_FF_10_1_10
  | 11, _ => exact ch_FF_10_1_11
  | 12, _ => exact ch_FF_10_1_12
  | 13, _ => exact ch_FF_10_1_13
  | n + 14, h => omega
theorem ch_FF_10_2_0 : goodB 2 (kid (rootAt false false 10) 2 0) = true := by decide +kernel
theorem ch_FF_10_2_1 : goodB 2 (kid (rootAt false false 10) 2 1) = true := by decide +kernel
theorem ch_FF_10_2_2 : goodB 2 (kid (rootAt false false 10) 2 2) = true := by decide +kernel
theorem ch_FF_10_2_3 : goodB 2 (kid (rootAt false false 10) 2 3) = true := by decide +kernel
theorem ch_FF_10_2_4 : goodB 2 (kid (rootAt false false 10) 2 4) = true := by decide +kernel
theorem ch_FF_10_2_5 : goodB 2 (kid (rootAt false false 10) 2 5) = true := by decide +kernel
theorem ch_FF_10_2_6 : goodB 2 (kid (rootAt false false 10) 2 6) = true := by decide +kernel
theorem ch_FF_10_2_7 : goodB 2 (kid (rootAt false false 10) 2 7) = true := by decide +kernel
theorem ch_FF_10_2_8 : goodB 2 (kid (rootAt false false 10) 2 8) = true := by decide +kernel
theorem ch_FF_10_2_9 : goodB 2 (kid (rootAt false false 10) 2 9) = true := by decide +kernel
theorem ch_FF_10_2_10 : goodB 2 (kid (rootAt false false 10) 2 10) = true := by decide +kernel
theorem ch_FF_10_2_11 : goodB 2 (kid (rootAt false false 10) 2 11) = true := by decide +kernel
theorem ch_FF_10_2_12 : goodB 2 (kid (rootAt false false 10) 2 12) = true := by decide +kernel
theorem ch_FF_10_2_13 : goodB 2 (kid (rootAt false false 10) 2 13) = true := by decide +kernel
theorem chs_FF_10_2 (l : ℕ) (hl : l < 14) : goodB 2 (kid (rootAt false false 10) 2 l) = true := by
  match l, hl with
  | 0, _ => exact ch_FF_10_2_0
  | 1, _ => exact ch_FF_10_2_1
  | 2, _ => exact ch_FF_10_2_2
  | 3, _ => exact ch_FF_10_2_3
  | 4, _ => exact ch_FF_10_2_4
  | 5, _ => exact ch_FF_10_2_5
  | 6, _ => exact ch_FF_10_2_6
  | 7, _ => exact ch_FF_10_2_7
  | 8, _ => exact ch_FF_10_2_8
  | 9, _ => exact ch_FF_10_2_9
  | 10, _ => exact ch_FF_10_2_10
  | 11, _ => exact ch_FF_10_2_11
  | 12, _ => exact ch_FF_10_2_12
  | 13, _ => exact ch_FF_10_2_13
  | n + 14, h => omega
theorem root_FF_10 : goodB 3 (rootAt false false 10) = true := by
  have h : (cands (rootAt false false 10).g).length = 3 ∧ ∀ j < 3, kidsOk (rootAt false false 10) j = true ∧ (kids (rootAt false false 10) j).length = 14 := by decide +kernel
  apply goodB_succ_of 2 _ 3 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have hl' : l < 14 := (h.2 j hj).2 ▸ hl
  match j, hj with
  | 0, _ => exact chs_FF_10_0 l hl'
  | 1, _ => exact chs_FF_10_1 l hl'
  | 2, _ => exact chs_FF_10_2 l hl'
  | n + 3, h => omega
theorem cert_FF : (rootInfo false false).1 = true ∧ (rootInfo false false).2.length = 11 ∧ ∀ i < 11, goodB 3 (rootAt false false i) = true := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro i hi
  match i, hi with
  | 0, _ => exact root_FF_0
  | 1, _ => exact root_FF_1
  | 2, _ => exact root_FF_2
  | 3, _ => exact root_FF_3
  | 4, _ => exact root_FF_4
  | 5, _ => exact root_FF_5
  | 6, _ => exact root_FF_6
  | 7, _ => exact root_FF_7
  | 8, _ => exact root_FF_8
  | 9, _ => exact root_FF_9
  | 10, _ => exact root_FF_10
  | n + 11, h => omega



#print axioms cert_FF

end RBM.Graph.LWCert
