/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWExpCertB
import RBM3D.Graph.LWExpCertBS0

/-!
# LW-14e-1': the kernel certificate for `LWG5Graph false true` with the corrected flag (chunks) and `cert_all'`

Same shape as `LWExpCertBS0` for `s = true`; `cert_all'` combines `cert_FF'` and `cert_FT'`.  Namespace `RBM.Graph.LWCert`.
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

/-! ### `s = true` -/

theorem root_FT_0' : goodB' 3 (rootAt' false true 0) = true := by
  have h : (cands (rootAt' false true 0).g).length = 2 ∧ ∀ j < 2, kidsOk' (rootAt' false true 0) j = true ∧ (kids' (rootAt' false true 0) j).length = 0 := by decide +kernel
  apply goodB'_succ_of 2 _ 2 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have := (h.2 j hj).2
  omega
theorem root_FT_1' : goodB' 3 (rootAt' false true 1) = true := by
  have h : (cands (rootAt' false true 1).g).length = 2 ∧ ∀ j < 2, kidsOk' (rootAt' false true 1) j = true ∧ (kids' (rootAt' false true 1) j).length = 0 := by decide +kernel
  apply goodB'_succ_of 2 _ 2 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have := (h.2 j hj).2
  omega
theorem root_FT_2' : goodB' 3 (rootAt' false true 2) = true := by
  have h : (cands (rootAt' false true 2).g).length = 2 ∧ ∀ j < 2, kidsOk' (rootAt' false true 2) j = true ∧ (kids' (rootAt' false true 2) j).length = 0 := by decide +kernel
  apply goodB'_succ_of 2 _ 2 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have := (h.2 j hj).2
  omega
theorem root_FT_3' : goodB' 3 (rootAt' false true 3) = true := by
  have h : (cands (rootAt' false true 3).g).length = 2 ∧ ∀ j < 2, kidsOk' (rootAt' false true 3) j = true ∧ (kids' (rootAt' false true 3) j).length = 0 := by decide +kernel
  apply goodB'_succ_of 2 _ 2 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have := (h.2 j hj).2
  omega
theorem root_FT_4' : goodB' 3 (rootAt' false true 4) = true := by
  have h : (cands (rootAt' false true 4).g).length = 2 ∧ ∀ j < 2, kidsOk' (rootAt' false true 4) j = true ∧ (kids' (rootAt' false true 4) j).length = 0 := by decide +kernel
  apply goodB'_succ_of 2 _ 2 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have := (h.2 j hj).2
  omega
theorem root_FT_5' : goodB' 3 (rootAt' false true 5) = true := by
  have h : (cands (rootAt' false true 5).g).length = 2 ∧ ∀ j < 2, kidsOk' (rootAt' false true 5) j = true ∧ (kids' (rootAt' false true 5) j).length = 0 := by decide +kernel
  apply goodB'_succ_of 2 _ 2 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have := (h.2 j hj).2
  omega
theorem root_FT_6' : goodB' 3 (rootAt' false true 6) = true := by
  have h : (cands (rootAt' false true 6).g).length = 2 ∧ ∀ j < 2, kidsOk' (rootAt' false true 6) j = true ∧ (kids' (rootAt' false true 6) j).length = 0 := by decide +kernel
  apply goodB'_succ_of 2 _ 2 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have := (h.2 j hj).2
  omega
theorem root_FT_7' : goodB' 3 (rootAt' false true 7) = true := by
  have h : (cands (rootAt' false true 7).g).length = 2 ∧ ∀ j < 2, kidsOk' (rootAt' false true 7) j = true ∧ (kids' (rootAt' false true 7) j).length = 0 := by decide +kernel
  apply goodB'_succ_of 2 _ 2 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have := (h.2 j hj).2
  omega
theorem root_FT_8' : goodB' 3 (rootAt' false true 8) = true := by
  have h : (cands (rootAt' false true 8).g).length = 3 ∧ ∀ j < 3, kidsOk' (rootAt' false true 8) j = true ∧ (kids' (rootAt' false true 8) j).length = 0 := by decide +kernel
  apply goodB'_succ_of 2 _ 3 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have := (h.2 j hj).2
  omega
theorem chc_FT_9_0_0_0 : kidsOk' (kid' (rootAt' false true 9) 0 0) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 0 0) 0).length = 0 := by decide +kernel
theorem chc_FT_9_0_0_1 : kidsOk' (kid' (rootAt' false true 9) 0 0) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 0 0) 1).length = 0 := by decide +kernel
theorem ch_FT_9_0_0' : goodB' 2 (kid' (rootAt' false true 9) 0 0) = true := lwcertB_two _ 2 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_0_0_0, lwcertB_nokids _ _ chc_FT_9_0_0_1])
theorem chc_FT_9_0_1_0 : kidsOk' (kid' (rootAt' false true 9) 0 1) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 0 1) 0).length = 0 := by decide +kernel
theorem chc_FT_9_0_1_1 : kidsOk' (kid' (rootAt' false true 9) 0 1) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 0 1) 1).length = 0 := by decide +kernel
theorem chc_FT_9_0_1_2 : kidsOk' (kid' (rootAt' false true 9) 0 1) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 0 1) 2).length = 0 := by decide +kernel
theorem ch_FT_9_0_1' : goodB' 2 (kid' (rootAt' false true 9) 0 1) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_0_1_0, lwcertB_nokids _ _ chc_FT_9_0_1_1, lwcertB_nokids _ _ chc_FT_9_0_1_2])
theorem chc_FT_9_0_2_0 : kidsOk' (kid' (rootAt' false true 9) 0 2) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 0 2) 0).length = 0 := by decide +kernel
theorem chc_FT_9_0_2_1 : kidsOk' (kid' (rootAt' false true 9) 0 2) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 0 2) 1).length = 0 := by decide +kernel
theorem chc_FT_9_0_2_2 : kidsOk' (kid' (rootAt' false true 9) 0 2) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 0 2) 2).length = 0 := by decide +kernel
theorem ch_FT_9_0_2' : goodB' 2 (kid' (rootAt' false true 9) 0 2) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_0_2_0, lwcertB_nokids _ _ chc_FT_9_0_2_1, lwcertB_nokids _ _ chc_FT_9_0_2_2])
theorem chc_FT_9_0_3_0 : kidsOk' (kid' (rootAt' false true 9) 0 3) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 0 3) 0).length = 0 := by decide +kernel
theorem chc_FT_9_0_3_1 : kidsOk' (kid' (rootAt' false true 9) 0 3) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 0 3) 1).length = 0 := by decide +kernel
theorem chc_FT_9_0_3_2 : kidsOk' (kid' (rootAt' false true 9) 0 3) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 0 3) 2).length = 0 := by decide +kernel
theorem ch_FT_9_0_3' : goodB' 2 (kid' (rootAt' false true 9) 0 3) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_0_3_0, lwcertB_nokids _ _ chc_FT_9_0_3_1, lwcertB_nokids _ _ chc_FT_9_0_3_2])
theorem chc_FT_9_0_4_0 : kidsOk' (kid' (rootAt' false true 9) 0 4) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 0 4) 0).length = 0 := by decide +kernel
theorem chc_FT_9_0_4_1 : kidsOk' (kid' (rootAt' false true 9) 0 4) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 0 4) 1).length = 0 := by decide +kernel
theorem chc_FT_9_0_4_2 : kidsOk' (kid' (rootAt' false true 9) 0 4) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 0 4) 2).length = 0 := by decide +kernel
theorem ch_FT_9_0_4' : goodB' 2 (kid' (rootAt' false true 9) 0 4) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_0_4_0, lwcertB_nokids _ _ chc_FT_9_0_4_1, lwcertB_nokids _ _ chc_FT_9_0_4_2])
theorem chc_FT_9_0_5_0 : kidsOk' (kid' (rootAt' false true 9) 0 5) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 0 5) 0).length = 0 := by decide +kernel
theorem chc_FT_9_0_5_1 : kidsOk' (kid' (rootAt' false true 9) 0 5) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 0 5) 1).length = 0 := by decide +kernel
theorem ch_FT_9_0_5' : goodB' 2 (kid' (rootAt' false true 9) 0 5) = true := lwcertB_two _ 2 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_0_5_0, lwcertB_nokids _ _ chc_FT_9_0_5_1])
theorem chc_FT_9_0_6_0 : kidsOk' (kid' (rootAt' false true 9) 0 6) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 0 6) 0).length = 0 := by decide +kernel
theorem chc_FT_9_0_6_1 : kidsOk' (kid' (rootAt' false true 9) 0 6) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 0 6) 1).length = 1 := by decide +kernel
theorem chd_FT_9_0_6_1_0 : goodB' 1 (kid' (kid' (rootAt' false true 9) 0 6) 1 0) = true := by decide +kernel
theorem chc_FT_9_0_6_2 : kidsOk' (kid' (rootAt' false true 9) 0 6) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 0 6) 2).length = 0 := by decide +kernel
theorem chc_FT_9_0_6_3 : kidsOk' (kid' (rootAt' false true 9) 0 6) 3 = true ∧ (kids' (kid' (rootAt' false true 9) 0 6) 3).length = 1 := by decide +kernel
theorem chd_FT_9_0_6_3_0 : goodB' 1 (kid' (kid' (rootAt' false true 9) 0 6) 3 0) = true := by decide +kernel
theorem ch_FT_9_0_6' : goodB' 2 (kid' (rootAt' false true 9) 0 6) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_0_6_0, lwcertB_onekid _ _ chc_FT_9_0_6_1 chd_FT_9_0_6_1_0, lwcertB_nokids _ _ chc_FT_9_0_6_2, lwcertB_onekid _ _ chc_FT_9_0_6_3 chd_FT_9_0_6_3_0])
theorem chc_FT_9_0_7_0 : kidsOk' (kid' (rootAt' false true 9) 0 7) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 0 7) 0).length = 0 := by decide +kernel
theorem chc_FT_9_0_7_1 : kidsOk' (kid' (rootAt' false true 9) 0 7) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 0 7) 1).length = 0 := by decide +kernel
theorem ch_FT_9_0_7' : goodB' 2 (kid' (rootAt' false true 9) 0 7) = true := lwcertB_two _ 2 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_0_7_0, lwcertB_nokids _ _ chc_FT_9_0_7_1])
theorem chc_FT_9_0_8_0 : kidsOk' (kid' (rootAt' false true 9) 0 8) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 0 8) 0).length = 0 := by decide +kernel
theorem chc_FT_9_0_8_1 : kidsOk' (kid' (rootAt' false true 9) 0 8) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 0 8) 1).length = 1 := by decide +kernel
theorem chd_FT_9_0_8_1_0 : goodB' 1 (kid' (kid' (rootAt' false true 9) 0 8) 1 0) = true := by decide +kernel
theorem chc_FT_9_0_8_2 : kidsOk' (kid' (rootAt' false true 9) 0 8) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 0 8) 2).length = 1 := by decide +kernel
theorem chd_FT_9_0_8_2_0 : goodB' 1 (kid' (kid' (rootAt' false true 9) 0 8) 2 0) = true := by decide +kernel
theorem chc_FT_9_0_8_3 : kidsOk' (kid' (rootAt' false true 9) 0 8) 3 = true ∧ (kids' (kid' (rootAt' false true 9) 0 8) 3).length = 0 := by decide +kernel
theorem ch_FT_9_0_8' : goodB' 2 (kid' (rootAt' false true 9) 0 8) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_0_8_0, lwcertB_onekid _ _ chc_FT_9_0_8_1 chd_FT_9_0_8_1_0, lwcertB_onekid _ _ chc_FT_9_0_8_2 chd_FT_9_0_8_2_0, lwcertB_nokids _ _ chc_FT_9_0_8_3])
theorem chc_FT_9_0_9_0 : kidsOk' (kid' (rootAt' false true 9) 0 9) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 0 9) 0).length = 0 := by decide +kernel
theorem chc_FT_9_0_9_1 : kidsOk' (kid' (rootAt' false true 9) 0 9) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 0 9) 1).length = 0 := by decide +kernel
theorem chc_FT_9_0_9_2 : kidsOk' (kid' (rootAt' false true 9) 0 9) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 0 9) 2).length = 1 := by decide +kernel
theorem chd_FT_9_0_9_2_0 : goodB' 1 (kid' (kid' (rootAt' false true 9) 0 9) 2 0) = true := by decide +kernel
theorem chc_FT_9_0_9_3 : kidsOk' (kid' (rootAt' false true 9) 0 9) 3 = true ∧ (kids' (kid' (rootAt' false true 9) 0 9) 3).length = 0 := by decide +kernel
theorem ch_FT_9_0_9' : goodB' 2 (kid' (rootAt' false true 9) 0 9) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_0_9_0, lwcertB_nokids _ _ chc_FT_9_0_9_1, lwcertB_onekid _ _ chc_FT_9_0_9_2 chd_FT_9_0_9_2_0, lwcertB_nokids _ _ chc_FT_9_0_9_3])
theorem chc_FT_9_0_10_0 : kidsOk' (kid' (rootAt' false true 9) 0 10) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 0 10) 0).length = 0 := by decide +kernel
theorem chc_FT_9_0_10_1 : kidsOk' (kid' (rootAt' false true 9) 0 10) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 0 10) 1).length = 0 := by decide +kernel
theorem chc_FT_9_0_10_2 : kidsOk' (kid' (rootAt' false true 9) 0 10) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 0 10) 2).length = 0 := by decide +kernel
theorem ch_FT_9_0_10' : goodB' 2 (kid' (rootAt' false true 9) 0 10) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_0_10_0, lwcertB_nokids _ _ chc_FT_9_0_10_1, lwcertB_nokids _ _ chc_FT_9_0_10_2])
theorem chc_FT_9_0_11_0 : kidsOk' (kid' (rootAt' false true 9) 0 11) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 0 11) 0).length = 0 := by decide +kernel
theorem chc_FT_9_0_11_1 : kidsOk' (kid' (rootAt' false true 9) 0 11) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 0 11) 1).length = 0 := by decide +kernel
theorem chc_FT_9_0_11_2 : kidsOk' (kid' (rootAt' false true 9) 0 11) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 0 11) 2).length = 0 := by decide +kernel
theorem chc_FT_9_0_11_3 : kidsOk' (kid' (rootAt' false true 9) 0 11) 3 = true ∧ (kids' (kid' (rootAt' false true 9) 0 11) 3).length = 1 := by decide +kernel
theorem chd_FT_9_0_11_3_0 : goodB' 1 (kid' (kid' (rootAt' false true 9) 0 11) 3 0) = true := by decide +kernel
theorem ch_FT_9_0_11' : goodB' 2 (kid' (rootAt' false true 9) 0 11) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_0_11_0, lwcertB_nokids _ _ chc_FT_9_0_11_1, lwcertB_nokids _ _ chc_FT_9_0_11_2, lwcertB_onekid _ _ chc_FT_9_0_11_3 chd_FT_9_0_11_3_0])
theorem chs_FT_9_0' (l : ℕ) (hl : l < 12) : goodB' 2 (kid' (rootAt' false true 9) 0 l) = true := by
  match l, hl with
  | 0, _ => exact ch_FT_9_0_0'
  | 1, _ => exact ch_FT_9_0_1'
  | 2, _ => exact ch_FT_9_0_2'
  | 3, _ => exact ch_FT_9_0_3'
  | 4, _ => exact ch_FT_9_0_4'
  | 5, _ => exact ch_FT_9_0_5'
  | 6, _ => exact ch_FT_9_0_6'
  | 7, _ => exact ch_FT_9_0_7'
  | 8, _ => exact ch_FT_9_0_8'
  | 9, _ => exact ch_FT_9_0_9'
  | 10, _ => exact ch_FT_9_0_10'
  | 11, _ => exact ch_FT_9_0_11'
  | n + 12, h => omega
theorem chc_FT_9_1_0_0 : kidsOk' (kid' (rootAt' false true 9) 1 0) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 1 0) 0).length = 0 := by decide +kernel
theorem chc_FT_9_1_0_1 : kidsOk' (kid' (rootAt' false true 9) 1 0) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 1 0) 1).length = 0 := by decide +kernel
theorem ch_FT_9_1_0' : goodB' 2 (kid' (rootAt' false true 9) 1 0) = true := lwcertB_two _ 2 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_1_0_0, lwcertB_nokids _ _ chc_FT_9_1_0_1])
theorem chc_FT_9_1_1_0 : kidsOk' (kid' (rootAt' false true 9) 1 1) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 1 1) 0).length = 0 := by decide +kernel
theorem chc_FT_9_1_1_1 : kidsOk' (kid' (rootAt' false true 9) 1 1) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 1 1) 1).length = 0 := by decide +kernel
theorem chc_FT_9_1_1_2 : kidsOk' (kid' (rootAt' false true 9) 1 1) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 1 1) 2).length = 0 := by decide +kernel
theorem ch_FT_9_1_1' : goodB' 2 (kid' (rootAt' false true 9) 1 1) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_1_1_0, lwcertB_nokids _ _ chc_FT_9_1_1_1, lwcertB_nokids _ _ chc_FT_9_1_1_2])
theorem chc_FT_9_1_2_0 : kidsOk' (kid' (rootAt' false true 9) 1 2) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 1 2) 0).length = 0 := by decide +kernel
theorem chc_FT_9_1_2_1 : kidsOk' (kid' (rootAt' false true 9) 1 2) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 1 2) 1).length = 0 := by decide +kernel
theorem chc_FT_9_1_2_2 : kidsOk' (kid' (rootAt' false true 9) 1 2) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 1 2) 2).length = 0 := by decide +kernel
theorem ch_FT_9_1_2' : goodB' 2 (kid' (rootAt' false true 9) 1 2) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_1_2_0, lwcertB_nokids _ _ chc_FT_9_1_2_1, lwcertB_nokids _ _ chc_FT_9_1_2_2])
theorem chc_FT_9_1_3_0 : kidsOk' (kid' (rootAt' false true 9) 1 3) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 1 3) 0).length = 0 := by decide +kernel
theorem chc_FT_9_1_3_1 : kidsOk' (kid' (rootAt' false true 9) 1 3) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 1 3) 1).length = 0 := by decide +kernel
theorem chc_FT_9_1_3_2 : kidsOk' (kid' (rootAt' false true 9) 1 3) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 1 3) 2).length = 0 := by decide +kernel
theorem ch_FT_9_1_3' : goodB' 2 (kid' (rootAt' false true 9) 1 3) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_1_3_0, lwcertB_nokids _ _ chc_FT_9_1_3_1, lwcertB_nokids _ _ chc_FT_9_1_3_2])
theorem chc_FT_9_1_4_0 : kidsOk' (kid' (rootAt' false true 9) 1 4) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 1 4) 0).length = 0 := by decide +kernel
theorem chc_FT_9_1_4_1 : kidsOk' (kid' (rootAt' false true 9) 1 4) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 1 4) 1).length = 0 := by decide +kernel
theorem chc_FT_9_1_4_2 : kidsOk' (kid' (rootAt' false true 9) 1 4) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 1 4) 2).length = 0 := by decide +kernel
theorem ch_FT_9_1_4' : goodB' 2 (kid' (rootAt' false true 9) 1 4) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_1_4_0, lwcertB_nokids _ _ chc_FT_9_1_4_1, lwcertB_nokids _ _ chc_FT_9_1_4_2])
theorem chc_FT_9_1_5_0 : kidsOk' (kid' (rootAt' false true 9) 1 5) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 1 5) 0).length = 0 := by decide +kernel
theorem chc_FT_9_1_5_1 : kidsOk' (kid' (rootAt' false true 9) 1 5) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 1 5) 1).length = 1 := by decide +kernel
theorem chd_FT_9_1_5_1_0 : goodB' 1 (kid' (kid' (rootAt' false true 9) 1 5) 1 0) = true := by decide +kernel
theorem chc_FT_9_1_5_2 : kidsOk' (kid' (rootAt' false true 9) 1 5) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 1 5) 2).length = 1 := by decide +kernel
theorem chd_FT_9_1_5_2_0 : goodB' 1 (kid' (kid' (rootAt' false true 9) 1 5) 2 0) = true := by decide +kernel
theorem chc_FT_9_1_5_3 : kidsOk' (kid' (rootAt' false true 9) 1 5) 3 = true ∧ (kids' (kid' (rootAt' false true 9) 1 5) 3).length = 0 := by decide +kernel
theorem ch_FT_9_1_5' : goodB' 2 (kid' (rootAt' false true 9) 1 5) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_1_5_0, lwcertB_onekid _ _ chc_FT_9_1_5_1 chd_FT_9_1_5_1_0, lwcertB_onekid _ _ chc_FT_9_1_5_2 chd_FT_9_1_5_2_0, lwcertB_nokids _ _ chc_FT_9_1_5_3])
theorem chc_FT_9_1_6_0 : kidsOk' (kid' (rootAt' false true 9) 1 6) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 1 6) 0).length = 0 := by decide +kernel
theorem chc_FT_9_1_6_1 : kidsOk' (kid' (rootAt' false true 9) 1 6) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 1 6) 1).length = 0 := by decide +kernel
theorem ch_FT_9_1_6' : goodB' 2 (kid' (rootAt' false true 9) 1 6) = true := lwcertB_two _ 2 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_1_6_0, lwcertB_nokids _ _ chc_FT_9_1_6_1])
theorem chc_FT_9_1_7_0 : kidsOk' (kid' (rootAt' false true 9) 1 7) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 1 7) 0).length = 0 := by decide +kernel
theorem chc_FT_9_1_7_1 : kidsOk' (kid' (rootAt' false true 9) 1 7) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 1 7) 1).length = 0 := by decide +kernel
theorem chc_FT_9_1_7_2 : kidsOk' (kid' (rootAt' false true 9) 1 7) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 1 7) 2).length = 1 := by decide +kernel
theorem chd_FT_9_1_7_2_0 : goodB' 1 (kid' (kid' (rootAt' false true 9) 1 7) 2 0) = true := by decide +kernel
theorem chc_FT_9_1_7_3 : kidsOk' (kid' (rootAt' false true 9) 1 7) 3 = true ∧ (kids' (kid' (rootAt' false true 9) 1 7) 3).length = 1 := by decide +kernel
theorem chd_FT_9_1_7_3_0 : goodB' 1 (kid' (kid' (rootAt' false true 9) 1 7) 3 0) = true := by decide +kernel
theorem ch_FT_9_1_7' : goodB' 2 (kid' (rootAt' false true 9) 1 7) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_1_7_0, lwcertB_nokids _ _ chc_FT_9_1_7_1, lwcertB_onekid _ _ chc_FT_9_1_7_2 chd_FT_9_1_7_2_0, lwcertB_onekid _ _ chc_FT_9_1_7_3 chd_FT_9_1_7_3_0])
theorem chc_FT_9_1_8_0 : kidsOk' (kid' (rootAt' false true 9) 1 8) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 1 8) 0).length = 0 := by decide +kernel
theorem chc_FT_9_1_8_1 : kidsOk' (kid' (rootAt' false true 9) 1 8) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 1 8) 1).length = 0 := by decide +kernel
theorem ch_FT_9_1_8' : goodB' 2 (kid' (rootAt' false true 9) 1 8) = true := lwcertB_two _ 2 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_1_8_0, lwcertB_nokids _ _ chc_FT_9_1_8_1])
theorem chc_FT_9_1_9_0 : kidsOk' (kid' (rootAt' false true 9) 1 9) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 1 9) 0).length = 0 := by decide +kernel
theorem chc_FT_9_1_9_1 : kidsOk' (kid' (rootAt' false true 9) 1 9) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 1 9) 1).length = 1 := by decide +kernel
theorem chd_FT_9_1_9_1_0 : goodB' 1 (kid' (kid' (rootAt' false true 9) 1 9) 1 0) = true := by decide +kernel
theorem chc_FT_9_1_9_2 : kidsOk' (kid' (rootAt' false true 9) 1 9) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 1 9) 2).length = 0 := by decide +kernel
theorem chc_FT_9_1_9_3 : kidsOk' (kid' (rootAt' false true 9) 1 9) 3 = true ∧ (kids' (kid' (rootAt' false true 9) 1 9) 3).length = 1 := by decide +kernel
theorem chd_FT_9_1_9_3_0 : goodB' 1 (kid' (kid' (rootAt' false true 9) 1 9) 3 0) = true := by decide +kernel
theorem ch_FT_9_1_9' : goodB' 2 (kid' (rootAt' false true 9) 1 9) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_1_9_0, lwcertB_onekid _ _ chc_FT_9_1_9_1 chd_FT_9_1_9_1_0, lwcertB_nokids _ _ chc_FT_9_1_9_2, lwcertB_onekid _ _ chc_FT_9_1_9_3 chd_FT_9_1_9_3_0])
theorem chc_FT_9_1_10_0 : kidsOk' (kid' (rootAt' false true 9) 1 10) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 1 10) 0).length = 0 := by decide +kernel
theorem chc_FT_9_1_10_1 : kidsOk' (kid' (rootAt' false true 9) 1 10) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 1 10) 1).length = 0 := by decide +kernel
theorem ch_FT_9_1_10' : goodB' 2 (kid' (rootAt' false true 9) 1 10) = true := lwcertB_two _ 2 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_1_10_0, lwcertB_nokids _ _ chc_FT_9_1_10_1])
theorem chc_FT_9_1_11_0 : kidsOk' (kid' (rootAt' false true 9) 1 11) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 1 11) 0).length = 1 := by decide +kernel
theorem chd_FT_9_1_11_0_0 : goodB' 1 (kid' (kid' (rootAt' false true 9) 1 11) 0 0) = true := by decide +kernel
theorem chc_FT_9_1_11_1 : kidsOk' (kid' (rootAt' false true 9) 1 11) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 1 11) 1).length = 0 := by decide +kernel
theorem chc_FT_9_1_11_2 : kidsOk' (kid' (rootAt' false true 9) 1 11) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 1 11) 2).length = 1 := by decide +kernel
theorem chd_FT_9_1_11_2_0 : goodB' 1 (kid' (kid' (rootAt' false true 9) 1 11) 2 0) = true := by decide +kernel
theorem chc_FT_9_1_11_3 : kidsOk' (kid' (rootAt' false true 9) 1 11) 3 = true ∧ (kids' (kid' (rootAt' false true 9) 1 11) 3).length = 0 := by decide +kernel
theorem ch_FT_9_1_11' : goodB' 2 (kid' (rootAt' false true 9) 1 11) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_onekid _ _ chc_FT_9_1_11_0 chd_FT_9_1_11_0_0, lwcertB_nokids _ _ chc_FT_9_1_11_1, lwcertB_onekid _ _ chc_FT_9_1_11_2 chd_FT_9_1_11_2_0, lwcertB_nokids _ _ chc_FT_9_1_11_3])
theorem chs_FT_9_1' (l : ℕ) (hl : l < 12) : goodB' 2 (kid' (rootAt' false true 9) 1 l) = true := by
  match l, hl with
  | 0, _ => exact ch_FT_9_1_0'
  | 1, _ => exact ch_FT_9_1_1'
  | 2, _ => exact ch_FT_9_1_2'
  | 3, _ => exact ch_FT_9_1_3'
  | 4, _ => exact ch_FT_9_1_4'
  | 5, _ => exact ch_FT_9_1_5'
  | 6, _ => exact ch_FT_9_1_6'
  | 7, _ => exact ch_FT_9_1_7'
  | 8, _ => exact ch_FT_9_1_8'
  | 9, _ => exact ch_FT_9_1_9'
  | 10, _ => exact ch_FT_9_1_10'
  | 11, _ => exact ch_FT_9_1_11'
  | n + 12, h => omega
theorem chc_FT_9_2_0_0 : kidsOk' (kid' (rootAt' false true 9) 2 0) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 2 0) 0).length = 0 := by decide +kernel
theorem chc_FT_9_2_0_1 : kidsOk' (kid' (rootAt' false true 9) 2 0) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 2 0) 1).length = 0 := by decide +kernel
theorem ch_FT_9_2_0' : goodB' 2 (kid' (rootAt' false true 9) 2 0) = true := lwcertB_two _ 2 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_2_0_0, lwcertB_nokids _ _ chc_FT_9_2_0_1])
theorem chc_FT_9_2_1_0 : kidsOk' (kid' (rootAt' false true 9) 2 1) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 2 1) 0).length = 0 := by decide +kernel
theorem chc_FT_9_2_1_1 : kidsOk' (kid' (rootAt' false true 9) 2 1) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 2 1) 1).length = 0 := by decide +kernel
theorem chc_FT_9_2_1_2 : kidsOk' (kid' (rootAt' false true 9) 2 1) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 2 1) 2).length = 0 := by decide +kernel
theorem ch_FT_9_2_1' : goodB' 2 (kid' (rootAt' false true 9) 2 1) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_2_1_0, lwcertB_nokids _ _ chc_FT_9_2_1_1, lwcertB_nokids _ _ chc_FT_9_2_1_2])
theorem chc_FT_9_2_2_0 : kidsOk' (kid' (rootAt' false true 9) 2 2) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 2 2) 0).length = 0 := by decide +kernel
theorem chc_FT_9_2_2_1 : kidsOk' (kid' (rootAt' false true 9) 2 2) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 2 2) 1).length = 0 := by decide +kernel
theorem chc_FT_9_2_2_2 : kidsOk' (kid' (rootAt' false true 9) 2 2) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 2 2) 2).length = 0 := by decide +kernel
theorem ch_FT_9_2_2' : goodB' 2 (kid' (rootAt' false true 9) 2 2) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_2_2_0, lwcertB_nokids _ _ chc_FT_9_2_2_1, lwcertB_nokids _ _ chc_FT_9_2_2_2])
theorem chc_FT_9_2_3_0 : kidsOk' (kid' (rootAt' false true 9) 2 3) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 2 3) 0).length = 0 := by decide +kernel
theorem chc_FT_9_2_3_1 : kidsOk' (kid' (rootAt' false true 9) 2 3) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 2 3) 1).length = 0 := by decide +kernel
theorem chc_FT_9_2_3_2 : kidsOk' (kid' (rootAt' false true 9) 2 3) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 2 3) 2).length = 0 := by decide +kernel
theorem ch_FT_9_2_3' : goodB' 2 (kid' (rootAt' false true 9) 2 3) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_2_3_0, lwcertB_nokids _ _ chc_FT_9_2_3_1, lwcertB_nokids _ _ chc_FT_9_2_3_2])
theorem chc_FT_9_2_4_0 : kidsOk' (kid' (rootAt' false true 9) 2 4) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 2 4) 0).length = 0 := by decide +kernel
theorem chc_FT_9_2_4_1 : kidsOk' (kid' (rootAt' false true 9) 2 4) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 2 4) 1).length = 0 := by decide +kernel
theorem chc_FT_9_2_4_2 : kidsOk' (kid' (rootAt' false true 9) 2 4) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 2 4) 2).length = 0 := by decide +kernel
theorem ch_FT_9_2_4' : goodB' 2 (kid' (rootAt' false true 9) 2 4) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_2_4_0, lwcertB_nokids _ _ chc_FT_9_2_4_1, lwcertB_nokids _ _ chc_FT_9_2_4_2])
theorem chc_FT_9_2_5_0 : kidsOk' (kid' (rootAt' false true 9) 2 5) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 2 5) 0).length = 0 := by decide +kernel
theorem chc_FT_9_2_5_1 : kidsOk' (kid' (rootAt' false true 9) 2 5) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 2 5) 1).length = 0 := by decide +kernel
theorem chc_FT_9_2_5_2 : kidsOk' (kid' (rootAt' false true 9) 2 5) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 2 5) 2).length = 0 := by decide +kernel
theorem ch_FT_9_2_5' : goodB' 2 (kid' (rootAt' false true 9) 2 5) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_2_5_0, lwcertB_nokids _ _ chc_FT_9_2_5_1, lwcertB_nokids _ _ chc_FT_9_2_5_2])
theorem chc_FT_9_2_6_0 : kidsOk' (kid' (rootAt' false true 9) 2 6) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 2 6) 0).length = 0 := by decide +kernel
theorem chc_FT_9_2_6_1 : kidsOk' (kid' (rootAt' false true 9) 2 6) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 2 6) 1).length = 0 := by decide +kernel
theorem chc_FT_9_2_6_2 : kidsOk' (kid' (rootAt' false true 9) 2 6) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 2 6) 2).length = 0 := by decide +kernel
theorem chc_FT_9_2_6_3 : kidsOk' (kid' (rootAt' false true 9) 2 6) 3 = true ∧ (kids' (kid' (rootAt' false true 9) 2 6) 3).length = 1 := by decide +kernel
theorem chd_FT_9_2_6_3_0 : goodB' 1 (kid' (kid' (rootAt' false true 9) 2 6) 3 0) = true := by decide +kernel
theorem ch_FT_9_2_6' : goodB' 2 (kid' (rootAt' false true 9) 2 6) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_2_6_0, lwcertB_nokids _ _ chc_FT_9_2_6_1, lwcertB_nokids _ _ chc_FT_9_2_6_2, lwcertB_onekid _ _ chc_FT_9_2_6_3 chd_FT_9_2_6_3_0])
theorem chc_FT_9_2_7_0 : kidsOk' (kid' (rootAt' false true 9) 2 7) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 2 7) 0).length = 0 := by decide +kernel
theorem chc_FT_9_2_7_1 : kidsOk' (kid' (rootAt' false true 9) 2 7) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 2 7) 1).length = 0 := by decide +kernel
theorem chc_FT_9_2_7_2 : kidsOk' (kid' (rootAt' false true 9) 2 7) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 2 7) 2).length = 0 := by decide +kernel
theorem ch_FT_9_2_7' : goodB' 2 (kid' (rootAt' false true 9) 2 7) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_2_7_0, lwcertB_nokids _ _ chc_FT_9_2_7_1, lwcertB_nokids _ _ chc_FT_9_2_7_2])
theorem chc_FT_9_2_8_0 : kidsOk' (kid' (rootAt' false true 9) 2 8) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 2 8) 0).length = 0 := by decide +kernel
theorem chc_FT_9_2_8_1 : kidsOk' (kid' (rootAt' false true 9) 2 8) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 2 8) 1).length = 1 := by decide +kernel
theorem chd_FT_9_2_8_1_0 : goodB' 1 (kid' (kid' (rootAt' false true 9) 2 8) 1 0) = true := by decide +kernel
theorem chc_FT_9_2_8_2 : kidsOk' (kid' (rootAt' false true 9) 2 8) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 2 8) 2).length = 0 := by decide +kernel
theorem chc_FT_9_2_8_3 : kidsOk' (kid' (rootAt' false true 9) 2 8) 3 = true ∧ (kids' (kid' (rootAt' false true 9) 2 8) 3).length = 0 := by decide +kernel
theorem ch_FT_9_2_8' : goodB' 2 (kid' (rootAt' false true 9) 2 8) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_2_8_0, lwcertB_onekid _ _ chc_FT_9_2_8_1 chd_FT_9_2_8_1_0, lwcertB_nokids _ _ chc_FT_9_2_8_2, lwcertB_nokids _ _ chc_FT_9_2_8_3])
theorem chc_FT_9_2_9_0 : kidsOk' (kid' (rootAt' false true 9) 2 9) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 2 9) 0).length = 1 := by decide +kernel
theorem chd_FT_9_2_9_0_0 : goodB' 1 (kid' (kid' (rootAt' false true 9) 2 9) 0 0) = true := by decide +kernel
theorem chc_FT_9_2_9_1 : kidsOk' (kid' (rootAt' false true 9) 2 9) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 2 9) 1).length = 0 := by decide +kernel
theorem chc_FT_9_2_9_2 : kidsOk' (kid' (rootAt' false true 9) 2 9) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 2 9) 2).length = 1 := by decide +kernel
theorem chd_FT_9_2_9_2_0 : goodB' 1 (kid' (kid' (rootAt' false true 9) 2 9) 2 0) = true := by decide +kernel
theorem chc_FT_9_2_9_3 : kidsOk' (kid' (rootAt' false true 9) 2 9) 3 = true ∧ (kids' (kid' (rootAt' false true 9) 2 9) 3).length = 0 := by decide +kernel
theorem ch_FT_9_2_9' : goodB' 2 (kid' (rootAt' false true 9) 2 9) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_onekid _ _ chc_FT_9_2_9_0 chd_FT_9_2_9_0_0, lwcertB_nokids _ _ chc_FT_9_2_9_1, lwcertB_onekid _ _ chc_FT_9_2_9_2 chd_FT_9_2_9_2_0, lwcertB_nokids _ _ chc_FT_9_2_9_3])
theorem chc_FT_9_2_10_0 : kidsOk' (kid' (rootAt' false true 9) 2 10) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 2 10) 0).length = 0 := by decide +kernel
theorem chc_FT_9_2_10_1 : kidsOk' (kid' (rootAt' false true 9) 2 10) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 2 10) 1).length = 0 := by decide +kernel
theorem ch_FT_9_2_10' : goodB' 2 (kid' (rootAt' false true 9) 2 10) = true := lwcertB_two _ 2 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_2_10_0, lwcertB_nokids _ _ chc_FT_9_2_10_1])
theorem chc_FT_9_2_11_0 : kidsOk' (kid' (rootAt' false true 9) 2 11) 0 = true ∧ (kids' (kid' (rootAt' false true 9) 2 11) 0).length = 0 := by decide +kernel
theorem chc_FT_9_2_11_1 : kidsOk' (kid' (rootAt' false true 9) 2 11) 1 = true ∧ (kids' (kid' (rootAt' false true 9) 2 11) 1).length = 1 := by decide +kernel
theorem chd_FT_9_2_11_1_0 : goodB' 1 (kid' (kid' (rootAt' false true 9) 2 11) 1 0) = true := by decide +kernel
theorem chc_FT_9_2_11_2 : kidsOk' (kid' (rootAt' false true 9) 2 11) 2 = true ∧ (kids' (kid' (rootAt' false true 9) 2 11) 2).length = 0 := by decide +kernel
theorem chc_FT_9_2_11_3 : kidsOk' (kid' (rootAt' false true 9) 2 11) 3 = true ∧ (kids' (kid' (rootAt' false true 9) 2 11) 3).length = 1 := by decide +kernel
theorem chd_FT_9_2_11_3_0 : goodB' 1 (kid' (kid' (rootAt' false true 9) 2 11) 3 0) = true := by decide +kernel
theorem ch_FT_9_2_11' : goodB' 2 (kid' (rootAt' false true 9) 2 11) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_9_2_11_0, lwcertB_onekid _ _ chc_FT_9_2_11_1 chd_FT_9_2_11_1_0, lwcertB_nokids _ _ chc_FT_9_2_11_2, lwcertB_onekid _ _ chc_FT_9_2_11_3 chd_FT_9_2_11_3_0])
theorem chs_FT_9_2' (l : ℕ) (hl : l < 12) : goodB' 2 (kid' (rootAt' false true 9) 2 l) = true := by
  match l, hl with
  | 0, _ => exact ch_FT_9_2_0'
  | 1, _ => exact ch_FT_9_2_1'
  | 2, _ => exact ch_FT_9_2_2'
  | 3, _ => exact ch_FT_9_2_3'
  | 4, _ => exact ch_FT_9_2_4'
  | 5, _ => exact ch_FT_9_2_5'
  | 6, _ => exact ch_FT_9_2_6'
  | 7, _ => exact ch_FT_9_2_7'
  | 8, _ => exact ch_FT_9_2_8'
  | 9, _ => exact ch_FT_9_2_9'
  | 10, _ => exact ch_FT_9_2_10'
  | 11, _ => exact ch_FT_9_2_11'
  | n + 12, h => omega
theorem root_FT_9' : goodB' 3 (rootAt' false true 9) = true := by
  have h : (cands (rootAt' false true 9).g).length = 3 ∧ ∀ j < 3, kidsOk' (rootAt' false true 9) j = true ∧ (kids' (rootAt' false true 9) j).length = 12 := by decide +kernel
  apply goodB'_succ_of 2 _ 3 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have hl' : l < 12 := (h.2 j hj).2 ▸ hl
  match j, hj with
  | 0, _ => exact chs_FT_9_0' l hl'
  | 1, _ => exact chs_FT_9_1' l hl'
  | 2, _ => exact chs_FT_9_2' l hl'
  | n + 3, h => omega
theorem chc_FT_10_0_0_0 : kidsOk' (kid' (rootAt' false true 10) 0 0) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 0 0) 0).length = 0 := by decide +kernel
theorem chc_FT_10_0_0_1 : kidsOk' (kid' (rootAt' false true 10) 0 0) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 0 0) 1).length = 0 := by decide +kernel
theorem ch_FT_10_0_0' : goodB' 2 (kid' (rootAt' false true 10) 0 0) = true := lwcertB_two _ 2 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_0_0_0, lwcertB_nokids _ _ chc_FT_10_0_0_1])
theorem chc_FT_10_0_1_0 : kidsOk' (kid' (rootAt' false true 10) 0 1) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 0 1) 0).length = 0 := by decide +kernel
theorem chc_FT_10_0_1_1 : kidsOk' (kid' (rootAt' false true 10) 0 1) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 0 1) 1).length = 0 := by decide +kernel
theorem chc_FT_10_0_1_2 : kidsOk' (kid' (rootAt' false true 10) 0 1) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 0 1) 2).length = 0 := by decide +kernel
theorem ch_FT_10_0_1' : goodB' 2 (kid' (rootAt' false true 10) 0 1) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_0_1_0, lwcertB_nokids _ _ chc_FT_10_0_1_1, lwcertB_nokids _ _ chc_FT_10_0_1_2])
theorem chc_FT_10_0_2_0 : kidsOk' (kid' (rootAt' false true 10) 0 2) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 0 2) 0).length = 0 := by decide +kernel
theorem chc_FT_10_0_2_1 : kidsOk' (kid' (rootAt' false true 10) 0 2) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 0 2) 1).length = 0 := by decide +kernel
theorem chc_FT_10_0_2_2 : kidsOk' (kid' (rootAt' false true 10) 0 2) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 0 2) 2).length = 0 := by decide +kernel
theorem ch_FT_10_0_2' : goodB' 2 (kid' (rootAt' false true 10) 0 2) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_0_2_0, lwcertB_nokids _ _ chc_FT_10_0_2_1, lwcertB_nokids _ _ chc_FT_10_0_2_2])
theorem chc_FT_10_0_3_0 : kidsOk' (kid' (rootAt' false true 10) 0 3) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 0 3) 0).length = 0 := by decide +kernel
theorem chc_FT_10_0_3_1 : kidsOk' (kid' (rootAt' false true 10) 0 3) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 0 3) 1).length = 0 := by decide +kernel
theorem chc_FT_10_0_3_2 : kidsOk' (kid' (rootAt' false true 10) 0 3) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 0 3) 2).length = 0 := by decide +kernel
theorem ch_FT_10_0_3' : goodB' 2 (kid' (rootAt' false true 10) 0 3) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_0_3_0, lwcertB_nokids _ _ chc_FT_10_0_3_1, lwcertB_nokids _ _ chc_FT_10_0_3_2])
theorem chc_FT_10_0_4_0 : kidsOk' (kid' (rootAt' false true 10) 0 4) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 0 4) 0).length = 0 := by decide +kernel
theorem chc_FT_10_0_4_1 : kidsOk' (kid' (rootAt' false true 10) 0 4) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 0 4) 1).length = 0 := by decide +kernel
theorem chc_FT_10_0_4_2 : kidsOk' (kid' (rootAt' false true 10) 0 4) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 0 4) 2).length = 0 := by decide +kernel
theorem ch_FT_10_0_4' : goodB' 2 (kid' (rootAt' false true 10) 0 4) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_0_4_0, lwcertB_nokids _ _ chc_FT_10_0_4_1, lwcertB_nokids _ _ chc_FT_10_0_4_2])
theorem chc_FT_10_0_5_0 : kidsOk' (kid' (rootAt' false true 10) 0 5) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 0 5) 0).length = 0 := by decide +kernel
theorem chc_FT_10_0_5_1 : kidsOk' (kid' (rootAt' false true 10) 0 5) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 0 5) 1).length = 0 := by decide +kernel
theorem ch_FT_10_0_5' : goodB' 2 (kid' (rootAt' false true 10) 0 5) = true := lwcertB_two _ 2 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_0_5_0, lwcertB_nokids _ _ chc_FT_10_0_5_1])
theorem chc_FT_10_0_6_0 : kidsOk' (kid' (rootAt' false true 10) 0 6) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 0 6) 0).length = 0 := by decide +kernel
theorem chc_FT_10_0_6_1 : kidsOk' (kid' (rootAt' false true 10) 0 6) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 0 6) 1).length = 1 := by decide +kernel
theorem chd_FT_10_0_6_1_0 : goodB' 1 (kid' (kid' (rootAt' false true 10) 0 6) 1 0) = true := by decide +kernel
theorem chc_FT_10_0_6_2 : kidsOk' (kid' (rootAt' false true 10) 0 6) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 0 6) 2).length = 0 := by decide +kernel
theorem chc_FT_10_0_6_3 : kidsOk' (kid' (rootAt' false true 10) 0 6) 3 = true ∧ (kids' (kid' (rootAt' false true 10) 0 6) 3).length = 1 := by decide +kernel
theorem chd_FT_10_0_6_3_0 : goodB' 1 (kid' (kid' (rootAt' false true 10) 0 6) 3 0) = true := by decide +kernel
theorem ch_FT_10_0_6' : goodB' 2 (kid' (rootAt' false true 10) 0 6) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_0_6_0, lwcertB_onekid _ _ chc_FT_10_0_6_1 chd_FT_10_0_6_1_0, lwcertB_nokids _ _ chc_FT_10_0_6_2, lwcertB_onekid _ _ chc_FT_10_0_6_3 chd_FT_10_0_6_3_0])
theorem chc_FT_10_0_7_0 : kidsOk' (kid' (rootAt' false true 10) 0 7) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 0 7) 0).length = 0 := by decide +kernel
theorem chc_FT_10_0_7_1 : kidsOk' (kid' (rootAt' false true 10) 0 7) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 0 7) 1).length = 0 := by decide +kernel
theorem ch_FT_10_0_7' : goodB' 2 (kid' (rootAt' false true 10) 0 7) = true := lwcertB_two _ 2 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_0_7_0, lwcertB_nokids _ _ chc_FT_10_0_7_1])
theorem chc_FT_10_0_8_0 : kidsOk' (kid' (rootAt' false true 10) 0 8) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 0 8) 0).length = 0 := by decide +kernel
theorem chc_FT_10_0_8_1 : kidsOk' (kid' (rootAt' false true 10) 0 8) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 0 8) 1).length = 1 := by decide +kernel
theorem chd_FT_10_0_8_1_0 : goodB' 1 (kid' (kid' (rootAt' false true 10) 0 8) 1 0) = true := by decide +kernel
theorem chc_FT_10_0_8_2 : kidsOk' (kid' (rootAt' false true 10) 0 8) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 0 8) 2).length = 1 := by decide +kernel
theorem chd_FT_10_0_8_2_0 : goodB' 1 (kid' (kid' (rootAt' false true 10) 0 8) 2 0) = true := by decide +kernel
theorem chc_FT_10_0_8_3 : kidsOk' (kid' (rootAt' false true 10) 0 8) 3 = true ∧ (kids' (kid' (rootAt' false true 10) 0 8) 3).length = 0 := by decide +kernel
theorem ch_FT_10_0_8' : goodB' 2 (kid' (rootAt' false true 10) 0 8) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_0_8_0, lwcertB_onekid _ _ chc_FT_10_0_8_1 chd_FT_10_0_8_1_0, lwcertB_onekid _ _ chc_FT_10_0_8_2 chd_FT_10_0_8_2_0, lwcertB_nokids _ _ chc_FT_10_0_8_3])
theorem chc_FT_10_0_9_0 : kidsOk' (kid' (rootAt' false true 10) 0 9) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 0 9) 0).length = 0 := by decide +kernel
theorem chc_FT_10_0_9_1 : kidsOk' (kid' (rootAt' false true 10) 0 9) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 0 9) 1).length = 0 := by decide +kernel
theorem chc_FT_10_0_9_2 : kidsOk' (kid' (rootAt' false true 10) 0 9) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 0 9) 2).length = 0 := by decide +kernel
theorem chc_FT_10_0_9_3 : kidsOk' (kid' (rootAt' false true 10) 0 9) 3 = true ∧ (kids' (kid' (rootAt' false true 10) 0 9) 3).length = 0 := by decide +kernel
theorem ch_FT_10_0_9' : goodB' 2 (kid' (rootAt' false true 10) 0 9) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_0_9_0, lwcertB_nokids _ _ chc_FT_10_0_9_1, lwcertB_nokids _ _ chc_FT_10_0_9_2, lwcertB_nokids _ _ chc_FT_10_0_9_3])
theorem chc_FT_10_0_10_0 : kidsOk' (kid' (rootAt' false true 10) 0 10) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 0 10) 0).length = 0 := by decide +kernel
theorem chc_FT_10_0_10_1 : kidsOk' (kid' (rootAt' false true 10) 0 10) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 0 10) 1).length = 0 := by decide +kernel
theorem chc_FT_10_0_10_2 : kidsOk' (kid' (rootAt' false true 10) 0 10) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 0 10) 2).length = 0 := by decide +kernel
theorem chc_FT_10_0_10_3 : kidsOk' (kid' (rootAt' false true 10) 0 10) 3 = true ∧ (kids' (kid' (rootAt' false true 10) 0 10) 3).length = 0 := by decide +kernel
theorem ch_FT_10_0_10' : goodB' 2 (kid' (rootAt' false true 10) 0 10) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_0_10_0, lwcertB_nokids _ _ chc_FT_10_0_10_1, lwcertB_nokids _ _ chc_FT_10_0_10_2, lwcertB_nokids _ _ chc_FT_10_0_10_3])
theorem chc_FT_10_0_11_0 : kidsOk' (kid' (rootAt' false true 10) 0 11) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 0 11) 0).length = 0 := by decide +kernel
theorem chc_FT_10_0_11_1 : kidsOk' (kid' (rootAt' false true 10) 0 11) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 0 11) 1).length = 0 := by decide +kernel
theorem chc_FT_10_0_11_2 : kidsOk' (kid' (rootAt' false true 10) 0 11) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 0 11) 2).length = 1 := by decide +kernel
theorem chd_FT_10_0_11_2_0 : goodB' 1 (kid' (kid' (rootAt' false true 10) 0 11) 2 0) = true := by decide +kernel
theorem chc_FT_10_0_11_3 : kidsOk' (kid' (rootAt' false true 10) 0 11) 3 = true ∧ (kids' (kid' (rootAt' false true 10) 0 11) 3).length = 0 := by decide +kernel
theorem ch_FT_10_0_11' : goodB' 2 (kid' (rootAt' false true 10) 0 11) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_0_11_0, lwcertB_nokids _ _ chc_FT_10_0_11_1, lwcertB_onekid _ _ chc_FT_10_0_11_2 chd_FT_10_0_11_2_0, lwcertB_nokids _ _ chc_FT_10_0_11_3])
theorem chc_FT_10_0_12_0 : kidsOk' (kid' (rootAt' false true 10) 0 12) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 0 12) 0).length = 0 := by decide +kernel
theorem chc_FT_10_0_12_1 : kidsOk' (kid' (rootAt' false true 10) 0 12) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 0 12) 1).length = 0 := by decide +kernel
theorem chc_FT_10_0_12_2 : kidsOk' (kid' (rootAt' false true 10) 0 12) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 0 12) 2).length = 0 := by decide +kernel
theorem ch_FT_10_0_12' : goodB' 2 (kid' (rootAt' false true 10) 0 12) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_0_12_0, lwcertB_nokids _ _ chc_FT_10_0_12_1, lwcertB_nokids _ _ chc_FT_10_0_12_2])
theorem chc_FT_10_0_13_0 : kidsOk' (kid' (rootAt' false true 10) 0 13) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 0 13) 0).length = 0 := by decide +kernel
theorem chc_FT_10_0_13_1 : kidsOk' (kid' (rootAt' false true 10) 0 13) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 0 13) 1).length = 0 := by decide +kernel
theorem chc_FT_10_0_13_2 : kidsOk' (kid' (rootAt' false true 10) 0 13) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 0 13) 2).length = 0 := by decide +kernel
theorem chc_FT_10_0_13_3 : kidsOk' (kid' (rootAt' false true 10) 0 13) 3 = true ∧ (kids' (kid' (rootAt' false true 10) 0 13) 3).length = 1 := by decide +kernel
theorem chd_FT_10_0_13_3_0 : goodB' 1 (kid' (kid' (rootAt' false true 10) 0 13) 3 0) = true := by decide +kernel
theorem ch_FT_10_0_13' : goodB' 2 (kid' (rootAt' false true 10) 0 13) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_0_13_0, lwcertB_nokids _ _ chc_FT_10_0_13_1, lwcertB_nokids _ _ chc_FT_10_0_13_2, lwcertB_onekid _ _ chc_FT_10_0_13_3 chd_FT_10_0_13_3_0])
theorem chs_FT_10_0' (l : ℕ) (hl : l < 14) : goodB' 2 (kid' (rootAt' false true 10) 0 l) = true := by
  match l, hl with
  | 0, _ => exact ch_FT_10_0_0'
  | 1, _ => exact ch_FT_10_0_1'
  | 2, _ => exact ch_FT_10_0_2'
  | 3, _ => exact ch_FT_10_0_3'
  | 4, _ => exact ch_FT_10_0_4'
  | 5, _ => exact ch_FT_10_0_5'
  | 6, _ => exact ch_FT_10_0_6'
  | 7, _ => exact ch_FT_10_0_7'
  | 8, _ => exact ch_FT_10_0_8'
  | 9, _ => exact ch_FT_10_0_9'
  | 10, _ => exact ch_FT_10_0_10'
  | 11, _ => exact ch_FT_10_0_11'
  | 12, _ => exact ch_FT_10_0_12'
  | 13, _ => exact ch_FT_10_0_13'
  | n + 14, h => omega
theorem chc_FT_10_1_0_0 : kidsOk' (kid' (rootAt' false true 10) 1 0) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 1 0) 0).length = 0 := by decide +kernel
theorem chc_FT_10_1_0_1 : kidsOk' (kid' (rootAt' false true 10) 1 0) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 1 0) 1).length = 0 := by decide +kernel
theorem ch_FT_10_1_0' : goodB' 2 (kid' (rootAt' false true 10) 1 0) = true := lwcertB_two _ 2 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_1_0_0, lwcertB_nokids _ _ chc_FT_10_1_0_1])
theorem chc_FT_10_1_1_0 : kidsOk' (kid' (rootAt' false true 10) 1 1) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 1 1) 0).length = 0 := by decide +kernel
theorem chc_FT_10_1_1_1 : kidsOk' (kid' (rootAt' false true 10) 1 1) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 1 1) 1).length = 0 := by decide +kernel
theorem chc_FT_10_1_1_2 : kidsOk' (kid' (rootAt' false true 10) 1 1) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 1 1) 2).length = 0 := by decide +kernel
theorem ch_FT_10_1_1' : goodB' 2 (kid' (rootAt' false true 10) 1 1) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_1_1_0, lwcertB_nokids _ _ chc_FT_10_1_1_1, lwcertB_nokids _ _ chc_FT_10_1_1_2])
theorem chc_FT_10_1_2_0 : kidsOk' (kid' (rootAt' false true 10) 1 2) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 1 2) 0).length = 0 := by decide +kernel
theorem chc_FT_10_1_2_1 : kidsOk' (kid' (rootAt' false true 10) 1 2) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 1 2) 1).length = 0 := by decide +kernel
theorem chc_FT_10_1_2_2 : kidsOk' (kid' (rootAt' false true 10) 1 2) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 1 2) 2).length = 0 := by decide +kernel
theorem ch_FT_10_1_2' : goodB' 2 (kid' (rootAt' false true 10) 1 2) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_1_2_0, lwcertB_nokids _ _ chc_FT_10_1_2_1, lwcertB_nokids _ _ chc_FT_10_1_2_2])
theorem chc_FT_10_1_3_0 : kidsOk' (kid' (rootAt' false true 10) 1 3) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 1 3) 0).length = 0 := by decide +kernel
theorem chc_FT_10_1_3_1 : kidsOk' (kid' (rootAt' false true 10) 1 3) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 1 3) 1).length = 0 := by decide +kernel
theorem chc_FT_10_1_3_2 : kidsOk' (kid' (rootAt' false true 10) 1 3) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 1 3) 2).length = 0 := by decide +kernel
theorem ch_FT_10_1_3' : goodB' 2 (kid' (rootAt' false true 10) 1 3) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_1_3_0, lwcertB_nokids _ _ chc_FT_10_1_3_1, lwcertB_nokids _ _ chc_FT_10_1_3_2])
theorem chc_FT_10_1_4_0 : kidsOk' (kid' (rootAt' false true 10) 1 4) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 1 4) 0).length = 0 := by decide +kernel
theorem chc_FT_10_1_4_1 : kidsOk' (kid' (rootAt' false true 10) 1 4) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 1 4) 1).length = 0 := by decide +kernel
theorem chc_FT_10_1_4_2 : kidsOk' (kid' (rootAt' false true 10) 1 4) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 1 4) 2).length = 0 := by decide +kernel
theorem ch_FT_10_1_4' : goodB' 2 (kid' (rootAt' false true 10) 1 4) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_1_4_0, lwcertB_nokids _ _ chc_FT_10_1_4_1, lwcertB_nokids _ _ chc_FT_10_1_4_2])
theorem chc_FT_10_1_5_0 : kidsOk' (kid' (rootAt' false true 10) 1 5) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 1 5) 0).length = 0 := by decide +kernel
theorem chc_FT_10_1_5_1 : kidsOk' (kid' (rootAt' false true 10) 1 5) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 1 5) 1).length = 1 := by decide +kernel
theorem chd_FT_10_1_5_1_0 : goodB' 1 (kid' (kid' (rootAt' false true 10) 1 5) 1 0) = true := by decide +kernel
theorem chc_FT_10_1_5_2 : kidsOk' (kid' (rootAt' false true 10) 1 5) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 1 5) 2).length = 1 := by decide +kernel
theorem chd_FT_10_1_5_2_0 : goodB' 1 (kid' (kid' (rootAt' false true 10) 1 5) 2 0) = true := by decide +kernel
theorem chc_FT_10_1_5_3 : kidsOk' (kid' (rootAt' false true 10) 1 5) 3 = true ∧ (kids' (kid' (rootAt' false true 10) 1 5) 3).length = 0 := by decide +kernel
theorem ch_FT_10_1_5' : goodB' 2 (kid' (rootAt' false true 10) 1 5) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_1_5_0, lwcertB_onekid _ _ chc_FT_10_1_5_1 chd_FT_10_1_5_1_0, lwcertB_onekid _ _ chc_FT_10_1_5_2 chd_FT_10_1_5_2_0, lwcertB_nokids _ _ chc_FT_10_1_5_3])
theorem chc_FT_10_1_6_0 : kidsOk' (kid' (rootAt' false true 10) 1 6) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 1 6) 0).length = 0 := by decide +kernel
theorem chc_FT_10_1_6_1 : kidsOk' (kid' (rootAt' false true 10) 1 6) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 1 6) 1).length = 0 := by decide +kernel
theorem ch_FT_10_1_6' : goodB' 2 (kid' (rootAt' false true 10) 1 6) = true := lwcertB_two _ 2 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_1_6_0, lwcertB_nokids _ _ chc_FT_10_1_6_1])
theorem chc_FT_10_1_7_0 : kidsOk' (kid' (rootAt' false true 10) 1 7) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 1 7) 0).length = 0 := by decide +kernel
theorem chc_FT_10_1_7_1 : kidsOk' (kid' (rootAt' false true 10) 1 7) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 1 7) 1).length = 0 := by decide +kernel
theorem chc_FT_10_1_7_2 : kidsOk' (kid' (rootAt' false true 10) 1 7) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 1 7) 2).length = 1 := by decide +kernel
theorem chd_FT_10_1_7_2_0 : goodB' 1 (kid' (kid' (rootAt' false true 10) 1 7) 2 0) = true := by decide +kernel
theorem chc_FT_10_1_7_3 : kidsOk' (kid' (rootAt' false true 10) 1 7) 3 = true ∧ (kids' (kid' (rootAt' false true 10) 1 7) 3).length = 1 := by decide +kernel
theorem chd_FT_10_1_7_3_0 : goodB' 1 (kid' (kid' (rootAt' false true 10) 1 7) 3 0) = true := by decide +kernel
theorem ch_FT_10_1_7' : goodB' 2 (kid' (rootAt' false true 10) 1 7) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_1_7_0, lwcertB_nokids _ _ chc_FT_10_1_7_1, lwcertB_onekid _ _ chc_FT_10_1_7_2 chd_FT_10_1_7_2_0, lwcertB_onekid _ _ chc_FT_10_1_7_3 chd_FT_10_1_7_3_0])
theorem chc_FT_10_1_8_0 : kidsOk' (kid' (rootAt' false true 10) 1 8) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 1 8) 0).length = 0 := by decide +kernel
theorem chc_FT_10_1_8_1 : kidsOk' (kid' (rootAt' false true 10) 1 8) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 1 8) 1).length = 0 := by decide +kernel
theorem ch_FT_10_1_8' : goodB' 2 (kid' (rootAt' false true 10) 1 8) = true := lwcertB_two _ 2 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_1_8_0, lwcertB_nokids _ _ chc_FT_10_1_8_1])
theorem chc_FT_10_1_9_0 : kidsOk' (kid' (rootAt' false true 10) 1 9) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 1 9) 0).length = 0 := by decide +kernel
theorem chc_FT_10_1_9_1 : kidsOk' (kid' (rootAt' false true 10) 1 9) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 1 9) 1).length = 1 := by decide +kernel
theorem chd_FT_10_1_9_1_0 : goodB' 1 (kid' (kid' (rootAt' false true 10) 1 9) 1 0) = true := by decide +kernel
theorem chc_FT_10_1_9_2 : kidsOk' (kid' (rootAt' false true 10) 1 9) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 1 9) 2).length = 0 := by decide +kernel
theorem chc_FT_10_1_9_3 : kidsOk' (kid' (rootAt' false true 10) 1 9) 3 = true ∧ (kids' (kid' (rootAt' false true 10) 1 9) 3).length = 1 := by decide +kernel
theorem chd_FT_10_1_9_3_0 : goodB' 1 (kid' (kid' (rootAt' false true 10) 1 9) 3 0) = true := by decide +kernel
theorem ch_FT_10_1_9' : goodB' 2 (kid' (rootAt' false true 10) 1 9) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_1_9_0, lwcertB_onekid _ _ chc_FT_10_1_9_1 chd_FT_10_1_9_1_0, lwcertB_nokids _ _ chc_FT_10_1_9_2, lwcertB_onekid _ _ chc_FT_10_1_9_3 chd_FT_10_1_9_3_0])
theorem chc_FT_10_1_10_0 : kidsOk' (kid' (rootAt' false true 10) 1 10) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 1 10) 0).length = 0 := by decide +kernel
theorem chc_FT_10_1_10_1 : kidsOk' (kid' (rootAt' false true 10) 1 10) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 1 10) 1).length = 0 := by decide +kernel
theorem ch_FT_10_1_10' : goodB' 2 (kid' (rootAt' false true 10) 1 10) = true := lwcertB_two _ 2 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_1_10_0, lwcertB_nokids _ _ chc_FT_10_1_10_1])
theorem chc_FT_10_1_11_0 : kidsOk' (kid' (rootAt' false true 10) 1 11) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 1 11) 0).length = 1 := by decide +kernel
theorem chd_FT_10_1_11_0_0 : goodB' 1 (kid' (kid' (rootAt' false true 10) 1 11) 0 0) = true := by decide +kernel
theorem chc_FT_10_1_11_1 : kidsOk' (kid' (rootAt' false true 10) 1 11) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 1 11) 1).length = 0 := by decide +kernel
theorem chc_FT_10_1_11_2 : kidsOk' (kid' (rootAt' false true 10) 1 11) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 1 11) 2).length = 1 := by decide +kernel
theorem chd_FT_10_1_11_2_0 : goodB' 1 (kid' (kid' (rootAt' false true 10) 1 11) 2 0) = true := by decide +kernel
theorem chc_FT_10_1_11_3 : kidsOk' (kid' (rootAt' false true 10) 1 11) 3 = true ∧ (kids' (kid' (rootAt' false true 10) 1 11) 3).length = 0 := by decide +kernel
theorem ch_FT_10_1_11' : goodB' 2 (kid' (rootAt' false true 10) 1 11) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_onekid _ _ chc_FT_10_1_11_0 chd_FT_10_1_11_0_0, lwcertB_nokids _ _ chc_FT_10_1_11_1, lwcertB_onekid _ _ chc_FT_10_1_11_2 chd_FT_10_1_11_2_0, lwcertB_nokids _ _ chc_FT_10_1_11_3])
theorem chc_FT_10_1_12_0 : kidsOk' (kid' (rootAt' false true 10) 1 12) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 1 12) 0).length = 0 := by decide +kernel
theorem chc_FT_10_1_12_1 : kidsOk' (kid' (rootAt' false true 10) 1 12) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 1 12) 1).length = 0 := by decide +kernel
theorem chc_FT_10_1_12_2 : kidsOk' (kid' (rootAt' false true 10) 1 12) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 1 12) 2).length = 0 := by decide +kernel
theorem chc_FT_10_1_12_3 : kidsOk' (kid' (rootAt' false true 10) 1 12) 3 = true ∧ (kids' (kid' (rootAt' false true 10) 1 12) 3).length = 0 := by decide +kernel
theorem ch_FT_10_1_12' : goodB' 2 (kid' (rootAt' false true 10) 1 12) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_1_12_0, lwcertB_nokids _ _ chc_FT_10_1_12_1, lwcertB_nokids _ _ chc_FT_10_1_12_2, lwcertB_nokids _ _ chc_FT_10_1_12_3])
theorem chc_FT_10_1_13_0 : kidsOk' (kid' (rootAt' false true 10) 1 13) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 1 13) 0).length = 0 := by decide +kernel
theorem chc_FT_10_1_13_1 : kidsOk' (kid' (rootAt' false true 10) 1 13) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 1 13) 1).length = 0 := by decide +kernel
theorem chc_FT_10_1_13_2 : kidsOk' (kid' (rootAt' false true 10) 1 13) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 1 13) 2).length = 0 := by decide +kernel
theorem chc_FT_10_1_13_3 : kidsOk' (kid' (rootAt' false true 10) 1 13) 3 = true ∧ (kids' (kid' (rootAt' false true 10) 1 13) 3).length = 0 := by decide +kernel
theorem ch_FT_10_1_13' : goodB' 2 (kid' (rootAt' false true 10) 1 13) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_1_13_0, lwcertB_nokids _ _ chc_FT_10_1_13_1, lwcertB_nokids _ _ chc_FT_10_1_13_2, lwcertB_nokids _ _ chc_FT_10_1_13_3])
theorem chs_FT_10_1' (l : ℕ) (hl : l < 14) : goodB' 2 (kid' (rootAt' false true 10) 1 l) = true := by
  match l, hl with
  | 0, _ => exact ch_FT_10_1_0'
  | 1, _ => exact ch_FT_10_1_1'
  | 2, _ => exact ch_FT_10_1_2'
  | 3, _ => exact ch_FT_10_1_3'
  | 4, _ => exact ch_FT_10_1_4'
  | 5, _ => exact ch_FT_10_1_5'
  | 6, _ => exact ch_FT_10_1_6'
  | 7, _ => exact ch_FT_10_1_7'
  | 8, _ => exact ch_FT_10_1_8'
  | 9, _ => exact ch_FT_10_1_9'
  | 10, _ => exact ch_FT_10_1_10'
  | 11, _ => exact ch_FT_10_1_11'
  | 12, _ => exact ch_FT_10_1_12'
  | 13, _ => exact ch_FT_10_1_13'
  | n + 14, h => omega
theorem chc_FT_10_2_0_0 : kidsOk' (kid' (rootAt' false true 10) 2 0) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 2 0) 0).length = 0 := by decide +kernel
theorem chc_FT_10_2_0_1 : kidsOk' (kid' (rootAt' false true 10) 2 0) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 2 0) 1).length = 0 := by decide +kernel
theorem ch_FT_10_2_0' : goodB' 2 (kid' (rootAt' false true 10) 2 0) = true := lwcertB_two _ 2 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_2_0_0, lwcertB_nokids _ _ chc_FT_10_2_0_1])
theorem chc_FT_10_2_1_0 : kidsOk' (kid' (rootAt' false true 10) 2 1) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 2 1) 0).length = 0 := by decide +kernel
theorem chc_FT_10_2_1_1 : kidsOk' (kid' (rootAt' false true 10) 2 1) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 2 1) 1).length = 0 := by decide +kernel
theorem chc_FT_10_2_1_2 : kidsOk' (kid' (rootAt' false true 10) 2 1) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 2 1) 2).length = 0 := by decide +kernel
theorem ch_FT_10_2_1' : goodB' 2 (kid' (rootAt' false true 10) 2 1) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_2_1_0, lwcertB_nokids _ _ chc_FT_10_2_1_1, lwcertB_nokids _ _ chc_FT_10_2_1_2])
theorem chc_FT_10_2_2_0 : kidsOk' (kid' (rootAt' false true 10) 2 2) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 2 2) 0).length = 0 := by decide +kernel
theorem chc_FT_10_2_2_1 : kidsOk' (kid' (rootAt' false true 10) 2 2) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 2 2) 1).length = 0 := by decide +kernel
theorem chc_FT_10_2_2_2 : kidsOk' (kid' (rootAt' false true 10) 2 2) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 2 2) 2).length = 0 := by decide +kernel
theorem ch_FT_10_2_2' : goodB' 2 (kid' (rootAt' false true 10) 2 2) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_2_2_0, lwcertB_nokids _ _ chc_FT_10_2_2_1, lwcertB_nokids _ _ chc_FT_10_2_2_2])
theorem chc_FT_10_2_3_0 : kidsOk' (kid' (rootAt' false true 10) 2 3) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 2 3) 0).length = 0 := by decide +kernel
theorem chc_FT_10_2_3_1 : kidsOk' (kid' (rootAt' false true 10) 2 3) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 2 3) 1).length = 0 := by decide +kernel
theorem chc_FT_10_2_3_2 : kidsOk' (kid' (rootAt' false true 10) 2 3) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 2 3) 2).length = 0 := by decide +kernel
theorem ch_FT_10_2_3' : goodB' 2 (kid' (rootAt' false true 10) 2 3) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_2_3_0, lwcertB_nokids _ _ chc_FT_10_2_3_1, lwcertB_nokids _ _ chc_FT_10_2_3_2])
theorem chc_FT_10_2_4_0 : kidsOk' (kid' (rootAt' false true 10) 2 4) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 2 4) 0).length = 0 := by decide +kernel
theorem chc_FT_10_2_4_1 : kidsOk' (kid' (rootAt' false true 10) 2 4) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 2 4) 1).length = 0 := by decide +kernel
theorem chc_FT_10_2_4_2 : kidsOk' (kid' (rootAt' false true 10) 2 4) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 2 4) 2).length = 0 := by decide +kernel
theorem ch_FT_10_2_4' : goodB' 2 (kid' (rootAt' false true 10) 2 4) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_2_4_0, lwcertB_nokids _ _ chc_FT_10_2_4_1, lwcertB_nokids _ _ chc_FT_10_2_4_2])
theorem chc_FT_10_2_5_0 : kidsOk' (kid' (rootAt' false true 10) 2 5) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 2 5) 0).length = 0 := by decide +kernel
theorem chc_FT_10_2_5_1 : kidsOk' (kid' (rootAt' false true 10) 2 5) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 2 5) 1).length = 0 := by decide +kernel
theorem chc_FT_10_2_5_2 : kidsOk' (kid' (rootAt' false true 10) 2 5) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 2 5) 2).length = 0 := by decide +kernel
theorem chc_FT_10_2_5_3 : kidsOk' (kid' (rootAt' false true 10) 2 5) 3 = true ∧ (kids' (kid' (rootAt' false true 10) 2 5) 3).length = 0 := by decide +kernel
theorem ch_FT_10_2_5' : goodB' 2 (kid' (rootAt' false true 10) 2 5) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_2_5_0, lwcertB_nokids _ _ chc_FT_10_2_5_1, lwcertB_nokids _ _ chc_FT_10_2_5_2, lwcertB_nokids _ _ chc_FT_10_2_5_3])
theorem chc_FT_10_2_6_0 : kidsOk' (kid' (rootAt' false true 10) 2 6) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 2 6) 0).length = 0 := by decide +kernel
theorem chc_FT_10_2_6_1 : kidsOk' (kid' (rootAt' false true 10) 2 6) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 2 6) 1).length = 0 := by decide +kernel
theorem chc_FT_10_2_6_2 : kidsOk' (kid' (rootAt' false true 10) 2 6) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 2 6) 2).length = 0 := by decide +kernel
theorem chc_FT_10_2_6_3 : kidsOk' (kid' (rootAt' false true 10) 2 6) 3 = true ∧ (kids' (kid' (rootAt' false true 10) 2 6) 3).length = 0 := by decide +kernel
theorem ch_FT_10_2_6' : goodB' 2 (kid' (rootAt' false true 10) 2 6) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_2_6_0, lwcertB_nokids _ _ chc_FT_10_2_6_1, lwcertB_nokids _ _ chc_FT_10_2_6_2, lwcertB_nokids _ _ chc_FT_10_2_6_3])
theorem chc_FT_10_2_7_0 : kidsOk' (kid' (rootAt' false true 10) 2 7) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 2 7) 0).length = 1 := by decide +kernel
theorem chd_FT_10_2_7_0_0 : goodB' 1 (kid' (kid' (rootAt' false true 10) 2 7) 0 0) = true := by decide +kernel
theorem chc_FT_10_2_7_1 : kidsOk' (kid' (rootAt' false true 10) 2 7) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 2 7) 1).length = 0 := by decide +kernel
theorem chc_FT_10_2_7_2 : kidsOk' (kid' (rootAt' false true 10) 2 7) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 2 7) 2).length = 1 := by decide +kernel
theorem chd_FT_10_2_7_2_0 : goodB' 1 (kid' (kid' (rootAt' false true 10) 2 7) 2 0) = true := by decide +kernel
theorem chc_FT_10_2_7_3 : kidsOk' (kid' (rootAt' false true 10) 2 7) 3 = true ∧ (kids' (kid' (rootAt' false true 10) 2 7) 3).length = 0 := by decide +kernel
theorem ch_FT_10_2_7' : goodB' 2 (kid' (rootAt' false true 10) 2 7) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_onekid _ _ chc_FT_10_2_7_0 chd_FT_10_2_7_0_0, lwcertB_nokids _ _ chc_FT_10_2_7_1, lwcertB_onekid _ _ chc_FT_10_2_7_2 chd_FT_10_2_7_2_0, lwcertB_nokids _ _ chc_FT_10_2_7_3])
theorem chc_FT_10_2_8_0 : kidsOk' (kid' (rootAt' false true 10) 2 8) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 2 8) 0).length = 0 := by decide +kernel
theorem chc_FT_10_2_8_1 : kidsOk' (kid' (rootAt' false true 10) 2 8) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 2 8) 1).length = 0 := by decide +kernel
theorem ch_FT_10_2_8' : goodB' 2 (kid' (rootAt' false true 10) 2 8) = true := lwcertB_two _ 2 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_2_8_0, lwcertB_nokids _ _ chc_FT_10_2_8_1])
theorem chc_FT_10_2_9_0 : kidsOk' (kid' (rootAt' false true 10) 2 9) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 2 9) 0).length = 0 := by decide +kernel
theorem chc_FT_10_2_9_1 : kidsOk' (kid' (rootAt' false true 10) 2 9) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 2 9) 1).length = 1 := by decide +kernel
theorem chd_FT_10_2_9_1_0 : goodB' 1 (kid' (kid' (rootAt' false true 10) 2 9) 1 0) = true := by decide +kernel
theorem chc_FT_10_2_9_2 : kidsOk' (kid' (rootAt' false true 10) 2 9) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 2 9) 2).length = 0 := by decide +kernel
theorem chc_FT_10_2_9_3 : kidsOk' (kid' (rootAt' false true 10) 2 9) 3 = true ∧ (kids' (kid' (rootAt' false true 10) 2 9) 3).length = 1 := by decide +kernel
theorem chd_FT_10_2_9_3_0 : goodB' 1 (kid' (kid' (rootAt' false true 10) 2 9) 3 0) = true := by decide +kernel
theorem ch_FT_10_2_9' : goodB' 2 (kid' (rootAt' false true 10) 2 9) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_2_9_0, lwcertB_onekid _ _ chc_FT_10_2_9_1 chd_FT_10_2_9_1_0, lwcertB_nokids _ _ chc_FT_10_2_9_2, lwcertB_onekid _ _ chc_FT_10_2_9_3 chd_FT_10_2_9_3_0])
theorem chc_FT_10_2_10_0 : kidsOk' (kid' (rootAt' false true 10) 2 10) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 2 10) 0).length = 0 := by decide +kernel
theorem chc_FT_10_2_10_1 : kidsOk' (kid' (rootAt' false true 10) 2 10) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 2 10) 1).length = 0 := by decide +kernel
theorem chc_FT_10_2_10_2 : kidsOk' (kid' (rootAt' false true 10) 2 10) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 2 10) 2).length = 0 := by decide +kernel
theorem ch_FT_10_2_10' : goodB' 2 (kid' (rootAt' false true 10) 2 10) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_2_10_0, lwcertB_nokids _ _ chc_FT_10_2_10_1, lwcertB_nokids _ _ chc_FT_10_2_10_2])
theorem chc_FT_10_2_11_0 : kidsOk' (kid' (rootAt' false true 10) 2 11) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 2 11) 0).length = 0 := by decide +kernel
theorem chc_FT_10_2_11_1 : kidsOk' (kid' (rootAt' false true 10) 2 11) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 2 11) 1).length = 0 := by decide +kernel
theorem chc_FT_10_2_11_2 : kidsOk' (kid' (rootAt' false true 10) 2 11) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 2 11) 2).length = 0 := by decide +kernel
theorem chc_FT_10_2_11_3 : kidsOk' (kid' (rootAt' false true 10) 2 11) 3 = true ∧ (kids' (kid' (rootAt' false true 10) 2 11) 3).length = 1 := by decide +kernel
theorem chd_FT_10_2_11_3_0 : goodB' 1 (kid' (kid' (rootAt' false true 10) 2 11) 3 0) = true := by decide +kernel
theorem ch_FT_10_2_11' : goodB' 2 (kid' (rootAt' false true 10) 2 11) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_2_11_0, lwcertB_nokids _ _ chc_FT_10_2_11_1, lwcertB_nokids _ _ chc_FT_10_2_11_2, lwcertB_onekid _ _ chc_FT_10_2_11_3 chd_FT_10_2_11_3_0])
theorem chc_FT_10_2_12_0 : kidsOk' (kid' (rootAt' false true 10) 2 12) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 2 12) 0).length = 0 := by decide +kernel
theorem chc_FT_10_2_12_1 : kidsOk' (kid' (rootAt' false true 10) 2 12) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 2 12) 1).length = 0 := by decide +kernel
theorem chc_FT_10_2_12_2 : kidsOk' (kid' (rootAt' false true 10) 2 12) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 2 12) 2).length = 0 := by decide +kernel
theorem ch_FT_10_2_12' : goodB' 2 (kid' (rootAt' false true 10) 2 12) = true := lwcertB_two _ 3 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_2_12_0, lwcertB_nokids _ _ chc_FT_10_2_12_1, lwcertB_nokids _ _ chc_FT_10_2_12_2])
theorem chc_FT_10_2_13_0 : kidsOk' (kid' (rootAt' false true 10) 2 13) 0 = true ∧ (kids' (kid' (rootAt' false true 10) 2 13) 0).length = 0 := by decide +kernel
theorem chc_FT_10_2_13_1 : kidsOk' (kid' (rootAt' false true 10) 2 13) 1 = true ∧ (kids' (kid' (rootAt' false true 10) 2 13) 1).length = 1 := by decide +kernel
theorem chd_FT_10_2_13_1_0 : goodB' 1 (kid' (kid' (rootAt' false true 10) 2 13) 1 0) = true := by decide +kernel
theorem chc_FT_10_2_13_2 : kidsOk' (kid' (rootAt' false true 10) 2 13) 2 = true ∧ (kids' (kid' (rootAt' false true 10) 2 13) 2).length = 0 := by decide +kernel
theorem chc_FT_10_2_13_3 : kidsOk' (kid' (rootAt' false true 10) 2 13) 3 = true ∧ (kids' (kid' (rootAt' false true 10) 2 13) 3).length = 0 := by decide +kernel
theorem ch_FT_10_2_13' : goodB' 2 (kid' (rootAt' false true 10) 2 13) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FT_10_2_13_0, lwcertB_onekid _ _ chc_FT_10_2_13_1 chd_FT_10_2_13_1_0, lwcertB_nokids _ _ chc_FT_10_2_13_2, lwcertB_nokids _ _ chc_FT_10_2_13_3])
theorem chs_FT_10_2' (l : ℕ) (hl : l < 14) : goodB' 2 (kid' (rootAt' false true 10) 2 l) = true := by
  match l, hl with
  | 0, _ => exact ch_FT_10_2_0'
  | 1, _ => exact ch_FT_10_2_1'
  | 2, _ => exact ch_FT_10_2_2'
  | 3, _ => exact ch_FT_10_2_3'
  | 4, _ => exact ch_FT_10_2_4'
  | 5, _ => exact ch_FT_10_2_5'
  | 6, _ => exact ch_FT_10_2_6'
  | 7, _ => exact ch_FT_10_2_7'
  | 8, _ => exact ch_FT_10_2_8'
  | 9, _ => exact ch_FT_10_2_9'
  | 10, _ => exact ch_FT_10_2_10'
  | 11, _ => exact ch_FT_10_2_11'
  | 12, _ => exact ch_FT_10_2_12'
  | 13, _ => exact ch_FT_10_2_13'
  | n + 14, h => omega
theorem root_FT_10' : goodB' 3 (rootAt' false true 10) = true := by
  have h : (cands (rootAt' false true 10).g).length = 3 ∧ ∀ j < 3, kidsOk' (rootAt' false true 10) j = true ∧ (kids' (rootAt' false true 10) j).length = 14 := by decide +kernel
  apply goodB'_succ_of 2 _ 3 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have hl' : l < 14 := (h.2 j hj).2 ▸ hl
  match j, hj with
  | 0, _ => exact chs_FT_10_0' l hl'
  | 1, _ => exact chs_FT_10_1' l hl'
  | 2, _ => exact chs_FT_10_2' l hl'
  | n + 3, h => omega
theorem cert_FT' : (rootInfo' false true).1 = true ∧ (rootInfo' false true).2.length = 11 ∧ ∀ i < 11, goodB' 3 (rootAt' false true i) = true := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro i hi
  match i, hi with
  | 0, _ => exact root_FT_0'
  | 1, _ => exact root_FT_1'
  | 2, _ => exact root_FT_2'
  | 3, _ => exact root_FT_3'
  | 4, _ => exact root_FT_4'
  | 5, _ => exact root_FT_5'
  | 6, _ => exact root_FT_6'
  | 7, _ => exact root_FT_7'
  | 8, _ => exact root_FT_8'
  | 9, _ => exact root_FT_9'
  | 10, _ => exact root_FT_10'
  | n + 11, h => omega


/-- **The kernel certificate**: for `k = false` and both `s`, all leaf properties hold at the root and every below-target root
term has a height-`3` AND-tree certificate (every candidate, every family, every partition term). -/
theorem cert_all' : ∀ s, (rootInfo' false s).1 = true ∧ (rootInfo' false s).2.all (goodB' 3) = true := by
  intro s
  have key : ∀ (c : Bool × List MNode), c.1 = true → c.2.length = 11 → (∀ i < 11, goodB' 3 (c.2.getD i default) = true) →
      c.1 = true ∧ c.2.all (goodB' 3) = true := by
    intro c h1 h2 h3
    refine ⟨h1, all_of_getD _ _ ?_⟩
    rw [h2]; exact h3
  cases s
  · exact key _ cert_FF'.1 cert_FF'.2.1 cert_FF'.2.2
  · exact key _ cert_FT'.1 cert_FT'.2.1 cert_FT'.2.2

#print axioms cert_FT'
#print axioms cert_all'

end RBM.Graph.LWCert
