-- T2311 pre-release check file
-- Dispatcher V1 (session_01RThagGKa4jNgUEWeKViyyg); Wed Oct 7 07:14 UTC 2026
-- Gate: LW-14e-3 (Sim)
-- Branch t/T2311; new file RBM3D/Graph/LWExpSim.lean

import RBM3D.Graph.LWExpTerm5
import RBM3D.Graph.LWExpCert

-- Section 1: dependency checks (verify merged names are accessible)
open RBM.Gauss.Sizes in
#check @MNode
open RBM.Gauss.Sizes in
#check @cMerge
open RBM.Gauss.Sizes in
#check @cPartition
open RBM.Gauss.Sizes in
#check @Cand
open RBM.Gauss.Sizes in
#check @cands
open RBM.Gauss.Sizes in
#check @fams
open RBM.Gauss.Sizes in
#check @renum
open RBM.Gauss.Sizes in
#check @labsOf
open RBM.Gauss.Sizes in
#check @partitionX
open RBM.Gauss.Sizes in
#check @pcomp
open RBM.Gauss.Sizes in
#check @RCand
open RBM.Gauss.Sizes in
#check @RCand.kids
open RBM.Gauss.Sizes in
#check @lwSplitLoopsX_spec
open RBM.Gauss.Sizes in
#check @val_eq_partitionX

-- Section 2: pins for T2311 (from probe bridge section)
-- These must compile after T2311 is written

section T2311Check
open RBM.Gauss.Sizes in
#check @Rel           -- simulation relation: MNode → PGraph (Fin 2) → Prop
open RBM.Gauss.Sizes in
#check @MNode.toP     -- model node as PGraph (Fin 2)
open RBM.Gauss.Sizes in
#check @Cand.toR      -- model Cand → RCand (N.toP h)
open RBM.Gauss.Sizes in
#check @cPartitionX   -- model partition with exponents
open RBM.Gauss.Sizes in
#check @famsX         -- model families with exponents
open RBM.Gauss.Sizes in
#check @childrenX     -- model children with exponents
open RBM.Gauss.Sizes in
#check @PartitionSim  -- Bridge 1 proposition
open RBM.Gauss.Sizes in
#check @ChildrenSim   -- Bridge 2 proposition
open RBM.Gauss.Sizes in
#check @partitionSim  -- : PartitionSim (proved)
open RBM.Gauss.Sizes in
#check @childrenSim   -- : ChildrenSim (proved)
end T2311Check
