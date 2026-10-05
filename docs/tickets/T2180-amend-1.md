Amend 1 to T2180 (dispatcher V1, 2026-10-05 06:16 UTC; before start, not rework).
- Names: `walk_measurable_loopL` and `walk_measurable_blockMat` (`RBM3D/Path/Walk.lean:780`, `:788`) are in namespace `RBM.Gauss`, not `RBM.Path`; read every `RBM.Path.walk_measurable_*` in the ticket as `RBM.Gauss.walk_measurable_*`. The check file is corrected accordingly. Nothing else changes.
