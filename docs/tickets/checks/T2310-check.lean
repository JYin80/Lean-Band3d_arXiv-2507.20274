-- T2310 stage-0 check
import RBM3D.Induction.QEndB1

namespace RBM.Gauss.Sizes
#check @STXiBootPT'   -- new pin
#check @STOeqQtPT'    -- new pin
end RBM.Gauss.Sizes

namespace RBM.Ind
#check @stOeqQtPT'_holds  -- ∀ d, STOeqQtPT' d
end RBM.Ind
