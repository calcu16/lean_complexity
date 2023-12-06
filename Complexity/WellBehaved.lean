import Complexity.Asymptotic
import Complexity.Basic

namespace Complexity

class WellBehaved (m: Model) where
  von_neumann: m.Data = m.Result
  bool_encoding: Encoding Bool m.Data
  prod_encoding: (α: Type _) → (β: Type _) → [Encoding α m.Data] → [Encoding β m.Data] → Encoding (α × β) m.Data
  const_prod_mk: (α: Type _) → (β: Type _) → [Encoding α m.Data] → [Encoding β m.Data] → Constant m (Prod.mk α β)
  const_prod_fst: (α: Type _) → (β: Type _) → [Encoding α m.Data] → [Encoding β m.Data] → Constant m (@Prod.fst α β)
  const_prod_snd: (α: Type _) → (β: Type _) → [Encoding α m.Data] → [Encoding β m.Data] → Constant m (@Prod.snd α β)


instance (m: Model) [wb: WellBehaved m]:
  Encoding Bool m.Data := wb.bool_encoding

instance (m: Model) [wb: WellBehaved m] (α: Type _) [Encoding α m.Data] (β: Type _) [Encoding β m.Data]:
  Encoding (α × β) m.Data := wb.prod_encoding α β


end Complexity