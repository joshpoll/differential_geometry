import order.filter analysis.topology.continuity analysis.real .normed_space

local notation f ` →_{`:50 a `} `:0 b := filter.tendsto f (nhds a) (nhds b)


variables {k : Type*} [normed_field k] 
variables {E : Type*}  [normed_space k E] 
variables {F : Type*} [normed_space k F]
variables {G : Type*} [normed_space k G]

include k
def is_ptws_cont (f : E → F) (a : E) := f →_{a} (f a)
-- TODO: pointwise continuous everywhere ↔ continuous
