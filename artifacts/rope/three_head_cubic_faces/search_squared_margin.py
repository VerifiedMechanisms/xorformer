"""Squared-hinge continuation of the 102-point pure-three search."""
from pathlib import Path
import sys
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'four_head_middle'))
import search_fixed_denominator_lp as lp
import search_fixed_denominator_qp as qp
from search_fixed_pattern import pattern

if __name__ == '__main__':
    z,y=pattern()
    for module in [lp,qp]:
        module.Z,module.Y=z,y
        module.X=np.c_[np.ones(len(z)),z]
        module.N,module.H=11,3
        module.NV=module.H*(module.N+1)
        module.ELL,module.K,module.BASE=module.NV,module.NV+module.H,module.NV+2*module.H
    qp.main()
