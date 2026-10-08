theorem ballot_secrecy
    (hsize : negligible (fun n => noncePointBound (ZMod (q n))))
    (hmain : MainReductionEfficient A.prepared A.representation)
    (hreject : RejectionReductionEfficient A.prepared A.representation)
    (hddh : DDHAssumption (q := q) A.representation A.generator) :
    negligible (fun n => ENNReal.ofReal (A.bias n))
