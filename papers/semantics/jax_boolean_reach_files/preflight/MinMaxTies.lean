import LeanNCD.Eval.Error
open LeanNCD.Eval
#eval [(minNaN 0.0 (-0.0)).toBits, (minNaN (-0.0) 0.0).toBits, (maxNaN 0.0 (-0.0)).toBits, (maxNaN (-0.0) 0.0).toBits]
#eval [(minNaN32 (0.0 : Float32) (-0.0)).toBits, (minNaN32 (-0.0 : Float32) 0.0).toBits, (maxNaN32 (0.0 : Float32) (-0.0)).toBits, (maxNaN32 (-0.0 : Float32) 0.0).toBits]
#eval [(minNaN (0.0/0.0) 1.0).isNaN, (minNaN 0.0 (0.0/0.0)).isNaN, (maxNaN 1.0 (0.0/0.0)).isNaN]
