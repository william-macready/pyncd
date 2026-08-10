import Jax

def bridgeSmokeNet : NetSpec where
  name := "LeanNCD-JAX-Bridge-Smoke"
  imageH := 1
  imageW := 2
  layers := [
    .dense 2 3 .relu,
    .dense 3 1 .identity
  ]

def bridgeSmokeConfig : TrainConfig where
  learningRate := 0.001
  batchSize := 1
  epochs := 1

#eval bridgeSmokeNet.validate!

def main (args : List String) : IO Unit := do
  let output := args.head?.getD "generated_bridge_smoke.py"
  let code := JaxCodegen.generate bridgeSmokeNet bridgeSmokeConfig .mnist "unused"
  IO.FS.writeFile output code
  IO.println s!"Generated {output}"
