# contract-materialx-shaders-lean

A Lean 4 model of physically based, toon and vector shaders, all expressed as MaterialX node graphs.

## What it is for

It formalizes toon shading ramps, exact-coverage vector rendering with a signed-distance-field fallback, the mapping between glTF materials and MaterialX, and a bounded instance-splatting primitive, so the whole shading pipeline stays portable as MaterialX.

## Building and running

```sh
lake build
```

## Licence

MIT. See [LICENSE](LICENSE).
