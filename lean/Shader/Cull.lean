/-!
# Cull — occlusion culling of composited layers (the pack-time CSG rule)

A key is a paint-ordered list of layers (bottom first), each a function from a point to a
premultiplied colour. The renderer composites source-over. The pack-time rule drops a layer from a
grid cell when an opaque layer above it covers the whole cell (a CSG test: cell minus the union of
the opaque cover is empty). This file proves the rule leaves the composite unchanged at every point
of the cell, over exact rationals (floats do not obey the algebra), and shows by a counterexample
that a layer under a cover that is only partly opaque cannot be dropped.
-/

namespace Shader.Cull

/-- A premultiplied RGBA colour. -/
structure Px where
  r : Rat
  g : Rat
  b : Rat
  a : Rat
  deriving Repr, DecidableEq

def Px.clear : Px := ⟨0, 0, 0, 0⟩

/-- Source-over: `s` painted on top of `d`, premultiplied. -/
def over (s d : Px) : Px :=
  ⟨s.r + d.r * (1 - s.a), s.g + d.g * (1 - s.a), s.b + d.b * (1 - s.a), s.a + d.a * (1 - s.a)⟩

/-- Composite a paint-ordered stack (bottom first) onto clear. -/
def composite (stack : List Px) : Px :=
  stack.foldl (fun acc l => over l acc) Px.clear

/-- An opaque source hides whatever is under it. -/
theorem over_opaque (s d : Px) (h : s.a = 1) : over s d = s := by
  cases s
  simp only at h
  subst h
  simp [over, Rat.sub_self, Rat.mul_zero, Rat.add_zero]

/-- Folding from any start over a stack whose first layer is opaque gives the same result. -/
theorem foldl_opaque_head (top : Px) (above : List Px) (h : top.a = 1) (x y : Px) :
    (top :: above).foldl (fun acc l => over l acc) x =
    (top :: above).foldl (fun acc l => over l acc) y := by
  simp [List.foldl, over_opaque top x h, over_opaque top y h]

/-- **Cull rule, pointwise.** Every layer below an opaque layer can be dropped. -/
theorem composite_cull (below above : List Px) (top : Px) (h : top.a = 1) :
    composite (below ++ top :: above) = composite (top :: above) := by
  unfold composite
  rw [List.foldl_append]
  exact foldl_opaque_head top above h _ _

/-- Layers as fields over points of type `P`. -/
def at_ {P : Type} (ls : List (P → Px)) (p : P) : List Px := ls.map (fun l => l p)

/-- **Cull rule, per cell.** If `top` is opaque at every point of the cell, the layers under it
can be dropped from that cell's list: the composite agrees at every point of the cell. -/
theorem cell_cull {P : Type} (cell : P → Prop) (below above : List (P → Px)) (top : P → Px)
    (cover : ∀ p, cell p → (top p).a = 1) :
    ∀ p, cell p → composite (at_ (below ++ top :: above) p) = composite (at_ (top :: above) p) := by
  intro p hp
  simp only [at_, List.map_append, List.map_cons]
  exact composite_cull _ _ _ (cover p hp)

/-- **Control.** A cover at alpha 1/2 does not hide the layer under it: dropping it changes the
composite, so the CSG test must use only fully opaque cover. -/
theorem partial_cover_not_cullable :
    composite [⟨1, 0, 0, 1⟩, ⟨0, 0, 1/2, 1/2⟩] ≠ composite [⟨0, 0, 1/2, 1/2⟩] := by
  decide +kernel

end Shader.Cull
