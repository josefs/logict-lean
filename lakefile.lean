import Lake
open Lake DSL

package «logict» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «LogicT» where
  srcDir := "."
