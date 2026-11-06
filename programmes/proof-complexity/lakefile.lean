import Lake
open Lake DSL

package programme

@[default_target]
lean_lib Programme where
  globs := #[.one `Programme, .submodules `Programme]
