import Lake
open Lake DSL

package bitstring where
  packagesDir := "/tmp/lean4-bitstring/packages"
  buildDir := "/tmp/lean4-bitstring/build"
  -- add package configuration options here

@[default_target]
lean_lib BitString where
  srcDir := "src"

@[default_target]
lean_exe Tests where
  srcDir := "tests"

require batteries from git "https://github.com/leanprover-community/batteries" @ "13f9b00769bdac2c0041406a6c2524a361e8d660"
