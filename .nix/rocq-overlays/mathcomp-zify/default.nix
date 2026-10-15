{
  lib,
  mkRocqDerivation,
  coq,
  mathcomp-boot,
  mathcomp-fingroup,
  mathcomp-algebra,
  stdlib,
  version ? null,
}:

mkRocqDerivation {
  namePrefix = [
    "mathcomp"
  ];
  pname = "zify";
  repo = "mczify";
  owner = "math-comp";
  inherit version;

  defaultVersion = "1.7.0+2.4+9.0";

  release."1.0.0+1.12+8.13".sha256 = "1j533vx6lacr89bj1bf15l1a0s7rvrx4l00wyjv99aczkfbz6h6k";
  release."1.1.0+1.12+8.13".sha256 = "1plf4v6q5j7wvmd5gsqlpiy0vwlw6hy5daq2x42gqny23w9mi2pr";
  release."1.3.0+1.12+8.13".sha256 = "sha256-ebfY8HatP4te44M6o84DSLpDCkMu4IroPCy+HqzOnTE=";
  release."1.5.0+2.0+8.16".sha256 = "sha256-boBYGvXdGFc6aPnjgSZYSoW4kmN5khtNrSV3DUv9DqM=";
  release."1.6.0+2.3+8.18".sha256 = "sha256-rI5ZWtgO0a2sxCVChTdASxWxhgYEbM4OhC0dnSMRzZ8=";
  release."1.7.0+2.4+9.0".sha256 = "sha256-rI5ZWtgO0a2sxCVChTdASxWxhgYEbM4OhC0dnSMRzZ8=";

  propagatedBuildInputs = [
    mathcomp-boot
    mathcomp-algebra
    mathcomp-fingroup
    stdlib
  ];

  meta = {
    description = "Micromega tactics for Mathematical Components";
    maintainers = with lib.maintainers; [ cohencyril ];
  };
}
