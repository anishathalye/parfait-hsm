# Parfait (SOSP'24)

This repository contains / links to three parts: verification of IPR theory,
verification of software, and verification of hardware.

Note: this repository is currently being refactored to split out the software verification framework into https://github.com/anishathalye/starling, merge Knox2 with the main Knox release at https://github.com/anishathalye/knox, and have a Docker image and nicer build scripts for the verified HSMs in this repo. If you're planning to write code on top of this research (as others have done on top of Knox 1.0), we suggest you contact Anish (aathalye@mit.edu) to check in on the status of this refactor.

## Virtual Machine

For easier setup, you can use the provided virtual machine: [x.anish.io/parfait-vm.tar.gz](https://x.anish.io/parfait-vm.tar.gz). The VM already has all dependencies and tools installed. We provide a `.qcow2` image (for a Debian 12 machine), along with a `.xml` file you can [use with libvirt](https://chatgpt.com/share/06960c56-0232-4973-95ce-f59a0b08d548). If you would like to use SSH to connect to this machine, it has sshd running. The user account is `parfait` and the password is `parfait`. We've already cloned this repository, in `~/src/parfait-hsm`.

## IPR Theory

We've formalized the theory of IPR in a self-contained repository. You can find it here: <https://github.com/anishathalye/ipr>.

Running the code in the repo requires the [Coq Proof Assistant](https://coq.inria.fr/). Once you have it installed, you can run `make` to check the proofs. We also have this running in CI, so you can also see the verification output there. For example, <https://github.com/anishathalye/ipr/actions/runs/10430773540/job/28889703561#step:4:498>.

## Software

See the two applications (PasswordHasher and ECDSA) in `software`.

You can cd into the appropriate directory and run `make` to build. You'll see messages that say all verification conditions have been discharged successfully, and it'll produce the C files in `dist/`.

### Dependencies

- Install F\* using the [Everest script](https://fstarlang.github.io/lowstar/html/Setup.html#installing-the-tools). Set your `$FSTAR_HOME` and `$KRML_HOME` appropriately.
- Use [this fork of hacl-star](https://github.com/anishathalye/hacl-star), branch `parfait`. It makes a small change to change a return value from a bool to a uint32 mask.

## Hardware

There are 2 x 2 directories in `hardware/hsms`, one for each combination of software and hardware.

You can cd into `proof` and run `racket correctness.rkt` to run the proof check. The password hasher should verify in about 10 minutes. ECDSA takes 100+ hours.

You can run `racket security.rkt` to run the security proof; this one takes longer than the correctness proof. The proof checker returns a zero exit code upon success; if there's a failure, it'll print a failure message along with returning a non-zero exit code.

We've committed some of the binaries (such as the CompCert JSON output, and the `hsm.smt2` Yosys output), if you want to re-use those and just run the verification, rather than building them yourself. If you'd like to build them yourself, you can `cd spec; make` to build the CompCert JSON files, and `cd proof; make` to build the `hsm.rkt` circuit representation.

Note that some of the proofs depend on the compiler output, so if you use a different version of the compiler, you will have to adjust those proofs.

### Dependencies

#### Required

Install these to run the verification scripts.

- [Racket]
- [Rosette]
- Use Knox2, the version of knox in this repo: you can go into `hardware/knox` and run `raco pkg install --auto` to install it.

#### Optional

Install these if you want to compile the firmware from the C sources, or if you want to extract the Yosys SMT-LIB output from the Verilog.

- [RISC-V compiler toolchain]
- [Yosys]
- [sv2v]
- [bin2coe]
- Use [this fork of CompCert](https://github.com/anishathalye/CompCert), which adds functionality to dump a JSON AST of the Asm for RISC-V. Configure it with `./configure -toolprefix riscv32-unknown-elf- rv32-linux`.

[RISC-V compiler toolchain]: https://github.com/riscv/riscv-gnu-toolchain
[Yosys]: https://github.com/YosysHQ/yosys
[Racket]: https://racket-lang.org/
[Rosette]: https://github.com/emina/rosette
[bin2coe]: https://github.com/anishathalye/bin2coe
[sv2v]: https://github.com/zachjs/sv2v
