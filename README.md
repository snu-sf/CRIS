# Contextual Refinement with Imaginary Specifications (CRIS)

## Development environment
The current CRIS source checkout uses Rocq 9.0. The opam setup pins `coq` to
9.0.0, and the locked Nix flake selects Rocq 9.0.1 via `pkgs.coq_9_0`.
Use either of the following options to install dependencies.

### Using opam
Requirement: opam (>=2.0.0) with an active switch.
```
./configure
```

### Using nix flake
Requirement: nix with flake enabled
```
nix develop
```

## Build
Build the project
```
make -j
```

## Contributing
Submit pull requests against the `master` branch.

Before requesting review:
- Rebase the branch to remove `WIP`, `fixup`, and other incidental commits.
- Keep each commit focused on one logical change.
- Add user-visible changes to the `Unreleased` section of
  [`CHANGELOG.md`](CHANGELOG.md).
- Ensure the project builds successfully.

Accepted pull requests preserve their individual commits rather than being
squashed, so the commit history should be ready for publication.
