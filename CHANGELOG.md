# Changelog

This file records notable changes to CRIS starting with the `v2026-07-22`
release.

## Unreleased

- rename: `closed_adequacy` -> `ISim_closed_adequacy`
- add `gsim_closed_adequacy`, `lsim_closed_adequacy`
- move `theories/simulations/filter` to `theories/filter`
- Add `Beh : Mod.t -> Tr.t -> iProp Σ`
- Redefine `refines` using `Beh`. This new definition is equivalent to the old one.
- change extraction setting of `SchI.choose_index` in `ExtrOcamlCRIS.v`
- optimize function lookup and post-inline normalization in `cStartFunSim`
  and `cInlineS`/`cInlineT`
- add a goal-local fast path to `solve_msk` while preserving its existing
  fallback
- make certificate-based function lookup expose module aliases structurally
  and fail fast on unsupported map combinators before the `simpl_map`
  fallback; custom lookup instances must also be registered in the
  `fnsem_lookup` hint database
- restore certificate lookup for dependent function-body maps in the opaque
  `fnsem_lookup` hint database
- keep recursive function-lookup certificate search inside its opaque hint
  database so unsupported module maps reach the `simpl_map` fallback
- reduce `SMod` function-map projections during certificate lookup so
  structured modules keep using the fast path
- replace Helping's client-visible request state with a resource-only
  `HelpPend`/`HelpDone` protocol and make `HelpingOn.try_run` request-ID-only
- add nested `IstHelp` transport and `helping_main_filtered` for client
  composition
- make `sYields` require progress and `sYield` introduce fresh continuation
  states atomically
- add an Iris-compatible proof mode for `BiProset` entailments, with a third
  tensor context and the `jStartProof`, `jStopProof`, `jIntros`, `jDestruct`,
  `jPoseProof`, `jAssert`, `jSplitL`, `jSplitR`, `jApply`, `jFrame`, and
  `jUnitIntro` tactics
- Remove legacy tactics for `ctx_refines` composition. (`ctxr_refl`,
  `ctxr_transL`, `ctxr_transR`, `ctxr_norm`, `ctxr_swap`, `ctxr_rotate`,
  `ctxr_drop`)

## 2026-07-22

### Added

- Published the first versioned release of CRIS.
- Added opam package metadata and installation through `./configure`.
