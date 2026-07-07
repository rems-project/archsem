# POPL27 submission branch

This file records the provenance of changes carried by the `popl27-submission`
branch on top of `origin/main`. The branch is maintained as a single squash
commit; PR/source provenance is authoritative here, not per-change local commit
IDs.

Base:

- `9a1aa048` (`fix(Isla): Keep zero PTEs (#193)`)

Included PRs:

| Order | PR | Source branch/ref | Source commit | Summary |
| ---: | --- | --- | --- | --- |
| 1 | [#204](https://github.com/rems-project/archsem/pull/204) | `origin/fix/tlbi-va` | `98426fe` | Match TLBI VA against wide blocks. |
| 2 | [#188](https://github.com/rems-project/archsem/pull/188) | `origin/fix/vmp-fault-ordering` | `abdfa32` | Remove acquire/release fault ordering in VMPromising. |
| 3 | [#202](https://github.com/rems-project/archsem/pull/202) | `origin/promising-vm-rmw` | `133d269` | Support atomic RMW pairs in VMPromising. |
| 4 | [#175](https://github.com/rems-project/archsem/pull/175) | `origin/fix/arm-exclusive-forwarding` | `a23e2e0` | Track exclusive forwarding views precisely. |
| 5 | [#189](https://github.com/rems-project/archsem/pull/189) | `origin/vmp-snapshot-ranges` | `290c5e5` | Track translation snapshot ranges in VMPromising. |
| 6 | [#203](https://github.com/rems-project/archsem/pull/203) | `origin/fix/vaddr-translation-start-strict` | `e273378` | Include strict view in translation start. |
| 7 | [#190](https://github.com/rems-project/archsem/pull/190) | `origin/fix/vmp-va-coherence` | `7d67c41` | Enforce VA translation coherence across the translated access footprint. |
| 8 | [#206](https://github.com/rems-project/archsem/pull/206) | `origin/fix/isla-negative-location-init` | `eb51fc7` | Support negative location initializers in Isla. |
| 9 | None | `origin/fix-archstate-register-defaults` | `104eb55` | Apply register defaults when running ArchSem-format tests directly. |

Support files:

| Order | PR | Source/ref | Files | Summary |
| ---: | --- | --- | --- | --- |
| 1 | None | Local support files | `config/Arm-vm.toml`, `config/Arm-vm-ets2.toml`, `config/Arm-vm-ets3.toml` | Add VM and ETS config files used for notes047 reruns. |
| 2 | None | `origin/update-sail-tiny-arm-version` / `df17b3f` | `coq-archsem-arm.opam.locked` | Update the Sail Tiny Arm pin used by the submission branch. |
