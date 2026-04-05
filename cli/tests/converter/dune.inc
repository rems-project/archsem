
(subdir arm/seq
 (rule
  (deps ../../../arm/seq/EOR.archsem.toml)
  (targets EOR.archsem.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/arm/seq/EOR.archsem.toml arm/seq/EOR.archsem.toml)))


(subdir arm/seq
 (rule
  (deps ../../../arm/seq/EOR.litmus.toml)
  (targets EOR.litmus.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/arm/seq/EOR.litmus.toml arm/seq/EOR.litmus.toml)))


(subdir arm/seq
 (rule
  (deps ../../../arm/seq/NOP+mem.archsem.toml)
  (targets NOP+mem.archsem.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/arm/seq/NOP+mem.archsem.toml arm/seq/NOP+mem.archsem.toml)))


(subdir arm/um
 (rule
  (deps ../../../arm/um/MP+dmbs-unobservable.archsem.toml)
  (targets MP+dmbs-unobservable.archsem.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/arm/um/MP+dmbs-unobservable.archsem.toml arm/um/MP+dmbs-unobservable.archsem.toml)))


(subdir arm/um
 (rule
  (deps ../../../arm/um/MP+dmbs.archsem.toml)
  (targets MP+dmbs.archsem.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/arm/um/MP+dmbs.archsem.toml arm/um/MP+dmbs.archsem.toml)))


(subdir arm/um
 (rule
  (deps ../../../arm/um/MP+dmbs.litmus.toml)
  (targets MP+dmbs.litmus.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/arm/um/MP+dmbs.litmus.toml arm/um/MP+dmbs.litmus.toml)))


(subdir arm/um
 (rule
  (deps ../../../arm/um/MP.archsem.toml)
  (targets MP.archsem.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/arm/um/MP.archsem.toml arm/um/MP.archsem.toml)))


(subdir arm/um
 (rule
  (deps ../../../arm/um/MP.litmus.toml)
  (targets MP.litmus.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/arm/um/MP.litmus.toml arm/um/MP.litmus.toml)))


(subdir arm/vm
 (rule
  (deps ../../../arm/vm/BBMSuccess.archsem.toml)
  (targets BBMSuccess.archsem.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/arm/vm/BBMSuccess.archsem.toml arm/vm/BBMSuccess.archsem.toml)))


(subdir arm/vm
 (rule
  (deps ../../../arm/vm/LDRPT+NoBBM.archsem.toml)
  (targets LDRPT+NoBBM.archsem.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/arm/vm/LDRPT+NoBBM.archsem.toml arm/vm/LDRPT+NoBBM.archsem.toml)))


(subdir arm/vm
 (rule
  (deps ../../../arm/vm/MP+VM.archsem.toml)
  (targets MP+VM.archsem.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/arm/vm/MP+VM.archsem.toml arm/vm/MP+VM.archsem.toml)))


(subdir arm/vm
 (rule
  (deps ../../../arm/vm/STRLDR+VM.archsem.toml)
  (targets STRLDR+VM.archsem.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/arm/vm/STRLDR+VM.archsem.toml arm/vm/STRLDR+VM.archsem.toml)))


(subdir x86/seq
 (rule
  (deps ../../../x86/seq/XOR.archsem.toml)
  (targets XOR.archsem.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/x86/seq/XOR.archsem.toml x86/seq/XOR.archsem.toml)))


(subdir x86/seq
 (rule
  (deps ../../../x86/seq/XOR.litmus.toml)
  (targets XOR.litmus.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/x86/seq/XOR.litmus.toml x86/seq/XOR.litmus.toml)))


(subdir x86/um
 (rule
  (deps ../../../x86/um/IRIW.archsem.toml)
  (targets IRIW.archsem.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/x86/um/IRIW.archsem.toml x86/um/IRIW.archsem.toml)))


(subdir x86/um
 (rule
  (deps ../../../x86/um/IRIW.litmus.toml)
  (targets IRIW.litmus.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/x86/um/IRIW.litmus.toml x86/um/IRIW.litmus.toml)))


(subdir x86/um
 (rule
  (deps ../../../x86/um/MP.archsem.toml)
  (targets MP.archsem.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/x86/um/MP.archsem.toml x86/um/MP.archsem.toml)))


(subdir x86/um
 (rule
  (deps ../../../x86/um/MP.litmus.toml)
  (targets MP.litmus.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/x86/um/MP.litmus.toml x86/um/MP.litmus.toml)))


(subdir x86/um
 (rule
  (deps ../../../x86/um/R_PO_MFENCE.archsem.toml)
  (targets R_PO_MFENCE.archsem.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/x86/um/R_PO_MFENCE.archsem.toml x86/um/R_PO_MFENCE.archsem.toml)))


(subdir x86/um
 (rule
  (deps ../../../x86/um/R_PO_MFENCE.litmus.toml)
  (targets R_PO_MFENCE.litmus.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/x86/um/R_PO_MFENCE.litmus.toml x86/um/R_PO_MFENCE.litmus.toml)))


(subdir x86/um
 (rule
  (deps ../../../x86/um/SB.archsem.toml)
  (targets SB.archsem.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/x86/um/SB.archsem.toml x86/um/SB.archsem.toml)))


(subdir x86/um
 (rule
  (deps ../../../x86/um/SB.litmus.toml)
  (targets SB.litmus.toml)
  (action
   (run archsem convert %{deps} -o %{targets}))))

(rule
 (alias runtest)
 (action
  (diff expect/x86/um/SB.litmus.toml x86/um/SB.litmus.toml)))

